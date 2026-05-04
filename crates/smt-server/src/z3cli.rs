use std::collections::HashMap;
use std::io::Write;
use std::process::{Command, Stdio};

use smt_wire::{
    request_flags, BinaryRequest, ModelBlock, ModelEntry, ScalarValue, Sort, UnsatCoreBlock,
    WireError,
};

use crate::backend::{Backend, QueryResult};
use crate::smt2::{request_to_smt2, Smt2Variable};

/// CLI adapter for installations that provide a `z3` executable on `PATH`.
#[derive(Debug, Clone)]
pub struct Z3CliBackend {
    executable: String,
}

impl Default for Z3CliBackend {
    fn default() -> Self {
        Self {
            executable: "z3".to_owned(),
        }
    }
}

impl Z3CliBackend {
    pub fn new(executable: impl Into<String>) -> Self {
        Self {
            executable: executable.into(),
        }
    }

    pub fn is_available(&self) -> bool {
        Command::new(&self.executable)
            .arg("--version")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map(|status| status.success())
            .unwrap_or(false)
    }
}

impl Backend for Z3CliBackend {
    fn name(&self) -> &'static str {
        "z3-cli"
    }

    fn handle(&self, request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        if !matches!(
            request.envelope.command,
            smt_wire::Command::Solve | smt_wire::Command::Simplify
        ) {
            return Ok(QueryResult::unknown(
                "z3 CLI backend currently handles SOLVE/SIMPLIFY only",
            ));
        }
        if request.envelope.command == smt_wire::Command::Simplify {
            return Ok(QueryResult::ok_simplify(smt_wire::SimplifyBlock {
                expression: request.expression.clone(),
                assertion_roots: request.assertion_roots.clone(),
                named_assertion_refs: request.named_assertion_refs.clone(),
                assumption_roots: request.assumption_roots.clone(),
            }));
        }
        let smt2 = request_to_smt2(request)?;
        let mut child = match Command::new(&self.executable)
            .arg("-in")
            .arg("-smt2")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        {
            Ok(child) => child,
            Err(err) => return Ok(QueryResult::unknown(format!("failed to start z3: {err}"))),
        };
        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(smt2.script.as_bytes()).map_err(|err| {
                WireError::invalid("z3 CLI", format!("failed to write SMT-LIB: {err}"))
            })?;
        }
        let output = child
            .wait_with_output()
            .map_err(|err| WireError::invalid("z3 CLI", format!("failed to wait for z3: {err}")))?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Ok(QueryResult::unknown(format!(
                "z3 exited with error: {stderr}"
            )));
        }
        let stdout = String::from_utf8_lossy(&output.stdout);
        parse_z3_output(request, &smt2.variables, &stdout)
    }
}

fn parse_z3_output(
    request: &BinaryRequest,
    variables: &[Smt2Variable],
    stdout: &str,
) -> smt_wire::Result<QueryResult> {
    let mut lines = stdout.lines().filter(|line| !line.trim().is_empty());
    let Some(status) = lines.next().map(str::trim) else {
        return Ok(QueryResult::unknown("z3 produced no status"));
    };
    match status {
        "sat" => {
            let model = if (request.envelope.flags & request_flags::WANT_MODEL) != 0 {
                Some(parse_get_value_model(
                    lines.collect::<Vec<_>>().join("\n").as_str(),
                    variables,
                )?)
            } else {
                None
            };
            Ok(QueryResult::sat(model))
        }
        "unsat" => {
            let core = if (request.envelope.flags & request_flags::WANT_CORE) != 0 {
                Some(parse_unsat_core(
                    lines.collect::<Vec<_>>().join(" ").as_str(),
                ))
            } else {
                None
            };
            Ok(QueryResult::unsat(core))
        }
        "unknown" => Ok(QueryResult::unknown("z3 returned unknown")),
        other => Ok(QueryResult::unknown(format!(
            "unrecognized z3 status {other:?}"
        ))),
    }
}

fn parse_get_value_model(text: &str, variables: &[Smt2Variable]) -> smt_wire::Result<ModelBlock> {
    let var_by_name = variables
        .iter()
        .map(|var| (var.name.clone(), var))
        .collect::<HashMap<_, _>>();
    let sexprs = parse_output_sexprs(text);
    let mut entries = Vec::new();
    for pair in flatten_pairs(&sexprs) {
        if pair.len() != 2 {
            continue;
        }
        let name = atom_text(&pair[0]);
        let Some(var) = var_by_name.get(&name) else {
            continue;
        };
        let value = scalar_from_smt_value(&pair[1], var.sort, var.width)?;
        entries.push(ModelEntry {
            node_ref: var.node_ref,
            value,
        });
    }
    Ok(ModelBlock { entries })
}

fn parse_unsat_core(text: &str) -> UnsatCoreBlock {
    let names = parse_output_sexprs(text)
        .into_iter()
        .flat_map(|expr| match expr {
            Out::List(items) => items.into_iter().map(|item| atom_text(&item)).collect(),
            atom => vec![atom_text(&atom)],
        })
        .collect();
    UnsatCoreBlock { names }
}

fn scalar_from_smt_value(value: &Out, sort: Sort, width: u32) -> smt_wire::Result<ScalarValue> {
    match sort {
        Sort::Bool => Ok(ScalarValue::bool(matches!(
            atom_text(value).as_str(),
            "true"
        ))),
        Sort::Bv => {
            let text = atom_text(value);
            let mut bytes = vec![0u8; (width as usize).div_ceil(8)];
            if let Some(bits) = text.strip_prefix("#b") {
                for (offset, ch) in bits.chars().rev().enumerate() {
                    if ch == '1' {
                        bytes[offset / 8] |= 1 << (offset % 8);
                    }
                }
            } else if let Some(hex) = text.strip_prefix("#x") {
                for (nibble, ch) in hex.chars().rev().enumerate() {
                    let v = ch.to_digit(16).ok_or_else(|| {
                        WireError::invalid("z3 model", format!("bad hex digit {ch}"))
                    })? as u8;
                    let bit = nibble * 4;
                    bytes[bit / 8] |= v << (bit % 8);
                }
            } else {
                return Err(WireError::invalid(
                    "z3 model",
                    format!("unsupported BV literal {text}"),
                ));
            }
            ScalarValue::bv(width, bytes)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Out {
    Atom(String),
    List(Vec<Out>),
}

fn flatten_pairs(exprs: &[Out]) -> Vec<Vec<Out>> {
    let mut out = Vec::new();
    for expr in exprs {
        match expr {
            Out::List(items) if items.iter().all(|item| matches!(item, Out::List(_))) => {
                for item in items {
                    if let Out::List(pair) = item {
                        out.push(pair.clone());
                    }
                }
            }
            Out::List(pair) => out.push(pair.clone()),
            Out::Atom(_) => {}
        }
    }
    out
}

fn atom_text(expr: &Out) -> String {
    match expr {
        Out::Atom(atom) => atom.clone(),
        Out::List(items) => items.iter().map(atom_text).collect::<Vec<_>>().join(" "),
    }
}

fn parse_output_sexprs(input: &str) -> Vec<Out> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '(' | ')' => tokens.push(ch.to_string()),
            c if c.is_whitespace() => {}
            '|' => {
                let mut atom = String::new();
                for c in chars.by_ref() {
                    if c == '|' {
                        break;
                    }
                    atom.push(c);
                }
                tokens.push(atom);
            }
            c => {
                let mut atom = c.to_string();
                while let Some(&next) = chars.peek() {
                    if next.is_whitespace() || next == '(' || next == ')' {
                        break;
                    }
                    atom.push(chars.next().expect("peeked char"));
                }
                tokens.push(atom);
            }
        }
    }
    let mut pos = 0;
    let mut exprs = Vec::new();
    while pos < tokens.len() {
        if let Some(expr) = parse_one(&tokens, &mut pos) {
            exprs.push(expr);
        } else {
            break;
        }
    }
    exprs
}

fn parse_one(tokens: &[String], pos: &mut usize) -> Option<Out> {
    if *pos >= tokens.len() {
        return None;
    }
    let token = tokens[*pos].clone();
    *pos += 1;
    if token == "(" {
        let mut items = Vec::new();
        while *pos < tokens.len() && tokens[*pos] != ")" {
            items.push(parse_one(tokens, pos)?);
        }
        if *pos < tokens.len() {
            *pos += 1;
        }
        Some(Out::List(items))
    } else if token == ")" {
        None
    } else {
        Some(Out::Atom(token))
    }
}
