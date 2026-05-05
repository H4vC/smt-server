use std::time::Instant;

use crate::blast::blast_query;
use crate::cnf;
use crate::config::Config;
use crate::error::{Error, Result};
use crate::ir::{NodeKind, Sort};
use crate::model::{build_model, Model, ScalarValue};
use crate::query::{Assertion, Command, Query};
use crate::sat::{solve_cnf, SatResult};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveStatus {
    Sat,
    Unsat,
    Unknown,
    Ok,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolveResult {
    pub status: SolveStatus,
    pub model: Option<Model>,
    pub core: Option<Vec<String>>,
    pub optimum: Option<ScalarValue>,
    pub message: Option<String>,
}

impl SolveResult {
    pub fn sat(model: Option<Model>) -> Self {
        Self {
            status: SolveStatus::Sat,
            model,
            core: None,
            optimum: None,
            message: None,
        }
    }

    pub fn unsat() -> Self {
        Self {
            status: SolveStatus::Unsat,
            model: None,
            core: None,
            optimum: None,
            message: None,
        }
    }

    pub fn sat_optimization(optimum: ScalarValue, model: Option<Model>) -> Self {
        Self {
            status: SolveStatus::Sat,
            model,
            core: None,
            optimum: Some(optimum),
            message: None,
        }
    }

    pub fn unknown(message: impl Into<String>) -> Self {
        Self {
            status: SolveStatus::Unknown,
            model: None,
            core: None,
            optimum: None,
            message: Some(message.into()),
        }
    }

    pub fn ok() -> Self {
        Self {
            status: SolveStatus::Ok,
            model: None,
            core: None,
            optimum: None,
            message: None,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Solver {
    config: Config,
}

impl Solver {
    pub fn new(config: Config) -> Self {
        Self { config }
    }

    pub fn config(&self) -> &Config {
        &self.config
    }

    pub fn solve(&mut self, query: &Query) -> Result<SolveResult> {
        if matches!(query.command, Command::Minimize | Command::Maximize) {
            return self.optimize(query);
        }
        let mut result = self.solve_once(query, query.want_model)?;
        if result.status == SolveStatus::Unsat && query.want_core {
            result.core = Some(self.extract_named_core(query)?);
        }
        Ok(result)
    }

    fn solve_once(&self, query: &Query, want_model: bool) -> Result<SolveResult> {
        match query.command {
            Command::Simplify => return Ok(SolveResult::ok()),
            Command::Minimize | Command::Maximize => {
                return Err(Error::internal(
                    "solve_once called with optimization command",
                ))
            }
            Command::Solve => {}
        }

        let deadline = self.config.budget.map(|budget| Instant::now() + budget);
        let blasted = blast_query(query)?;
        let cnf = cnf::encode(&blasted.gates, blasted.assertion);
        let sat = solve_cnf(
            self.config.sat_backend,
            cnf.num_vars,
            cnf.clauses,
            &[],
            deadline,
        );
        match sat {
            SatResult::Sat(assignment) => {
                let model = if want_model {
                    Some(build_model(&blasted.variables, &assignment)?)
                } else {
                    None
                };
                Ok(SolveResult::sat(model))
            }
            SatResult::Unsat => Ok(SolveResult::unsat()),
            SatResult::Unknown(message) => Ok(SolveResult::unknown(message)),
        }
    }

    fn optimize(&self, query: &Query) -> Result<SolveResult> {
        let target = query
            .target
            .ok_or_else(|| Error::invalid("optimization", "missing target"))?;
        let width = match query.arena.sort(target)? {
            Sort::Bv(width) => width,
            Sort::Bool => return Err(Error::invalid("optimization", "target is not BV")),
        };
        let minimize = query.command == Command::Minimize;
        let mut fixed = query.clone();
        fixed.command = Command::Solve;
        fixed.want_model = false;
        fixed.want_core = false;
        fixed.target = None;

        match self.solve_once(&fixed, false)?.status {
            SolveStatus::Sat => {}
            SolveStatus::Unsat => return Ok(SolveResult::unsat()),
            SolveStatus::Unknown => {
                return Ok(SolveResult::unknown("optimization base query unknown"))
            }
            SolveStatus::Ok => {
                return Ok(SolveResult::unknown("optimization base query returned OK"))
            }
        }

        let mut optimum = vec![0u8; (width as usize).div_ceil(8)];
        for bit in (0..width).rev() {
            let prefer_one = match (query.signed, minimize, bit == width - 1) {
                (false, true, _) => false,
                (false, false, _) => true,
                (true, true, true) => true,
                (true, true, false) => false,
                (true, false, true) => false,
                (true, false, false) => true,
            };
            let mut trial = fixed.clone();
            assert_target_bit(&mut trial, target, bit, prefer_one)?;
            match self.solve_once(&trial, false)?.status {
                SolveStatus::Sat => {
                    fixed = trial;
                    if prefer_one {
                        set_bit(&mut optimum, bit);
                    }
                }
                SolveStatus::Unsat => {
                    assert_target_bit(&mut fixed, target, bit, !prefer_one)?;
                    if !prefer_one {
                        set_bit(&mut optimum, bit);
                    }
                }
                SolveStatus::Unknown => {
                    return Ok(SolveResult::unknown("optimization bit query unknown"))
                }
                SolveStatus::Ok => {
                    return Ok(SolveResult::unknown("optimization bit query returned OK"))
                }
            }
        }

        let model = if query.want_model {
            match self.solve_once(&fixed, true)? {
                SolveResult {
                    status: SolveStatus::Sat,
                    model,
                    ..
                } => model,
                other => {
                    return Ok(SolveResult::unknown(format!(
                        "optimization final model query returned {:?}",
                        other.status
                    )))
                }
            }
        } else {
            None
        };
        Ok(SolveResult::sat_optimization(
            ScalarValue::Bv {
                width,
                bytes: optimum,
            },
            model,
        ))
    }

    fn extract_named_core(&self, query: &Query) -> Result<Vec<String>> {
        let mut active = query
            .assertions
            .iter()
            .enumerate()
            .filter_map(|(index, assertion)| assertion.name.as_ref().map(|_| index))
            .collect::<Vec<_>>();
        let mut pos = 0;
        while pos < active.len() {
            let candidate = active[pos];
            let trial_active = active
                .iter()
                .copied()
                .filter(|&index| index != candidate)
                .collect::<Vec<_>>();
            let trial = query_with_named_subset(query, &trial_active);
            match self.solve_once(&trial, false)?.status {
                SolveStatus::Unsat => active = trial_active,
                SolveStatus::Sat | SolveStatus::Unknown | SolveStatus::Ok => pos += 1,
            }
        }
        Ok(active
            .into_iter()
            .filter_map(|index| query.assertions[index].name.clone())
            .collect())
    }
}

fn assert_target_bit(
    query: &mut Query,
    target: crate::ir::TermId,
    bit: u32,
    value: bool,
) -> Result<()> {
    let extracted = query.arena.add(
        NodeKind::BvExtract {
            child: target,
            high: bit,
            low: bit,
        },
        Sort::Bv(1),
    )?;
    let constant = query.arena.add(
        NodeKind::BvConst {
            width: 1,
            bytes: vec![u8::from(value)],
        },
        Sort::Bv(1),
    )?;
    let eq = query
        .arena
        .add(NodeKind::BvEq(extracted, constant), Sort::Bool)?;
    query.assertions.push(Assertion {
        root: eq,
        name: None,
    });
    Ok(())
}

fn set_bit(bytes: &mut [u8], bit: u32) {
    bytes[(bit / 8) as usize] |= 1 << (bit % 8);
}

fn query_with_named_subset(query: &Query, active_named_indices: &[usize]) -> Query {
    let mut trial = query.clone();
    trial.assertions = query
        .assertions
        .iter()
        .enumerate()
        .filter(|(index, assertion)| {
            assertion.name.is_none() || active_named_indices.contains(index)
        })
        .map(|(_, assertion)| assertion.clone())
        .collect();
    trial.want_model = false;
    trial.want_core = false;
    trial
}

pub fn solve_query(query: &Query, config: &Config) -> Result<SolveResult> {
    Solver::new(config.clone()).solve(query)
}

pub fn unsupported_to_unknown(result: Result<SolveResult>) -> Result<SolveResult> {
    match result {
        Err(Error::Unsupported(message)) => Ok(SolveResult::unknown(message)),
        other => other,
    }
}
