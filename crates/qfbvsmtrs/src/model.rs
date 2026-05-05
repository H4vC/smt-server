use crate::blast::BlastedVariable;
use crate::error::{Error, Result};
use crate::ir::{bytes_for_width, mask_unused_high_bits, Sort, TermId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarValue {
    Bool(bool),
    Bv { width: u32, bytes: Vec<u8> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModelEntry {
    pub term: TermId,
    pub name: String,
    pub external: Option<u32>,
    pub value: ScalarValue,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Model {
    pub entries: Vec<ModelEntry>,
}

impl Model {
    pub fn get(&self, name: &str) -> Option<&ScalarValue> {
        self.entries
            .iter()
            .find(|entry| entry.name == name)
            .map(|entry| &entry.value)
    }
}

pub fn build_model(variables: &[BlastedVariable], assignment: &[bool]) -> Result<Model> {
    let mut entries = Vec::with_capacity(variables.len());
    for variable in variables {
        let value = match variable.sort {
            Sort::Bool => {
                let gate = variable.bits[0];
                ScalarValue::Bool(gate_value(assignment, gate)?)
            }
            Sort::Bv(width) => {
                let mut bytes = vec![0u8; bytes_for_width(width)?];
                for (bit, gate) in variable.bits.iter().enumerate() {
                    if gate_value(assignment, *gate)? {
                        bytes[bit / 8] |= 1 << (bit % 8);
                    }
                }
                mask_unused_high_bits(&mut bytes, width);
                ScalarValue::Bv { width, bytes }
            }
        };
        entries.push(ModelEntry {
            term: variable.term,
            name: variable.name.clone(),
            external: variable.external,
            value,
        });
    }
    Ok(Model { entries })
}

pub fn scalar_to_smt(value: &ScalarValue) -> String {
    match value {
        ScalarValue::Bool(false) => "false".to_owned(),
        ScalarValue::Bool(true) => "true".to_owned(),
        ScalarValue::Bv { width, bytes } => {
            let mut out = String::with_capacity(*width as usize + 2);
            out.push_str("#b");
            for bit in (0..*width).rev() {
                let byte = bytes[(bit / 8) as usize];
                out.push(if ((byte >> (bit % 8)) & 1) != 0 {
                    '1'
                } else {
                    '0'
                });
            }
            out
        }
    }
}

fn gate_value(assignment: &[bool], gate: crate::gates::GateId) -> Result<bool> {
    assignment.get(gate.index()).copied().ok_or_else(|| {
        Error::internal(format!(
            "missing SAT assignment for gate {} ({} values)",
            gate.raw(),
            assignment.len()
        ))
    })
}
