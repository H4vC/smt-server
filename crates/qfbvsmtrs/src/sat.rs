use std::time::Instant;

use crate::error::Error;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatResult {
    Sat(Vec<bool>), // 1-based CNF variable values are returned at index var-1
    Unsat,
    Unknown(String),
}

#[derive(Debug, Clone)]
pub struct DpllSolver {
    num_vars: usize,
    clauses: Vec<Vec<i32>>,
    scores: Vec<usize>,
    deadline: Option<Instant>,
}

impl DpllSolver {
    pub fn new(num_vars: usize, clauses: Vec<Vec<i32>>, deadline: Option<Instant>) -> Self {
        let mut scores = vec![0usize; num_vars + 1];
        for clause in &clauses {
            for &lit in clause {
                scores[lit.unsigned_abs() as usize] += 1;
            }
        }
        Self {
            num_vars,
            clauses,
            scores,
            deadline,
        }
    }

    pub fn solve(&self, assumptions: &[i32]) -> SatResult {
        let mut assignment = vec![None; self.num_vars + 1];
        for &assumption in assumptions {
            if let Err(()) = assign_lit(&mut assignment, assumption) {
                return SatResult::Unsat;
            }
        }
        match self.search(assignment) {
            Ok(Some(model)) => {
                let values = (1..=self.num_vars)
                    .map(|var| model[var].unwrap_or(false))
                    .collect();
                SatResult::Sat(values)
            }
            Ok(None) => SatResult::Unsat,
            Err(Error::Timeout) => SatResult::Unknown("budget exhausted".to_owned()),
            Err(err) => SatResult::Unknown(err.to_string()),
        }
    }

    fn search(
        &self,
        mut assignment: Vec<Option<bool>>,
    ) -> Result<Option<Vec<Option<bool>>>, Error> {
        self.check_deadline()?;
        if !self.unit_propagate(&mut assignment)? {
            return Ok(None);
        }
        if self.all_clauses_satisfied(&assignment) {
            return Ok(Some(assignment));
        }
        let Some(var) = self.choose_var(&assignment) else {
            return Ok(Some(assignment));
        };

        let mut true_branch = assignment.clone();
        true_branch[var] = Some(true);
        if let Some(model) = self.search(true_branch)? {
            return Ok(Some(model));
        }

        let mut false_branch = assignment;
        false_branch[var] = Some(false);
        self.search(false_branch)
    }

    fn unit_propagate(&self, assignment: &mut [Option<bool>]) -> Result<bool, Error> {
        loop {
            self.check_deadline()?;
            let mut changed = false;
            for clause in &self.clauses {
                let mut satisfied = false;
                let mut unassigned = 0usize;
                let mut last_unassigned = 0i32;
                for &lit in clause {
                    match lit_value(assignment, lit) {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            unassigned += 1;
                            last_unassigned = lit;
                        }
                    }
                }
                if satisfied {
                    continue;
                }
                if unassigned == 0 {
                    return Ok(false);
                }
                if unassigned == 1 {
                    if assign_lit(assignment, last_unassigned).is_err() {
                        return Ok(false);
                    }
                    changed = true;
                }
            }
            if !changed {
                return Ok(true);
            }
        }
    }

    fn all_clauses_satisfied(&self, assignment: &[Option<bool>]) -> bool {
        self.clauses.iter().all(|clause| {
            clause
                .iter()
                .any(|&lit| matches!(lit_value(assignment, lit), Some(true)))
        })
    }

    fn choose_var(&self, assignment: &[Option<bool>]) -> Option<usize> {
        (1..=self.num_vars)
            .filter(|&var| assignment[var].is_none())
            .max_by_key(|&var| self.scores[var])
    }

    fn check_deadline(&self) -> Result<(), Error> {
        if let Some(deadline) = self.deadline {
            if Instant::now() >= deadline {
                return Err(Error::Timeout);
            }
        }
        Ok(())
    }
}

fn assign_lit(assignment: &mut [Option<bool>], lit: i32) -> Result<(), ()> {
    let var = lit.unsigned_abs() as usize;
    let value = lit > 0;
    match assignment[var] {
        Some(existing) if existing != value => Err(()),
        Some(_) => Ok(()),
        None => {
            assignment[var] = Some(value);
            Ok(())
        }
    }
}

fn lit_value(assignment: &[Option<bool>], lit: i32) -> Option<bool> {
    let var = lit.unsigned_abs() as usize;
    assignment[var].map(|value| if lit > 0 { value } else { !value })
}
