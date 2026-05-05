use std::time::Instant;

use crate::config::SatBackendKind;
use crate::error::Error;
use varisat::ExtendFormula;

const BUDGETED_SPLR_CLAUSE_LIMIT: usize = 250_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatResult {
    Sat(Vec<bool>), // 1-based CNF variable values are returned at index var-1
    Unsat,
    Unknown(String),
}

pub fn solve_cnf(
    backend: SatBackendKind,
    num_vars: usize,
    clauses: Vec<Vec<i32>>,
    assumptions: &[i32],
    deadline: Option<Instant>,
) -> SatResult {
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return SatResult::Unknown("budget exhausted".to_owned());
    }
    match backend {
        SatBackendKind::Splr
            if deadline.is_some() && clauses.len() > BUDGETED_SPLR_CLAUSE_LIMIT =>
        {
            DpllSolver::new(num_vars, clauses, deadline).solve(assumptions)
        }
        SatBackendKind::Splr => solve_with_splr(num_vars, clauses, assumptions, deadline),
        SatBackendKind::Varisat => solve_with_varisat(num_vars, clauses, assumptions, deadline),
        SatBackendKind::Dpll => DpllSolver::new(num_vars, clauses, deadline).solve(assumptions),
    }
}

fn solve_with_varisat(
    num_vars: usize,
    clauses: Vec<Vec<i32>>,
    assumptions: &[i32],
    deadline: Option<Instant>,
) -> SatResult {
    if deadline.is_some() {
        // Varisat's public library API has assumption support but no interrupt/timeout hook.
        // Keep budgeted solves on backends that can poll or honor a time limit.
        return SatResult::Unknown("varisat backend does not support deadlines".to_owned());
    }

    let mut formula = varisat::CnfFormula::new();
    formula.set_var_count(num_vars);
    for clause in &clauses {
        let lits = clause
            .iter()
            .map(|&lit| varisat::Lit::from_dimacs(lit as isize))
            .collect::<Vec<_>>();
        formula.add_clause(&lits);
    }

    let mut solver = varisat::Solver::new();
    solver.add_formula(&formula);
    let assumption_lits = assumptions
        .iter()
        .map(|&lit| varisat::Lit::from_dimacs(lit as isize))
        .collect::<Vec<_>>();
    solver.assume(&assumption_lits);

    match solver.solve() {
        Ok(true) => {
            let mut assignment = vec![false; num_vars];
            if let Some(model) = solver.model() {
                for lit in model {
                    let index = lit.index();
                    if index < assignment.len() {
                        assignment[index] = lit.is_positive();
                    }
                }
            }
            SatResult::Sat(assignment)
        }
        Ok(false) => SatResult::Unsat,
        Err(err) => SatResult::Unknown(format!("varisat error: {err}")),
    }
}

fn solve_with_splr(
    num_vars: usize,
    clauses: Vec<Vec<i32>>,
    assumptions: &[i32],
    deadline: Option<Instant>,
) -> SatResult {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solve_with_splr_inner(num_vars, clauses, assumptions, deadline)
    })) {
        Ok(result) => result,
        Err(_) => SatResult::Unknown("splr backend panicked".to_owned()),
    }
}

fn solve_with_splr_inner(
    num_vars: usize,
    mut clauses: Vec<Vec<i32>>,
    assumptions: &[i32],
    deadline: Option<Instant>,
) -> SatResult {
    for &assumption in assumptions {
        clauses.push(vec![assumption]);
    }

    let mut config = splr::Config {
        quiet_mode: true,
        use_log: false,
        show_journal: false,
        ..splr::Config::default()
    };
    if let Some(deadline) = deadline {
        let Some(remaining) = deadline.checked_duration_since(Instant::now()) else {
            return SatResult::Unknown("budget exhausted".to_owned());
        };
        config.c_timeout = remaining.as_secs_f64();
    }

    match splr::Solver::try_from((config, clauses.as_ref())) {
        Ok(mut solver) => match splr::SolveIF::solve(&mut solver) {
            Ok(splr::Certificate::SAT(model)) => {
                let mut assignment = vec![false; num_vars];
                for lit in model {
                    let index = lit.unsigned_abs() as usize;
                    if (1..=num_vars).contains(&index) {
                        assignment[index - 1] = lit > 0;
                    }
                }
                SatResult::Sat(assignment)
            }
            Ok(splr::Certificate::UNSAT) => SatResult::Unsat,
            Err(splr::SolverError::EmptyClause)
            | Err(splr::SolverError::Inconsistent)
            | Err(splr::SolverError::RootLevelConflict(_)) => SatResult::Unsat,
            Err(splr::SolverError::TimeOut) => SatResult::Unknown("budget exhausted".to_owned()),
            Err(err) => SatResult::Unknown(format!("splr error: {err}")),
        },
        Err(Ok(splr::Certificate::UNSAT)) => SatResult::Unsat,
        Err(Ok(splr::Certificate::SAT(model))) => {
            let mut assignment = vec![false; num_vars];
            for lit in model {
                let index = lit.unsigned_abs() as usize;
                if (1..=num_vars).contains(&index) {
                    assignment[index - 1] = lit > 0;
                }
            }
            SatResult::Sat(assignment)
        }
        Err(Err(splr::SolverError::EmptyClause))
        | Err(Err(splr::SolverError::Inconsistent))
        | Err(Err(splr::SolverError::RootLevelConflict(_))) => SatResult::Unsat,
        Err(Err(splr::SolverError::TimeOut)) => SatResult::Unknown("budget exhausted".to_owned()),
        Err(Err(err)) => SatResult::Unknown(format!("splr error: {err}")),
    }
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
