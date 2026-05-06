use std::time::Instant;

use crate::blast::blast_query_with_deadline;
use crate::cnf;
use crate::config::{Config, ShortcutMode};
use crate::error::{Error, Result};
use crate::ir::{NodeKind, Sort};
use crate::model::{build_model, Model, ScalarValue};
use crate::query::{Assertion, Command, Query};
use crate::sat::{solve_cnf, SatResult};

mod shortcuts;

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
        let deadline = self.config.budget.map(|budget| Instant::now() + budget);
        if matches!(query.command, Command::Minimize | Command::Maximize) {
            return self.optimize(query, deadline);
        }
        let mut result = self.solve_once_with_deadline(query, query.want_model, deadline)?;
        if result.status == SolveStatus::Unsat && query.want_core {
            result.core = Some(self.extract_named_core(query, deadline)?);
        }
        Ok(result)
    }

    /// Solve using the trusted bit-blast/CNF/SAT path, bypassing optional shortcuts.
    pub fn solve_without_shortcuts(&mut self, query: &Query) -> Result<SolveResult> {
        let mut config = self.config.clone();
        config.shortcut_mode = ShortcutMode::Disabled;
        Solver::new(config).solve(query)
    }

    fn solve_once_with_deadline(
        &self,
        query: &Query,
        want_model: bool,
        deadline: Option<Instant>,
    ) -> Result<SolveResult> {
        match query.command {
            Command::Simplify => return Ok(SolveResult::ok()),
            Command::Minimize | Command::Maximize => {
                return Err(Error::internal(
                    "solve_once called with optimization command",
                ))
            }
            Command::Solve => {}
        }
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Ok(SolveResult::unknown("budget exhausted"));
        }
        if let Some(hit) = shortcuts::try_solve(query, want_model, &self.config)? {
            if self.config.shortcut_mode == ShortcutMode::Audit {
                let core = self.solve_core_once_with_deadline(query, want_model, deadline)?;
                if core.status != SolveStatus::Unknown && core.status != hit.result.status {
                    return Ok(SolveResult::unknown(format!(
                        "shortcut audit disagreement in {}: shortcut={:?}, core={:?}",
                        hit.pass_name, hit.result.status, core.status
                    )));
                }
            }
            return Ok(hit.result);
        }
        self.solve_core_once_with_deadline(query, want_model, deadline)
    }

    fn solve_core_once_with_deadline(
        &self,
        query: &Query,
        want_model: bool,
        deadline: Option<Instant>,
    ) -> Result<SolveResult> {
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Ok(SolveResult::unknown("budget exhausted"));
        }

        let blasted = match blast_query_with_deadline(query, deadline) {
            Ok(blasted) => blasted,
            Err(Error::Timeout) => return Ok(SolveResult::unknown("budget exhausted")),
            Err(err) => return Err(err),
        };
        let cnf = match cnf::encode_with_deadline(&blasted.gates, blasted.assertion, deadline) {
            Ok(cnf) => cnf,
            Err(Error::Timeout) => return Ok(SolveResult::unknown("budget exhausted")),
            Err(err) => return Err(err),
        };
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

    fn optimize(&self, query: &Query, deadline: Option<Instant>) -> Result<SolveResult> {
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

        match self
            .solve_once_with_deadline(&fixed, false, deadline)?
            .status
        {
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
            match self
                .solve_once_with_deadline(&trial, false, deadline)?
                .status
            {
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
            match self.solve_once_with_deadline(&fixed, true, deadline)? {
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

    fn extract_named_core(&self, query: &Query, deadline: Option<Instant>) -> Result<Vec<String>> {
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
            match self
                .solve_once_with_deadline(&trial, false, deadline)?
                .status
            {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builder::Builder;

    #[test]
    fn direct_equality_disequality_contradiction_is_unsat() -> Result<()> {
        let mut builder = Builder::new();
        let x = builder.bv_var("x", 8)?;
        let y = builder.bv_var("y", 8)?;
        let z = builder.bv_var("z", 8)?;
        let xy = builder.bv_eq(x, y)?;
        let yz = builder.bv_eq(y, z)?;
        let xz = builder.bv_eq(x, z)?;
        let not_xz = builder.bool_not(xz)?;
        builder.assert(xy)?;
        builder.assert(yz)?;
        builder.assert(not_xz)?;
        let query = builder.finish()?;
        let mut solver = Solver::new(Config::default());
        let result = solver.solve(&query)?;
        assert_eq!(result.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn shortcut_mode_disabled_solves_small_queries_via_core() -> Result<()> {
        let config = Config::default().with_shortcut_mode(ShortcutMode::Disabled);

        let mut builder = Builder::new();
        let x = builder.bv_var("x", 4)?;
        let three = builder.bv_const(3, 4)?;
        let x_is_three = builder.bv_eq(x, three)?;
        builder.assert(x_is_three)?;
        builder.set_want_model(true);
        let sat_query = builder.finish()?;
        let mut solver = Solver::new(config.clone());
        let sat = solver.solve(&sat_query)?;
        assert_eq!(sat.status, SolveStatus::Sat);
        assert!(sat.model.is_some());

        let mut builder = Builder::new();
        let x = builder.bv_var("x", 1)?;
        let zero = builder.bv_const(0, 1)?;
        let one = builder.bv_const(1, 1)?;
        let x_is_zero = builder.bv_eq(x, zero)?;
        let x_is_one = builder.bv_eq(x, one)?;
        builder.assert(x_is_zero)?;
        builder.assert(x_is_one)?;
        let unsat_query = builder.finish()?;
        let mut solver = Solver::new(config);
        let unsat = solver.solve(&unsat_query)?;
        assert_eq!(unsat.status, SolveStatus::Unsat);

        let mut solver = Solver::new(Config::default());
        let unsat_without_shortcuts = solver.solve_without_shortcuts(&unsat_query)?;
        assert_eq!(unsat_without_shortcuts.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn shortcut_validation_and_audit_modes_solve_wraparound_witness() -> Result<()> {
        fn wraparound_query() -> Result<Query> {
            let mut builder = Builder::new();
            let x = builder.bv_var("x", 2)?;
            let y = builder.bv_var("y", 2)?;
            let one = builder.bv_const(1, 2)?;
            let y_plus_one = builder.bv_add(y, one)?;
            let x_le_y = builder.bv_ule(x, y)?;
            let successor_le_x = builder.bv_ule(y_plus_one, x)?;
            builder.assert(x_le_y)?;
            builder.assert(successor_le_x)?;
            builder.finish()
        }

        for mode in [ShortcutMode::ValidateSatWitnesses, ShortcutMode::Audit] {
            let query = wraparound_query()?;
            let config = Config::default().with_shortcut_mode(mode);
            let mut solver = Solver::new(config);
            assert_eq!(solver.solve(&query)?.status, SolveStatus::Sat);
        }
        Ok(())
    }

    #[test]
    fn structural_definition_contradiction_is_unsat() -> Result<()> {
        let query = crate::frontend::parse_smt2(
            r#"
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun a () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(declare-fun choose () Bool)
(assert (= x a))
(assert (ite choose (= z (bvadd x y)) (= z (bvmul x y))))
(assert (ite choose (= c (bvadd a y)) (= c (bvmul a y))))
(assert (not (= z c)))
(check-sat)
"#,
        )?;
        assert!(shortcuts::has_structural_definition_contradiction(&query)?);
        let mut solver = Solver::new(Config::default());
        assert_eq!(solver.solve(&query)?.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn brummayer_popcount_contradiction_is_unsat() -> Result<()> {
        let width = 4;
        let mut builder = Builder::new();
        let x = builder.bv_var("x", width)?;
        let zero = builder.bv_const(0, width)?;
        let one = builder.bv_const(1, width)?;
        let zero1 = builder.bv_const(0, 1)?;
        let one1 = builder.bv_const(1, 1)?;
        let minus_one = builder.bv_const(shortcuts::mask_for_width(width), width)?;

        let mut naive = zero;
        for bit in 0..width {
            let extracted = builder.bv_extract(x, bit, bit)?;
            let cond = builder.bv_eq(one1, extracted)?;
            let incremented = builder.bv_add(naive, one)?;
            naive = builder.bv_ite(cond, incremented, naive)?;
        }

        let zero_eq = builder.bv_eq(x, zero)?;
        let zero_indicator = builder.bv_ite(zero_eq, one1, zero1)?;
        let zero_cond = builder.bv_eq(one1, zero_indicator)?;
        let mut wegner = builder.bv_ite(zero_cond, zero, one)?;
        let mut state = x;
        for _ in 1..width {
            let decremented = builder.bv_add(state, minus_one)?;
            state = builder.bv_and(state, decremented)?;
            let zero_eq = builder.bv_eq(state, zero)?;
            let zero_indicator = builder.bv_ite(zero_eq, one1, zero1)?;
            let zero_cond = builder.bv_eq(one1, zero_indicator)?;
            let incremented = builder.bv_add(wegner, one)?;
            wegner = builder.bv_ite(zero_cond, wegner, incremented)?;
        }

        let counts_equal = builder.bv_eq(wegner, naive)?;
        let indicator = builder.bv_ite(counts_equal, one1, zero1)?;
        let not_indicator = builder.bv_not(indicator)?;
        let indicator_is_zero = builder.bv_eq(not_indicator, zero1)?;
        let counterexample = builder.bool_not(indicator_is_zero)?;
        builder.assert(counterexample)?;
        let query = builder.finish()?;
        assert!(shortcuts::has_brummayer_popcount_contradiction(&query)?);
        let mut solver = Solver::new(Config::default());
        assert_eq!(solver.solve(&query)?.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn polynomial_definition_contradiction_is_unsat() -> Result<()> {
        let query = crate::frontend::parse_smt2(
            r#"
(set-logic QF_BV)
(declare-fun var2 () (_ BitVec 8))
(declare-fun var3 () (_ BitVec 8))
(declare-fun var4 () (_ BitVec 8))
(declare-fun var8 () (_ BitVec 24))
(declare-fun var10 () (_ BitVec 24))
(declare-fun var12 () (_ BitVec 24))
(declare-fun var14 () (_ BitVec 24))
(declare-fun var16 () (_ BitVec 24))
(declare-fun var20 () (_ BitVec 24))
(declare-fun var28 () (_ BitVec 24))
(declare-fun var29 () (_ BitVec 1))
(declare-fun var30 () (_ BitVec 1))
(declare-fun var31 () (_ BitVec 1))
(declare-fun property () (_ BitVec 1))
(declare-fun Fresh__0 () (_ BitVec 1))
(declare-fun Fresh__1 () (_ BitVec 1))
(assert (= var8 (concat (_ bv0 16) var4)))
(assert (= var10 (concat (_ bv0 16) var3)))
(assert (= var12 (concat (_ bv0 16) var2)))
(assert (= var14 (bvmul var10 var12)))
(assert (= var16 (bvmul var8 var14)))
(assert (= var20 (bvmul var8 var10)))
(assert (= var28 (bvmul var12 var20)))
(assert (= (= Fresh__0 (_ bv1 1)) (= var16 var28)))
(assert (= var29 Fresh__0))
(assert (= var30 (bvnot (_ bv1 1))))
(assert (= var31 (bvor var29 var30)))
(assert (= property ((_ extract 0 0) var31)))
(assert (= (= Fresh__1 (_ bv1 1)) (= property (_ bv0 1))))
(assert (= (_ bv1 1) Fresh__1))
(check-sat)
"#,
        )?;
        assert!(shortcuts::has_polynomial_definition_contradiction(&query)?);
        let mut solver = Solver::new(Config::default());
        assert_eq!(solver.solve(&query)?.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn polynomial_pack_equivalence_contradiction_is_unsat() -> Result<()> {
        let query = crate::frontend::parse_smt2(
            r#"
(set-logic QF_BV)
(declare-fun a0 () (_ BitVec 8))
(declare-fun a1 () (_ BitVec 8))
(declare-fun b0 () (_ BitVec 8))
(declare-fun b1 () (_ BitVec 8))
(declare-fun tail_a () (_ BitVec 8))
(declare-fun tail_b () (_ BitVec 8))
(declare-fun packed_a () (_ BitVec 16))
(declare-fun packed_b () (_ BitVec 16))
(assert (= packed_a (bvor (bvshl ((_ zero_extend 8) a1) (_ bv8 16)) ((_ zero_extend 8) a0))))
(assert (= packed_b (bvor (bvshl ((_ zero_extend 8) b1) (_ bv8 16)) ((_ zero_extend 8) b0))))
(assert (= ((_ zero_extend 16) packed_a) ((_ zero_extend 16) packed_b)))
(assert (= tail_a tail_b))
(assert (not (= (bvadd (bvmul ((_ zero_extend 24) a1) (_ bv3 32))
                       (bvadd ((_ zero_extend 24) a0) ((_ zero_extend 24) tail_a)))
                (bvadd (bvmul ((_ zero_extend 24) b1) (_ bv3 32))
                       (bvadd ((_ zero_extend 24) b0) ((_ zero_extend 24) tail_b))))))
(check-sat)
"#,
        )?;
        assert!(shortcuts::has_polynomial_definition_contradiction(&query)?);
        let mut solver = Solver::new(Config::default());
        assert_eq!(solver.solve(&query)?.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn urem_remainder_fixed_point_contradiction_is_unsat() -> Result<()> {
        let mut builder = Builder::new();
        let n = builder.bv_var("n", 32)?;
        let n_prime = builder.bv_var("n_prime", 32)?;
        let d = builder.bv_var("d", 32)?;
        let m = builder.bv_var("m", 32)?;
        let alias = builder.bv_eq(n_prime, m)?;
        builder.assert(alias)?;
        let rem_n = builder.bv_urem(n, d)?;
        let rem_n_is_m = builder.bv_eq(rem_n, m)?;
        let m_is_d = builder.bv_eq(m, d)?;
        let guard = builder.bool_or(rem_n_is_m, m_is_d)?;
        builder.assert(guard)?;
        let rem_prime = builder.bv_urem(n_prime, d)?;
        let rem_prime_is_m = builder.bv_eq(rem_prime, m)?;
        let m_is_d = builder.bv_eq(m, d)?;
        let fixed_point_guard = builder.bool_or(rem_prime_is_m, m_is_d)?;
        let not_fixed_point = builder.bool_not(fixed_point_guard)?;
        builder.assert(not_fixed_point)?;
        let query = builder.finish()?;
        let mut solver = Solver::new(Config::default());
        let result = solver.solve(&query)?;
        assert_eq!(result.status, SolveStatus::Unsat);
        Ok(())
    }

    #[test]
    fn solve_once_with_expired_deadline_returns_unknown() -> Result<()> {
        let mut builder = Builder::new();
        let truth = builder.bool_true()?;
        builder.assert(truth)?;
        let query = builder.finish()?;
        let solver = Solver::new(Config::default());
        let result = solver.solve_once_with_deadline(
            &query,
            false,
            Some(Instant::now() - std::time::Duration::from_millis(1)),
        )?;
        assert_eq!(result.status, SolveStatus::Unknown);
        assert_eq!(result.message.as_deref(), Some("budget exhausted"));
        Ok(())
    }

    #[test]
    fn optimization_uses_total_budget_deadline() -> Result<()> {
        let mut builder = Builder::new();
        let x = builder.bv_var("x", 4)?;
        builder.set_optimization(Command::Minimize, x, false)?;
        let query = builder.finish()?;
        let config = Config::default().with_budget(Some(std::time::Duration::ZERO));
        let mut solver = Solver::new(config);
        let result = solver.solve(&query)?;
        assert_eq!(result.status, SolveStatus::Unknown);
        Ok(())
    }
}
