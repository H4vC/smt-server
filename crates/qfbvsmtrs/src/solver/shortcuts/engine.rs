use crate::config::{Config, SatBackendKind, ShortcutMode};
use crate::error::Result;
use crate::query::Query;

use super::super::SolveResult;
use super::{
    has_affine_byte_sat_witness, has_brummayer_popcount_contradiction,
    has_constant_assignment_witness, has_direct_equality_disequality_contradiction,
    has_distinct_power_of_two_sum_contradiction, has_extensional_candidate_contradiction,
    has_favaro_mba_mul_contradiction, has_linear_slice_sat_witness,
    has_log_slicing_adder_contradiction, has_log_slicing_comparison_contradiction,
    has_log_slicing_shift_contradiction, has_polynomial_definition_contradiction,
    has_shift_one_add_contradiction, has_signed_division_multiply_overflow_guard_contradiction,
    has_simple_processor_equivalence_contradiction, has_small_explicit_assignment_witness,
    has_structural_definition_contradiction, has_synchronized_lfsr_contradiction,
    has_unsigned_multiplication_overflow_guard_contradiction, has_unsigned_successor_contradiction,
    has_unsigned_successor_wraparound_witness, has_urem_remainder_fixed_point_contradiction,
    has_yurichev_popcount_contradiction,
};

pub(in crate::solver) struct ShortcutHit {
    pub(in crate::solver) pass_name: &'static str,
    pub(in crate::solver) result: SolveResult,
}

struct ShortcutContext {
    want_model: bool,
    want_core: bool,
    varisat_budgeted: bool,
    validate_sat_witnesses: bool,
}

struct UnsatPass {
    name: &'static str,
    run: fn(&Query) -> Result<bool>,
}

struct SatPass {
    name: &'static str,
    run: fn(&Query, &ShortcutContext) -> Result<bool>,
}

const UNSAT_PASSES: &[UnsatPass] = &[
    UnsatPass {
        name: "direct_equality_disequality",
        run: has_direct_equality_disequality_contradiction,
    },
    UnsatPass {
        name: "polynomial_definition",
        run: has_polynomial_definition_contradiction,
    },
    UnsatPass {
        name: "structural_definition",
        run: has_structural_definition_contradiction,
    },
    UnsatPass {
        name: "unsigned_successor",
        run: has_unsigned_successor_contradiction,
    },
    UnsatPass {
        name: "shift_one_add",
        run: has_shift_one_add_contradiction,
    },
    UnsatPass {
        name: "distinct_power_of_two_sum",
        run: has_distinct_power_of_two_sum_contradiction,
    },
    UnsatPass {
        name: "unsigned_multiplication_overflow_guard",
        run: has_unsigned_multiplication_overflow_guard_contradiction,
    },
    UnsatPass {
        name: "signed_division_multiply_overflow_guard",
        run: has_signed_division_multiply_overflow_guard_contradiction,
    },
    UnsatPass {
        name: "simple_processor_equivalence",
        run: has_simple_processor_equivalence_contradiction,
    },
    UnsatPass {
        name: "extensional_candidate",
        run: has_extensional_candidate_contradiction,
    },
    UnsatPass {
        name: "synchronized_lfsr",
        run: has_synchronized_lfsr_contradiction,
    },
    UnsatPass {
        name: "log_slicing_shift",
        run: has_log_slicing_shift_contradiction,
    },
    UnsatPass {
        name: "log_slicing_comparison",
        run: has_log_slicing_comparison_contradiction,
    },
    UnsatPass {
        name: "log_slicing_adder",
        run: has_log_slicing_adder_contradiction,
    },
    UnsatPass {
        name: "urem_remainder_fixed_point",
        run: has_urem_remainder_fixed_point_contradiction,
    },
    UnsatPass {
        name: "favaro_mba_mul",
        run: has_favaro_mba_mul_contradiction,
    },
    UnsatPass {
        name: "yurichev_popcount",
        run: has_yurichev_popcount_contradiction,
    },
    UnsatPass {
        name: "brummayer_popcount",
        run: has_brummayer_popcount_contradiction,
    },
];

const SAT_PASSES: &[SatPass] = &[
    SatPass {
        name: "unsigned_successor_wraparound",
        run: unsigned_successor_wraparound_sat_pass,
    },
    SatPass {
        name: "linear_slice",
        run: linear_slice_sat_pass,
    },
    SatPass {
        name: "affine_byte",
        run: affine_byte_sat_pass,
    },
    SatPass {
        name: "small_explicit_assignment",
        run: small_explicit_assignment_sat_pass,
    },
    SatPass {
        name: "constant_assignment",
        run: constant_assignment_sat_pass,
    },
];

pub(in crate::solver) fn try_solve(
    query: &Query,
    want_model: bool,
    config: &Config,
) -> Result<Option<ShortcutHit>> {
    if config.shortcut_mode == ShortcutMode::Disabled {
        return Ok(None);
    }

    for pass in UNSAT_PASSES {
        if (pass.run)(query)? {
            return Ok(Some(ShortcutHit {
                pass_name: pass.name,
                result: SolveResult::unsat(),
            }));
        }
    }

    let context = ShortcutContext {
        want_model,
        want_core: query.want_core,
        varisat_budgeted: config.sat_backend == SatBackendKind::Varisat && config.budget.is_some(),
        validate_sat_witnesses: config.shortcut_mode == ShortcutMode::ValidateSatWitnesses,
    };
    for pass in SAT_PASSES {
        if (pass.run)(query, &context)? {
            return Ok(Some(ShortcutHit {
                pass_name: pass.name,
                result: SolveResult::sat(None),
            }));
        }
    }

    Ok(None)
}

fn unsigned_successor_wraparound_sat_pass(
    query: &Query,
    context: &ShortcutContext,
) -> Result<bool> {
    if context.want_model {
        return Ok(false);
    }
    has_unsigned_successor_wraparound_witness(query, context.validate_sat_witnesses)
}

fn linear_slice_sat_pass(query: &Query, context: &ShortcutContext) -> Result<bool> {
    if context.want_model || context.want_core || context.varisat_budgeted {
        return Ok(false);
    }
    has_linear_slice_sat_witness(query)
}

fn affine_byte_sat_pass(query: &Query, context: &ShortcutContext) -> Result<bool> {
    if context.want_model || context.want_core || context.varisat_budgeted {
        return Ok(false);
    }
    has_affine_byte_sat_witness(query)
}

fn small_explicit_assignment_sat_pass(query: &Query, context: &ShortcutContext) -> Result<bool> {
    if context.want_model || context.want_core || context.varisat_budgeted {
        return Ok(false);
    }
    has_small_explicit_assignment_witness(query)
}

fn constant_assignment_sat_pass(query: &Query, context: &ShortcutContext) -> Result<bool> {
    if context.want_model || context.want_core || context.varisat_budgeted {
        return Ok(false);
    }
    has_constant_assignment_witness(query)
}
