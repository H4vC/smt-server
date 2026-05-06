//! Optional conclusive shortcut recognizers.
//!
//! This module is intentionally outside the core bit-blast/CNF/SAT path in
//! `solver.rs`. The top-level order below preserves the historical shortcut
//! order so the mechanical extraction does not change default behavior.

mod arithmetic;
mod assignment;
mod common;
mod direct_eq;
mod division_remainder;
mod engine;
mod extensional;
mod favaro_mba;
mod lfsr;
mod log_slicing;
mod overflow_guards;
mod polynomial;
mod popcount;
mod simple_processor;
mod structural;
mod successor;
mod witnesses;

use arithmetic::{has_distinct_power_of_two_sum_contradiction, has_shift_one_add_contradiction};
use assignment::{has_constant_assignment_witness, has_small_explicit_assignment_witness};
pub(super) use common::{
    bv_add_parts, collect_bool_or_leaves, collect_bv_equalities_and_disequalities,
    equivalent_under_equalities, is_all_ones_bv_const, is_asserted_nonzero_power_of_two,
    is_one_bv_const, is_shift_left_one_of, is_signed_min_bv_const, is_zero_bv_const,
    same_unordered_pair, BvPair, BvSlice, TermUnion,
};
use direct_eq::has_direct_equality_disequality_contradiction;
use division_remainder::has_urem_remainder_fixed_point_contradiction;
pub(super) use engine::try_solve;
use extensional::has_extensional_candidate_contradiction;
use favaro_mba::has_favaro_mba_mul_contradiction;
use lfsr::{bv_eq_pair, collect_bool_and_conjuncts, has_synchronized_lfsr_contradiction};
use log_slicing::{
    bv_and_parts, collect_bv_xor_terms, has_log_slicing_adder_contradiction,
    has_log_slicing_comparison_contradiction, has_log_slicing_shift_contradiction, is_bv_not_of,
};
use overflow_guards::{
    has_signed_division_multiply_overflow_guard_contradiction,
    has_unsigned_multiplication_overflow_guard_contradiction,
};
pub(super) use polynomial::has_polynomial_definition_contradiction;
pub(super) use popcount::has_brummayer_popcount_contradiction;
use popcount::has_yurichev_popcount_contradiction;
use simple_processor::{
    has_simple_processor_equivalence_contradiction, is_bv_const_u64, matches_extract,
};
pub(super) use structural::has_structural_definition_contradiction;
use successor::{
    collect_unsigned_less_or_equal, has_unsigned_successor_contradiction,
    has_unsigned_successor_wraparound_witness,
};
pub(super) use witnesses::mask_for_width;
use witnesses::{
    bytes_to_u64, const_u64, has_affine_byte_sat_witness, has_linear_slice_sat_witness,
};
