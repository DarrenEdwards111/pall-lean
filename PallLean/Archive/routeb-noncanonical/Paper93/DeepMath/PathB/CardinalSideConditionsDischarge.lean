import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum

/-!
# Kernel-only discharge of cardinal side-conditions at the paper scale

This file isolates the small "cardinal arithmetic" side-conditions that
appear repeatedly inside the projected identity-minor / SAT-decider gauge
stack (e.g. `R72AmplituhedronFrontier`, `SATDeciderGaugeRealFrontier`,
`ProjectedIdentityMinorConcrete`, ...).

Every theorem in this file:

* takes only the paper-scale predicate `n ≥ 2 ^ 804` as hypothesis, or no
  hypothesis at all;
* concludes a *cardinal-arithmetic* fact (`n ≥ 2`, `n ≥ 4`, `1 ≤ n`,
  `1 < n`, `Nat.log 2 n ≥ 804`, `Nat.log 2 n ≥ 1`) that downstream files
  currently re-derive inline by `calc` + `omega`;
* uses only kernel-admissible reasoning (`Nat.pow_le_pow_right`,
  `Nat.le_log_of_pow_le`, `pow_one`, `Nat.log_pow`, `omega`,
  `Nat.pow_le_pow_left`).

These are *(a)*-class predicates from the side-condition triage:
trivially discharge-able kernel-only at the abstract level, *not* paper-scale
quantitative claims.  The genuine quantitative claim
`n ^ 200 < Nat.choose (n/3) (Nat.log 2 n)`
(`PaperFaithfulCompilation.arithmetic_gap_2pow804`) is *(c)*-class and
remains proved separately at the paper scale.

After importing this file, downstream theorems can replace the local
`have hn2 : n ≥ 2 := by ...` boilerplate with one of the named lemmas
below and avoid duplicating the kernel-only derivation.

## Axiom audit

All theorems below should depend only on
`[propext, Classical.choice, Quot.sound]` (the kernel-only Mathlib base).
-/

namespace PallLean.Paper93.DeepMath.PathB
namespace CardinalSideConditionsDischarge

/-! ### Pure paper-scale numeric facts (no hypothesis) -/

/-- `2 ^ 804 ≥ 2`.  This is the absolute kernel-only fact that
underlies the `n ≥ 2 ^ 804 ⇒ n ≥ 2` derivation. -/
theorem two_pow_804_ge_two : (2 : ℕ) ≤ 2 ^ 804 := by
  calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)

/-- `2 ^ 804 ≥ 4`. -/
theorem two_pow_804_ge_four : (4 : ℕ) ≤ 2 ^ 804 := by
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)

/-- `Nat.log 2 (2 ^ 804) = 804`. -/
theorem log_two_pow_804 : Nat.log 2 (2 ^ 804) = 804 :=
  Nat.log_pow (by norm_num : 1 < 2) 804

/-! ### Discharges from the paper-scale predicate `n ≥ 2 ^ 804` -/

/-- `n ≥ 2 ^ 804 ⇒ n ≥ 2`.  This is the most-repeated boilerplate
discharge in the projected-identity-minor / SAT-decider-gauge stack. -/
theorem n_ge_two_of_paper_scale {n : ℕ} (hn : n ≥ 2 ^ 804) : n ≥ 2 :=
  le_trans two_pow_804_ge_two hn

/-- `n ≥ 2 ^ 804 ⇒ n ≥ 4`. -/
theorem n_ge_four_of_paper_scale {n : ℕ} (hn : n ≥ 2 ^ 804) : n ≥ 4 :=
  le_trans two_pow_804_ge_four hn

/-- `n ≥ 2 ^ 804 ⇒ 1 ≤ n`. -/
theorem one_le_of_paper_scale {n : ℕ} (hn : n ≥ 2 ^ 804) : 1 ≤ n := by
  have h2 : 2 ≤ n := n_ge_two_of_paper_scale hn
  omega

/-- `n ≥ 2 ^ 804 ⇒ 1 < n`. -/
theorem one_lt_of_paper_scale {n : ℕ} (hn : n ≥ 2 ^ 804) : 1 < n := by
  have h2 : 2 ≤ n := n_ge_two_of_paper_scale hn
  omega

/-- `n ≥ 2 ^ 804 ⇒ 0 < n`. -/
theorem pos_of_paper_scale {n : ℕ} (hn : n ≥ 2 ^ 804) : 0 < n := by
  have h2 : 2 ≤ n := n_ge_two_of_paper_scale hn
  omega

/-! ### `Nat.log` discharges from the paper-scale predicate -/

/-- `n ≥ 2 ^ 804 ⇒ Nat.log 2 n ≥ 804`.

This is the kernel-only base of the `arithmetic_gap_2pow804` proof: it
turns the paper-scale predicate into the lower bound on the binary
logarithm that drives the binomial gap.  It is proved purely via
`Nat.le_log_of_pow_le`. -/
theorem log_ge_804_of_paper_scale {n : ℕ} (hn : n ≥ 2 ^ 804) :
    804 ≤ Nat.log 2 n :=
  Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn

/-- `n ≥ 2 ^ 804 ⇒ Nat.log 2 n ≥ 1`.

This is the precise side-condition discharged inline at the start of
`GodMoveReal.compiled_np_lower_bound_any_dtm`.  Once factored out, that
inline derivation collapses to a single application of this lemma. -/
theorem log_ge_one_of_paper_scale {n : ℕ} (hn : n ≥ 2 ^ 804) :
    1 ≤ Nat.log 2 n := by
  have h804 : 804 ≤ Nat.log 2 n := log_ge_804_of_paper_scale hn
  omega

/-- `n ≥ 2 ^ 804 ⇒ Nat.log 2 n ≥ 201`.

Used inside `arithmetic_gap_2pow804` to drive `n ^ 200 < n ^ 201 ≤ n ^ (log n / 4)`. -/
theorem log_div_four_ge_201_of_paper_scale {n : ℕ} (hn : n ≥ 2 ^ 804) :
    201 ≤ Nat.log 2 n / 4 := by
  have h804 : 804 ≤ Nat.log 2 n := log_ge_804_of_paper_scale hn
  omega

/-! ### `2 ^ 20` companion discharge

The binomial bound used by `arithmetic_gap_2pow804` actually only needs
`n ≥ 2 ^ 20`; we record the matching paper-scale discharge for parity. -/

/-- `2 ^ 20 ≤ 2 ^ 804`. -/
theorem two_pow_20_le_two_pow_804 : (2 : ℕ) ^ 20 ≤ 2 ^ 804 :=
  Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)

/-- `n ≥ 2 ^ 804 ⇒ n ≥ 2 ^ 20`. -/
theorem n_ge_two_pow_20_of_paper_scale {n : ℕ} (hn : n ≥ 2 ^ 804) :
    n ≥ 2 ^ 20 :=
  le_trans two_pow_20_le_two_pow_804 hn

/-! ## Axiom audit anchors

Each theorem below should depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms two_pow_804_ge_two
#print axioms two_pow_804_ge_four
#print axioms log_two_pow_804
#print axioms n_ge_two_of_paper_scale
#print axioms n_ge_four_of_paper_scale
#print axioms one_le_of_paper_scale
#print axioms one_lt_of_paper_scale
#print axioms pos_of_paper_scale
#print axioms log_ge_804_of_paper_scale
#print axioms log_ge_one_of_paper_scale
#print axioms log_div_four_ge_201_of_paper_scale
#print axioms two_pow_20_le_two_pow_804
#print axioms n_ge_two_pow_20_of_paper_scale

end CardinalSideConditionsDischarge
end PallLean.Paper93.DeepMath.PathB
