import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolographicProjectionInterface

/-!
# Grounded Cook--Levin obstruction

This note records the exact tension exposed by grounding the holographic
interface in the actual Cook--Levin polynomial.

The real `compiledPoly (cook_levin_compilation M n ...)` is the correct
semantic substrate, but it already carries the axiom-free NP-side SPDP lower
bound for every DTM.  Therefore a legacy Theorem-207 witness whose
`paperCompiledPoly` is identified with the real Cook--Levin bulk would force
the same object to satisfy both the paper P-side bound and the existing
NP-side lower bound.

The point is not a new separation theorem.  It is the audit theorem showing
that the abstract `paperCompiledPoly` cannot be silently replaced by the
semantic Cook--Levin bulk while keeping the low-rank P-side field.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation

/-! ## The real substrate has the NP-side lower bound -/

/-- The actual Cook--Levin bulk used by the holographic projection interface
inherits the existing axiom-free lower bound for every DTM. -/
theorem actualCookLevinBulk_spdp_lower_bound_any_dtm
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (actualCookLevinBulkPoly M n (by omega : n ≥ 2) htb hns) := by
  simpa [actualCookLevinBulkPoly] using
    GodMoveReal.compiled_np_lower_bound_any_dtm M n hn htb hns

/-! ## Grounding a legacy witness forces the P-side bound onto that object -/

/-- If the legacy abstract `paperCompiledPoly` is identified with the actual
Cook--Levin bulk, then the witness's P-side field becomes a P-side bound on the
semantic substrate itself. -/
theorem theorem207Witness_p_side_bound_on_actualBulk_of_grounded
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : GlobalGodMoveGauge.Theorem207Witness
      M n hn (by omega : n ≥ 2) htb hns)
    (hground :
      W.paperCompiledPoly =
        actualCookLevinBulkPoly M n (by omega : n ≥ 2) htb hns) :
    mlBlockedSpdpRank
      (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (actualCookLevinBulkPoly M n (by omega : n ≥ 2) htb hns) ≤ n ^ 200 := by
  simpa [hground] using W.compiled_p_side_bound

/-- A grounded legacy Theorem-207 witness would put both the existing lower
bound and the paper P-side upper bound on the same actual Cook--Levin object. -/
theorem theorem207Witness_grounded_actualBulk_rank_sandwich
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : GlobalGodMoveGauge.Theorem207Witness
      M n hn (by omega : n ≥ 2) htb hns)
    (hground :
      W.paperCompiledPoly =
        actualCookLevinBulkPoly M n (by omega : n ≥ 2) htb hns) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤ n ^ 200 := by
  exact le_trans
    (actualCookLevinBulk_spdp_lower_bound_any_dtm M n hn htb hns)
    (theorem207Witness_p_side_bound_on_actualBulk_of_grounded
      M n hn htb hns W hground)

/-- At the paper scale, the grounded replacement of `paperCompiledPoly` by the
actual Cook--Levin bulk is impossible: it would contradict the established
arithmetic gap `n^200 < choose(n/3, log n)`. -/
theorem no_theorem207Witness_grounded_to_actualCookLevinBulk
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : GlobalGodMoveGauge.Theorem207Witness
      M n hn (by omega : n ≥ 2) htb hns) :
    Not
      (W.paperCompiledPoly =
        actualCookLevinBulkPoly M n (by omega : n ≥ 2) htb hns) := by
  intro hground
  exact (not_le_of_gt (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn))
    (theorem207Witness_grounded_actualBulk_rank_sandwich M n hn htb hns W hground)

/-! ## Kernel-only axiom trace -/

#print axioms actualCookLevinBulk_spdp_lower_bound_any_dtm
#print axioms theorem207Witness_p_side_bound_on_actualBulk_of_grounded
#print axioms theorem207Witness_grounded_actualBulk_rank_sandwich
#print axioms no_theorem207Witness_grounded_to_actualCookLevinBulk

end PallLean.Paper93.DeepMath.PathB
