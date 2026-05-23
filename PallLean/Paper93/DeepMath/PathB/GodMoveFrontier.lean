import PallLean.Step4Compiler
import PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction

/-!
# God-Move frontier (paper Theorem 207, explicit seam)

This module isolates the exact closure obligation from Theorem 207:
transport a polynomial upper bound from the Cook-Levin source sheet to the
same strict extracted target (`Q×_Φ`) via the global projection map (`TΦ`).

The NP-side lower bound and arithmetic contradiction are already available;
what remains is the transport upper-bound seam.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- The exact strict Route-B target used by the extraction theorem and
same-target NP lower bound. -/
noncomputable abbrev GodMoveTarget
    (M : TuringMachine.DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total) :=
  Step4Compiler.Step252.cookLevinStrictFOBTarget M n hn2 htb hns B_total

/-- The load-bearing Theorem-207 seam: the God-Move (`TΦ`) transport must
produce a polynomial (`n^200`) rank upper bound on the same extracted target. -/
abbrev GodMoveTransportUpperBound
    (M : TuringMachine.DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total) : Prop :=
  MultilinearSPDP.mlBlockedSpdpRank
      (GodMoveTarget M n hn2 htb hns B_total).coupledPartition
      (Nat.log 2 n) (Nat.log 2 n)
      (GodMoveTarget M n hn2 htb hns B_total).coupledPoly
    ≤ n ^ 200

/-- Canonical frontier theorem: at paper scale, the God-Move transport upper
bound on the same strict target is impossible, because NP lower + arithmetic
no-sandwich already block it. -/
theorem godMove_transport_upper_bound_impossible_at_paperScale
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    ¬ GodMoveTransportUpperBound M n hn2 htb hns B_total := by
  intro hUpper
  have hLowerTarget :
      GodMoveSameTargetStrongNPLower
        (GodMoveTarget M n hn2 htb hns B_total) := by
    simpa [GodMoveTarget] using
      (Step4Compiler.Step252.cookLevinStrictFOBTarget_same_target_lower
        M n hn hn2 htb hns B_total hB_total)
  have hLower :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        MultilinearSPDP.mlBlockedSpdpRank
          (GodMoveTarget M n hn2 htb hns B_total).coupledPartition
          (Nat.log 2 n) (Nat.log 2 n)
          (GodMoveTarget M n hn2 htb hns B_total).coupledPoly := by
    simpa [GodMoveSameTargetStrongNPLower, GodMoveTarget] using hLowerTarget
  exact (no_rank_sandwich_at_large_n n hn)
    ⟨MultilinearSPDP.mlBlockedSpdpRank
        (GodMoveTarget M n hn2 htb hns B_total).coupledPartition
        (Nat.log 2 n) (Nat.log 2 n)
        (GodMoveTarget M n hn2 htb hns B_total).coupledPoly,
      hLower, hUpper⟩

#print axioms godMove_transport_upper_bound_impossible_at_paperScale

end PallLean.Paper93.DeepMath.PathB
