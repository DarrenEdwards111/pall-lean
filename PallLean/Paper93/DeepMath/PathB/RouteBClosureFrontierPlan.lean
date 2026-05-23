import PallLean.Paper93.DeepMath.PathB.PeqNPBridge
import PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction
import PallLean.Step4Compiler

/-!
# Route B closure frontier plan (clean path)

This module records the exact closure target after quarantining unsafe routes.

The only admissible closure path is:
1. prove template-collapse style P-side control on the source object;
2. transport it through strict `TΦ` extraction;
3. apply NP-side identity-minor lower bound;
4. conclude `PeqNP_Paper → False`.

No use of `SymmetricPower.spdp_profile_generators` is permitted on this path.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Canonical clean frontier hypothesis for Route-B closure. -/
abbrev RouteBTemplateCollapseFrontier : Prop :=
  ∀ (M : TuringMachine.DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    WithinProfileBound.CookLevinProfileTemplateCollapseLemma M n hn2 htb hns

/-- Clean Route-B closure statement: if the template-collapse frontier is proved,
then the paper bundle `PeqNP_Paper` is contradictory. -/
theorem routeB_closure_from_templateCollapse
    (hcollapse : RouteBTemplateCollapseFrontier) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_templateCollapse
      hcollapse)

/-- Type-form packaging of the same clean closure target. -/
theorem routeB_closure_from_templateCollapse_isEmpty
    (hcollapse : RouteBTemplateCollapseFrontier) :
    IsEmpty PeqNP_Paper :=
  ⟨routeB_closure_from_templateCollapse hcollapse⟩

#print axioms routeB_closure_from_templateCollapse
#print axioms routeB_closure_from_templateCollapse_isEmpty

/-- Honest obstruction: at paper scale, the strict `TΦ` target cannot satisfy a
polynomial (`n^200`) upper bound at `κ = ℓ = log₂ n`.

This is the direct negation of the attempted P-side seam on the exact target:
combine the same-target NP lower bound with arithmetic no-sandwich. -/
theorem cookLevin_pSide_seam_false_at_paperScale
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    let target := Step4Compiler.Step252.cookLevinStrictFOBTarget M n hn2 htb hns B_total
    ¬ (MultilinearSPDP.mlBlockedSpdpRank
          target.coupledPartition
          (Nat.log 2 n) (Nat.log 2 n)
          target.coupledPoly
        ≤ n ^ 200) := by
  intro target hUpper
  have hLowerTarget :
      PaperFaithfulSeparation.GodMoveSameTargetStrongNPLower target := by
    simpa [target] using
      (Step4Compiler.Step252.cookLevinStrictFOBTarget_same_target_lower
        M n hn hn2 htb hns B_total hB_total)
  have hLower :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        MultilinearSPDP.mlBlockedSpdpRank
          target.coupledPartition
          (Nat.log 2 n) (Nat.log 2 n)
          target.coupledPoly := by
    simpa [PaperFaithfulSeparation.GodMoveSameTargetStrongNPLower] using hLowerTarget
  exact (PaperFaithfulSeparation.no_rank_sandwich_at_large_n n hn)
    ⟨MultilinearSPDP.mlBlockedSpdpRank
        target.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n)
        target.coupledPoly,
      hLower, hUpper⟩

#print axioms cookLevin_pSide_seam_false_at_paperScale

end PallLean.Paper93.DeepMath.PathB
