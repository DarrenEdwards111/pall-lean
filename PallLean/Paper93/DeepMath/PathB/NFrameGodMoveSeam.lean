import PallLean.Step4Compiler
import PallLean.WithinProfileBound
import PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction

/-!
# N-Frame → God-Move seam (positive-closure interface)

This file defines the candidate new seam requested for paper-faithful Route B:
a Bridge-A style N-Frame/God-Move hypothesis strong enough to discharge the
`templateCollapse` obligation used by Step252.

No claim is made here that the seam is already proved.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open WithinProfileBound
open Step4Compiler

/-- Candidate Bridge-A seam: a uniform N-Frame/God-Move hypothesis that
provides the exact template-collapse statement required by Step252. -/
abbrev NFrameGodMoveBridgeA : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinProfileTemplateCollapseLemma M n hn2 htb hns

/-- Positive Route-B closure if the N-Frame/God-Move Bridge-A seam is proved. -/
theorem routeB_positive_closure_from_nframe_godmove_bridgeA
    (hBridgeA : NFrameGodMoveBridgeA) :
    P ≠ NP := by
  apply Step252.P_ne_NP_from_cookLevin_templateCollapse_hypothesis
  intro hPeq
  refine ⟨hPeq.decider, 2 ^ 804, le_rfl, hPeq.timeBound_le, hPeq.numStates_bound, ?_, ?_⟩
  · have h2_804 : (2 : ℕ) ≤ 2 ^ 804 := by
      calc
        (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · exact hBridgeA hPeq.decider (2 ^ 804) (le_rfl) (by
      have h2_804 : (2 : ℕ) ≤ 2 ^ 804 := by
        calc
          (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
      omega) hPeq.timeBound_le hPeq.numStates_bound

#print axioms routeB_positive_closure_from_nframe_godmove_bridgeA

/-- Under the paper bundle assumption (`PeqNP_Paper`), the Bridge-A seam is
refutable: template-collapse would force no bounded SAT decider, contradicting
the bundled SAT decider witness. -/
theorem not_nframe_godmove_bridgeA_of_PeqNP
    (hPeq : PaperFaithfulSeparation.PeqNP_Paper) :
    ¬ NFrameGodMoveBridgeA := by
  intro hBridgeA
  have hNo : PallLean.Paper93.DeepMath.PathB.NoBoundedSATDeciderAtPaperScale :=
    PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_templateCollapse
      hBridgeA
  let n : ℕ := 2 ^ 804
  have hn : n ≥ 2 ^ 804 := by simpa [n]
  have hn2 : n ≥ 2 := by
    calc
      (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = n := by simp [n]
  have hns : hPeq.decider.numStates ≤ n := by
    exact le_trans hPeq.numStates_bound (by simpa [n])
  exact (hNo hPeq.decider n hn hn2 hPeq.timeBound_le hns) hPeq.decides_3sat

#print axioms not_nframe_godmove_bridgeA_of_PeqNP

end PallLean.Paper93.DeepMath.PathB
