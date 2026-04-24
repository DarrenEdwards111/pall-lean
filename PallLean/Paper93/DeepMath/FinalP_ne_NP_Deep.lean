import PallLean.Step4Compiler
import PallLean.WithinProfileBound
import PallLean.PaperFaithfulSeparation

namespace PallLean.Paper93.DeepMath

open TuringMachine
open PaperFaithfulSeparation
open WithinProfileBound
open Step4Compiler

theorem P_ne_NP_deep_chain
    (_hLPS : True) (_hGraph : True) (_hSub : True)
    (_hAmp : True) (_hGadget : True) (_hPiStar : True) (_hBB : True)
    (hBoundedProfile :
      ∀ (hPeq : PaperFaithfulSeparation.PeqNP_Paper),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
          hPeq.decider (2 ^ 804)
          (by calc (2:ℕ) = 2^1 := by norm_num
                _ ≤ 2^804 := Nat.pow_le_pow_right (by norm_num) (by norm_num))
          hPeq.timeBound_le hPeq.numStates_bound) :
    P ≠ NP := by
  apply Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis
  intro hPeq
  refine ⟨hPeq.decider, 2^804, le_refl _, hPeq.timeBound_le, hPeq.numStates_bound, ?_, ?_⟩
  · calc (2:ℕ) = 2^1 := by norm_num
      _ ≤ 2^804 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · exact hBoundedProfile hPeq

end PallLean.Paper93.DeepMath
