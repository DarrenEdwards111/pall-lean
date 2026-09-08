import PallLean.Step4Compiler

/-! A concrete easy machine falsifies the old unprojected profile target.
This is NOT a refutation of P != NP, N-Frame in general, or the separate
crossing-energy hardness conjecture. -/

namespace EasyMachineProfileAudit
open TuringMachine

def acceptAll : DTM where
  numStates := 3
  hStates := by decide
  transition := fun _ bit => (⟨1, by decide⟩, bit, false)
  timeBound := 1
  hTimeBound := by decide

theorem acceptAll_accepts_in_one_step (n : ℕ) (hn : 1 ≤ n)
    (input : Fin n → Bool) :
    (run acceptAll n 1 (initialConfig acceptAll n hn input)).state =
      acceptState acceptAll := by
  rfl

theorem acceptAll_accepts (n : ℕ) (hn : 1 ≤ n)
    (input : Fin n → Bool) : accepts acceptAll n hn input := by
  refine ⟨1, ?_, acceptAll_accepts_in_one_step n hn input⟩
  simpa [timeSteps, acceptAll] using hn

theorem three_le_scale : 3 ≤ (2 : ℕ) ^ 804 := by
  calc
    3 ≤ (2 : ℕ) ^ 2 := by decide
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by decide) (by decide)

theorem two_le_scale : 2 ≤ (2 : ℕ) ^ 804 := by
  have := three_le_scale
  omega

theorem acceptAll_profile_frontier_false :
    ¬ WithinProfileBound.CookLevinWithinProfileFinrankFrontier
      acceptAll (2 ^ 804) two_le_scale (by decide) three_le_scale := by
  intro h
  exact Step4Compiler.bounded_params_at_2pow804_absurd
    acceptAll (2 ^ 804) (le_refl _) (by decide)
    three_le_scale two_le_scale h

end EasyMachineProfileAudit

#print axioms EasyMachineProfileAudit.acceptAll_accepts_in_one_step
#print axioms EasyMachineProfileAudit.acceptAll_accepts
#print axioms EasyMachineProfileAudit.acceptAll_profile_frontier_false
