import PallLean.GodMoveCore
import PallLean.PaperFaithfulSeparation

/-!
# Phase-1 audit: the hypothesis of `Step4Compiler.P_ne_NP_Lean` is refutable

`Step4Compiler.P_ne_NP_Lean (hsep : PeqNP_Paper → False) (hExtract : P = NP → PeqNP_Paper)`
is the only Lean theorem in the active import closure with conclusion `P ≠ NP`.
Here we show `PeqNP_Paper` is *inhabited* (by a 3-state machine that accepts on
its first step), because the legacy `ThreeCNF` has only positive literals and
`DecidesSAT` never relates the accepted input to the formula.  Hence `hsep` is
false and `P_ne_NP_Lean` is vacuous.  (Builds on the repo's own
`research-audits/nframe-fixed-invariant/GodMoveSATSemanticsCheck.lean`.)
-/

namespace Phase1Audit
open PaperFaithfulSeparation TuringMachine

def alwaysAccept : DTM where
  numStates := 3
  hStates := by decide
  transition := fun _ bit => (1, bit, true)
  timeBound := 1
  hTimeBound := by decide

theorem alwaysAccept_accepts (n : ℕ) (hn : 1 ≤ n) (input : Fin n → Bool) :
    accepts alwaysAccept n hn input := by
  refine ⟨1, ?_, ?_⟩
  · simpa [timeSteps, alwaysAccept] using hn
  · rfl

theorem alwaysAccept_decidesSAT : DecidesSAT alwaysAccept where
  accepts_sat := fun _ n hn _ _ => ⟨fun _ => false, alwaysAccept_accepts n hn _⟩
  rejects_unsat := fun _ _ _ _ hnot _ =>
    (hnot ⟨fun _ => true, fun _ _ => Or.inl rfl⟩).elim

def trivialPeqNP : PeqNP_Paper where
  decider := alwaysAccept
  timeBound_le := by decide
  numStates_bound := le_trans (by decide : 3 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by decide))
  decides_3sat := alwaysAccept_decidesSAT

/-- The `hsep` premise of `P_ne_NP_Lean` is false. -/
theorem hsep_refuted : ¬ (PeqNP_Paper → False) := fun h => h trivialPeqNP

/-- And `hExtract` is trivially true for the same reason (it carries no content). -/
def hExtract_trivial {α : Prop} : α → PeqNP_Paper := fun _ => trivialPeqNP

end Phase1Audit

#print axioms Phase1Audit.hsep_refuted
