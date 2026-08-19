import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSkipCountReduction

/-!
# The one-bit skip label is not injective

For the two singleton terms `x0` and `x1`, the restrictions `(*,0)` and `(0,*)` have the
same canonical depth, deepest end state, and skip label.  Consequently no decoder base computed
only from that public encoding can reproduce both original term-falsification patterns.

This is a kernel-checked obstruction to the proposed `SkipBaseRecoverable` route.  It does not
contradict the switching lemma; it shows that the standard clause-count-free proof needs a different
completion/encoding (or more clause-boundary information) than this single advance bit.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open PallLean.Paper93.DeepMath.PathB
open SwitchingCounting

def skipCollisionC0 : Clause 2 := ⟨[Rung4Literal.pos 0]⟩
def skipCollisionC1 : Clause 2 := ⟨[Rung4Literal.pos 1]⟩
def skipCollisionDnf : List (Clause 2) := [skipCollisionC0, skipCollisionC1]

/-- `x0` is free and `x1` is fixed false. -/
def skipCollisionRho0 : Restriction 2 := fun i => if i = 0 then none else some false

/-- `x0` is fixed false and `x1` is free. -/
def skipCollisionRho1 : Restriction 2 := fun i => if i = 0 then some false else none

theorem skipCollision_restrictions_ne : skipCollisionRho0 ≠ skipCollisionRho1 := by
  decide

theorem skipCollision_depth0 :
    (canonicalDT skipCollisionDnf 2 skipCollisionRho0).depth = 1 := by
  decide

theorem skipCollision_depth1 :
    (canonicalDT skipCollisionDnf 2 skipCollisionRho1).depth = 1 := by
  decide

theorem skipCollision_end :
    deepestEnd skipCollisionDnf 2 skipCollisionRho0 =
      deepestEnd skipCollisionDnf 2 skipCollisionRho1 := by
  decide

theorem skipCollision_sequence :
    deepestSkipSeq skipCollisionDnf 2 skipCollisionRho0 =
      deepestSkipSeq skipCollisionDnf 2 skipCollisionRho1 := by
  decide

theorem skipCollision_label :
    flatToSkipLabel 1 1 (deepestSkipSeq skipCollisionDnf 2 skipCollisionRho0) =
      flatToSkipLabel 1 1 (deepestSkipSeq skipCollisionDnf 2 skipCollisionRho1) := by
  rw [skipCollision_sequence]

theorem skipCollision_selected_ne :
    deepestSel skipCollisionDnf 2 skipCollisionRho0 ≠
      deepestSel skipCollisionDnf 2 skipCollisionRho1 := by
  decide

/-- No function of the deepest end state and the one-bit skip label can reconstruct the selected
set on this depth-one shell.  This rules out the encoding itself, not merely the particular
base-relative implementation. -/
theorem no_skipLabel_selected_decoder_collision :
    ¬ ∃ D : Restriction 2 → SkipLabel 1 1 → Finset (Fin 2),
      ∀ ρ ∈ ({skipCollisionRho0, skipCollisionRho1} : Finset (Restriction 2)),
        D (deepestEnd skipCollisionDnf 2 ρ)
            (flatToSkipLabel 1 1 (deepestSkipSeq skipCollisionDnf 2 ρ)) =
          deepestSel skipCollisionDnf 2 ρ := by
  rintro ⟨D, hD⟩
  have h0 := hD skipCollisionRho0 (by simp)
  have h1 := hD skipCollisionRho1 (by simp)
  rw [skipCollision_end, skipCollision_label] at h0
  exact skipCollision_selected_ne (h0.symm.trans h1)

/-- **Formal obstruction.**  The base-recovery property required by the one-bit skip decoder is
false even for a width-one, two-term DNF and a two-element depth-one bad set. -/
theorem not_skipBaseRecoverable_collision :
    ¬ SkipBaseRecoverable (w := 1) (s := 1) (F := 2) skipCollisionDnf
      {skipCollisionRho0, skipCollisionRho1} := by
  rintro ⟨B, hB⟩
  have h0 := hB skipCollisionRho0 (by simp)
  have h1 := hB skipCollisionRho1 (by simp)
  have hf0 := h0.2 skipCollisionC0 (by simp [skipCollisionDnf, skipCollisionC0])
  have hf1 := h1.2 skipCollisionC0 (by simp [skipCollisionDnf, skipCollisionC0])
  have harg : B (deepestEnd skipCollisionDnf 2 skipCollisionRho0)
        (flatToSkipLabel 1 1 (deepestSkipSeq skipCollisionDnf 2 skipCollisionRho0)) =
      B (deepestEnd skipCollisionDnf 2 skipCollisionRho1)
        (flatToSkipLabel 1 1 (deepestSkipSeq skipCollisionDnf 2 skipCollisionRho1)) := by
    rw [skipCollision_end, skipCollision_label]
  rw [harg] at hf0
  have hr0 : termFalsified skipCollisionRho0 skipCollisionC0 = false := by decide
  have hr1 : termFalsified skipCollisionRho1 skipCollisionC0 = true := by decide
  rw [hr0] at hf0
  rw [hr1] at hf1
  rw [hf0] at hf1
  contradiction

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.no_skipLabel_selected_decoder_collision
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.not_skipBaseRecoverable_collision
