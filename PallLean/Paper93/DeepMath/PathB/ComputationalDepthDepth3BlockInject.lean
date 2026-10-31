import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockPeel

/-!
# Block-DT model, foundation 6: the injection (branch only)

`ρ` is recovered from the boundary `(blockEncode cs F ρ, blockMasks cs F ρ)` by **freeing the masked
(block) variables**: `recoverRho (blockMasks ρ) (blockEncode ρ) = ρ`.  Hence the map
`ρ ↦ (blockEncode cs F ρ, blockMasks cs F ρ)` is **injective** — the basis of the holographic count
(`|Bad| ≤ |leaves| · |labels|`), with no `2^|cs|` factor.

* `killTerm_outside` — `killTerm` leaves non-block coordinates equal to `ρ`.
* `recoverRho` — free the masked coordinates of the boundary.
* `blockEncode_recover` — `recoverRho (blockMasks cs F ρ) (blockEncode cs F ρ) = ρ`.
* `block_injective` — `ρ ↦ (blockEncode cs F ρ, blockMasks cs F ρ)` is injective.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `killTerm` leaves a non-block coordinate equal to `ρ`. -/
theorem killTerm_outside {ρ : Restriction n} {T : Clause n} {v : Fin n}
    (h : ¬(ρ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits))) :
    killTerm ρ T v = ρ v := by
  simp only [killTerm]
  by_cases hvn : ρ v = none
  · rw [if_pos hvn]
    have hnor : ¬((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits) :=
      fun hor => h ⟨hvn, hor⟩
    rw [if_neg (fun hp => hnor (Or.inl hp)), if_neg (fun hn => hnor (Or.inr hn))]
    exact hvn.symm
  · rw [if_neg hvn]

/-- Free the masked coordinates of the boundary. -/
def recoverRho (masks : List (Fin n → Bool)) (enc : Restriction n) : Restriction n :=
  fun v => if masks.any (fun mask => mask v) then none else enc v

/-- **The recovery identity.**  Freeing the masked (block) variables of the boundary recovers `ρ`. -/
theorem blockEncode_recover (cs : List (Clause n)) :
    ∀ (F : ℕ) (ρ : Restriction n),
      recoverRho (blockMasks cs F ρ) (blockEncode cs F ρ) = ρ := by
  intro F
  induction F with
  | zero => intro ρ; funext v; simp [recoverRho, blockMasks, blockEncode]
  | succ F ih =>
    intro ρ
    cases hany : SwitchingCounting.anyTermSat cs ρ with
    | true => funext v; simp [recoverRho, blockMasks, blockEncode, hany]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs ρ with
      | none => funext v; simp [recoverRho, blockMasks, blockEncode, hany, hact]
      | some T =>
        funext v
        have hmask : blockMasks cs (F + 1) ρ
            = (fun v => decide (ρ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits
                ∨ (Rung4Literal.neg v) ∈ T.lits))) :: blockMasks cs F (killTerm ρ T) := by
          rw [blockMasks]; simp only [hany, Bool.false_eq_true, if_false, hact]
        have hihv := congrFun (ih (killTerm ρ T)) v
        simp only [recoverRho] at hihv ⊢
        rw [hmask]
        simp only [List.any_cons]
        by_cases hmT : (ρ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits))
        · simp only [decide_eq_true_eq.mpr hmT, Bool.true_or, if_true]
          exact hmT.1.symm
        · simp only [decide_eq_false_iff_not.mpr hmT, Bool.false_or]
          by_cases hrest : (blockMasks cs F (killTerm ρ T)).any (fun mask => mask v) = true
          · rw [if_pos hrest]
            rw [if_pos hrest] at hihv
            rw [killTerm_outside hmT] at hihv
            exact hihv
          · rw [if_neg hrest]
            rw [if_neg hrest] at hihv
            rw [blockEncode_succ_apply hany hact, if_neg hmT, hihv, killTerm_outside hmT]

/-- **The injection.**  `ρ ↦ (blockEncode cs F ρ, blockMasks cs F ρ)` is injective. -/
theorem block_injective (cs : List (Clause n)) (F : ℕ) {ρ₁ ρ₂ : Restriction n}
    (henc : blockEncode cs F ρ₁ = blockEncode cs F ρ₂)
    (hmask : blockMasks cs F ρ₁ = blockMasks cs F ρ₂) : ρ₁ = ρ₂ := by
  rw [← blockEncode_recover cs F ρ₁, ← blockEncode_recover cs F ρ₂, henc, hmask]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.blockEncode_recover
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.block_injective
