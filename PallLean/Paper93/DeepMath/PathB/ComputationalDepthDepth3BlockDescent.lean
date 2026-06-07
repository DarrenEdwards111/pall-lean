import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockKill

/-!
# Block-DT model, foundation 2: the block descent (branch only)

The block descent is **deterministic** (unlike the binary `deepestEnd`, which compares child depths):
at each block, kill the active term (`killTerm`) and recurse.  This is the canonical *deepest* branch
of the block tree — killing keeps the path going, satisfying would stop it.

* `blockEnd cs F σ` — the leaf after `F` blocks (the canonical falsifying path's end-state).
* `blockStream cs F σ` — the active terms killed, in order.
* `Extends_trans` — transitivity of `Extends`.
* `blockEnd_extends` — the leaf extends `σ` (each block only fills free coordinates).
* `blockStream_length_le` — at most `F` blocks.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The block descent leaf.**  Kill the active term each block; stop when none is active. -/
def blockEnd (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → (Fin n → Option Bool)
  | 0, σ => σ
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then σ
    else match SwitchingCounting.activeTerm cs σ with
      | none => σ
      | some T => blockEnd cs fuel (killTerm σ T)

/-- **The block active-term stream.**  The terms killed along the block descent, in order. -/
def blockStream (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → List (Clause n)
  | 0, _ => []
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then []
    else match SwitchingCounting.activeTerm cs σ with
      | none => []
      | some T => T :: blockStream cs fuel (killTerm σ T)

/-- `Extends` is transitive. -/
theorem Extends_trans {ρ σ τ : Restriction n} (h1 : Extends ρ σ) (h2 : Extends σ τ) :
    Extends ρ τ := fun v b h => h2 v b (h1 v b h)

/-- **The block leaf extends `σ`.** -/
theorem blockEnd_extends (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool), Extends σ (blockEnd cs F σ) := by
  intro F
  induction F with
  | zero => intro σ v b h; rw [blockEnd]; exact h
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => intro v b h; rw [blockEnd]; simp only [hany, if_true]; exact h
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        intro v b h; rw [blockEnd]; simp only [hany, Bool.false_eq_true, if_false, hact]; exact h
      | some T =>
        have hstep : blockEnd cs (F + 1) σ = blockEnd cs F (killTerm σ T) := by
          rw [blockEnd]; simp only [hany, Bool.false_eq_true, if_false, hact]
        rw [hstep]
        exact Extends_trans (killTerm_extends σ T) (ih (killTerm σ T))

/-- **At most `F` blocks.** -/
theorem blockStream_length_le (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool), (blockStream cs F σ).length ≤ F := by
  intro F
  induction F with
  | zero => intro σ; simp [blockStream]
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [blockStream]; simp only [hany, if_true, List.length_nil]; omega
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [blockStream]; simp only [hany, Bool.false_eq_true, if_false, hact, List.length_nil]; omega
      | some T =>
        have hstep : blockStream cs (F + 1) σ = T :: blockStream cs F (killTerm σ T) := by
          rw [blockStream]; simp only [hany, Bool.false_eq_true, if_false, hact]
        rw [hstep, List.length_cons]
        have := ih (killTerm σ T); omega

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.blockEnd_extends
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.blockStream_length_le
