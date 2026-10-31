import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockDescent
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SatEncode

/-!
# Block-DT model, foundation 3: the satisfying global encoding (branch only)

`blockEncode cs F σ` is the boundary object of the holographic count: it follows the block descent
(killing terms to fix the block sequence) but sets **each block's term to its satisfying assignment**
(all that block's free variables to satisfying values), so the encoded restriction *satisfies every
killed term*.  The decoder then peels (`peelStream`) to read off the block stream.

* `blockEncode` — set this block's free coordinates of `T` to satisfying values, recurse (on the killed
  state) for later blocks.
* `blockEncode_extends` — it extends `σ` (only fills free coordinates).

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The satisfying global encoding.**  At each block with active term `T`: a coordinate free in `σ`
and occurring in `T` is set to its satisfying value; everything else follows the recursion on the
killed state. -/
def blockEncode (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → (Fin n → Option Bool)
  | 0, σ => σ
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then σ
    else match SwitchingCounting.activeTerm cs σ with
      | none => σ
      | some T =>
        fun v =>
          if σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits) then
            (if (Rung4Literal.pos v) ∈ T.lits then some true else some false)
          else blockEncode cs fuel (killTerm σ T) v

/-- **The satisfying global encoding extends `σ`.** -/
theorem blockEncode_extends (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool), Extends σ (blockEncode cs F σ) := by
  intro F
  induction F with
  | zero => intro σ v b h; rw [blockEncode]; exact h
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => intro v b h; rw [blockEncode]; simp only [hany, if_true]; exact h
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        intro v b h; rw [blockEncode]; simp only [hany, Bool.false_eq_true, if_false, hact]; exact h
      | some T =>
        intro v b h
        rw [blockEncode]
        simp only [hany, Bool.false_eq_true, if_false, hact]
        rw [if_neg (by rintro ⟨hn, _⟩; rw [h] at hn; exact absurd hn (by simp))]
        exact Extends_trans (killTerm_extends σ T) (ih (killTerm σ T)) v b h

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.blockEncode_extends
