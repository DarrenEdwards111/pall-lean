import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockRecover

/-!
# Block-DT model, foundation 5: the peel advance (branch only)

The obstruction (brick 4): `killTerm` cannot advance the peel, because `blockEncode` has already *fixed*
the block's variables (to satisfying values), and `killTerm` only touches *free* coordinates.  The fix:
reset exactly the **block variables** of `T` (those free in `σ` and occurring in `T`) to their killing
values.  This file proves the resulting **advance equality**:

  `blockEncode cs F (killTerm σ T) v =`
  `  if (σ v = none ∧ v ∈ T) then (killTerm σ T) v else blockEncode cs (F+1) σ v`,

i.e. `blockEncode cs F (killTerm σ T)` is `blockEncode cs (F+1) σ` with the block variables of `T` reset
from satisfying to killing values.  This is exactly the peel step: from the boundary that satisfies `T`
(and all later terms) to the boundary that has `T` killed (and still satisfies the later terms) — so the
*next* first satisfied term is the next active term.

The block-variable set `{v : σ v = none ∧ v ∈ T}` is precisely the stars-pattern the label records
(positions `< w` within `T`), so this advance is realised by a label-aware peel.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The peel advance.**  `blockEncode cs F (killTerm σ T)` equals `blockEncode cs (F+1) σ` with the
block variables of `T` reset to their killing values. -/
theorem blockEncode_advance {cs : List (Clause n)} {F : ℕ} {σ : Restriction n} {T : Clause n}
    (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T) (v : Fin n) :
    blockEncode cs F (killTerm σ T) v =
      if σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits) then
        killTerm σ T v
      else blockEncode cs (F + 1) σ v := by
  by_cases hc : σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits)
  · rw [if_pos hc]
    obtain ⟨hvn, hvT⟩ := hc
    have hkv : killTerm σ T v = some (if (Rung4Literal.pos v) ∈ T.lits then false else true) := by
      simp only [killTerm]
      rw [if_pos hvn]
      by_cases hp : (Rung4Literal.pos v) ∈ T.lits
      · rw [if_pos hp, if_pos hp]
      · rcases hvT with hp' | hn
        · exact absurd hp' hp
        · rw [if_neg hp, if_pos hn, if_neg hp]
    rw [hkv]
    exact blockEncode_extends cs F (killTerm σ T) v _ hkv
  · rw [if_neg hc, blockEncode_succ_apply hany hact, if_neg hc]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.blockEncode_advance
