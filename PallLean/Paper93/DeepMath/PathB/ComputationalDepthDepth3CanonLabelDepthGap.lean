import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DepthReplayTie
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEncPath

/-!
# The `canonLabelLen ↔ max-depth` gap is uncloseable pointwise

The encLits route bounds `canonLabelLen` — the **single satisfying-completion path** length; the
collapse needs `canonicalDT.depth` — the **max over all branches**.  The codebase asserts
`canonLabelLen ≤ depth` and that a good `canonLabelLen` "need not have `depth ≤ budget`".  This file
makes the obstruction a *theorem*: there is **no** pointwise bound `depth ≤ (satisfying-path length)`.

The witness is `cs = [{x₀}, {¬x₀, x₁}]` with `ρ` everywhere free:

* `encLits ρ cs = [x₀]` — the satisfying completion greedily satisfies `{x₀}`, which then **falsifies**
  `{¬x₀, x₁}`, so the satisfying path has length `1` and never touches `x₁`.
* but the canonical tree's **deepest** branch takes `x₀ := false` (falsifying `{x₀}`), which makes
  `¬x₀` true and leaves `x₁` free in the second clause — a *second* query — so `depth ≥ 2`
  (`canonicalDT_depth_ge_replay`, the all-falsify chain of length 2).

Hence `(encLits ρ cs).length = 1 < 2 ≤ depth`.  Since `canonLabelLen ≤ (encLits ρ cs).length` (the
canonical label dedupes the path literals), the same restriction has `canonLabelLen < depth`.

## Conclusion

`depth ≤ canonLabelLen` is **false** as a pointwise inequality — the gap is not a missing lemma but a
genuine quantity mismatch (the deepest branch explores falsify directions the satisfying completion
skips).  The switching lemma closes it only *probabilistically / in the aggregate*: the **count** of
restrictions with deep trees is small.  That aggregate bound is exactly the deepest-branch switching
count, whose tight decoder is the **empty-skip wall** (characterized, information-theoretic).  So
"closing the gap" is the irreducible switching-lemma content, here shown not to reduce to any
pointwise `canonLabelLen` bound — **not** faked.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP
untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

/-- The witness DNF `[{x₀}, {¬x₀, x₁}]` over `Fin 2`. -/
def gapCs : List (Clause 2) :=
  [⟨[Rung4Literal.pos 0]⟩, ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1]⟩]

/-- The everywhere-free restriction. -/
def gapRho : Fin 2 → Option Bool := fun _ => none

/-- **The satisfying-completion path is strictly shorter than the depth.**  For the witness, the
encLits satisfying path has length `1` while the canonical tree's depth is `≥ 2` — so there is no
pointwise bound `depth ≤ (satisfying-path length)`. -/
theorem encLits_length_lt_depth :
    (encLits gapRho gapCs).length < (canonicalDT gapCs 2 gapRho).depth := by
  have hdepth : 2 ≤ (canonicalDT gapCs 2 gapRho).depth :=
    canonicalDT_depth_ge_replay gapCs 2 gapRho 2 (le_refl 2) (by decide)
  have hlen : (encLits gapRho gapCs).length = 1 := by decide
  omega

/-- **The gap is uncloseable pointwise.**  There is a DNF and a restriction whose canonical-tree
depth strictly exceeds its satisfying-completion path length — so `depth ≤ (satisfying-path length)`
is not a theorem. -/
theorem depth_gt_satpath_witness :
    ∃ (cs : List (Clause 2)) (ρ : Fin 2 → Option Bool) (fuel : ℕ),
      (encLits ρ cs).length < (canonicalDT cs fuel ρ).depth :=
  ⟨gapCs, gapRho, 2, encLits_length_lt_depth⟩

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.encLits_length_lt_depth
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.depth_gt_satpath_witness
