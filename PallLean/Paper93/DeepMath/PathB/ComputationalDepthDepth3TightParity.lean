import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseCoreTight
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityRel

/-!
# Tight switching, step 14: the parity connection over the tight tree (branch `razborov-recoverRho-wip`)

The reconciliation that dissolves the `canonicalDT ↔ canonicalDTree` worry.  The tight `(2w)^s` count and
collapse (bricks 50–52) are over the **single-literal** canonical tree `canonicalDT`; the existing parity
capstone `shallow_canonical_not_parity` is over the **block** tree `canonicalDTree`, and
`depth canonicalDTree ≥ depth canonicalDT` runs the wrong way for a free bridge.

The resolution: we do **not** need a depth bridge at all.  The relativized parity lower bound
`parity_needs_full_depth_rel` is *generic* over `DTree n` — it says **any** decision tree computing parity
on a `σ`-subcube has depth `≥ stars σ`.  Since `toDTree (canonicalDT cs F σ)` computes `dnfValue cs` on the
`σ`-subcube (`canonicalDT_eval` + `toDTree_eval` + `dnfEval_eq_dnfValue`) and has depth equal to
`(canonicalDT cs F σ).depth` (`toDTree_depth`), the same argument applies to the *single-literal* tree.  So
**`canonicalDT` shallowness — exactly what the tight count delivers — already forces `DNF ≠ parity`** on the
subcube.  No block tree, no depth comparison.

* `canonicalDT_depth_ge_of_parity` — if `dnfValue cs` computes parity on the `σ`-subcube (and `stars σ ≤ F`)
  then `stars σ ≤ (canonicalDT cs F σ).depth`.
* `shallow_canonicalDT_not_parity` — if `(canonicalDT cs F σ).depth < stars σ` then some `σ`-consistent `x`
  witnesses `dnfValue cs x ≠ parity x`.

This is the tight analogue of foundation 29 (`shallow_canonical_not_parity`), and it is the missing piece
that lets the tight `canonicalDT` collapse feed a parity contradiction without the block tree.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Parity ⇒ the single-literal canonical tree is deep.**  If `dnfValue cs` computes parity on the
`σ`-subcube and `stars σ ≤ F`, then the single-literal canonical tree has depth `≥ stars σ`.  Proved by
applying the *generic* relativized parity bound to `toDTree (canonicalDT cs F σ)`. -/
theorem canonicalDT_depth_ge_of_parity (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    (hsf : SwitchingCounting.stars σ ≤ F)
    (hpar : ∀ x, DTree.agreeRestriction σ x → DTree.dnfValue cs x = DTree.parity x) :
    SwitchingCounting.stars σ ≤ (canonicalDT cs F σ).depth := by
  by_contra hlt
  push_neg at hlt
  refine DTree.parity_needs_full_depth_rel (toDTree (canonicalDT cs F σ)) σ ?_ ?_
  · intro x hx
    rw [toDTree_eval, canonicalDT_eval F σ x hsf hx, dnfEval_eq_dnfValue]
    exact hpar x hx
  · rw [toDTree_depth]; exact hlt

/-- **A shallow single-literal canonical tree cannot compute parity on the subcube.**  The tight analogue of
`shallow_canonical_not_parity`: if `depth < stars σ` (what the tight count delivers), some `σ`-consistent
input witnesses `dnfValue ≠ parity`. -/
theorem shallow_canonicalDT_not_parity (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    (hsf : SwitchingCounting.stars σ ≤ F)
    (hshallow : (canonicalDT cs F σ).depth < SwitchingCounting.stars σ) :
    ∃ x, DTree.agreeRestriction σ x ∧ DTree.dnfValue cs x ≠ DTree.parity x := by
  by_contra hall
  push_neg at hall
  exact absurd (canonicalDT_depth_ge_of_parity cs F σ hsf hall) (by omega)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDT_depth_ge_of_parity
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.shallow_canonicalDT_not_parity
