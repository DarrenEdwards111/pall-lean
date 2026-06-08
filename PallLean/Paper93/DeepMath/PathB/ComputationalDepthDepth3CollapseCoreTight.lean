import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseAdapter
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TreeBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeToCNF

/-!
# Tight switching, step 4: the collapse core over the tight-count tree (branch `razborov-recoverRho-wip`)

The collapse port (the user's *option 2*): re-express the per-gate switching collapse over
`toDTree (canonicalDT cs F ρ)` — the `DTree` image of the **single-literal** canonical tree — instead of
the block tree `canonicalDTree`.  This is the tree the **tight `(2w)^s` count** (`tight_descent_switching_prob`)
is about, so the tight cap now governs the collapse's shallowness directly.

The eval-correctness reuses `canonicalDT_eval` (the single-literal tree computes the DNF on extensions),
bridged by `toDTree_eval` (step 3) and the trivial `dnfEval = dnfValue` / `Rung4Restriction.Extends =
agreeRestriction` identifications; the width bound reuses `dtreeToCNF_width` + `toDTree_depth`.

* `evalLits_eq_all`, `dnfEval_eq_dnfValue` — the DNF-semantics bridge (`dnfEval = DTree.dnfValue`).
* `collapse_core_tight` — `dtreeToCNF (toDTree (canonicalDT cs F ρ))` is a CNF computing `cs` on the
  `ρ`-subcube, every clause of width `< s` whenever the single-literal tree has depth `< s`.

So one gate collapses to a width-`< s` CNF whose underlying tree is `canonicalDT` — the tight-count tree.
The shallowness hypothesis `depth (canonicalDT …) < s` is exactly what `tight_descent_switching_prob`
delivers (no `(4^w+1)^F`).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting Rung4DNFTerm

variable {n : ℕ}

/-- `evalLits` is `List.all` of the literal evaluations. -/
theorem evalLits_eq_all (l : List (Rung4Literal n)) (x : Fin n → Bool) :
    evalLits l x = l.all (fun ℓ => Rung4Literal.eval ℓ x) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [evalLits, List.all_cons, ih]

/-- The collapse-adapter DNF value equals the `DTree` DNF value. -/
theorem dnfEval_eq_dnfValue (cs : List (Clause n)) (x : Fin n → Bool) :
    dnfEval cs x = DTree.dnfValue cs x := by
  unfold dnfEval DTree.dnfValue
  simp only [evalLits_eq_all]

/-- **The collapse core over the tight-count tree.**  With fuel `≥ stars` and the single-literal canonical
tree shallow (`depth < s`), its `dtreeToCNF` (via `toDTree`) is a width-`< s` CNF computing `cs` on the
`ρ`-subcube. -/
theorem collapse_core_tight (F s : ℕ) (cs : List (Clause n)) {ρ : Fin n → Option Bool}
    (hstars : SwitchingCounting.stars ρ ≤ F)
    (hshallow : (canonicalDT cs F ρ).depth < s) :
    (∀ x, DTree.agreeRestriction ρ x →
        cnfValue (dtreeToCNF (toDTree (canonicalDT cs F ρ))) x = DTree.dnfValue cs x)
      ∧ (∀ C ∈ dtreeToCNF (toDTree (canonicalDT cs F ρ)), C.lits.length < s) := by
  refine ⟨fun x hx => ?_, fun C hC => ?_⟩
  · rw [dtreeToCNF_eval, toDTree_eval, canonicalDT_eval F ρ x hstars hx, dnfEval_eq_dnfValue]
  · have hwidth := dtreeToCNF_width (toDTree (canonicalDT cs F ρ)) C hC
    rw [toDTree_depth] at hwidth
    omega

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dnfEval_eq_dnfValue
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapse_core_tight
