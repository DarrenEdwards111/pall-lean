import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayeredMerge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reduces

/-!
# Tight switching, step 41: the collapse+merge composition (branch `razborov-recoverRho-wip`)

The merge half of the per-round oracle (step 1 of the recursive-tower plan): after a collapse produces an
`OR`-of-`DNF`s (resp. `AND`-of-`CNF`s), merging with the same-type parent restores a single bottom `DNF`
(resp. `CNF`), one level shorter — and the whole round is one `EquivOn`.  Since `EquivOn ρ` is transitive
(it is pointwise eval-equality on the subcube), a collapse `EquivOn` composes with the (unconditional,
eval-preserving) merge `EquivOn` (`merge_gOr_dnf_EquivOn` / `merge_gAnd_cnf_EquivOn`) into a single
collapse+merge round.

* `EquivOn.trans` — `EquivOn ρ` is transitive.
* `collapse_then_merge_or` — compose a collapse-to-`OR`-of-`DNF`s with the `OR`-of-`DNF` merge.
* `collapse_then_merge_and` — the `AND`-of-`CNF` dual.

These are the round combinators the leaf-recursive oracle uses; the remaining work is the leaf-recursive
collapse over `Layered`-valued gates (the existing collapse rounds take clause-list gates, so they are
depth-4-bottom; deeper towers need the collapse applied at the leaves), which is a genuine generalisation.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **`EquivOn ρ` is transitive** (pointwise eval-equality on the `ρ`-subcube). -/
theorem EquivOn.trans {ρ : Fin n → Option Bool} {A B C : Layered n}
    (h1 : EquivOn ρ A B) (h2 : EquivOn ρ B C) : EquivOn ρ A C :=
  fun x hx => (h1 x hx).trans (h2 x hx)

/-- **Collapse + `OR`-merge round.**  A collapse equating `A` to an `OR` of `DNF` gates composes with the
`OR`-of-`DNF` merge into a single round equating `A` to the merged bottom `DNF`. -/
theorem collapse_then_merge_or {ρ : Fin n → Option Bool} {A : Layered n}
    (ds : List (List (Clause n)))
    (hcollapse : EquivOn ρ A (gOr (ds.map dnf))) :
    EquivOn ρ A (dnf ds.flatten) :=
  EquivOn.trans hcollapse (merge_gOr_dnf_EquivOn ρ ds)

/-- **Collapse + `AND`-merge round (dual).**  A collapse equating `A` to an `AND` of `CNF` gates composes
with the `AND`-of-`CNF` merge into a single round equating `A` to the merged bottom `CNF`. -/
theorem collapse_then_merge_and {ρ : Fin n → Option Bool} {A : Layered n}
    (cs : List (List (Clause n)))
    (hcollapse : EquivOn ρ A (gAnd (cs.map cnf))) :
    EquivOn ρ A (cnf cs.flatten) :=
  EquivOn.trans hcollapse (merge_gAnd_cnf_EquivOn ρ cs)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapse_then_merge_or
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapse_then_merge_and
