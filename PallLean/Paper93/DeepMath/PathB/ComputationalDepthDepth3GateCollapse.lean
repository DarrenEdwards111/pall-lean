import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseCoreList

/-!
# AC⁰ reduction, foundation 30: the whole-gate collapses (branch only)

The depth-`3 → 2` round operations, dual to the layer collapses (which are depth-`4 → 3`).  After a layer
collapse leaves an `OR`-of-`CNF`s (or an `AND`-of-`DNF`s), the next round collapses that *whole* gate to a
single `DNF` (resp. `CNF`) on the subcube — the switching of the bottom CNFs/DNFs with the merge built into
the `flatMap` (brick 29's list cores).  Phrased as restriction-given `EquivOn`s, they are `Reduces` steps
(brick 20) ready to chain.

* `collapse_gAnd_dnf_at` — `gAnd (Cs.map dnf)` `EquivOn ρ` `cnf (concatenated switched clauses)`, width `<s`.
* `collapse_gOr_cnf_at` — `gOr (Cs.map cnf)` `EquivOn ρ` `dnf (concatenated switched terms)`, width `<s`.

With the layer collapses (bricks 17/26) and the merge (brick 28), these are the full set of one-round
operations the `d`-fold loop chains.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace Layered

variable {n : ℕ}

/-- **Whole `AND`-of-`DNF`s collapse.**  Given `ρ` shallow for every DNF gate, the `AND`-of-`DNF`s is
`EquivOn ρ` the single `CNF` concatenating the switched clauses, of width `< s`. -/
theorem collapse_gAnd_dnf_at (w F s : ℕ) (Cs : List (List (Clause n))) (ρ : Fin n → Option Bool)
    (hstars : stars ρ < F) (hshallow : ∀ g ∈ Cs, (canonicalDTree g w F ρ).depth < s) :
    EquivOn ρ (gAnd (Cs.map dnf))
        (cnf (Cs.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ))))
      ∧ (∀ C ∈ Cs.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ)), C.lits.length < s) := by
  obtain ⟨heq, hwidth⟩ := collapse_core_list w F s Cs hstars hshallow
  refine ⟨fun x hx => ?_, hwidth⟩
  rw [eval_gAnd_dnf, eval_cnf]
  exact (heq x hx).symm

/-- **Whole `OR`-of-`CNF`s collapse (dual).**  Given `ρ` shallow for every gate's negated DNF, the
`OR`-of-`CNF`s is `EquivOn ρ` the single `DNF` concatenating the switched terms, of width `< s`. -/
theorem collapse_gOr_cnf_at (w F s : ℕ) (Cs : List (List (Clause n))) (ρ : Fin n → Option Bool)
    (hstars : stars ρ < F) (hshallow : ∀ g ∈ Cs, (canonicalDTree (negDNF g) w F ρ).depth < s) :
    EquivOn ρ (gOr (Cs.map cnf))
        (dnf (Cs.flatMap (fun g => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ)))))
      ∧ (∀ T ∈ Cs.flatMap (fun g => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ))),
          T.lits.length < s) := by
  obtain ⟨heq, hwidth⟩ := collapse_core_or_list w F s Cs hstars hshallow
  refine ⟨fun x hx => ?_, hwidth⟩
  rw [eval_gOr_cnf, eval_dnf]
  exact (heq x hx).symm

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_gAnd_dnf_at
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_gOr_cnf_at
