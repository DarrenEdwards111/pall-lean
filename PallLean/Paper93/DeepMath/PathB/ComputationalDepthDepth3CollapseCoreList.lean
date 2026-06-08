import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerCollapse

/-!
# AC⁰ reduction, foundation 29: the list-form collapse cores (branch only)

A round's output gates arrive as a *list* (one collapsed gate per gate of the previous round), but the
collapse cores (brick 17) are stated over a `Finset` (via `G.toList`).  The cores never use the
finiteness — only `G.toList` — so we restate them over a plain `List`, removing the `List`↔`Finset`
friction that blocks chaining round `i+1` onto round `i`'s output.

* `collapse_core_list` — `AND`-of-`DNF`s (over a clause-list-list `Cs`) collapses, given `ρ` shallow for
  every gate, to one `CNF` on the `ρ`-subcube, width `< s`.
* `collapse_core_or_list` — the dual.

These are the round cores in the exact shape the multi-round loop produces and consumes.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace Layered

variable {n : ℕ}

private theorem all_congr {α : Type*} (l : List α) (P Q : α → Bool) (h : ∀ a ∈ l, P a = Q a) :
    l.all P = l.all Q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

private theorem any_congr {α : Type*} (l : List α) (P Q : α → Bool) (h : ∀ a ∈ l, P a = Q a) :
    l.any P = l.any Q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- **List-form `AND`-of-`DNF` collapse core.**  Given `ρ` shallow for every gate of the list `Cs`, the
concatenated `dtreeToCNF` computes the `AND` of the DNFs on the `ρ`-subcube, width `< s`. -/
theorem collapse_core_list (w F s : ℕ) (Cs : List (List (Clause n))) {ρ : Fin n → Option Bool}
    (hstars : stars ρ < F) (hshallow : ∀ g ∈ Cs, (canonicalDTree g w F ρ).depth < s) :
    (∀ x, DTree.agreeRestriction ρ x →
        cnfValue (Cs.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ))) x
          = (ACircuit.and (Cs.map dnfToCircuit)).eval x)
      ∧ (∀ C ∈ Cs.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ)), C.lits.length < s) := by
  constructor
  · intro x hx
    have h1 : (ACircuit.and (Cs.map dnfToCircuit)).eval x
        = Cs.all (fun g => DTree.dnfValue g x) := by
      rw [ACircuit.eval_and, List.all_map]
      exact all_congr _ _ _ (fun g _ => dnfToCircuit_eval g x)
    have h2 : cnfValue (Cs.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ))) x
        = Cs.all (fun g => DTree.dnfValue g x) := by
      rw [cnfValue, List.all_flatMap]
      apply all_congr
      intro g _
      rw [← cnfValue, dtreeToCNF_eval, canonicalDTree_eval g w F ρ x hstars hx]
    rw [h2, h1]
  · intro C hC
    rw [List.mem_flatMap] at hC
    obtain ⟨g, hg, hCg⟩ := hC
    have hwidth := dtreeToCNF_width (canonicalDTree g w F ρ) C hCg
    have hshal := hshallow g hg
    omega

/-- **List-form `OR`-of-`CNF` collapse core (dual).** -/
theorem collapse_core_or_list (w F s : ℕ) (Cs : List (List (Clause n))) {ρ : Fin n → Option Bool}
    (hstars : stars ρ < F)
    (hshallow : ∀ g ∈ Cs, (canonicalDTree (negDNF g) w F ρ).depth < s) :
    (∀ x, DTree.agreeRestriction ρ x →
        DTree.dnfValue
            (Cs.flatMap (fun g =>
              dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ)))) x
          = (ACircuit.or (Cs.map cnfToCircuit)).eval x)
      ∧ (∀ T ∈ Cs.flatMap (fun g =>
              dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ))), T.lits.length < s) := by
  constructor
  · intro x hx
    have h1 : (ACircuit.or (Cs.map cnfToCircuit)).eval x
        = Cs.any (fun g => cnfValue g x) := by
      rw [ACircuit.eval_or, List.any_map]
      exact any_congr _ _ _ (fun g _ => cnfToCircuit_eval g x)
    have h2 : DTree.dnfValue
          (Cs.flatMap (fun g =>
            dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ)))) x
        = Cs.any (fun g => cnfValue g x) := by
      rw [DTree.dnfValue, List.any_flatMap]
      apply any_congr
      intro g _
      rw [← DTree.dnfValue, dtreeToDNF_eval, DTree.negTree_eval,
        canonicalDTree_eval (negDNF g) w F ρ x hstars hx, ← cnfValue_eq_not_dnfValue_negDNF]
    rw [h2, h1]
  · intro T hT
    rw [List.mem_flatMap] at hT
    obtain ⟨g, hg, hTg⟩ := hT
    have hwidth := dtreeToDNF_width (DTree.negTree (canonicalDTree (negDNF g) w F ρ)) T hTg
    rw [DTree.negTree_depth] at hwidth
    have hshal := hshallow g hg
    omega

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_core_list
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_core_or_list
