import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalFresh
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DnfFresh

/-!
# AC⁰ reduction, foundation 19: the well-formedness-preserving layer collapse (branch only)

The layer collapse (brick 82) reduces an alternation level under one restriction, but its output gates
are bare clause-lists.  For the *next* round to apply, those clauses must again satisfy the switching
hypotheses — distinct variables (`Nodup`) and consistency (`Consistent`).  Here we close that loop: the
collapsed gates' clauses are well-formed, because they are `dtreeToCNF`/`dtreeToDNF` of a **fresh**
canonical tree (bricks 15/18) of a distinct-variable input.

* `collapse_or_layer_wf` — `collapse_or_layer` plus: every output `CNF` clause is `Consistent` and has
  distinct variables.
* `collapse_and_layer_wf` — the dual, for the output `DNF` terms.

Together with the width bound (`< s`), the output is a valid input to the next round at width `w' = s` —
the precondition closure the depth induction iterates.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace Layered

variable {n : ℕ}

/-- **The well-formedness-preserving `OR`-layer collapse.**  The collapsed `CNF` clauses are `Consistent`
with distinct variables, so the output re-enters the next round. -/
theorem collapse_or_layer_wf {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s : ℕ) (hF : n < F)
    (gates : List (Finset (List (Clause n)))) (Gtot : Finset (List (Clause n)))
    (hsub : ∀ G ∈ gates, G ⊆ Gtot)
    (hcons : ∀ g ∈ Gtot, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ Gtot, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ Gtot, ∀ T ∈ g, T.lits.length ≤ w)
    (hsmall : (Gtot.card : ℚ)
        * ((2 * p / (1 - p)) ^ s
            * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)) < 1) :
    ∃ ρ : Fin n → Option Bool,
      EquivOn ρ (gOr (gates.map (fun G => gAnd (G.toList.map dnf))))
          (gOr (gates.map (fun G => cnf (G.toList.flatMap
            (fun g => dtreeToCNF (canonicalDTree g w F ρ))))))
        ∧ (∀ G ∈ gates, ∀ C ∈ G.toList.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ)),
            C.lits.length < s)
        ∧ (∀ G ∈ gates, ∀ C ∈ G.toList.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ)),
            Consistent C ∧ (C.lits.map litVarOf).Nodup) := by
  obtain ⟨ρ, hequiv, hwidth⟩ :=
    collapse_or_layer hp0 hp3 w F s hF gates Gtot hsub hcons hnd hw hsmall
  refine ⟨ρ, hequiv, hwidth, ?_⟩
  intro G hG C hC
  rw [List.mem_flatMap] at hC
  obtain ⟨g, hg, hCg⟩ := hC
  have hndg : ∀ T ∈ g, (T.lits.map litVarOf).Nodup := hnd g (hsub G hG (Finset.mem_toList.mp hg))
  have hfresh := canonicalDTree_fresh g w hndg F ρ
  exact ⟨dtreeToCNF_consistent _ hfresh C hCg, dtreeToCNF_nodup _ hfresh C hCg⟩

/-- **The well-formedness-preserving `AND`-layer collapse (dual).**  The collapsed `DNF` terms are
`Consistent` with distinct variables. -/
theorem collapse_and_layer_wf {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s : ℕ) (hF : n < F)
    (gates : List (Finset (List (Clause n)))) (Gtot : Finset (List (Clause n)))
    (hsub : ∀ G ∈ gates, G ⊆ Gtot)
    (hcons : ∀ g ∈ Gtot, ∀ C ∈ g, Consistent C)
    (hnd : ∀ g ∈ Gtot, ∀ C ∈ g, (C.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ Gtot, ∀ C ∈ g, C.lits.length ≤ w)
    (hsmall : (Gtot.card : ℚ)
        * ((2 * p / (1 - p)) ^ s
            * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)) < 1) :
    ∃ ρ : Fin n → Option Bool,
      EquivOn ρ (gAnd (gates.map (fun G => gOr (G.toList.map cnf))))
          (gAnd (gates.map (fun G => dnf (G.toList.flatMap
            (fun g => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ)))))))
        ∧ (∀ G ∈ gates, ∀ T ∈ G.toList.flatMap
              (fun g => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ))),
            T.lits.length < s)
        ∧ (∀ G ∈ gates, ∀ T ∈ G.toList.flatMap
              (fun g => dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ))),
            Consistent T ∧ (T.lits.map litVarOf).Nodup) := by
  obtain ⟨ρ, hequiv, hwidth⟩ :=
    collapse_and_layer hp0 hp3 w F s hF gates Gtot hsub hcons hnd hw hsmall
  refine ⟨ρ, hequiv, hwidth, ?_⟩
  intro G hG T hT
  rw [List.mem_flatMap] at hT
  obtain ⟨g, hg, hTg⟩ := hT
  have hndg : ∀ C ∈ g, (C.lits.map litVarOf).Nodup := hnd g (hsub G hG (Finset.mem_toList.mp hg))
  have hndneg : ∀ C ∈ negDNF g, (C.lits.map litVarOf).Nodup := by
    intro C hC
    rw [negDNF, List.mem_map] at hC
    obtain ⟨C0, hC0, rfl⟩ := hC
    have hmap : (C0.lits.map negLit).map litVarOf = C0.lits.map litVarOf := by
      rw [List.map_map]; exact List.map_congr_left (fun ℓ _ => litVarOf_negLit ℓ)
    simpa [hmap] using hndg C0 hC0
  have hfresh := DTree.negTree_fresh _ (canonicalDTree_fresh (negDNF g) w hndneg F ρ)
  exact ⟨dtreeToDNF_consistent _ hfresh T hTg, dtreeToDNF_nodup _ hfresh T hTg⟩

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_or_layer_wf
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_and_layer_wf
