import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Layered

/-!
# AC⁰ reduction, foundation 17: the simultaneous layer collapse (branch only)

The genuine inductive step of the multi-round switching argument: a whole *layer* of bottom gates
collapses under a **single** restriction.  This is the primitive the per-gate collapse
(brick 81) could not supply on its own — the union bound must be taken over *all* bottom gates of the
layer at once, so one restriction makes every gate shallow simultaneously, and the depth of the entire
circuit drops by one in lockstep.

* `collapse_core` / `collapse_core_or` — the restriction-given core: once `ρ` makes a gate's bottom DNFs
  (resp. negated CNFs) shallow, the concatenated `dtreeToCNF` (resp. `dtreeToDNF`) computes the gate on the
  `ρ`-subcube with width `< s`.  This is `single_round_collapse`'s body factored out so a *shared* `ρ` can
  drive many gates.
* `collapse_or_layer` — an `OR` of `AND`-of-`DNF` gates collapses, under one restriction (union bound over
  the union of all gates' DNFs), to an `OR` of `CNF`s.  Depth `4 → 3`.
* `collapse_and_layer` — the dual: an `AND` of `OR`-of-`CNF` gates collapses to an `AND` of `DNF`s.

Iterating the two layer collapses (alternating, threading the restrictions via `round_compose`/`composeR`,
re-establishing `Nodup`+`Consistent` by bricks 79/80) drives a depth-`d` tower to depth `2`.  Terminating
at the depth-2 parity bound (brick 35) and the `poly(w)` base remain.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace Layered

variable {n : ℕ}

private theorem all_congr {α : Type*} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

private theorem any_congr {α : Type*} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- `eval` of an `AND`-of-`DNF` tower as an `ACircuit`. -/
theorem eval_gAnd_dnf (gs : List (List (Clause n))) (x : Fin n → Bool) :
    eval (gAnd (gs.map dnf)) x = (ACircuit.and (gs.map dnfToCircuit)).eval x := by
  simp only [eval, toCircuit, toCircuitList_eq, List.map_map]; rfl

/-- `eval` of an `OR`-of-`CNF` tower as an `ACircuit`. -/
theorem eval_gOr_cnf (gs : List (List (Clause n))) (x : Fin n → Bool) :
    eval (gOr (gs.map cnf)) x = (ACircuit.or (gs.map cnfToCircuit)).eval x := by
  simp only [eval, toCircuit, toCircuitList_eq, List.map_map]; rfl

/-- **The restriction-given collapse core (`AND`-of-`DNF`).**  Once `ρ` makes every bottom DNF of `G`
shallow, the concatenated `dtreeToCNF` computes the `AND` of the DNFs on the `ρ`-subcube, width `< s`. -/
theorem collapse_core (w F s : ℕ) (G : Finset (List (Clause n))) {ρ : Fin n → Option Bool}
    (hstars : stars ρ < F) (hshallow : ∀ g ∈ G, (canonicalDTree g w F ρ).depth < s) :
    (∀ x, DTree.agreeRestriction ρ x →
        cnfValue (G.toList.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ))) x
          = (ACircuit.and (G.toList.map dnfToCircuit)).eval x)
      ∧ (∀ C ∈ G.toList.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ)),
          C.lits.length < s) := by
  constructor
  · intro x hx
    have h1 : (ACircuit.and (G.toList.map dnfToCircuit)).eval x
        = G.toList.all (fun g => DTree.dnfValue g x) := by
      rw [ACircuit.eval_and, List.all_map]
      exact all_congr _ _ _ (fun g _ => dnfToCircuit_eval g x)
    have h2 : cnfValue (G.toList.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ))) x
        = G.toList.all (fun g => DTree.dnfValue g x) := by
      rw [cnfValue, List.all_flatMap]
      apply all_congr
      intro g _
      rw [← cnfValue, dtreeToCNF_eval, canonicalDTree_eval g w F ρ x hstars hx]
    rw [h2, h1]
  · intro C hC
    rw [List.mem_flatMap] at hC
    obtain ⟨g, hg, hCg⟩ := hC
    have hwidth := dtreeToCNF_width (canonicalDTree g w F ρ) C hCg
    have hshal := hshallow g (Finset.mem_toList.mp hg)
    omega

/-- **The restriction-given collapse core (`OR`-of-`CNF`, dual).**  Once `ρ` makes every gate's negated DNF
shallow, the concatenated negated `dtreeToDNF` computes the `OR` of the CNFs on the `ρ`-subcube. -/
theorem collapse_core_or (w F s : ℕ) (G : Finset (List (Clause n))) {ρ : Fin n → Option Bool}
    (hstars : stars ρ < F)
    (hshallow : ∀ g ∈ G, (canonicalDTree (negDNF g) w F ρ).depth < s) :
    (∀ x, DTree.agreeRestriction ρ x →
        DTree.dnfValue
            (G.toList.flatMap (fun g =>
              dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ)))) x
          = (ACircuit.or (G.toList.map cnfToCircuit)).eval x)
      ∧ (∀ T ∈ G.toList.flatMap (fun g =>
              dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ))), T.lits.length < s) := by
  constructor
  · intro x hx
    have h1 : (ACircuit.or (G.toList.map cnfToCircuit)).eval x
        = G.toList.any (fun g => cnfValue g x) := by
      rw [ACircuit.eval_or, List.any_map]
      exact any_congr _ _ _ (fun g _ => cnfToCircuit_eval g x)
    have h2 : DTree.dnfValue
          (G.toList.flatMap (fun g =>
            dtreeToDNF (DTree.negTree (canonicalDTree (negDNF g) w F ρ)))) x
        = G.toList.any (fun g => cnfValue g x) := by
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
    have hshal := hshallow g (Finset.mem_toList.mp hg)
    omega

/-- **The simultaneous `OR`-layer collapse.**  An `OR` of `AND`-of-`DNF` gates collapses, under a single
restriction (union bound over all gates' DNFs), to an `OR` of `CNF`s.  Depth `4 → 3`. -/
theorem collapse_or_layer {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s : ℕ) (hF : n < F)
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
            C.lits.length < s) := by
  obtain ⟨ρ, hρ⟩ := exists_shallow_all hp0 hp3 w F s Gtot hcons hnd hw hsmall
  have hstars : stars ρ < F :=
    lt_of_le_of_lt (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  have hshallow : ∀ G ∈ gates, ∀ g ∈ G, (canonicalDTree g w F ρ).depth < s :=
    fun G hG g hg => hρ g (hsub G hG hg)
  refine ⟨ρ, ?_, ?_⟩
  · intro x hx
    rw [eval_gOr, eval_gOr, List.any_map, List.any_map]
    apply any_congr
    intro G hG
    simp only [Function.comp_apply]
    rw [eval_gAnd_dnf, eval_cnf]
    exact ((collapse_core w F s G hstars (hshallow G hG)).1 x hx).symm
  · intro G hG C hC
    exact (collapse_core w F s G hstars (hshallow G hG)).2 C hC

/-- **The simultaneous `AND`-layer collapse (dual).**  An `AND` of `OR`-of-`CNF` gates collapses, under a
single restriction, to an `AND` of `DNF`s.  Depth `4 → 3`. -/
theorem collapse_and_layer {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s : ℕ) (hF : n < F)
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
            T.lits.length < s) := by
  classical
  -- the negated gate set inherits the switching hypotheses (De Morgan, brick 75)
  have hcons' : ∀ g ∈ Gtot.image negDNF, ∀ T ∈ g, Consistent T := by
    intro g hg T hT
    rw [Finset.mem_image] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [negDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    exact consistent_negClause (hcons g0 hg0 C hC)
  have hnd' : ∀ g ∈ Gtot.image negDNF, ∀ T ∈ g, (T.lits.map litVarOf).Nodup := by
    intro g hg T hT
    rw [Finset.mem_image] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [negDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    have hmap : (C.lits.map negLit).map litVarOf = C.lits.map litVarOf := by
      rw [List.map_map]; exact List.map_congr_left (fun ℓ _ => litVarOf_negLit ℓ)
    simpa [hmap] using hnd g0 hg0 C hC
  have hw' : ∀ g ∈ Gtot.image negDNF, ∀ T ∈ g, T.lits.length ≤ w := by
    intro g hg T hT
    rw [Finset.mem_image] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [negDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    simpa using hw g0 hg0 C hC
  have hcap_nonneg : 0 ≤ (2 * p / (1 - p)) ^ s
      * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ) := by
    have hp1 : (0 : ℚ) < 1 - p := by linarith
    positivity
  have hsmall' : ((Gtot.image negDNF).card : ℚ)
      * ((2 * p / (1 - p)) ^ s
          * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)) < 1 :=
    lt_of_le_of_lt
      (by exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le) hcap_nonneg)
      hsmall
  obtain ⟨ρ, hρ⟩ := exists_shallow_all hp0 hp3 w F s (Gtot.image negDNF) hcons' hnd' hw' hsmall'
  have hstars : stars ρ < F :=
    lt_of_le_of_lt (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  have hshallow : ∀ G ∈ gates, ∀ g ∈ G, (canonicalDTree (negDNF g) w F ρ).depth < s :=
    fun G hG g hg => hρ (negDNF g) (Finset.mem_image_of_mem negDNF (hsub G hG hg))
  refine ⟨ρ, ?_, ?_⟩
  · intro x hx
    rw [eval_gAnd, eval_gAnd, List.all_map, List.all_map]
    apply all_congr
    intro G hG
    simp only [Function.comp_apply]
    rw [eval_gOr_cnf, eval_dnf]
    exact ((collapse_core_or w F s G hstars (hshallow G hG)).1 x hx).symm
  · intro G hG T hT
    exact (collapse_core_or w F s G hstars (hshallow G hG)).2 T hT

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_core
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_core_or
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_or_layer
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_and_layer
