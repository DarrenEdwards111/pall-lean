import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightLayerCollapse

/-!
# Tight switching, step 20: the tight dual collapse core (`OR`-of-`CNF` → `DNF`) (branch `razborov-recoverRho-wip`)

The dual of `collapse_core_tight_list` (step 16), needed to reach a *single bottom `DNF`* endpoint for the
parity capstone.  The `F`-independent analogue of the crude `collapse_core_or` (`canonicalDTree`): once `ρ`
makes every gate's *negated* DNF's single-literal canonical tree shallow, the concatenated
`dtreeToDNF (negTree (toDTree (canonicalDT (negDNF g) F ρ)))` computes the `OR` of the CNFs on the
`ρ`-subcube, width `< s`.

This is the round that turns a depth-3 `OR`-of-`CNF` tower into a depth-2 bottom `DNF`, on which
`shallow_canonicalDT_not_parity` (step 14) then applies — closing the depth-3 case.

* `collapse_core_or_tight` — the dual collapse core over the tight tree.

Carries the per-`negDNF`-gate shallowness; eval-correctness needs `stars ρ ≤ F` (free from `n ≤ F`).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered Classical

variable {n : ℕ}

private theorem any_congr_or {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.any_cons, List.any_cons, h a (by simp),
      ih (fun b hb => h b (by simp [hb]))]

/-- **The tight dual collapse core (`OR`-of-`CNF`).**  Once `ρ` makes every gate's negated DNF's
single-literal canonical tree shallow (with `stars ρ ≤ F`), the concatenated negated `dtreeToDNF` computes
the `OR` of the CNFs on the `ρ`-subcube, width `< s`. -/
theorem collapse_core_or_tight (F s : ℕ) (G : Finset (List (Clause n)))
    {ρ : Fin n → Option Bool} (hstars : SwitchingCounting.stars ρ ≤ F)
    (hshallow : ∀ g ∈ G, (canonicalDT (negDNF g) F ρ).depth < s) :
    (∀ x, DTree.agreeRestriction ρ x →
        DTree.dnfValue
            (G.toList.flatMap (fun g =>
              dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ))))) x
          = (ACircuit.or (G.toList.map cnfToCircuit)).eval x)
      ∧ (∀ T ∈ G.toList.flatMap (fun g =>
              dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ)))),
            T.lits.length < s) := by
  constructor
  · intro x hx
    have h1 : (ACircuit.or (G.toList.map cnfToCircuit)).eval x
        = G.toList.any (fun g => cnfValue g x) := by
      rw [ACircuit.eval_or, List.any_map]
      exact any_congr_or _ _ _ (fun g _ => cnfToCircuit_eval g x)
    have h2 : DTree.dnfValue
          (G.toList.flatMap (fun g =>
            dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ))))) x
        = G.toList.any (fun g => cnfValue g x) := by
      rw [DTree.dnfValue, List.any_flatMap]
      apply any_congr_or
      intro g _
      rw [← DTree.dnfValue, dtreeToDNF_eval, DTree.negTree_eval, toDTree_eval,
        canonicalDT_eval (cs := negDNF g) F ρ x hstars hx, dnfEval_eq_dnfValue,
        ← cnfValue_eq_not_dnfValue_negDNF]
    rw [h2, h1]
  · intro T hT
    rw [List.mem_flatMap] at hT
    obtain ⟨g, hg, hTg⟩ := hT
    have hwidth := dtreeToDNF_width (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ))) T hTg
    rw [DTree.negTree_depth, toDTree_depth] at hwidth
    have hshal := hshallow g (Finset.mem_toList.mp hg)
    omega

/-- **The tight dual `EquivOn` round (`OR`-of-`CNF` → `DNF`).**  Depth `3 → 2`: an `OR` of `CNF` gates
collapses, under a single `F`-independent restriction, to a single bottom `DNF` built from the negated
single-literal canonical trees.  This is the round whose endpoint `shallow_canonicalDT_not_parity` (step 14)
refutes. -/
theorem collapse_to_dnf_layer_tight {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (hF : n ≤ F) (G : Finset (List (Clause n)))
    (hnf : ∀ g ∈ G.image negDNF, ∀ ρ : Restriction n, ∀ U ∈ g,
      SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ g ∈ G.image negDNF, ∀ ρ : Restriction n,
      SwitchingCounting.anyTermSat g (deepestEnd g F ρ) = false)
    (hpos : ∀ g ∈ G.image negDNF, ∀ ρ : Restriction n, ∀ q ∈ deepestFullSeq g F ρ, q.1 < w)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ)) < 1)
    (hsmall : ((G.image negDNF).card : ℚ)
        * (((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
            / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ)))) < 1) :
    ∃ ρ : Fin n → Option Bool,
      (∀ g ∈ G, (canonicalDT (negDNF g) F ρ).depth < s)
        ∧ EquivOn ρ (gOr (G.toList.map cnf))
          (dnf (G.toList.flatMap (fun g =>
            dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ))))))
        ∧ (∀ T ∈ G.toList.flatMap (fun g =>
              dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ)))),
            T.lits.length < s) := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_shallow_all_tight hp0 hp3 (G.image negDNF) hnf hleaf hpos hr1 hsmall
  have hstars : SwitchingCounting.stars ρ ≤ F :=
    le_trans (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  have hshallow : ∀ g ∈ G, (canonicalDT (negDNF g) F ρ).depth < s :=
    fun g hg => hρ (negDNF g) (Finset.mem_image_of_mem _ hg)
  refine ⟨ρ, hshallow, ?_, ?_⟩
  · intro x hx
    rw [eval_gOr_cnf, eval_dnf]
    exact ((collapse_core_or_tight F s G hstars hshallow).1 x hx).symm
  · exact (collapse_core_or_tight F s G hstars hshallow).2

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapse_core_or_tight
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapse_to_dnf_layer_tight
