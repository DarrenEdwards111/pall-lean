import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShallowAllTight
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseCoreTight
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerCollapse

/-!
# Tight switching, step 16: the tight `EquivOn` layer collapse (branch `razborov-recoverRho-wip`)

The other remaining wire: threading the tight `canonicalDT` collapse into the `Layered`/`EquivOn`/`Reduces`
spine.  This is the `F`-independent analogue of `collapse_or_layer` (foundation; crude, `canonicalDTree`,
`(4^w+1)^F`).  An `OR` of `AND`-of-`DNF` gates collapses, under a single restriction, to an `OR` of `CNF`s
(depth `4 → 3`), with the collapse `CNF` built from the **single-literal** tree
`dtreeToCNF (toDTree (canonicalDT g F ρ))` and the union-bound threshold `F`-independent.

The key that makes `canonicalDT`'s eval-correctness (`canonicalDT_eval`, which needs `stars ρ ≤ F`) hold for
the produced `ρ` is simply `n ≤ F`: `stars ρ ≤ n ≤ F` for *every* `ρ`.  Crucially — unlike the crude route —
taking `F ≥ n` no longer costs anything in the budget, because the tight cap `#gates · r^s/(1-r)` does **not**
depend on `F` (`tight_switching_budget`, step 10).  So `F ≥ n` buys eval-correctness for free while the
threshold stays `F`-independent.

* `collapse_core_tight_list` — the flattened `dtreeToCNF (toDTree (canonicalDT · F ρ))` over a gate set
  computes the `AND` of the gates' DNFs on the `ρ`-subcube, width `< s`.
* `collapse_or_layer_tight` — the simultaneous `OR`-layer collapse as an `EquivOn` round, `F`-independent.

This `EquivOn` is exactly what `Reduces.head`/`Reduces.round` and the `iterated_not_parity` spine consume —
so the tight collapse now plugs into the reduction chain, with the parity capstone supplied by
`shallow_canonicalDT_not_parity` (step 14) over the same `canonicalDT`.

## Honest scope

Carries the per-gate global alive/leaf/position hypotheses (the empty-skip wall, brick 49) explicitly.  This
is the `OR`-of-`AND`-of-`DNF` (depth-4 → 3) collapse; iterating it and discharging the survivor budget
(`s ≤ stars ρ`, step 15's third bad event applied subcube-relatively) to reach a closed depth-`d`
`parity ∉ AC⁰` is the remaining structural induction.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

private theorem all_congr_aux {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.all_cons, List.all_cons, h a (by simp),
      ih (fun b hb => h b (by simp [hb]))]

private theorem any_congr_aux {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.any_cons, List.any_cons, h a (by simp),
      ih (fun b hb => h b (by simp [hb]))]

/-- **The tight flattened collapse core (`AND`-of-`DNF`).**  Once `ρ` makes every gate's single-literal
canonical tree shallow (and `stars ρ ≤ F`), the concatenated `dtreeToCNF (toDTree (canonicalDT · F ρ))`
computes the `AND` of the DNFs on the `ρ`-subcube, with width `< s`. -/
theorem collapse_core_tight_list (F s : ℕ) (G : Finset (List (Clause n)))
    {ρ : Fin n → Option Bool} (hstars : SwitchingCounting.stars ρ ≤ F)
    (hshallow : ∀ g ∈ G, (canonicalDT g F ρ).depth < s) :
    (∀ x, DTree.agreeRestriction ρ x →
        cnfValue (G.toList.flatMap (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ)))) x
          = (ACircuit.and (G.toList.map dnfToCircuit)).eval x)
      ∧ (∀ C ∈ G.toList.flatMap (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ))),
          C.lits.length < s) := by
  constructor
  · intro x hx
    have h1 : (ACircuit.and (G.toList.map dnfToCircuit)).eval x
        = G.toList.all (fun g => DTree.dnfValue g x) := by
      rw [ACircuit.eval_and, List.all_map]
      exact all_congr_aux _ _ _ (fun g _ => dnfToCircuit_eval g x)
    have h2 : cnfValue (G.toList.flatMap (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ)))) x
        = G.toList.all (fun g => DTree.dnfValue g x) := by
      rw [cnfValue, List.all_flatMap]
      apply all_congr_aux
      intro g hg
      rw [← cnfValue]
      exact (collapse_core_tight F s g hstars (hshallow g (Finset.mem_toList.mp hg))).1 x hx
    rw [h2, h1]
  · intro C hC
    rw [List.mem_flatMap] at hC
    obtain ⟨g, hg, hCg⟩ := hC
    exact (collapse_core_tight F s g hstars (hshallow g (Finset.mem_toList.mp hg))).2 C hCg

/-- **The tight simultaneous `OR`-layer collapse.**  An `OR` of `AND`-of-`DNF` gates collapses, under a
single restriction (`F`-independent union bound over all gates), to an `OR` of `CNF`s built from the
single-literal canonical tree.  Depth `4 → 3`, threshold independent of the fuel `F`. -/
theorem collapse_or_layer_tight {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (hF : n ≤ F)
    (gates : List (Finset (List (Clause n)))) (Gtot : Finset (List (Clause n)))
    (hsub : ∀ G ∈ gates, G ⊆ Gtot)
    (hnf : ∀ g ∈ Gtot, ∀ ρ : Restriction n, ∀ U ∈ g,
      SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ g ∈ Gtot, ∀ ρ : Restriction n,
      SwitchingCounting.anyTermSat g (deepestEnd g F ρ) = false)
    (hpos : ∀ g ∈ Gtot, ∀ ρ : Restriction n, ∀ q ∈ deepestFullSeq g F ρ, q.1 < w)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ)) < 1)
    (hsmall : (Gtot.card : ℚ)
        * (((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
            / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ)))) < 1) :
    ∃ ρ : Fin n → Option Bool,
      EquivOn ρ (gOr (gates.map (fun G => gAnd (G.toList.map dnf))))
          (gOr (gates.map (fun G => cnf (G.toList.flatMap
            (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ)))))))
        ∧ (∀ G ∈ gates, ∀ C ∈ G.toList.flatMap
              (fun g => dtreeToCNF (toDTree (canonicalDT g F ρ))), C.lits.length < s) := by
  obtain ⟨ρ, hρ⟩ := exists_shallow_all_tight hp0 hp3 Gtot hnf hleaf hpos hr1 hsmall
  have hstars : SwitchingCounting.stars ρ ≤ F :=
    le_trans (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  have hshallow : ∀ G ∈ gates, ∀ g ∈ G, (canonicalDT g F ρ).depth < s :=
    fun G hG g hg => hρ g (hsub G hG hg)
  refine ⟨ρ, ?_, ?_⟩
  · intro x hx
    rw [eval_gOr, eval_gOr, List.any_map, List.any_map]
    apply any_congr_aux
    intro G hG
    simp only [Function.comp_apply]
    rw [eval_gAnd_dnf, eval_cnf]
    exact ((collapse_core_tight_list F s G hstars (hshallow G hG)).1 x hx).symm
  · intro G hG C hC
    exact (collapse_core_tight_list F s G hstars (hshallow G hG)).2 C hC

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapse_core_tight_list
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapse_or_layer_tight
