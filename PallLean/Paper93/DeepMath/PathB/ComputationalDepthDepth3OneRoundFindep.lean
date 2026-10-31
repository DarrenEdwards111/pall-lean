import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingProbFindep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShallowSurvivor
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerCollapseAt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reduces

/-!
# Block-DT model, route-2 step [164]: the m-FREE extends-τ survivor and one-round (option (b) rung 3)

The iterated tower restricts further each round, so the per-round survivor must **extend** the
running base `τ` (not start from `∅` as the global [157] does).  Here we give the m-free analog of
`exists_shallow_survivor_extends`: the survivor comes from the m-free, `F`-independent **conditional**
switching bound `descent_switching_prob_findep` (base `4w+1`, geometric, on the `extBox τ` subcube),
so the budget carries no clause-count `m`.

* `exists_shallow_survivor_extends_findep` — under the m-free conditional budget, some `ρ` extends
  `τ`, keeps `k < stars ρ`, and makes every gate's block-tree shallower than `s`.
* `one_round_or_findep` — the m-free analog of `one_round_or`: one fully-assembled reduction round
  (`Reduces` step collapsing the `OR`-layer, well-formed outputs), driven by the m-free budget.

The deep-cap is now `geom · extBox-mass` with `geom = (r')^s/(1-r')`, `r' = (2p/(1-p))(4w+1)`, in
place of the m-ful `card · cap` — the clause-count `m` is gone.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The m-free extends-`τ` shallow survivor.**  Mirrors `exists_shallow_survivor_extends`, but the
per-gate deep weight is bounded by the m-free conditional switching bound `descent_switching_prob_findep`
(geometric cap `(r')^s/(1-r')`, base `4w+1`, no clause count `m`).  The budget compares the low-survivor
mass plus `card · geom · (extBox-mass)` against the full `extBox τ` mass `((1-p)/2)^(n - stars τ)`. -/
theorem exists_shallow_survivor_extends_findep {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w : ℕ} [NeZero w] (F s k : ℕ)
    (τ : Fin n → Option Bool) (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (hsmall :
        (∑ σ ∈ (extBox τ).filter (fun σ => stars σ ≤ k), pweight p σ)
          + (G.card : ℚ)
              * ((((2 * p / (1 - p)) * (4 * w + 1)) ^ s
                    / (1 - (2 * p / (1 - p)) * (4 * w + 1)))
                  * ((1 - p) / 2) ^ (n - stars τ))
        < ((1 - p) / 2) ^ (n - stars τ)) :
    ∃ ρ : Fin n → Option Bool,
      Extends τ ρ ∧ (∀ g ∈ G, (canonicalDTree g w F ρ).depth < s) ∧ k < stars ρ := by
  classical
  set geom : ℚ := ((2 * p / (1 - p)) * (4 * w + 1)) ^ s
    / (1 - (2 * p / (1 - p)) * (4 * w + 1)) with hgeom
  have hp1 : p ≤ 1 := by linarith
  have hpw_nonneg : ∀ ρ : Fin n → Option Bool, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 hp1 ρ
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ σ, Extends τ σ → (∀ g ∈ G, depth < s) → stars σ ≤ k
  have hhigh : (∑ σ ∈ (extBox τ).filter (fun σ => ¬ stars σ ≤ k), pweight p σ)
      ≤ (G.card : ℚ) * (geom * ((1 - p) / 2) ^ (n - stars τ)) := by
    calc ∑ σ ∈ (extBox τ).filter (fun σ => ¬ stars σ ≤ k), pweight p σ
        ≤ ∑ σ ∈ (extBox τ).filter (fun σ => ¬ stars σ ≤ k), ∑ g ∈ G,
            (if s ≤ (canonicalDTree g w F σ).depth then pweight p σ else 0) := by
          apply Finset.sum_le_sum
          intro σ hσ
          rw [Finset.mem_filter, mem_extBox] at hσ
          have hbad : ∃ g ∈ G, s ≤ (canonicalDTree g w F σ).depth := by
            by_contra hno
            push_neg at hno
            exact hσ.2 (hcon σ hσ.1 hno)
          obtain ⟨g, hg, hgσ⟩ := hbad
          have hnn : ∀ g' ∈ G,
              (0 : ℚ) ≤ (if s ≤ (canonicalDTree g' w F σ).depth then pweight p σ else 0) := by
            intro g' _
            split
            · exact hpw_nonneg σ
            · exact le_refl 0
          have hsingle := Finset.single_le_sum hnn hg
          rwa [if_pos hgσ] at hsingle
      _ = ∑ g ∈ G, ∑ σ ∈ (extBox τ).filter (fun σ => ¬ stars σ ≤ k),
            (if s ≤ (canonicalDTree g w F σ).depth then pweight p σ else 0) := Finset.sum_comm
      _ ≤ ∑ _g ∈ G, (geom * ((1 - p) / 2) ^ (n - stars τ)) := by
          apply Finset.sum_le_sum
          intro g hg
          rw [← Finset.sum_filter]
          have hbound := descent_switching_prob_findep hp0 hp3 g (hcons g hg) (hnd g hg) w
            (hw g hg) hr' F s τ
            (Bad := ((extBox τ).filter (fun σ => ¬ stars σ ≤ k)).filter
              (fun σ => s ≤ (canonicalDTree g w F σ).depth))
            (fun σ hσ => mem_extBox.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hσ).1).1)
            (fun σ hσ => (Finset.mem_filter.mp hσ).2)
          rw [pweight_sum_extends] at hbound
          rw [hgeom]
          exact hbound
      _ = (G.card : ℚ) * (geom * ((1 - p) / 2) ^ (n - stars τ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsplit : (∑ σ ∈ (extBox τ).filter (fun σ => stars σ ≤ k), pweight p σ)
      + (∑ σ ∈ (extBox τ).filter (fun σ => ¬ stars σ ≤ k), pweight p σ)
      = ((1 - p) / 2) ^ (n - stars τ) := by
    rw [Finset.sum_filter_add_sum_filter_not, pweight_sum_extends]
  linarith

/-- **One reduction round (`OR`-layer), m-free.**  The m-free analog of `one_round_or`: the survivor
`ρ` (extending `τ`, `k < stars ρ`) comes from the m-free conditional budget, and the `OR`-of-`AND`-of-
`DNF` layer `Reduces` on `ρ`'s subcube to an `OR`-of-`CNF`s with well-formed, width-`<s` clauses. -/
theorem one_round_or_findep {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w : ℕ} [NeZero w] (F s k : ℕ) (hF : n < F)
    (τ : Fin n → Option Bool)
    (gates : List (Finset (List (Clause n)))) (Gtot : Finset (List (Clause n)))
    (hsub : ∀ G ∈ gates, G ⊆ Gtot)
    (hcons : ∀ g ∈ Gtot, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ Gtot, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ Gtot, ∀ T ∈ g, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (hsmall :
        (∑ σ ∈ (extBox τ).filter (fun σ => stars σ ≤ k), pweight p σ)
          + (Gtot.card : ℚ)
              * ((((2 * p / (1 - p)) * (4 * w + 1)) ^ s
                    / (1 - (2 * p / (1 - p)) * (4 * w + 1)))
                  * ((1 - p) / 2) ^ (n - stars τ))
        < ((1 - p) / 2) ^ (n - stars τ)) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ k < stars ρ
      ∧ (∀ x, DTree.agreeRestriction ρ x →
          Reduces x (gOr (gates.map (fun G => gAnd (G.toList.map dnf))))
            (gOr (gates.map (fun G => cnf (G.toList.flatMap
              (fun g => dtreeToCNF (canonicalDTree g w F ρ)))))))
      ∧ (∀ G ∈ gates, ∀ C ∈ G.toList.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ)),
          Consistent C ∧ (C.lits.map litVarOf).Nodup ∧ C.lits.length < s) := by
  obtain ⟨ρ, hext, hshallowG, hstarsρ⟩ :=
    exists_shallow_survivor_extends_findep hp0 hp3 F s k τ Gtot hcons hnd hw hr' hsmall
  have hstarsF : stars ρ < F :=
    lt_of_le_of_lt (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  have hshallow : ∀ G ∈ gates, ∀ g ∈ G, (canonicalDTree g w F ρ).depth < s :=
    fun G hG g hg => hshallowG g (hsub G hG hg)
  have hndgates : ∀ G ∈ gates, ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup :=
    fun G hG g hg => hnd g (hsub G hG hg)
  obtain ⟨hequiv, hwidth, hwf⟩ := collapse_or_layer_at w F s gates ρ hstarsF hndgates hshallow
  exact ⟨ρ, hext, hstarsρ, fun x hx => Reduces.head hequiv hx,
    fun G hG C hC => ⟨(hwf G hG C hC).1, (hwf G hG C hC).2, hwidth G hG C hC⟩⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_shallow_survivor_extends_findep
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.one_round_or_findep
