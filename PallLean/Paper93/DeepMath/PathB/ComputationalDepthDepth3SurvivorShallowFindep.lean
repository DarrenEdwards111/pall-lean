import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityRefuteFindep

/-!
# Block-DT model, route-2 step [157]: the m-FREE multi-gate survivor lemma (branch `razborov-recoverRho-wip`)

The existing unconditional survivor lemma `exists_survivor_shallow_uncond` uses the per-gate cap
`tight_switching_budget_uncond` with base `2wm` — the clause-count `m` forces `p ≈ 1/(wm)`, which makes the
multi-round / depth-`(d+2)` budget vacuous (this is exactly the obstruction route 2 was built to remove).
Here we give the **`m`-free** analog: using the `F`-independent, `m`-free deep cap
`descent_switching_findep_le` (base `4w`, brick 156), the three-event union bound produces a survivor making
*every* gate's canonical *block*-tree shallow — with **no dependence on the clause count `m`**.

* `exists_survivor_shallow_findep` — low-star tail + high-star tail + `(#gates)·(r')^s/(1-r') < 1` ⟹ a
  restriction `ρ` with `s ≤ stars ρ < F` making every gate's `canonicalDTree` shallower than `s`,
  `r' = (2p/(1-p))(4w+1) < 1`, `m`-free.

Gates must be consistent with nodup-variable terms (the hypotheses of brick 155b/156); these hold for honest
DNF gates and are `m`-free.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The m-free three-event union bound.**  With per-gate width `≤ w` (and consistent, nodup-variable
terms), if the low/high star tails and the `m`-free deep cap `(#gates)·(r')^s/(1-r')` total `< 1`, some
restriction has `s ≤ stars ρ < F` and makes every gate's block-tree shallower than `s`. -/
theorem exists_survivor_shallow_findep {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (hsmall :
        (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
            pweight p ρ)
          + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F ≤ SwitchingCounting.stars ρ),
              pweight p ρ)
          + (G.card : ℚ)
              * (((2 * p / (1 - p)) * (4 * w + 1)) ^ s
                  / (1 - (2 * p / (1 - p)) * (4 * w + 1))) < 1) :
    ∃ ρ : Restriction n, s ≤ SwitchingCounting.stars ρ ∧ SwitchingCounting.stars ρ < F ∧
      ∀ g ∈ G, (canonicalDTree g w F ρ).depth < s := by
  classical
  set cap : ℚ := ((2 * p / (1 - p)) * (4 * w + 1)) ^ s
    / (1 - (2 * p / (1 - p)) * (4 * w + 1)) with hcap
  have hpw_nonneg : ∀ ρ : Restriction n, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 (by linarith) ρ
  by_contra hcon
  push_neg at hcon
  have hcase : ∀ ρ : Restriction n,
      SwitchingCounting.stars ρ < s ∨ F ≤ SwitchingCounting.stars ρ
        ∨ ∃ g ∈ G, s ≤ (canonicalDTree g w F ρ).depth := by
    intro ρ
    by_cases h1 : SwitchingCounting.stars ρ < s
    · exact Or.inl h1
    · by_cases h2 : F ≤ SwitchingCounting.stars ρ
      · exact Or.inr (Or.inl h2)
      · obtain ⟨g, hg, hgρ⟩ := hcon ρ (Nat.le_of_not_lt h1) (Nat.not_le.mp h2)
        exact Or.inr (Or.inr ⟨g, hg, hgρ⟩)
  have key : (1 : ℚ) ≤
      (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
          pweight p ρ)
        + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F ≤ SwitchingCounting.stars ρ),
            pweight p ρ)
        + (G.card : ℚ) * cap := by
    calc (1 : ℚ) = ∑ ρ : Restriction n, pweight p ρ := (pweight_sum_eq_one p).symm
      _ ≤ ∑ ρ : Restriction n,
            ((if SwitchingCounting.stars ρ < s then pweight p ρ else 0)
              + (if F ≤ SwitchingCounting.stars ρ then pweight p ρ else 0)
              + ∑ g ∈ G, (if s ≤ (canonicalDTree g w F ρ).depth then pweight p ρ else 0)) := by
          apply Finset.sum_le_sum
          intro ρ _
          have hlo_nn : (0 : ℚ) ≤ (if SwitchingCounting.stars ρ < s then pweight p ρ else 0) := by
            split <;> first | exact hpw_nonneg ρ | exact le_refl 0
          have hhi_nn : (0 : ℚ) ≤ (if F ≤ SwitchingCounting.stars ρ then pweight p ρ else 0) := by
            split <;> first | exact hpw_nonneg ρ | exact le_refl 0
          have hsum_nn : (0 : ℚ) ≤
              ∑ g ∈ G, (if s ≤ (canonicalDTree g w F ρ).depth then pweight p ρ else 0) :=
            Finset.sum_nonneg
              (fun g' _ => by split <;> first | exact hpw_nonneg ρ | exact le_refl 0)
          rcases hcase ρ with hlo | hhi | ⟨g, hg, hgρ⟩
          · rw [if_pos hlo]; linarith
          · rw [if_pos hhi]; linarith
          · have hnn : ∀ g' ∈ G,
                (0 : ℚ) ≤ (if s ≤ (canonicalDTree g' w F ρ).depth then pweight p ρ else 0) :=
              fun g' _ => by split <;> first | exact hpw_nonneg ρ | exact le_refl 0
            have hsingle := Finset.single_le_sum hnn hg
            rw [if_pos hgρ] at hsingle
            linarith
      _ = (∑ ρ : Restriction n, (if SwitchingCounting.stars ρ < s then pweight p ρ else 0))
            + (∑ ρ : Restriction n, (if F ≤ SwitchingCounting.stars ρ then pweight p ρ else 0))
            + ∑ ρ : Restriction n,
                ∑ g ∈ G, (if s ≤ (canonicalDTree g w F ρ).depth then pweight p ρ else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
              pweight p ρ)
            + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F ≤ SwitchingCounting.stars ρ),
                pweight p ρ)
            + ∑ g ∈ G, ∑ ρ : Restriction n,
                (if s ≤ (canonicalDTree g w F ρ).depth then pweight p ρ else 0) := by
          rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_comm]
      _ ≤ (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
              pweight p ρ)
            + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F ≤ SwitchingCounting.stars ρ),
                pweight p ρ)
            + (G.card : ℚ) * cap := by
          have hgate : ∑ g ∈ G, ∑ ρ : Restriction n,
              (if s ≤ (canonicalDTree g w F ρ).depth then pweight p ρ else 0) ≤ (G.card : ℚ) * cap := by
            calc ∑ g ∈ G, ∑ ρ : Restriction n,
                    (if s ≤ (canonicalDTree g w F ρ).depth then pweight p ρ else 0)
                ≤ ∑ _g ∈ G, cap := by
                  apply Finset.sum_le_sum
                  intro g hg
                  rw [← Finset.sum_filter]
                  exact descent_switching_findep_le hp0 hp3 g (hcons g hg) (hnd g hg) w (hw g hg)
                    hr' F s (fun σ hσ => (Finset.mem_filter.mp hσ).2)
              _ = (G.card : ℚ) * cap := by rw [Finset.sum_const, nsmul_eq_mul]
          linarith
  linarith

/-- **The m-free unconditional single-DNF parity refutation.**  A single bottom DNF `D` (width `≤ w`,
consistent nodup-variable terms — **no clause-count bound**) disagrees with parity at some subcube point,
under the `m`-free, `F`-independent star-tail + deep-cap budget. -/
theorem dnf_not_parity_findep {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (D : List (Clause n))
    (hcons : ∀ T ∈ D, Consistent T) (hnd : ∀ T ∈ D, (T.lits.map litVarOf).Nodup)
    (hw : ∀ T ∈ D, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (hsmall :
        (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
            pweight p ρ)
          + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F ≤ SwitchingCounting.stars ρ),
              pweight p ρ)
          + (((2 * p / (1 - p)) * (4 * w + 1)) ^ s
              / (1 - (2 * p / (1 - p)) * (4 * w + 1))) < 1) :
    ∃ (ρ : Restriction n) (x : Fin n → Bool),
      DTree.agreeRestriction ρ x ∧ DTree.dnfValue D x ≠ DTree.parity x := by
  classical
  obtain ⟨ρ, hge, hlt, hshallow⟩ :=
    exists_survivor_shallow_findep hp0 hp3 ({D} : Finset (List (Clause n)))
      (fun g hg T hT => by rw [Finset.mem_singleton] at hg; subst hg; exact hcons T hT)
      (fun g hg T hT => by rw [Finset.mem_singleton] at hg; subst hg; exact hnd T hT)
      (fun g hg T hT => by rw [Finset.mem_singleton] at hg; subst hg; exact hw T hT)
      hr'
      (by rw [Finset.card_singleton, Nat.cast_one, one_mul]; exact hsmall)
  have hsh : (canonicalDTree D w F ρ).depth < SwitchingCounting.stars ρ :=
    lt_of_lt_of_le (hshallow D (Finset.mem_singleton.mpr rfl)) hge
  have hex : ∃ x, DTree.agreeRestriction ρ x ∧ DTree.dnfValue D x ≠ DTree.parity x := by
    by_contra hall
    push_neg at hall
    have hge2 := canonicalDTree_depth_ge_of_parity D w F ρ hlt hall
    omega
  obtain ⟨x, hx, hne⟩ := hex
  exact ⟨ρ, x, hx, hne⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_survivor_shallow_findep
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dnf_not_parity_findep
