import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingProbExtends

/-!
# AC⁰ reduction, foundation 33: uniform-budget subcube-relative switching (branch only)

The corrected conditional existence: with the *scaled* switching bound (brick 32), the conditioning mass
`((1-p)/2)^(n-stars τ)` appears on *both* sides of the union bound and **cancels**, so the budget is the
round-independent `#gates · cap < 1` — exactly the unconditional budget, now valid relative to any base `τ`.
This is what lets the `d`-round loop reuse one fixed parameter set at every level.

* `exists_shallow_all_extends_unif` — `#gates · cap < 1` ⟹ `∃ ρ`, `Extends τ ρ` and every gate shallow.

Compared to brick 23 (`exists_shallow_all_extends`, whose budget `#gates·cap < ((1-p)/2)^(n-stars τ)` shrank
each round), this is the iterable form.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Uniform-budget subcube-relative switching.**  If `#gates · cap < 1` (round-independent), some
restriction extending `τ` makes every gate's canonical tree shallow. -/
theorem exists_shallow_all_extends_unif {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s : ℕ)
    (τ : Fin n → Option Bool) (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w)
    (hsmall : (G.card : ℚ)
        * ((2 * p / (1 - p)) ^ s
            * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)) < 1) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ ∀ g ∈ G, (canonicalDTree g w F ρ).depth < s := by
  classical
  by_contra hcon
  push_neg at hcon
  set cap : ℚ := (2 * p / (1 - p)) ^ s
    * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ) with hcap
  have hp1 : p ≤ 1 := by linarith
  have hmass_pos : 0 < ((1 - p) / 2) ^ (n - stars τ) := by
    have : (0 : ℚ) < (1 - p) / 2 := by linarith
    exact pow_pos this _
  have hpw_nonneg : ∀ ρ : Fin n → Option Bool, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 hp1 ρ
  have key : ((1 - p) / 2) ^ (n - stars τ)
      ≤ (G.card : ℚ) * cap * ((1 - p) / 2) ^ (n - stars τ) := by
    calc ((1 - p) / 2) ^ (n - stars τ) = ∑ σ ∈ extBox τ, pweight p σ := (pweight_sum_extends p τ).symm
      _ ≤ ∑ σ ∈ extBox τ, ∑ g ∈ G,
            (if s ≤ (canonicalDTree g w F σ).depth then pweight p σ else 0) := by
        apply Finset.sum_le_sum
        intro σ hσ
        obtain ⟨g, hg, hgσ⟩ := hcon σ (mem_extBox.mp hσ)
        have hnn : ∀ g' ∈ G,
            (0 : ℚ) ≤ (if s ≤ (canonicalDTree g' w F σ).depth then pweight p σ else 0) := by
          intro g' _
          split
          · exact hpw_nonneg σ
          · exact le_refl 0
        have hsingle := Finset.single_le_sum hnn hg
        rwa [if_pos hgσ] at hsingle
      _ = ∑ g ∈ G, ∑ σ ∈ extBox τ,
            (if s ≤ (canonicalDTree g w F σ).depth then pweight p σ else 0) := Finset.sum_comm
      _ ≤ ∑ _g ∈ G, cap * ((1 - p) / 2) ^ (n - stars τ) := by
        apply Finset.sum_le_sum
        intro g hg
        rw [← Finset.sum_filter]
        exact descent_switching_le_extends hp0 hp3 g (hcons g hg) (hnd g hg) w (hw g hg) F s τ
          (fun σ hσ => mem_extBox.mp (Finset.mem_filter.mp hσ).1)
          (fun σ hσ => (Finset.mem_filter.mp hσ).2)
      _ = (G.card : ℚ) * cap * ((1 - p) / 2) ^ (n - stars τ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hlt : (G.card : ℚ) * cap * ((1 - p) / 2) ^ (n - stars τ)
      < 1 * ((1 - p) / 2) ^ (n - stars τ) := mul_lt_mul_of_pos_right hsmall hmass_pos
  rw [one_mul] at hlt
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_shallow_all_extends_unif
