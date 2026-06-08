import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShallowExtends
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarTailExtends

/-!
# AC⁰ reduction, foundation 25: the conditional switching primitive (branch only)

The complete subcube-relative switching step: a restriction that **extends `τ`**, makes **every gate
shallow**, *and* **retains more than `k` survivors**.  This is the single existence statement the multi-round
coordinate budget consumes — applying it with `τ` = the previous round's restriction keeps the survivor sets
nested and bounded below, so the budget survives `d` rounds.

The union bound now excludes two bad events on the conditional measure (total mass `((1-p)/2)^(n - stars τ)`,
brick 22): a deep gate (capped by `descent_switching_le`, brick 60) or a low survivor count (the conditional
lower-tail weight, brick 24).  If their combined weight is below the total mass, a good high-survivor
restriction extending `τ` exists.

* `exists_shallow_survivor_extends` — `#gates · cap + (low-survivor weight) < ((1-p)/2)^(n - stars τ)`
  ⟹ `∃ ρ`, `Extends τ ρ`, every gate shallow under `ρ`, and `k < stars ρ`.

This closes the conditional switching primitive (bricks 22–25): the switching round can now be applied
*relative to a subcube*, with the survivor count under control — exactly what `tower_not_parity`'s
coordinate budget (brick 21) needs.  Iterating it across `d` rounds (threading the restriction and
re-establishing the gate hypotheses by bricks 14/15/18/19) is the remaining assembly.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The conditional switching primitive.**  If the combined conditional weight of deep-gate and
low-survivor restrictions is below the conditioning mass, some restriction extending `τ` makes every gate
shallow and keeps more than `k` survivors. -/
theorem exists_shallow_survivor_extends {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s k : ℕ)
    (τ : Fin n → Option Bool) (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w)
    (hsmall : (G.card : ℚ)
          * ((2 * p / (1 - p)) ^ s
              * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ))
        + (∑ σ ∈ (extBox τ).filter (fun σ => stars σ ≤ k), pweight p σ)
        < ((1 - p) / 2) ^ (n - stars τ)) :
    ∃ ρ : Fin n → Option Bool,
      Extends τ ρ ∧ (∀ g ∈ G, (canonicalDTree g w F ρ).depth < s) ∧ k < stars ρ := by
  classical
  set cap : ℚ := (2 * p / (1 - p)) ^ s
    * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ) with hcap
  have hp1 : p ≤ 1 := by linarith
  have hpw_nonneg : ∀ ρ : Fin n → Option Bool, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 hp1 ρ
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ σ, Extends τ σ → (∀ g ∈ G, depth < s) → stars σ ≤ k
  have hhigh : (∑ σ ∈ (extBox τ).filter (fun σ => ¬ stars σ ≤ k), pweight p σ)
      ≤ (G.card : ℚ) * cap := by
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
      _ ≤ ∑ _g ∈ G, cap := by
          apply Finset.sum_le_sum
          intro g hg
          rw [← Finset.sum_filter]
          exact descent_switching_le hp0 hp3 g (hcons g hg) (hnd g hg) w (hw g hg) F s
            (fun σ hσ => (Finset.mem_filter.mp hσ).2)
      _ = (G.card : ℚ) * cap := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsplit : (∑ σ ∈ (extBox τ).filter (fun σ => stars σ ≤ k), pweight p σ)
      + (∑ σ ∈ (extBox τ).filter (fun σ => ¬ stars σ ≤ k), pweight p σ)
      = ((1 - p) / 2) ^ (n - stars τ) := by
    rw [Finset.sum_filter_add_sum_filter_not, pweight_sum_extends]
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_shallow_survivor_extends
