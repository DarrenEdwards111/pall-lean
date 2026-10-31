import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShallowExtendsUnif
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarTailExtends

/-!
# AC⁰ reduction, foundation 34: the uniform conditional switching primitive (branch only)

The complete iterable switching step: a restriction extending `τ` that makes every gate shallow *and* keeps
more than `k` survivors, under a budget whose conditioning mass has **cancelled**.  Combining the scaled
deep bound (brick 32) and the conditional star tail (brick 24), both divided by the conditioning mass
`((1-p)/2)^(n-stars τ)`, the union bound becomes

  `#gates · cap · t^k + (t·p + (1-p))^(stars τ) < t^k`,

with no `((1-p)/2)^(…)` factor — the mass cancels exactly.  This is the form the `d`-round loop applies with
one fixed parameter set at every level.

* `exists_shallow_survivor_extends_unif` — the uniform conditional switching primitive.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The uniform conditional switching primitive.**  Under the mass-cancelled budget, some restriction
extending `τ` makes every gate shallow and keeps more than `k` survivors. -/
theorem exists_shallow_survivor_extends_unif {p t : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1) (w F s k : ℕ)
    (τ : Fin n → Option Bool) (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w)
    (hsmall : (G.card : ℚ)
            * ((2 * p / (1 - p)) ^ s
                * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ))
            * t ^ k
          + (t * p + (1 - p)) ^ (stars τ)
        < t ^ k) :
    ∃ ρ : Fin n → Option Bool,
      Extends τ ρ ∧ (∀ g ∈ G, (canonicalDTree g w F ρ).depth < s) ∧ k < stars ρ := by
  classical
  set cap : ℚ := (2 * p / (1 - p)) ^ s
    * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ) with hcap
  have hp1 : p ≤ 1 := by linarith
  have hmass_pos : 0 < ((1 - p) / 2) ^ (n - stars τ) := by
    have : (0 : ℚ) < (1 - p) / 2 := by linarith
    exact pow_pos this _
  have hpw_nonneg : ∀ ρ : Fin n → Option Bool, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 hp1 ρ
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ σ, Extends τ σ → (∀ g ∈ G, depth < s) → stars σ ≤ k
  have hhigh : (∑ σ ∈ (extBox τ).filter (fun σ => ¬ stars σ ≤ k), pweight p σ)
      ≤ (G.card : ℚ) * cap * ((1 - p) / 2) ^ (n - stars τ) := by
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
      _ ≤ ∑ _g ∈ G, cap * ((1 - p) / 2) ^ (n - stars τ) := by
          apply Finset.sum_le_sum
          intro g hg
          rw [← Finset.sum_filter]
          exact descent_switching_le_extends hp0 hp3 g (hcons g hg) (hnd g hg) w (hw g hg) F s τ
            (fun σ hσ => mem_extBox.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hσ).1).1)
            (fun σ hσ => (Finset.mem_filter.mp hσ).2)
      _ = (G.card : ℚ) * cap * ((1 - p) / 2) ^ (n - stars τ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hlow : t ^ k * (∑ σ ∈ (extBox τ).filter (fun σ => stars σ ≤ k), pweight p σ)
      ≤ ((1 - p) / 2) ^ (n - stars τ) * (t * p + (1 - p)) ^ (stars τ) :=
    stars_tail_le_extends ht0.le ht1 hp0 hp1 τ k
  have hsplit : (∑ σ ∈ (extBox τ).filter (fun σ => stars σ ≤ k), pweight p σ)
      + (∑ σ ∈ (extBox τ).filter (fun σ => ¬ stars σ ≤ k), pweight p σ)
      = ((1 - p) / 2) ^ (n - stars τ) := by
    rw [Finset.sum_filter_add_sum_filter_not, pweight_sum_extends]
  have hfactored : t ^ k * ((1 - p) / 2) ^ (n - stars τ)
      ≤ ((t * p + (1 - p)) ^ (stars τ) + t ^ k * ((G.card : ℚ) * cap))
          * ((1 - p) / 2) ^ (n - stars τ) := by
    have hht := mul_le_mul_of_nonneg_left hhigh (pow_nonneg ht0.le k)
    calc t ^ k * ((1 - p) / 2) ^ (n - stars τ)
        = t ^ k * (∑ σ ∈ (extBox τ).filter (fun σ => stars σ ≤ k), pweight p σ)
            + t ^ k * (∑ σ ∈ (extBox τ).filter (fun σ => ¬ stars σ ≤ k), pweight p σ) := by
          rw [← hsplit]; ring
      _ ≤ ((1 - p) / 2) ^ (n - stars τ) * (t * p + (1 - p)) ^ (stars τ)
            + t ^ k * ((G.card : ℚ) * cap * ((1 - p) / 2) ^ (n - stars τ)) := by linarith
      _ = ((t * p + (1 - p)) ^ (stars τ) + t ^ k * ((G.card : ℚ) * cap))
            * ((1 - p) / 2) ^ (n - stars τ) := by ring
  have hfinal : t ^ k ≤ (t * p + (1 - p)) ^ (stars τ) + t ^ k * ((G.card : ℚ) * cap) :=
    le_of_mul_le_mul_right hfactored hmass_pos
  nlinarith [hfinal, hsmall]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_shallow_survivor_extends_unif
