import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9d

/-!
# Shrinkage brick A9e: the union-bound reduction

The counting scaffold for `hitCount ≥ bigN/2`:

* `seqCount` — the total number of restriction sequences; **`seqCount_eq_bigN`
  (proved)** identifies it with `bigN R.card r`;
* `missCount bi` — the number of sequences whose free pool misses block `bi`;
* **`seqCount_le_hit_add_miss` (proved)** — the union bound: every sequence is
  good or misses some block, so
  `seqCount r R ≤ hitCount r R + Σ_bi missCount bi r R`.

Combining these (A9f) with a bound on `missCount` gives `hitCount ≥ bigN/2`.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- Total number of `r`-step restriction sequences from `R`. -/
def seqCount {N : ℕ} : ℕ → Finset (Fin N) → ℕ
  | 0, _ => 1
  | r + 1, R => ∑ i ∈ R, (seqCount r (R.erase i) + seqCount r (R.erase i))

theorem seqCount_eq_bigN {N : ℕ} :
    ∀ (r : ℕ) (R : Finset (Fin N)), seqCount r R = bigN R.card r := by
  intro r
  induction r with
  | zero => intro R; rfl
  | succ r ih =>
    intro R
    show (∑ i ∈ R, (seqCount r (R.erase i) + seqCount r (R.erase i)))
      = bigN R.card (r + 1)
    have hstep : ∀ i ∈ R, seqCount r (R.erase i) + seqCount r (R.erase i)
        = 2 * bigN (R.card - 1) r := by
      intro i hi
      rw [ih (R.erase i), Finset.card_erase_of_mem hi]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, smul_eq_mul]
    show R.card * (2 * bigN (R.card - 1) r) = 2 * R.card * bigN (R.card - 1) r
    ring

/-- Number of `r`-step sequences from `R` whose free pool misses block `bi`. -/
noncomputable def missCount {k m : ℕ} (hm : 0 < m) (bi : Fin k) :
    ℕ → Finset (Fin (k * m)) → ℕ
  | 0, R => if (∀ j, emb hm bi j ∉ R) then 1 else 0
  | r + 1, R => ∑ i ∈ R, (missCount hm bi r (R.erase i) + missCount hm bi r (R.erase i))

/-- **THE UNION BOUND (proved)**: every restriction sequence is good or misses
some block. -/
theorem seqCount_le_hit_add_miss {k m : ℕ} (hm : 0 < m) :
    ∀ (r : ℕ) (R : Finset (Fin (k * m))),
      seqCount r R ≤ hitCount hm r R + ∑ bi : Fin k, missCount hm bi r R := by
  intro r
  induction r with
  | zero =>
    intro R
    show (1 : ℕ) ≤ (if HitsAll hm R then 1 else 0)
      + ∑ bi : Fin k, (if (∀ j, emb hm bi j ∉ R) then 1 else 0)
    by_cases hH : HitsAll hm R
    · rw [if_pos hH]; omega
    · rw [if_neg hH]
      have hex : ∃ bi, ∀ j, emb hm bi j ∉ R := by
        by_contra hc
        push_neg at hc
        exact hH hc
      obtain ⟨bi0, hbi0⟩ := hex
      have hle : (if (∀ j, emb hm bi0 j ∉ R) then (1 : ℕ) else 0)
          ≤ ∑ bi : Fin k, (if (∀ j, emb hm bi j ∉ R) then 1 else 0) :=
        Finset.single_le_sum (f := fun bi => if (∀ j, emb hm bi j ∉ R) then 1 else 0)
          (fun bi _ => Nat.zero_le _) (Finset.mem_univ bi0)
      rw [if_pos hbi0] at hle
      omega
  | succ r ih =>
    intro R
    have key : ∀ i ∈ R, seqCount r (R.erase i) + seqCount r (R.erase i)
        ≤ (hitCount hm r (R.erase i) + hitCount hm r (R.erase i))
          + ∑ bi : Fin k,
              (missCount hm bi r (R.erase i) + missCount hm bi r (R.erase i)) := by
      intro i _
      have hih := ih (R.erase i)
      have hsum : (∑ bi : Fin k,
          (missCount hm bi r (R.erase i) + missCount hm bi r (R.erase i)))
          = 2 * ∑ bi : Fin k, missCount hm bi r (R.erase i) := by
        rw [Finset.sum_add_distrib]; ring
      rw [hsum]; omega
    calc seqCount (r + 1) R
        = ∑ i ∈ R, (seqCount r (R.erase i) + seqCount r (R.erase i)) := rfl
      _ ≤ ∑ i ∈ R, ((hitCount hm r (R.erase i) + hitCount hm r (R.erase i))
            + ∑ bi : Fin k,
                (missCount hm bi r (R.erase i) + missCount hm bi r (R.erase i))) :=
          Finset.sum_le_sum key
      _ = (∑ i ∈ R, (hitCount hm r (R.erase i) + hitCount hm r (R.erase i)))
          + ∑ i ∈ R, ∑ bi : Fin k,
              (missCount hm bi r (R.erase i) + missCount hm bi r (R.erase i)) :=
          Finset.sum_add_distrib
      _ = hitCount hm (r + 1) R + ∑ bi : Fin k, missCount hm bi (r + 1) R := by
          show (∑ i ∈ R, (hitCount hm r (R.erase i) + hitCount hm r (R.erase i)))
            + ∑ i ∈ R, ∑ bi : Fin k,
                (missCount hm bi r (R.erase i) + missCount hm bi r (R.erase i))
            = (∑ i ∈ R, (hitCount hm r (R.erase i) + hitCount hm r (R.erase i)))
            + ∑ bi : Fin k, ∑ i ∈ R,
                (missCount hm bi r (R.erase i) + missCount hm bi r (R.erase i))
          rw [Finset.sum_comm]

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.seqCount_eq_bigN
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.seqCount_le_hit_add_miss
