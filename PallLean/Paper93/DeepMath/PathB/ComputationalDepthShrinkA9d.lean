import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9c

/-!
# Shrinkage brick A9d: the `resSum` lower bound

The recursive `resSum` (A5) is bounded below by `B` times the count of
restriction sequences whose free pool hits every block:

* `HitsAll` / `hitCount` — the block-hitting predicate and the recursive count
  of good restriction sequences;
* `restrictF1_restrF` — one more restriction extends the restricted set;
* **`resSum_hit_ge` (proved)** — for the Andreev function,
  `B · hitCount r R ≤ resSum r R (restrF T v (andreevStar hm f))` whenever the
  pool `R` is disjoint from the already-restricted set `T` and `B ≤ dmsizeC f`.
  (Induction on `r`; the leaf is the block-hitting reduction A9c, the step
  threads one more restriction into `T`.)

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- The free pool hits every block. -/
def HitsAll {k m : ℕ} (hm : 0 < m) (R : Finset (Fin (k * m))) : Prop :=
  ∀ i : Fin k, ∃ j : Fin m, emb hm i j ∈ R

/-- The count of `r`-step restriction sequences from `R` whose free pool hits
every block. -/
noncomputable def hitCount {k m : ℕ} (hm : 0 < m) :
    ℕ → Finset (Fin (k * m)) → ℕ
  | 0, R => if HitsAll hm R then 1 else 0
  | r + 1, R => ∑ i ∈ R, (hitCount hm r (R.erase i) + hitCount hm r (R.erase i))

theorem restrictF1_restrF {n : ℕ} (i : Fin n) (b : Bool) (T : Finset (Fin n))
    (v : Fin n → Bool) (g : (Fin n → Bool) → Bool) (hi : i ∉ T) :
    restrictF1 i b (restrF T v g)
      = restrF (insert i T) (Function.update v i b) g := by
  funext y
  show g (fun w => if w ∈ T then v w else (Function.update y i b) w)
    = g (fun w => if w ∈ insert i T then (Function.update v i b) w else y w)
  congr 1
  funext w
  by_cases hwi : w = i
  · subst hwi
    rw [if_neg hi, Function.update_self, if_pos (Finset.mem_insert_self w T),
      Function.update_self]
  · rw [Function.update_of_ne hwi]
    by_cases hwT : w ∈ T
    · rw [if_pos hwT, if_pos (Finset.mem_insert_of_mem hwT),
        Function.update_of_ne hwi]
    · have hwins : w ∉ insert i T := by
        rw [Finset.mem_insert]
        push_neg
        exact ⟨hwi, hwT⟩
      rw [if_neg hwT, if_neg hwins]

/-- **THE `resSum` LOWER BOUND (proved).** -/
theorem resSum_hit_ge {k m : ℕ} (hm : 0 < m) (hk : 0 < k)
    (f : (Fin k → Bool) → Bool) (B : ℕ) (hB : B ≤ dmsizeC f) :
    ∀ (r : ℕ) (R T : Finset (Fin (k * m))) (v : Fin (k * m) → Bool),
      Disjoint R T →
      B * hitCount hm r R ≤ resSum r R (restrF T v (andreevStar hm f)) := by
  intro r
  induction r with
  | zero =>
    intro R T v hdisj
    show B * (if HitsAll hm R then 1 else 0)
      ≤ dmsizeC (restrF T v (andreevStar hm f))
    by_cases hR : HitsAll hm R
    · rw [if_pos hR, Nat.mul_one]
      refine andreev_hit_ge hm hk f B hB T v ?_
      intro i'
      obtain ⟨j, hj⟩ := hR i'
      exact ⟨j, Finset.disjoint_left.mp hdisj hj⟩
    · rw [if_neg hR, Nat.mul_zero]
      exact Nat.zero_le _
  | succ r ih =>
    intro R T v hdisj
    show B * (∑ i ∈ R, (hitCount hm r (R.erase i) + hitCount hm r (R.erase i)))
      ≤ ∑ i ∈ R,
          (resSum r (R.erase i)
              (restrictF1 i false (restrF T v (andreevStar hm f)))
            + resSum r (R.erase i)
              (restrictF1 i true (restrF T v (andreevStar hm f))))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hiR => ?_)
    have hiT : i ∉ T := Finset.disjoint_left.mp hdisj hiR
    have hdisj' : Disjoint (R.erase i) (insert i T) := by
      rw [Finset.disjoint_left]
      intro w hw
      obtain ⟨hwi, hwR⟩ := Finset.mem_erase.mp hw
      rw [Finset.mem_insert]
      push_neg
      exact ⟨hwi, Finset.disjoint_left.mp hdisj hwR⟩
    rw [restrictF1_restrF i false T v (andreevStar hm f) hiT,
      restrictF1_restrF i true T v (andreevStar hm f) hiT]
    have hf := ih (R.erase i) (insert i T) (Function.update v i false) hdisj'
    have ht := ih (R.erase i) (insert i T) (Function.update v i true) hdisj'
    calc B * (hitCount hm r (R.erase i) + hitCount hm r (R.erase i))
        = B * hitCount hm r (R.erase i) + B * hitCount hm r (R.erase i) := by ring
      _ ≤ resSum r (R.erase i)
              (restrF (insert i T) (Function.update v i false) (andreevStar hm f))
          + resSum r (R.erase i)
              (restrF (insert i T) (Function.update v i true) (andreevStar hm f)) :=
        Nat.add_le_add hf ht

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.resSum_hit_ge
