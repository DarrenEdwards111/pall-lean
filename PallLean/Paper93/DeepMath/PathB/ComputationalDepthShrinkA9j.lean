import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9i

/-!
# Shrinkage brick A9j: the miss bound from the falling-factorial inequality

The last brick: identify `missCount` with `countN` of the cardinalities, giving
its closed form, and reduce the miss bound to a clean permutation inequality.

* `blk` — a block's coordinate set;
* **`missCount_eq_countN` (proved)** — `missCount bi r R = countN r |R| |blk∩R|`
  (induction on `r`; the recursion respects the two cardinalities);
* **`missCount_univ` (proved)** —
  `missCount bi r univ = 2^r · perm r m · perm (n−m) (r−m)`;
* **`miss_bound_of_perm` (proved)** — if `m ≤ r` and
  `2k·perm r m ≤ perm n m`, then `2·Σ_bi missCount ≤ bigN n r`.

Combined with `andreev_shrinkage_of_miss` (A9g), the whole Andreev shrinkage is
now conditional ONLY on the falling-factorial inequality `2k·perm r m ≤ perm n m`
— a completely standard `ℕ` statement.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- The coordinate set of block `bi`. -/
def blk {k m : ℕ} (hm : 0 < m) (bi : Fin k) : Finset (Fin (k * m)) :=
  Finset.univ.image (fun j : Fin m => emb hm bi j)

theorem emb_bi_inj {k m : ℕ} (hm : 0 < m) (bi : Fin k) :
    Function.Injective (fun j : Fin m => emb hm bi j) := by
  intro j j' h
  have h2 := congrArg (offOf hm) h
  rwa [off_emb, off_emb] at h2

theorem mem_blk {k m : ℕ} (hm : 0 < m) (bi : Fin k) (w : Fin (k * m)) :
    w ∈ blk hm bi ↔ ∃ j, emb hm bi j = w := by
  rw [blk, Finset.mem_image]
  constructor
  · rintro ⟨j, -, hj⟩; exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩; exact ⟨j, Finset.mem_univ j, hj⟩

theorem blk_card {k m : ℕ} (hm : 0 < m) (bi : Fin k) : (blk hm bi).card = m := by
  rw [blk, Finset.card_image_of_injective _ (emb_bi_inj hm bi), Finset.card_univ,
    Fintype.card_fin]

/-- **The miss-count parameterisation (proved).** -/
theorem missCount_eq_countN {k m : ℕ} (hm : 0 < m) (bi : Fin k) :
    ∀ (r : ℕ) (R : Finset (Fin (k * m))),
      missCount hm bi r R = countN r R.card ((blk hm bi ∩ R).card) := by
  intro r
  induction r with
  | zero =>
    intro R
    show (if (∀ j, emb hm bi j ∉ R) then 1 else 0)
      = (if (blk hm bi ∩ R).card = 0 then 1 else 0)
    by_cases hP : ∀ j, emb hm bi j ∉ R
    · rw [if_pos hP]
      have hc : (blk hm bi ∩ R).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro w hw
        rw [Finset.mem_inter] at hw
        obtain ⟨hwblk, hwR⟩ := hw
        obtain ⟨j, hj⟩ := (mem_blk hm bi w).mp hwblk
        rw [← hj] at hwR
        exact hP j hwR
      rw [if_pos hc]
    · rw [if_neg hP]
      have hc : (blk hm bi ∩ R).card ≠ 0 := by
        push_neg at hP
        obtain ⟨j, hj⟩ := hP
        have hmem : emb hm bi j ∈ blk hm bi ∩ R :=
          Finset.mem_inter.mpr ⟨(mem_blk hm bi _).mpr ⟨j, rfl⟩, hj⟩
        have := Finset.card_pos.mpr ⟨emb hm bi j, hmem⟩
        omega
      rw [if_neg hc]
  | succ r ih =>
    intro R
    have hinter : ∀ i, blk hm bi ∩ R.erase i = (blk hm bi ∩ R).erase i := by
      intro i
      ext w
      simp only [Finset.mem_inter, Finset.mem_erase]
      tauto
    have hval : ∀ i ∈ R, missCount hm bi r (R.erase i)
        = countN r (R.card - 1) (((blk hm bi ∩ R).erase i).card) := by
      intro i hi
      rw [ih (R.erase i), Finset.card_erase_of_mem hi, hinter]
    have hsplit : ∑ i ∈ R, countN r (R.card - 1) (((blk hm bi ∩ R).erase i).card)
        = (blk hm bi ∩ R).card * countN r (R.card - 1) ((blk hm bi ∩ R).card - 1)
          + (R.card - (blk hm bi ∩ R).card)
            * countN r (R.card - 1) ((blk hm bi ∩ R).card) := by
      rw [← Finset.sum_filter_add_sum_filter_not R (· ∈ blk hm bi)]
      have h1 : ∑ i ∈ R.filter (· ∈ blk hm bi),
          countN r (R.card - 1) (((blk hm bi ∩ R).erase i).card)
          = (blk hm bi ∩ R).card
            * countN r (R.card - 1) ((blk hm bi ∩ R).card - 1) := by
        have hc : ∀ i ∈ R.filter (· ∈ blk hm bi),
            countN r (R.card - 1) (((blk hm bi ∩ R).erase i).card)
            = countN r (R.card - 1) ((blk hm bi ∩ R).card - 1) := by
          intro i hi
          obtain ⟨hiR, hib⟩ := Finset.mem_filter.mp hi
          rw [Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hib, hiR⟩)]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
        congr 1
        rw [Finset.filter_mem_eq_inter, Finset.inter_comm]
      have h2 : ∑ i ∈ R.filter (fun i => ¬ i ∈ blk hm bi),
          countN r (R.card - 1) (((blk hm bi ∩ R).erase i).card)
          = (R.card - (blk hm bi ∩ R).card)
            * countN r (R.card - 1) ((blk hm bi ∩ R).card) := by
        have hc : ∀ i ∈ R.filter (fun i => ¬ i ∈ blk hm bi),
            countN r (R.card - 1) (((blk hm bi ∩ R).erase i).card)
            = countN r (R.card - 1) ((blk hm bi ∩ R).card) := by
          intro i hi
          obtain ⟨hiR, hib⟩ := Finset.mem_filter.mp hi
          rw [Finset.erase_eq_of_notMem (fun h => hib (Finset.mem_inter.mp h).1)]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
        congr 1
        have hcard := Finset.card_filter_add_card_filter_not (s := R) (· ∈ blk hm bi)
        have hfi : (R.filter (· ∈ blk hm bi)).card = (blk hm bi ∩ R).card := by
          rw [Finset.filter_mem_eq_inter, Finset.inter_comm]
        omega
      rw [h1, h2]
    show ∑ i ∈ R, (missCount hm bi r (R.erase i) + missCount hm bi r (R.erase i))
      = 2 * ((blk hm bi ∩ R).card * countN r (R.card - 1) ((blk hm bi ∩ R).card - 1)
        + (R.card - (blk hm bi ∩ R).card)
          * countN r (R.card - 1) ((blk hm bi ∩ R).card))
    rw [Finset.sum_add_distrib, Finset.sum_congr rfl hval, hsplit]
    ring

theorem missCount_univ {k m : ℕ} (hm : 0 < m) (bi : Fin k) (r : ℕ) :
    missCount hm bi r (Finset.univ : Finset (Fin (k * m)))
      = 2 ^ r * (perm r m * perm (k * m - m) (r - m)) := by
  rw [missCount_eq_countN hm bi r Finset.univ]
  have h1 : (blk hm bi ∩ (Finset.univ : Finset (Fin (k * m)))).card = m := by
    rw [Finset.inter_univ, blk_card]
  have h2 : (Finset.univ : Finset (Fin (k * m))).card = k * m := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [h1, h2, countN_closed]

/-- **THE MISS BOUND FROM THE PERMUTATION INEQUALITY (proved).** -/
theorem miss_bound_of_perm {k m : ℕ} (hm : 0 < m) (r : ℕ) (hmr : m ≤ r)
    (hperm : 2 * k * perm r m ≤ perm (k * m) m) :
    2 * (∑ bi : Fin k, missCount hm bi r (Finset.univ : Finset (Fin (k * m))))
      ≤ bigN (k * m) r := by
  have hval : ∀ bi : Fin k,
      missCount hm bi r (Finset.univ : Finset (Fin (k * m)))
        = 2 ^ r * (perm r m * perm (k * m - m) (r - m)) :=
    fun bi => missCount_univ hm bi r
  rw [Finset.sum_congr rfl (fun bi _ => hval bi), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- 2 * (k * (2^r * (perm r m * perm (n-m)(r-m)))) ≤ bigN n r
  rw [bigN_eq_perm]
  -- bigN n r = 2^r * perm n r, perm n r = perm n m * perm (n-m)(r-m)
  have hfac : perm (k * m) r = perm (k * m) m * perm (k * m - m) (r - m) := by
    have := perm_add m (r - m) (k * m)
    rwa [Nat.add_sub_cancel' hmr] at this
  rw [hfac]
  have hmul : 2 * k * perm r m * perm (k * m - m) (r - m)
      ≤ perm (k * m) m * perm (k * m - m) (r - m) :=
    Nat.mul_le_mul_right _ hperm
  calc 2 * (k * (2 ^ r * (perm r m * perm (k * m - m) (r - m))))
      = 2 ^ r * (2 * k * perm r m * perm (k * m - m) (r - m)) := by ring
    _ ≤ 2 ^ r * (perm (k * m) m * perm (k * m - m) (r - m)) :=
        Nat.mul_le_mul_left _ hmul

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.missCount_eq_countN
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.miss_bound_of_perm
