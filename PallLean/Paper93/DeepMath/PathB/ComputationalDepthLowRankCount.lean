import Mathlib

/-!
# Counting low-rank matrices, and the probabilistic-method skeleton

The reusable engine for the probabilistic existence of a rank-rigid (best-partition-hard) matrix.  The crux —
absent from Mathlib — is the rank factorization `rank M ≤ s ⟹ M = A · B` with inner dimension `s`, from which the
count `#{h×h 𝔽₂ matrices of rank ≤ s} ≤ 2^{2hs}` follows by the surjection `(A,B) ↦ A·B`.

* `exists_span_of_finrank_le` — a `finrank ≤ s` subspace has a spanning family of size `s` (padded basis);
* `rank_factor` — `rank M ≤ s ⟹ ∃ A B, M = A · B` (inner dimension `s`);
* `card_lowRank_le` — `#{h×h 𝔽₂ matrices of rank ≤ s} ≤ 2^{2hs}`;
* `exists_avoiding` — the probabilistic-method pigeonhole: if `Σ_test |Bad test| < |Ω|`, some `ω` avoids every bad
  set.

Combined (`SCOPE_BEST_PARTITION_HARD.md`), these give: a random symmetric matrix is rank-rigid, so a best-partition-
hard function exists.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LowRankCount

open Matrix

/-- A subspace of `finrank ≤ s` has a spanning family of size `s` (a basis padded with zeros). -/
theorem exists_span_of_finrank_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) (s : ℕ) (hW : Module.finrank K W ≤ s) :
    ∃ v : Fin s → V, W ≤ Submodule.span K (Set.range v) := by
  classical
  let b := Module.finBasis K W
  refine ⟨fun i => if h : i.val < Module.finrank K W then (b ⟨i.val, h⟩ : V) else 0, ?_⟩
  have hspan : (W : Submodule K V) = Submodule.span K (Set.range (fun j => (b j : V))) := by
    have hrc : (Set.range (fun j => (b j : V))) = (W.subtype) '' (Set.range b) := by
      rw [← Set.range_comp]; rfl
    rw [hrc, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  refine le_trans (le_of_eq hspan) (Submodule.span_mono ?_)
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨j.val, lt_of_lt_of_le j.isLt hW⟩, by simp⟩

/-- **Rank factorization** (absent from Mathlib): a matrix of rank `≤ s` factors as `A · B` with inner
dimension `s`. -/
theorem rank_factor {h s : ℕ} {K : Type*} [Field K] (M : Matrix (Fin h) (Fin h) K) (hr : M.rank ≤ s) :
    ∃ (A : Matrix (Fin h) (Fin s) K) (B : Matrix (Fin s) (Fin h) K), M = A * B := by
  classical
  obtain ⟨v, hv⟩ := exists_span_of_finrank_le (LinearMap.range M.mulVecLin) s (by
    rw [← Matrix.rank]; exact hr)
  have hcol : ∀ j, ∃ c : Fin s → K, ∑ k, c k • v k = fun i => M i j := by
    intro j
    have hmem : (fun i => M i j) ∈ Submodule.span K (Set.range v) := by
      apply hv
      exact ⟨Pi.single j 1, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]; rfl⟩
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc⟩
  choose B hB using hcol
  refine ⟨fun i k => v k i, fun k j => B j k, ?_⟩
  ext i j
  have hij := congrFun (hB j) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hij
  rw [Matrix.mul_apply]
  simp_rw [mul_comm (v _ i)]
  exact hij.symm

/-- **Count of low-rank matrices**: at most `2^{2hs}` of the `h×h` `𝔽₂` matrices have rank `≤ s`. -/
theorem card_lowRank_le (h s : ℕ) :
    (Finset.univ.filter (fun M : Matrix (Fin h) (Fin h) (ZMod 2) => M.rank ≤ s)).card
      ≤ 2 ^ (2 * h * s) := by
  classical
  have hM : ∀ a b : ℕ, Fintype.card (Matrix (Fin a) (Fin b) (ZMod 2)) = 2 ^ (a * b) := by
    intro a b
    rw [Fintype.card_congr (Matrix.of (m := Fin a) (n := Fin b) (α := ZMod 2)).symm,
      Fintype.card_fun, Fintype.card_fun, ZMod.card 2, Fintype.card_fin, Fintype.card_fin,
      ← pow_mul, Nat.mul_comm]
  have hsub :
      (Finset.univ.filter (fun M : Matrix (Fin h) (Fin h) (ZMod 2) => M.rank ≤ s))
        ⊆ Finset.image
            (fun AB : Matrix (Fin h) (Fin s) (ZMod 2) × Matrix (Fin s) (Fin h) (ZMod 2) =>
              AB.1 * AB.2) Finset.univ := by
    intro M hM
    rw [Finset.mem_filter] at hM
    obtain ⟨A, B, hAB⟩ := rank_factor M hM.2
    exact Finset.mem_image.mpr ⟨(A, B), Finset.mem_univ _, hAB.symm⟩
  calc (Finset.univ.filter (fun M : Matrix (Fin h) (Fin h) (ZMod 2) => M.rank ≤ s)).card
      ≤ (Finset.image
          (fun AB : Matrix (Fin h) (Fin s) (ZMod 2) × Matrix (Fin s) (Fin h) (ZMod 2) =>
            AB.1 * AB.2) Finset.univ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ :
          Finset (Matrix (Fin h) (Fin s) (ZMod 2) × Matrix (Fin s) (Fin h) (ZMod 2))).card :=
        Finset.card_image_le
    _ = 2 ^ (2 * h * s) := by
        rw [Finset.card_univ, Fintype.card_prod, hM h s, hM s h, ← pow_add]
        ring_nf

/-- **Probabilistic-method pigeonhole.**  If the total size of the bad sets is smaller than the ground set, some
element avoids every bad set. -/
theorem exists_avoiding {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*} (T : Finset ι)
    (Bad : ι → Finset Ω) (hlt : ∑ i ∈ T, (Bad i).card < Fintype.card Ω) :
    ∃ ω : Ω, ∀ i ∈ T, ω ∉ Bad i := by
  by_contra hc
  push_neg at hc
  have hsubset : (Finset.univ : Finset Ω) ⊆ T.biUnion Bad := by
    intro ω _
    obtain ⟨i, hi, hω⟩ := hc ω
    exact Finset.mem_biUnion.mpr ⟨i, hi, hω⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_univ] at hcard
  have hbu := Finset.card_biUnion_le (s := T) (t := Bad)
  omega

end PallLean.Paper93.DeepMath.PathB.LowRankCount

#print axioms PallLean.Paper93.DeepMath.PathB.LowRankCount.rank_factor
#print axioms PallLean.Paper93.DeepMath.PathB.LowRankCount.card_lowRank_le
#print axioms PallLean.Paper93.DeepMath.PathB.LowRankCount.exists_avoiding
