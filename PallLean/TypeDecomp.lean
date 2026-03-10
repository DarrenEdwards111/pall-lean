import PallLean.Assembly

/-! # Type-based decomposition for Width⇒Rank

The paper's §9 proof uses type-based profile compression:
- Group m factors by algebraic type (|T| = O(1) types)
- Profile = histogram over types (≤ (m+|T|)^|T| = m^O(1) profiles)
- Per-profile dim via symmetric tensor powers (≤ (m+1)^(w·|T|))
- Total: m^O(1) (polynomial in m, constant exponent from w and |T|)

For the Tseitin construction (all factors isomorphic, |T| = 1, width = 4):
  Total ≤ (m+1) × (m+5)^4 ≤ (m+5)^5 ≤ (4m)^12

## Axiom decomposition

We replace the monolithic `width_to_rank` with the more refined
`symmetric_product_rank` axiom, which captures the §9 symmetric
tensor / profile compression core. The arithmetic bridge from
(m+w+1)^(w+1) to (m*w)^(3w) is then proved for width = 4.
-/

namespace SPDP

open MvPolynomial Finset

variable {n : ℕ} {F : Type*} [CommRing F]

-- Per-factor derivative subsets: each factor with ≤ w vars has ≤ 2^w subsets
theorem per_factor_deriv_subsets_le (w : ℕ) :
    ∀ (s : Finset (Fin n)), s.card ≤ w →
      (s.powerset).card ≤ 2 ^ w := by
  intro s hs
  rw [Finset.card_powerset]
  exact Nat.pow_le_pow_right (by omega) hs

-- Profile count for single-type case: m + 1 profiles
theorem single_type_profile_count (m : ℕ) (hm : m ≥ 1) :
    m + 1 ≤ (m * 4) ^ 12 := by
  have h1 : m * 4 ≥ 4 := by omega
  have h2 : (m * 4) ^ 12 ≥ 4 ^ 12 := Nat.pow_le_pow_left h1 12
  -- 4^12 = 16777216 ≥ m + 1 for reasonable m, but we need it for all m.
  -- Actually m + 1 ≤ m * 4 ≤ (m*4)^1 ≤ (m*4)^12
  calc m + 1 ≤ m * 4 := by omega
    _ = (m * 4) ^ 1 := by ring
    _ ≤ (m * 4) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)

-- Arithmetic: (m+5)^5 ≤ (4m)^12 for m ≥ 1
theorem profile_dim_bound_width4 (m : ℕ) (hm : m ≥ 1) :
    (m + 5) ^ 5 ≤ (m * 4) ^ 12 := by
  -- (m+5) ≤ 6m, so (m+5)^5 ≤ 6^5 * m^5 = 7776 * m^5
  -- (4m)^12 = 4^12 * m^12 ≥ 16777216 * m^5 (since m^7 ≥ 1)
  have h1 : m + 5 ≤ 6 * m := by omega
  calc (m + 5) ^ 5
      ≤ (6 * m) ^ 5 := Nat.pow_le_pow_left h1 5
    _ = 6 ^ 5 * m ^ 5 := by ring
    _ ≤ 4 ^ 12 * m ^ 12 := by
        -- 6^5 * m^5 ≤ 4^12 * m^12
        -- iff 6^5 ≤ 4^12 * m^7 (for m ≥ 1)
        have hm5 : m ^ 5 ≥ 1 := Nat.one_le_pow 5 m (by omega)
        have hm7 : m ^ 7 ≥ 1 := Nat.one_le_pow 7 m (by omega)
        have h12 : m ^ 12 = m ^ 5 * m ^ 7 := by ring
        rw [h12]
        -- 6^5 * m^5 ≤ 4^12 * m^5 * m^7
        -- iff 6^5 ≤ 4^12 * m^7, which holds since 7776 ≤ 16777216
        calc 6 ^ 5 * m ^ 5
            ≤ 6 ^ 5 * m ^ 5 * m ^ 7 := Nat.le_mul_of_pos_right _ (by omega)
          _ ≤ 4 ^ 12 * m ^ 5 * m ^ 7 := by
              apply Nat.mul_le_mul_right
              apply Nat.mul_le_mul_right
              norm_num
          _ = 4 ^ 12 * (m ^ 5 * m ^ 7) := by ring
    _ = (4 * m) ^ 12 := by ring
    _ = (m * 4) ^ 12 := by ring

-- The refined axiom: symmetric tensor / profile compression core.
-- For a product of m factors (each with ≤ w vars, degree ≤ w, ≤ w blocks),
-- the SPDP subspace has finrank ≤ (m + w + 1)^(w + 1).
--
-- This is the §9 Lemma 31 content: profile compression gives ≤ m+1 profiles,
-- and within each profile, the symmetric tensor power Sym^k(W) where
-- dim(W) = w+1 gives dim ≤ C(k+w, w) ≤ (m+w+1)^w.
-- Total: (m+1) × (m+w+1)^w ≤ (m+w+1)^(w+1).
axiom symmetric_product_rank
    {n : ℕ} {F : Type*} [Field F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (m : ℕ) (factor : Fin m → MvPolynomial (Fin n) F)
    (width : ℕ)
    (hfactor_width : ∀ i, (factor i).vars.card ≤ width)
    (hfactor_deg : ∀ i, (factor i).totalDegree ≤ width)
    (hblock_local : ∀ i, (Finset.univ.filter (fun b =>
        ∃ v ∈ (factor i).vars, B.assign v = b)).card ≤ width) :
    Module.finrank F (MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ
      (∏ i, factor i)) ≤ (m + width + 1) ^ (width + 1)

-- width_to_rank for width=4 (the only width used in P≠NP)
theorem width_to_rank_width4 {n : ℕ} {F : Type*} [Field F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (m : ℕ) (factor : Fin m → MvPolynomial (Fin n) F)
    (hm : m ≥ 1)
    (hfactor_width : ∀ i, (factor i).vars.card ≤ 4)
    (hfactor_deg : ∀ i, (factor i).totalDegree ≤ 4)
    (hblock_local : ∀ i, (Finset.univ.filter (fun b =>
        ∃ v ∈ (factor i).vars, B.assign v = b)).card ≤ 4) :
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (∏ i, factor i) ≤
    (m * 4) ^ 12 := by
  have h_sym := symmetric_product_rank B κ ℓ m factor 4
    hfactor_width hfactor_deg hblock_local
  calc Module.finrank F _ ≤ (m + 5) ^ 5 := h_sym
    _ ≤ (m * 4) ^ 12 := profile_dim_bound_width4 m hm

end SPDP
