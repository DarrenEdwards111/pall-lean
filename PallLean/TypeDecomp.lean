import PallLean.Assembly

/-! # Type-based decomposition for Width⇒Rank

Decomposes `symmetric_product_rank` into concrete mathematical components:

1. **Local derivative space** W_f: span of all derivatives of f by subsets
   of its variables. Dimension ≤ 2^w (PROVED).

2. **Profile subspace**: for each profile k (number of differentiated factors),
   the SPDP generators lie in Sym^k(W) ⊗ (undifferentiated tail).

3. **Symmetric tensor dimension**: dim Sym^k(V) = C(k+d-1, d-1) where d = dim V.

4. **Assembly**: total rank ≤ Σ_k dim(profile subspace_k) ≤ (m+w+1)^(w+1).

## Current status

- `localDerivSpace_finrank_le`: PROVED (dim W ≤ 2^w)
- `profile_dim_bound_width4`: PROVED (arithmetic bridge)
- Profile subspace containment: TODO (Lemma 31 core)
- Symmetric tensor dimension: TODO
-/

namespace SPDP

open MvPolynomial Finset

/-! ## Local derivative space -/

/-- The local derivative space of a polynomial f: the span of all iterated
    partial derivatives of f by subsets of its variables.

    For f with vars ⊆ {v₁,...,v_w}, W_f = span{∂_S f | S ⊆ vars(f)}.
    By pderiv_comm (Layer 3), the order of derivatives doesn't matter,
    so the derivatives are indexed by subsets, not sequences.

    W_f captures all possible "local contributions" of f in an SPDP
    decomposition: each factor receives some derivatives from the
    block-admissible list, and the result lies in W_f. -/
noncomputable def localDerivSpace {n : ℕ} {F : Type*} [CommRing F] [DecidableEq F]
    (f : MvPolynomial (Fin n) F) : Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    (Finset.image (fun S : Finset (Fin n) =>
      iterDerivList S.val.toList f) f.vars.powerset : Set _)

/-- The local derivative space is spanned by at most 2^w elements
    (the powerset of vars(f)), giving finrank ≤ 2^w.

    This is the per-factor dimension bound used in profile compression. -/
theorem localDerivSpace_finrank_le {n : ℕ} {F : Type*} [Field F] [DecidableEq F]
    (f : MvPolynomial (Fin n) F) (w : ℕ) (hw : f.vars.card ≤ w) :
    Module.finrank F (localDerivSpace f) ≤ 2 ^ w := by
  unfold localDerivSpace
  -- The span of a finite set has finrank ≤ the set's cardinality
  set img := Finset.image (fun S : Finset (Fin n) =>
    iterDerivList S.val.toList f) f.vars.powerset with himg_def
  -- The span of img (a finset) has finrank ≤ img.card
  -- finrank_span_le_card : finrank R (span R s) ≤ s.toFinset.card for Set s [Fintype s]
  have h1 : Module.finrank F (Submodule.span F (↑img : Set (MvPolynomial (Fin n) F))) ≤
      img.card := by
    convert finrank_span_le_card (R := F) (M := MvPolynomial (Fin n) F)
      ((↑img) : Set (MvPolynomial (Fin n) F)) using 1
    simp
  calc Module.finrank F (localDerivSpace f)
      = Module.finrank F (Submodule.span F (↑img : Set (MvPolynomial (Fin n) F))) := by
          rfl
    _ ≤ img.card := h1
    _ ≤ f.vars.powerset.card := Finset.card_image_le
    _ = 2 ^ f.vars.card := Finset.card_powerset f.vars
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw

/-- For width = 4: local derivative space has finrank ≤ 16. -/
theorem localDerivSpace_finrank_le_16 {n : ℕ} {F : Type*} [Field F] [DecidableEq F]
    (f : MvPolynomial (Fin n) F) (hw : f.vars.card ≤ 4) :
    Module.finrank F (localDerivSpace f) ≤ 16 := by
  have := localDerivSpace_finrank_le f 4 hw
  norm_num at this ⊢
  exact this

/-! ## Tighter bound: block-admissible derivatives

Block-admissibility constrains each factor to receive at most 1 derivative
per block it touches. For width w (≤ w blocks per factor), a factor receives
at most w derivatives, but crucially the derivatives must come from DISTINCT
blocks. This gives ≤ C(w, 0) + C(w, 1) + ... + C(w, w) = 2^w subsets.

For the SPDP bound, we actually only need the derivatives that are
"allocated" to this factor by the Leibniz decomposition. The allocated
derivatives form a subset of the factor's variables. -/

/-- The number of distinct derivative results for a factor with ≤ w variables
    is at most w + 1, when each factor receives at most 1 derivative
    (the common case in the single-type profile). -/
theorem single_deriv_options_le (w : ℕ) :
    w + 1 ≤ 2 ^ w := w.lt_two_pow_self

/-! ## Profile counting -/

-- Profile count for single-type case: m + 1 profiles
theorem single_type_profile_count (m : ℕ) (hm : m ≥ 1) :
    m + 1 ≤ (m * 4) ^ 12 := by
  calc m + 1 ≤ m * 4 := by omega
    _ = (m * 4) ^ 1 := by ring
    _ ≤ (m * 4) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)

/-! ## Arithmetic bridge -/

-- (m+5)^5 ≤ (4m)^12 for m ≥ 1
theorem profile_dim_bound_width4 (m : ℕ) (hm : m ≥ 1) :
    (m + 5) ^ 5 ≤ (m * 4) ^ 12 := by
  have h1 : m + 5 ≤ 6 * m := by omega
  calc (m + 5) ^ 5
      ≤ (6 * m) ^ 5 := Nat.pow_le_pow_left h1 5
    _ = 6 ^ 5 * m ^ 5 := by ring
    _ ≤ 4 ^ 12 * (m ^ 5 * m ^ 7) := by
        have hm7 : m ^ 7 ≥ 1 := Nat.one_le_pow 7 m (by omega)
        calc 6 ^ 5 * m ^ 5
            ≤ 6 ^ 5 * m ^ 5 * m ^ 7 := Nat.le_mul_of_pos_right _ (by omega)
          _ ≤ 4 ^ 12 * m ^ 5 * m ^ 7 := by
              apply Nat.mul_le_mul_right
              apply Nat.mul_le_mul_right
              norm_num
          _ = 4 ^ 12 * (m ^ 5 * m ^ 7) := by ring
    _ = (4 * m) ^ 12 := by
        rw [show (4 * m) ^ 12 = 4 ^ 12 * m ^ 12 from by ring,
            show m ^ 12 = m ^ 5 * m ^ 7 from by ring]
    _ = (m * 4) ^ 12 := by ring

/-! ## Symmetric tensor power dimension (stars-and-bars)

For a vector space W of dimension d, Sym^k(W) has dimension C(k+d-1, d-1).
This is the "stars and bars" formula.

For the Width⇒Rank bound with single type:
- W has dim d ≤ w + 1 (at most w+1 derivative outcomes per factor)
- Profile k counts how many factors receive derivatives (0 ≤ k ≤ m)
- Per-profile dim ≤ C(k + w, w) ≤ (k + w + 1)^w ≤ (m + w + 1)^w
- Total over profiles: (m+1) × (m+w+1)^w ≤ (m+w+1)^(w+1)

This gives symmetric_product_rank. -/

-- Stars-and-bars: C(n, k) ≤ n^k (from Mathlib)
theorem choose_le_pow' (n k : ℕ) : Nat.choose n k ≤ n ^ k :=
  Nat.choose_le_pow n k

-- Symmetric tensor dimension bound: C(k+d, d) ≤ (k+d)^d ≤ (k+d+1)^d
theorem sym_tensor_dim_le (d k : ℕ) :
    Nat.choose (k + d) d ≤ (k + d + 1) ^ d := by
  calc Nat.choose (k + d) d ≤ (k + d) ^ d := Nat.choose_le_pow (k + d) d
    _ ≤ (k + d + 1) ^ d := Nat.pow_le_pow_left (by omega) d

end SPDP
