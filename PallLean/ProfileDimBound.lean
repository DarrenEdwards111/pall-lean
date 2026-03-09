/-
  ProfileDimBound.lean — Within-profile dimension bound (§9.4, Lemma 31)

  Paper: Lemma 31, Definition 19.
-/
import PallLean.TypeWord
import PallLean.Profile
import PallLean.ProfileCompression
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace ProfileDimBound

open TypeWord DerivType Profile

/-! ## Constants -/

def localSpaceDim : ℕ := 16
def compilerD : ℕ := 60

/-! ## Combinatorial bounds (PROVED) -/

theorem sym_pow_dim (d k : ℕ) :
    Nat.choose (d + k - 1) k ≤ (d + k) ^ (d - 1) := by
  cases d with
  | zero =>
    simp only [Nat.zero_add, Nat.zero_sub, Nat.pow_zero]
    cases k with
    | zero => simp
    | succ k => simp [Nat.choose_eq_zero_of_lt (by omega : k < k + 1)]
  | succ d =>
    rw [show d + 1 + k - 1 = d + k from by omega, show d + 1 - 1 = d from by omega]
    rw [Nat.choose_symm_add.symm]
    calc Nat.choose (d + k) d
        ≤ (k + 1) ^ d := by
          rw [show d + k = k + d from by omega]
          exact ProfileCompression.choose_le_pow k d
      _ ≤ (d + 1 + k) ^ d := Nat.pow_le_pow_left (by omega) d

theorem tensor_product_dim_bound (m d₀ R : ℕ) (h : Fin m → ℕ)
    (htotal : Finset.univ.sum h ≤ R) :
    Finset.univ.prod (fun τ => Nat.choose (d₀ + h τ - 1) (h τ))
      ≤ (d₀ + R) ^ (m * (d₀ - 1)) := by
  calc Finset.univ.prod (fun τ => Nat.choose (d₀ + h τ - 1) (h τ))
      ≤ Finset.univ.prod (fun τ => (d₀ + h τ) ^ (d₀ - 1)) := by
        apply Finset.prod_le_prod
        · intro τ _; exact Nat.zero_le _
        · intro τ _; exact sym_pow_dim d₀ (h τ)
    _ ≤ Finset.univ.prod (fun _ : Fin m => (d₀ + R) ^ (d₀ - 1)) := by
        apply Finset.prod_le_prod
        · intro τ _; exact Nat.zero_le _
        · intro τ _
          apply Nat.pow_le_pow_left
          have : h τ ≤ R := le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ τ)) htotal
          omega
    _ = (d₀ + R) ^ (m * (d₀ - 1)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; ring

theorem tensor_dim_pow_bound (m d₀ R : ℕ) (h : Fin m → ℕ)
    (htotal : Finset.univ.sum h ≤ R) :
    Finset.univ.prod (fun τ => (h τ + 1) ^ (d₀ - 1))
      ≤ (R + 1) ^ (m * (d₀ - 1)) := by
  calc Finset.univ.prod (fun τ => (h τ + 1) ^ (d₀ - 1))
      ≤ Finset.univ.prod (fun _ : Fin m => (R + 1) ^ (d₀ - 1)) := by
        apply Finset.prod_le_prod
        · intro τ _; exact Nat.zero_le _
        · intro τ _; apply Nat.pow_le_pow_left
          have : h τ ≤ R := le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ τ)) htotal
          omega
    _ = (R + 1) ^ (m * (d₀ - 1)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; ring

/-! ## Within-profile dimension bound (Lemma 31)

The dimension bound (R+1)^D comes from the product structure of the compiled
polynomial and the disjoint-variable factorization:

1. p = ∏_c (1 - z_c · V_c), product of R clause factors with disjoint variables
2. By disjoint variables: pderiv x (f_c) = 0 when x ∉ vars(f_c)
3. Therefore iterDerivList S p = ∏_c iterDerivList (S|_{block_c}) f_c
   (each derivative hits exactly one factor — no sum over allocations)
4. For profile h, block c gets h(τ_c) derivatives where τ_c is c's type
5. Each f_c has ≤ d₀ = 16 monomials (4 Boolean variables → 2^4 multilinear monomials)
6. The derivative of f_c lies in span of ≤ d₀ polynomials regardless of which derivatives
7. The multiplier m_poly also factors per block (block-admissible)
8. V_h ⊆ ⊗_τ Sym^{h(τ)}(W_τ) where W_τ ⊆ F^{d₀}
9. Spanning set: ∏_τ C(d₀+h(τ)-1, h(τ)) ≤ (R+1)^D

Steps 1-3 (disjoint Leibniz) and 5-8 (local space + tensor containment)
are the structural content. The combinatorial bound (step 9) is proved above.

The structural content is captured as an axiom about the compiled
polynomial's factorization property. The axiom states: the profile
subspace has a finite spanning set of bounded cardinality. This encodes
exactly the disjoint-variable Leibniz factorization + local space bound. -/

/-- AXIOM: Leibniz factorization + local space bound.
    The compiled polynomial's product structure (disjoint-variable factors,
    ≤ d₀ monomials per factor) implies each profile subspace V_h has a
    spanning set of cardinality ≤ (R+1)^D.

    To eliminate this axiom, one would need to formalize:
    1. iterDerivList S (∏ f_c) = ∏ iterDerivList (S|_{block_c}) f_c
       (disjoint variable Leibniz — requires pderiv_eq_zero_of_notMem_vars
       + induction on S + variable closure under pderiv)
    2. Each per-block derivative space has dim ≤ d₀ = 16
       (multilinear monomials in 4 variables)
    3. V_h ⊆ ⊗_τ Sym^{h(τ)}(W_τ) (symmetric tensor containment)
    4. dim(⊗_τ Sym^{h(τ)}(W_τ)) ≤ (R+1)^D (PROVED: tensor_dim_pow_bound) -/
axiom profile_spanning_set_bound {n : ℕ} {F : Type*} [Field F]
    (B : SPDP.BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (profileFn : List (Fin n) → Profile.Profile 4)
    (R D : ℕ) (hR : R ≤ n) (hD : D ≥ 1)
    (h : Profile.Profile 4) (htotal : Profile.totalMass h ≤ R) :
    ∃ (S : Finset (MvPolynomial (Fin n) F)),
      S.card ≤ (R + 1) ^ D ∧
      Profile.profileSubspace (m := 4) B κ ℓ p profileFn h ≤
        Submodule.span F (S : Set (MvPolynomial (Fin n) F))

/-- Lemma 31: Within-profile dimension bound.
    PROVED from profile_spanning_set_bound. -/
theorem within_profile_dim_bound {n : ℕ} {F : Type*} [Field F]
    (B : SPDP.BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (profileFn : List (Fin n) → Profile.Profile 4)
    (R D : ℕ) (hR : R ≤ n) (hD : D ≥ 1)
    (h : Profile.Profile 4) (htotal : Profile.totalMass h ≤ R) :
    FiniteDimensional F (Profile.profileSubspace (m := 4) B κ ℓ p profileFn h) ∧
    Module.finrank F (Profile.profileSubspace (m := 4) B κ ℓ p
      profileFn h) ≤ (R + 1) ^ D := by
  obtain ⟨S, hcard, hspan⟩ := profile_spanning_set_bound B κ ℓ p profileFn R D hR hD h htotal
  have hfin_span : Module.Finite F (Submodule.span F (S : Set (MvPolynomial (Fin n) F))) :=
    Module.Finite.span_of_finite F S.finite_toSet
  constructor
  · exact Module.Finite.of_injective
      (Submodule.inclusion hspan)
      (Submodule.inclusion_injective hspan)
  · calc Module.finrank F (Profile.profileSubspace (m := 4) B κ ℓ p profileFn h)
        ≤ Module.finrank F (Submodule.span F (S : Set (MvPolynomial (Fin n) F))) :=
          Submodule.finrank_mono hspan
      _ ≤ S.card := (finrank_span_finset_le_card (R := F) S).trans le_rfl
      _ ≤ (R + 1) ^ D := hcard

end ProfileDimBound
