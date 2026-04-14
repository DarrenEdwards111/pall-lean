/-
  SymmetricPower.lean — Symmetric power functor formalization and
  proof of leibniz_symmetric_power_descent_bound

  ## Overview

  This file:
  1. Formalizes the symmetric power functor dimension formula
  2. Defines the profile factorization structure for product polynomials
  3. Proves leibniz_symmetric_power_descent_bound from the profile factorization

  ## Mathematical Content

  For a finite-dimensional vector space W of dimension d, the m-th symmetric power
  Sym^m(W) has dimension C(m+d-1, d-1) ≤ (m+1)^(d-1).

  For the Cook-Levin compiled polynomial p = ∏ᵢ(1-Cᵢ), the Leibniz product rule
  classifies iterated derivatives by "profiles" (constraint-type histograms).
  Within each profile h, the contributions factor through symmetric powers of
  local interface spaces of dimension ≤ 3, giving within-profile span dimension
  ≤ ∏_τ C(h(τ)+2, 2) ≤ (κ+1)^8.

  With ≤ (κ+1)^4 profiles, the total SPDP rank is ≤ (κ+1)^12 = combinedProfileBound(κ).

  ## Axiom and Leibniz connection

  The single remaining axiom is `spdp_profile_generators`: the SPDP subspace of the
  compiled polynomial is spanned by generators indexed by (profile, template) pairs,
  with ≤ (κ+1)^4 profiles and ≤ (κ+1)^8 templates per profile. This encodes the
  paper's §9 Theorem 92 (profile compression) at the level of explicit generators.

  The Leibniz product rule (Lemma 2, `iterDerivList_finset_prod_mem_span` from
  LeibnizProduct.lean) provides the foundation: each iterated derivative of the
  compiled product lies in the span of distributed derivative products.  After
  multiplying by the shift monomial and applying mlProj, the SPDP generators
  decompose into profile-classified terms.  The axiom encodes the cardinality
  bound on these profile-classified terms.

  The theorem `product_leibniz_profile_cover` is then proved from this axiom by
  taking the span of each profile's generators as a submodule.
-/
import PallLean.CookLevinDefs
import PallLean.MultilinearSPDP
import PallLean.IterDerivHelpers
import PallLean.LeibnizProduct
import Mathlib.Tactic

namespace SymmetricPower

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation
open LeibnizProduct

attribute [local instance] Classical.dec

/-! ## Part 1: Symmetric Power Dimension Formula

The symmetric power Sym^m(V) of a d-dimensional space has dimension
C(m+d-1, d-1). This is bounded above by (m+1)^(d-1).

For d = 3 (the Cook-Levin local interface dimension):
  dim(Sym^m(W_τ)) = C(m+2, 2) ≤ (m+1)^2

These bounds are used to estimate the within-profile template count. -/

/-- Stars-and-bars: C(m + d, d) ≤ (m+1)^d.
    Bounds dim(Sym^m(V)) when dim(V) = d+1. -/
theorem sym_power_dim_le (m d : ℕ) : Nat.choose (m + d) d ≤ (m + 1) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hrw : m + (d + 1) = m + d + 1 := by omega
    rw [hrw]
    have key : (m + d + 1) * Nat.choose (m + d) d =
      Nat.choose (m + d + 1) (d + 1) * (d + 1) := by
      have := Nat.add_one_mul_choose_eq (m + d) d
      linarith
    have hle : Nat.choose (m + d + 1) (d + 1) * (d + 1) ≤ (m + 1) ^ (d + 1) * (d + 1) := by
      rw [← key]
      calc (m + d + 1) * Nat.choose (m + d) d
          ≤ (m + d + 1) * (m + 1) ^ d := Nat.mul_le_mul_left _ ih
        _ ≤ ((m + 1) * (d + 1)) * (m + 1) ^ d := by
            apply Nat.mul_le_mul_right; nlinarith
        _ = (m + 1) ^ (d + 1) * (d + 1) := by ring
    exact Nat.le_of_mul_le_mul_right hle (by omega)

/-- For local interface dim = 3: C(m+2, 2) ≤ (m+1)^2. -/
theorem sym_power_dim3_le (m : ℕ) : Nat.choose (m + 2) 2 ≤ (m + 1) ^ 2 :=
  sym_power_dim_le m 2

/-- Profile count: C(κ+4, 4) ≤ (κ+1)^4.
    Number of histograms over 4 constraint types summing to ≤ κ. -/
theorem profile_count_le (κ : ℕ) : Nat.choose (κ + 4) 4 ≤ (κ + 1) ^ 4 :=
  sym_power_dim_le κ 4

/-- Booleanity local factor after compilation: 1 - z(1-z) = 1 - z + z^2. -/
noncomputable def boolFactor (N : ℕ) (v : Fin N) : MvPolynomial (Fin N) ℚ :=
  1 - (MvPolynomial.X v * (1 - MvPolynomial.X v))

/-- Adjacency local factor after compilation: 1 - z_i z_{i+1}. -/
noncomputable def adjFactor (N : ℕ) (i j : Fin N) : MvPolynomial (Fin N) ℚ :=
  1 - (MvPolynomial.X i * MvPolynomial.X j)

/-! ### Local outcome classification for booleanity factors

For boolFactor on variable v, the possible nonzero iterated derivatives are:
- 0 hits: boolFactor N v = 1 - z_v + z_v^2
- 1 hit by v: pderiv v (boolFactor N v) = -1 + 2z_v
- 2 hits by v: pderiv v (pderiv v (boolFactor N v)) = C 2
- ≥3 hits: 0 (proved in iterDerivList_boolFactor_eq_zero_of_length_ge_three)

After mlProj (multilinear projection), all outcomes lie in span{C 1, X v}
(the 2-dimensional local interface space for booleanity).

### Local outcome classification for adjacency factors

For adjFactor on variables (i,j) with i ≠ j, the possible nonzero derivatives are:
- 0 hits: adjFactor N i j = 1 - X i * X j
- 1 hit by i: pderiv i (adjFactor N i j) = -(X j)
- 1 hit by j: pderiv j (adjFactor N i j) = -(X i)
- 2 cross-hits (i then j or j then i): C (-1)
- 2 same-variable hits: 0
- ≥3 hits: 0 (proved in iterDerivList_adjFactor_eq_zero_of_length_ge_three)

After mlProj, all outcomes lie in span{C 1, X i, X j}
(the 3-dimensional local interface space for adjacency). -/

/-! ## Part 2: Symmetric Power Structure for Local Interface Spaces

Each Cook-Levin constraint type τ has a local interface space W_τ of dimension ≤ 3.
- Booleanity z(1-z): derivatives give {1-2z, 0} → W_bool ≅ span{1, z} → dim ≤ 3
- Adjacency z_i·z_{i+1}: derivatives give {z_{i+1}, z_i} → W_adj ≅ span{z_i, z_{i+1}} → dim ≤ 3
- Transition constraints: similar, dim ≤ 3

The m-th symmetric power Sym^m(W_τ) represents the space of "symmetric"
multilinear products of m elements from W_τ. Its dimension is C(m+2, 2). -/

/-- The booleanity local interface span is generated by the constant and the local variable. -/
def boolInterfaceSpan (N : ℕ) (v : Fin N) : Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  Submodule.span ℚ (({1} ∪ {MvPolynomial.X v} : Finset (MvPolynomial (Fin N) ℚ)) : Set (MvPolynomial (Fin N) ℚ))

/-- The adjacency local interface span is generated by the constant and the two endpoint variables. -/
def adjInterfaceSpan (N : ℕ) (i j : Fin N) : Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  Submodule.span ℚ (({1} ∪ {MvPolynomial.X i} ∪ {MvPolynomial.X j} : Finset (MvPolynomial (Fin N) ℚ)) : Set (MvPolynomial (Fin N) ℚ))

/-- The basic generators lie in the booleanity interface span. -/
private theorem one_mem_boolInterfaceSpan (N : ℕ) (v : Fin N) :
    (1 : MvPolynomial (Fin N) ℚ) ∈ boolInterfaceSpan N v := by
  unfold boolInterfaceSpan
  exact Submodule.subset_span (by simp)

private theorem X_mem_boolInterfaceSpan (N : ℕ) (v : Fin N) :
    MvPolynomial.X v ∈ boolInterfaceSpan N v := by
  unfold boolInterfaceSpan
  exact Submodule.subset_span (by simp)

/-- The basic generators lie in the adjacency interface span. -/
private theorem one_mem_adjInterfaceSpan (N : ℕ) (i j : Fin N) :
    (1 : MvPolynomial (Fin N) ℚ) ∈ adjInterfaceSpan N i j := by
  unfold adjInterfaceSpan
  exact Submodule.subset_span (by simp)

private theorem Xi_mem_adjInterfaceSpan (N : ℕ) (i j : Fin N) :
    MvPolynomial.X i ∈ adjInterfaceSpan N i j := by
  unfold adjInterfaceSpan
  exact Submodule.subset_span (by simp)

private theorem Xj_mem_adjInterfaceSpan (N : ℕ) (i j : Fin N) :
    MvPolynomial.X j ∈ adjInterfaceSpan N i j := by
  unfold adjInterfaceSpan
  exact Submodule.subset_span (by simp)

/-- Booleanity local factor depends only on its single variable. -/
theorem boolFactor_vars_subset (N : ℕ) (v : Fin N) :
    (boolFactor N v).vars ⊆ ({v} : Finset (Fin N)) := by
  unfold boolFactor
  intro x hx
  have hsub := MvPolynomial.vars_sub_subset
    (p := (1 : MvPolynomial (Fin N) ℚ))
    (q := (MvPolynomial.X v * (1 - MvPolynomial.X v)))
  have hx' := hsub hx
  simp only [Finset.mem_union, MvPolynomial.vars_one] at hx'
  rcases hx' with hx' | hx'
  · cases hx'
  have hmul := MvPolynomial.vars_mul
    (MvPolynomial.X v : MvPolynomial (Fin N) ℚ)
    (1 - MvPolynomial.X v)
  have hx'' := hmul hx'
  simp only [Finset.mem_union] at hx''
  cases hx'' with
  | inl hX =>
      simpa [MvPolynomial.vars_X] using hX
  | inr hrest =>
      have hsub2 := MvPolynomial.vars_sub_subset
        (p := (1 : MvPolynomial (Fin N) ℚ))
        (q := (MvPolynomial.X v : MvPolynomial (Fin N) ℚ))
      have hx''' := hsub2 hrest
      simp only [Finset.mem_union, MvPolynomial.vars_one,
        MvPolynomial.vars_X] at hx'''
      simpa using hx'''

/-- Adjacency local factor depends only on its endpoint variables. -/
theorem adjFactor_vars_subset (N : ℕ) (i j : Fin N) :
    (adjFactor N i j).vars ⊆ ({i, j} : Finset (Fin N)) := by
  unfold adjFactor
  intro x hx
  have hsub := MvPolynomial.vars_sub_subset
    (p := (1 : MvPolynomial (Fin N) ℚ))
    (q := (MvPolynomial.X i * MvPolynomial.X j))
  have hx' := hsub hx
  simp only [Finset.mem_union, MvPolynomial.vars_one] at hx'
  rcases hx' with hx' | hx'
  · cases hx'
  have hmul := MvPolynomial.vars_mul
    (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)
    (MvPolynomial.X j : MvPolynomial (Fin N) ℚ)
  have hx'' := hmul hx'
  simp only [Finset.mem_union, MvPolynomial.vars_X, Finset.mem_singleton,
    Finset.mem_insert] at hx'' ⊢
  exact hx''

/-- If a derivative list hits a variable outside the booleanity support, the iterated derivative vanishes. -/
theorem iterDerivList_boolFactor_eq_zero_of_exists_offsupport
    (N : ℕ) (v : Fin N) (S : List (Fin N))
    (hbad : ∃ x ∈ S, x ≠ v) :
    iterDerivList S (boolFactor N v) = 0 := by
  rcases hbad with ⟨x, hxS, hxv⟩
  apply IterDerivHelpers.iterDerivList_eq_zero_of_mem_notMem_vars S x (boolFactor N v) hxS
  intro hxmem
  have hsub := boolFactor_vars_subset N v hxmem
  have hxeq : x = v := by simpa using hsub
  exact hxv hxeq

/-- If a derivative list hits a variable outside the adjacency support, the iterated derivative vanishes. -/
theorem iterDerivList_adjFactor_eq_zero_of_exists_offsupport
    (N : ℕ) (i j : Fin N) (S : List (Fin N))
    (hbad : ∃ x ∈ S, x ≠ i ∧ x ≠ j) :
    iterDerivList S (adjFactor N i j) = 0 := by
  rcases hbad with ⟨x, hxS, hxi, hxj⟩
  apply IterDerivHelpers.iterDerivList_eq_zero_of_mem_notMem_vars S x (adjFactor N i j) hxS
  intro hxmem
  have hsub := adjFactor_vars_subset N i j hxmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsub
  cases hsub with
  | inl hi => exact hxi hi
  | inr hj => exact hxj hj

/-- A third hit on the booleanity variable kills the local factor. -/
theorem iterDerivList_boolFactor_triple_self_zero
    (N : ℕ) (v : Fin N) (S : List (Fin N)) :
    iterDerivList (v :: v :: v :: S) (boolFactor N v) = 0 := by
  unfold boolFactor
  simp only [IterDerivHelpers.iterDerivList_cons, map_sub, pderiv_one,
    pderiv_mul, MvPolynomial.pderiv_X_self, one_mul, zero_mul, zero_add, add_zero,
    map_one, sub_eq_add_neg, map_add, map_neg]
  ring_nf
  simp only [map_zero, mul_zero]
  exact SPDP.foldl_pderiv_zero S

/-- Any booleanity iterated derivative with at least three hits on its support vanishes. -/
theorem iterDerivList_boolFactor_eq_zero_of_length_ge_three
    (N : ℕ) (v : Fin N) (S : List (Fin N))
    (hS : 3 ≤ S.length)
    (hsupp : ∀ x ∈ S, x = v) :
    iterDerivList S (boolFactor N v) = 0 := by
  cases S with
  | nil => simp at hS
  | cons a1 t1 =>
      cases t1 with
      | nil => simp at hS
      | cons a2 t2 =>
          cases t2 with
          | nil => simp at hS
          | cons a3 rest =>
              have h1 : a1 = v := hsupp a1 (by simp)
              have h2 : a2 = v := hsupp a2 (by simp)
              have h3 : a3 = v := hsupp a3 (by simp)
              rw [h1, h2, h3]
              simpa using iterDerivList_boolFactor_triple_self_zero N v rest

/-! ### Concrete derivative computations for boolFactor -/

/-- Single derivative of boolFactor: pderiv v (1 - z(1-z)) = -1 + 2z. -/
theorem pderiv_boolFactor_self (N : ℕ) (v : Fin N) :
    MvPolynomial.pderiv v (boolFactor N v) = -1 + 2 * MvPolynomial.X v := by
  unfold boolFactor
  simp only [map_sub, pderiv_one, pderiv_mul, MvPolynomial.pderiv_X_self,
    one_mul, zero_mul, zero_add, add_zero, map_one, sub_eq_add_neg, map_add,
    map_neg, map_sub]
  ring

/-- After two same-variable derivatives, boolFactor becomes a constant (C 2). -/
private theorem two_deriv_boolFactor_is_const (N : ℕ) (v : Fin N) :
    ∃ (c : ℚ), MvPolynomial.pderiv v (MvPolynomial.pderiv v (boolFactor N v)) =
      MvPolynomial.C c := by
  refine ⟨2, ?_⟩
  unfold boolFactor
  simp only [map_sub, pderiv_one, pderiv_mul, MvPolynomial.pderiv_X_self,
    one_mul, zero_mul, zero_add, add_zero, map_one, sub_eq_add_neg, map_add,
    map_neg]
  ring_nf
  simp [map_ofNat]

/-! ### Concrete derivative computations for adjFactor -/

/-- Single derivative of adjFactor by the first variable: pderiv i (1 - z_i z_j) = -(z_j). -/
theorem pderiv_adjFactor_fst (N : ℕ) (i j : Fin N) (hij : i ≠ j) :
    MvPolynomial.pderiv i (adjFactor N i j) = -(MvPolynomial.X j) := by
  unfold adjFactor
  simp only [map_sub, pderiv_one, pderiv_mul, MvPolynomial.pderiv_X_self]
  rw [MvPolynomial.pderiv_X_of_ne hij.symm]
  ring

/-- Single derivative of adjFactor by the second variable: pderiv j (1 - z_i z_j) = -(z_i). -/
theorem pderiv_adjFactor_snd (N : ℕ) (i j : Fin N) (hij : i ≠ j) :
    MvPolynomial.pderiv j (adjFactor N i j) = -(MvPolynomial.X i) := by
  unfold adjFactor
  simp only [map_sub, pderiv_one, pderiv_mul, MvPolynomial.pderiv_X_self]
  rw [MvPolynomial.pderiv_X_of_ne hij]
  ring

/-- Cross-derivative of adjFactor: pderiv j (pderiv i (1 - z_i z_j)) = -1. -/
theorem pderiv_cross_adjFactor (N : ℕ) (i j : Fin N) (hij : i ≠ j) :
    MvPolynomial.pderiv j (MvPolynomial.pderiv i (adjFactor N i j)) =
    -(1 : MvPolynomial (Fin N) ℚ) := by
  unfold adjFactor
  simp only [map_sub, pderiv_one, pderiv_mul, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne hij.symm, mul_zero, add_zero, zero_sub,
    map_neg, one_mul]

/-- The concrete first derivative outcomes for adjacency lie in the local interface span. -/
theorem pderiv_adjFactor_fst_mem_adjInterfaceSpan (N : ℕ) (i j : Fin N) (hij : i ≠ j) :
    MvPolynomial.pderiv i (adjFactor N i j) ∈ adjInterfaceSpan N i j := by
  rw [pderiv_adjFactor_fst N i j hij]
  exact Submodule.neg_mem (adjInterfaceSpan N i j) (Xj_mem_adjInterfaceSpan N i j)

theorem pderiv_adjFactor_snd_mem_adjInterfaceSpan (N : ℕ) (i j : Fin N) (hij : i ≠ j) :
    MvPolynomial.pderiv j (adjFactor N i j) ∈ adjInterfaceSpan N i j := by
  rw [pderiv_adjFactor_snd N i j hij]
  exact Submodule.neg_mem (adjInterfaceSpan N i j) (Xi_mem_adjInterfaceSpan N i j)

/-- The cross derivative outcome for adjacency is constant, hence lies in the local interface span. -/
theorem pderiv_cross_adjFactor_mem_adjInterfaceSpan (N : ℕ) (i j : Fin N) (hij : i ≠ j) :
    MvPolynomial.pderiv j (MvPolynomial.pderiv i (adjFactor N i j)) ∈ adjInterfaceSpan N i j := by
  rw [pderiv_cross_adjFactor N i j hij]
  exact Submodule.neg_mem (adjInterfaceSpan N i j) (one_mem_adjInterfaceSpan N i j)

/-- After any two in-support derivatives, adjFactor becomes a constant. -/
private theorem two_deriv_adjFactor_is_const (N : ℕ) (i j a b : Fin N) (hij : i ≠ j)
    (ha : a = i ∨ a = j) (hb : b = i ∨ b = j) :
    ∃ (c : ℚ), MvPolynomial.pderiv b (MvPolynomial.pderiv a (adjFactor N i j)) =
      MvPolynomial.C c := by
  unfold adjFactor
  cases ha with
  | inl ha =>
    cases hb with
    | inl hb =>
      exact ⟨0, by subst ha; subst hb; simp only [map_sub, pderiv_one, pderiv_mul,
        MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne hij.symm,
        mul_zero, add_zero, zero_sub, map_neg, zero_mul, neg_zero, map_zero]⟩
    | inr hb =>
      exact ⟨-1, by subst ha; subst hb; simp only [map_sub, pderiv_one, pderiv_mul,
        MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne hij.symm,
        mul_zero, add_zero, zero_sub, map_neg, one_mul]; simp [map_ofNat]⟩
  | inr ha =>
    cases hb with
    | inl hb =>
      exact ⟨-1, by subst ha; subst hb; simp only [map_sub, pderiv_one, pderiv_mul,
        MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne hij,
        mul_one, zero_mul, zero_add, zero_sub, map_neg,
        MvPolynomial.pderiv_X_of_ne hij.symm, neg_zero, sub_zero]; simp [map_ofNat]⟩
    | inr hb =>
      exact ⟨0, by subst ha; subst hb; simp only [map_sub, pderiv_one, pderiv_mul,
        MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne hij,
        mul_one, zero_mul, zero_add, zero_sub, map_neg, mul_zero, neg_zero, map_zero]⟩


/-- Any iterated derivative of adjFactor with ≥3 in-support hits vanishes. -/
theorem iterDerivList_adjFactor_eq_zero_of_length_ge_three
    (N : ℕ) (i j : Fin N) (hij : i ≠ j) (S : List (Fin N))
    (hS : 3 ≤ S.length)
    (hsupp : ∀ x ∈ S, x = i ∨ x = j) :
    iterDerivList S (adjFactor N i j) = 0 := by
  cases S with
  | nil => simp at hS
  | cons a t1 =>
    cases t1 with
    | nil => simp at hS
    | cons b t2 =>
      have ha := hsupp a (by simp)
      have hb := hsupp b (by simp)
      obtain ⟨c, hc⟩ := two_deriv_adjFactor_is_const N i j a b hij ha hb
      simp only [IterDerivHelpers.iterDerivList_cons] at *
      rw [hc]
      cases t2 with
      | nil => simp at hS
      | cons d rest =>
        simp only [IterDerivHelpers.iterDerivList_cons]
        rw [MvPolynomial.pderiv_C]
        exact SPDP.foldl_pderiv_zero _

/-! ### Derivative of boolFactor by a different variable is zero -/

/-- pderiv v (boolFactor N w) = 0 when v ≠ w.
    Since boolFactor N w only involves variable w, any other derivative kills it. -/
theorem pderiv_boolFactor_of_ne (N : ℕ) (v w : Fin N) (hvw : v ≠ w) :
    MvPolynomial.pderiv v (boolFactor N w) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  have hsub := boolFactor_vars_subset N w hmem
  simp only [Finset.mem_singleton] at hsub
  exact hvw hsub

/-! ### Iterated derivative of boolFactor product over disjoint variables

For a product ∏_{j ∈ s} boolFactor N j of booleanity factors (each involving
a single distinct variable), and a nodup list S whose elements are all in s,
the iterated derivative iterDerivList S (∏_{j ∈ s} boolFactor N j) equals
(∏_{v ∈ S.toFinset} pderiv v (boolFactor N v)) * (∏_{j ∈ s \ S.toFinset} boolFactor N j).

This is Target 3 from the identity construction roadmap. -/

/-- Single pderiv step for boolFactor product: differentiating by v ∈ s gives
    pderiv v (boolFactor N v) * ∏_{j ∈ s.erase v} boolFactor N j. -/
theorem pderiv_boolFactor_prod (N : ℕ) (s : Finset (Fin N)) (v : Fin N) (hv : v ∈ s) :
    MvPolynomial.pderiv v (s.prod (boolFactor N)) =
      MvPolynomial.pderiv v (boolFactor N v) * (s.erase v).prod (boolFactor N) := by
  apply ProductDeriv.pderiv_prod_single hv
  intro j hj hjv
  exact pderiv_boolFactor_of_ne N v j hjv.symm

/-- Iterated derivative of boolFactor product: for a nodup list S with all elements in s,
    iterDerivList S (∏_{j ∈ s} boolFactor N j) =
      (∏_{v ∈ S} pderiv v (boolFactor N v)) * (∏_{j ∈ s \ S.toFinset} boolFactor N j).

    Each derivative in S hits exactly one factor (the one with the matching variable),
    because boolFactor N j only involves variable j (disjoint supports). -/
theorem iterDerivList_boolFactor_prod (N : ℕ) (s : Finset (Fin N))
    (S : List (Fin N)) (hS : S.Nodup) (hSs : ∀ v ∈ S, v ∈ s) :
    iterDerivList S (s.prod (boolFactor N)) =
      (S.map (fun v => MvPolynomial.pderiv v (boolFactor N v))).prod *
      (s \ S.toFinset).prod (boolFactor N) := by
  induction S generalizing s with
  | nil =>
    simp [iterDerivList, List.toFinset_nil, Finset.sdiff_empty]
  | cons v rest ih =>
    have hv_s : v ∈ s := hSs v (by simp)
    have hnd : rest.Nodup := (List.nodup_cons.mp hS).2
    have hv_notin : v ∉ rest := (List.nodup_cons.mp hS).1
    simp only [IterDerivHelpers.iterDerivList_cons]
    rw [pderiv_boolFactor_prod N s v hv_s]
    -- Now we need: iterDerivList rest (pderiv v (boolFactor N v) * (s.erase v).prod (boolFactor N))
    -- pderiv v (boolFactor N v) = -1 + 2 * X v, which is killed by pderiv w for w ∈ rest (w ≠ v)
    -- So we can factor it out using iterDerivList_mul_left_const
    have hconst : ∀ w ∈ rest, MvPolynomial.pderiv w (MvPolynomial.pderiv v (boolFactor N v)) = 0 := by
      intro w hw
      have hwv : w ≠ v := fun h => hv_notin (h ▸ hw)
      -- pderiv v (boolFactor N v) has vars ⊆ {v}, so pderiv w kills it for w ≠ v
      apply IterDerivHelpers.pderiv_eq_zero_of_pderiv_eq_zero w v
      exact pderiv_boolFactor_of_ne N w v hwv
    rw [IterDerivHelpers.iterDerivList_mul_left_const rest _ _ hconst]
    -- Now apply IH to the remaining product over s.erase v
    have hrest_s : ∀ w ∈ rest, w ∈ s.erase v := by
      intro w hw
      have hwv : w ≠ v := fun h => hv_notin (h ▸ hw)
      exact Finset.mem_erase.mpr ⟨hwv, hSs w (by simp [hw])⟩
    rw [ih (s.erase v) hnd hrest_s]
    -- Now simplify both sides
    simp only [List.map_cons, List.prod_cons]
    ring_nf
    congr 1
    -- Need: s.erase v \ rest.toFinset = s \ (v :: rest).toFinset
    congr 1
    ext x
    simp only [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hxv, hxs⟩, hxr⟩
      exact ⟨hxs, fun h => h.elim (fun h => hxv h) (fun h => hxr h)⟩
    · rintro ⟨hxs, hxvr⟩
      exact ⟨⟨fun h => hxvr (Or.inl h), hxs⟩, fun h => hxvr (Or.inr h)⟩

/-! ### mlProj computations for boolFactor derivatives

For the Kronecker coefficient computation in the identity minor argument,
we need to compute mlProj of products involving boolFactor derivatives.
Key facts:
- mlProj(X v) = X v  (X v is multilinear)
- mlProj(X v * X v) = 0  (X v^2 is not multilinear)
- mlProj(X v * (-1 + 2 * X v)) = -X v  (follows from linearity + above) -/

/-- X v is multilinear -/
theorem isMultilinear_X {N : ℕ} (v : Fin N) :
    IsMultilinear (MvPolynomial.X v : MvPolynomial (Fin N) ℚ) := by
  intro α hα i
  rw [MvPolynomial.mem_support_iff] at hα
  rw [MvPolynomial.coeff_X'] at hα
  split_ifs at hα with h
  · rw [Finsupp.ext_iff] at h
    have := h i
    simp only [Finsupp.single_apply] at this
    split_ifs at this with hiv
    · subst hiv; omega
    · omega
  · exact absurd rfl hα

/-- mlProj fixes X v (since X v is already multilinear) -/
theorem mlProj_X {N : ℕ} (v : Fin N) :
    mlProj (MvPolynomial.X v : MvPolynomial (Fin N) ℚ) = MvPolynomial.X v :=
  mlProj_of_isMultilinear _ (isMultilinear_X v)

/-- X v * X v = monomial (Finsupp.single v 2) 1 is not multilinear, so mlProj kills it -/
theorem mlProj_X_sq_zero {N : ℕ} (v : Fin N) :
    mlProj (MvPolynomial.X v * MvPolynomial.X v : MvPolynomial (Fin N) ℚ) = 0 := by
  -- X v * X v = monomial (single v 1 + single v 1) 1 = monomial (single v 2) 1
  have hXX : (MvPolynomial.X v : MvPolynomial (Fin N) ℚ) * MvPolynomial.X v =
      MvPolynomial.monomial (Finsupp.single v 1 + Finsupp.single v 1) (1 * 1) := by
    rw [MvPolynomial.X, MvPolynomial.monomial_mul]
  rw [hXX, mul_one]
  have hadd : Finsupp.single v 1 + Finsupp.single v 1 = Finsupp.single v 2 := by
    ext i; simp [Finsupp.single_apply]; split_ifs <;> omega
  rw [hadd, mlProj_monomial]
  simp only [ite_eq_right_iff]
  intro hml
  exfalso
  have := hml v
  simp [Finsupp.single_apply] at this

/-- mlProj(X v * pderiv v (boolFactor N v)) = -(X v).
    Key computation for the Kronecker delta property of SPDP generators. -/
theorem mlProj_X_mul_pderiv_boolFactor {N : ℕ} (v : Fin N) :
    mlProj (MvPolynomial.X v * MvPolynomial.pderiv v (boolFactor N v) :
      MvPolynomial (Fin N) ℚ) = -(MvPolynomial.X v) := by
  rw [pderiv_boolFactor_self N v]
  -- X v * (-1 + 2 * X v) = -X v + 2 * (X v * X v)
  have hexpand : (MvPolynomial.X v : MvPolynomial (Fin N) ℚ) * (-1 + 2 * MvPolynomial.X v) =
      -(MvPolynomial.X v) + 2 * (MvPolynomial.X v * MvPolynomial.X v) := by ring
  rw [hexpand, mlProj_add]
  -- mlProj(-X v) = -(mlProj(X v)) = -(X v)
  have hml_neg : mlProj (-(MvPolynomial.X v : MvPolynomial (Fin N) ℚ)) =
      -mlProj (MvPolynomial.X v) := by
    have : -(MvPolynomial.X v : MvPolynomial (Fin N) ℚ) = (-1 : ℚ) • MvPolynomial.X v := by simp
    rw [this, mlProj_smul]; simp
  rw [hml_neg, mlProj_X v]
  -- mlProj(2 * (X v * X v)) = 2 • mlProj(X v * X v) = 2 • 0 = 0
  -- Use: 2 * p = MvPolynomial.C 2 * p = (2 : ℚ) • p for ℚ-algebra
  conv_lhs => rw [show (2 : MvPolynomial (Fin N) ℚ) = MvPolynomial.C 2 from by simp [map_ofNat]]
  rw [MvPolynomial.C_mul', mlProj_smul, mlProj_X_sq_zero v, smul_zero, add_zero]

/-- mlProj of boolFactor: mlProj(1 - z(1-z)) = 1 - z.
    Since boolFactor N v = 1 - X v + X v^2, and mlProj drops X v^2. -/
theorem mlProj_boolFactor {N : ℕ} (v : Fin N) :
    mlProj (boolFactor N v : MvPolynomial (Fin N) ℚ) = 1 - MvPolynomial.X v := by
  unfold boolFactor
  -- 1 - X v * (1 - X v) = 1 - X v + X v * X v
  have hexpand : (1 : MvPolynomial (Fin N) ℚ) - MvPolynomial.X v * (1 - MvPolynomial.X v) =
      (1 - MvPolynomial.X v) + MvPolynomial.X v * MvPolynomial.X v := by ring
  rw [hexpand, mlProj_add, mlProj_X_sq_zero v, add_zero]
  -- 1 - X v is multilinear: show every monomial in support has degree ≤ 1 in each variable
  apply mlProj_of_isMultilinear
  intro α hα i
  -- coeff α (1 - X v) ≠ 0 implies α = 0 or α = single v 1
  by_contra h_gt
  push_neg at h_gt
  have hi : 2 ≤ α i := h_gt
  -- α = 0 is impossible since α i ≥ 2
  have h0 : α ≠ 0 := by intro he; subst he; simp at hi
  -- α = single v 1 is impossible since (single v 1) i ≤ 1
  have hv : α ≠ Finsupp.single v 1 := by
    intro he; subst he; simp [Finsupp.single_apply] at hi; split_ifs at hi <;> omega
  -- coeff α (1 - X v) = 0 for all other α, contradiction
  have hcoeff : MvPolynomial.coeff α ((1 : MvPolynomial (Fin N) ℚ) - MvPolynomial.X v) = 0 := by
    simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, MvPolynomial.coeff_X']
    rw [if_neg (Ne.symm h0), if_neg (Ne.symm hv), sub_self]
  exact (MvPolynomial.mem_support_iff.mp hα) hcoeff

/-! ### Coefficient of tag monomial in boolFactor SPDP generator

For the Kronecker delta property, we need the coefficient of the "tag monomial"
τ_S = ∏_{s∈S} z_s in the SPDP generator mlProj(∏_{s∈S} z_s * iterDerivList S p_bool).

Key computation: for the single-variable case,
  coeff (single v 1) (X v * pderiv v (boolFactor N v)) = -1
since X v * (-1 + 2 * X v) = -X v + 2*X v^2, and coeff (single v 1) (-X v) = -1,
while X v^2 contributes coefficient 0 at the multilinear monomial single v 1.
-/

/-- Coefficient of (single v 1) in X v * pderiv v (boolFactor N v) is -1. -/
theorem coeff_X_mul_pderiv_boolFactor {N : ℕ} (v : Fin N) :
    MvPolynomial.coeff (Finsupp.single v 1)
      (MvPolynomial.X v * MvPolynomial.pderiv v (boolFactor N v) :
        MvPolynomial (Fin N) ℚ) = -1 := by
  rw [pderiv_boolFactor_self N v]
  -- X v * (-1 + 2 * X v) = -X v + 2 * (X v * X v)
  have hexpand : (MvPolynomial.X v : MvPolynomial (Fin N) ℚ) * (-1 + 2 * MvPolynomial.X v) =
      -(MvPolynomial.X v) + 2 * (MvPolynomial.X v * MvPolynomial.X v) := by ring
  rw [hexpand]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_neg, MvPolynomial.coeff_X']
  simp only [ite_true]
  -- coeff (single v 1) (2 * X v * X v) = 2 * coeff (single v 1) (X v * X v)
  -- X v * X v = monomial (single v 2) 1, and single v 1 ≠ single v 2
  -- 2 * (X v * X v) has no multilinear monomial at single v 1
  -- because X v * X v only has the monomial single v 2
  -- Strategy: use mlProj_X_sq_zero to note mlProj(X v * X v) = 0
  -- then coeff (single v 1) (2 * 0) = 0
  conv_lhs =>
    rw [show (2 : MvPolynomial (Fin N) ℚ) = MvPolynomial.C 2 from by simp [map_ofNat]]
  rw [MvPolynomial.C_mul']
  -- coeff (single v 1) of smul = 2 * coeff (single v 1)
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.coeff_C_mul]
  -- coeff (single v 1) (X v * X v) = 0 since single v 1 is multilinear
  -- and mlProj(X v * X v) = 0 means all multilinear coefficients are 0
  have h0 : MvPolynomial.coeff (Finsupp.single v 1) (MvPolynomial.X v * MvPolynomial.X v : MvPolynomial (Fin N) ℚ) = 0 := by
    rw [← coeff_mlProj_of_isMultilinear_mono _ _
      (fun i => by simp [Finsupp.single_apply]; split_ifs <;> omega),
      mlProj_X_sq_zero v, MvPolynomial.coeff_zero]
  rw [h0, mul_zero, add_zero]

/-- Coefficient of (single v 1) in mlProj of the boolFactor single-variable SPDP generator is -1. -/
theorem coeff_mlProj_X_mul_pderiv_boolFactor {N : ℕ} (v : Fin N) :
    MvPolynomial.coeff (Finsupp.single v 1)
      (mlProj (MvPolynomial.X v * MvPolynomial.pderiv v (boolFactor N v) :
        MvPolynomial (Fin N) ℚ)) = -1 := by
  -- single v 1 is multilinear, so coeff at mlProj = coeff at original
  rw [coeff_mlProj_of_isMultilinear_mono _ _ (fun i => by simp [Finsupp.single_apply]; split_ifs <;> omega)]
  exact coeff_X_mul_pderiv_boolFactor v

/-! ### Profile compression: proved infrastructure and remaining gap

The proved lemmas above establish:

**Leibniz decomposition** (spdp_generator_in_leibniz_span):
  Every SPDP generator mlProj(m * iterDerivList S p) lies in the span of
  distributed derivative products.

**Locality** (iterDerivList_{bool,adj}Factor_eq_zero_of_exists_offsupport):
  A derivative on a variable outside a factor's support kills that factor.

**Saturation** (iterDerivList_{bool,adj}Factor_eq_zero_of_length_ge_three):
  ≥3 in-support derivatives kill any local factor (degree ≤ 2).

**Local outcome classification** (pderiv_{boolFactor_self,adjFactor_fst,adjFactor_snd,cross_adjFactor}):
  The concrete derivative outcomes are explicit polynomials in ≤ 3 variables.

Together these show that each distributed derivative product is a product of ≤ 4
local outcomes per touched constraint (original, 1st, 2nd derivative, or 0),
with each outcome lying in a local interface space of dimension ≤ 3.

**Remaining gap for spdp_profile_generators**: The profile compression bound
  (κ+1)^4 profiles × (κ+1)^8 generators/profile requires the symmetric power
  argument: within a fixed derivative profile (histogram of hit counts across
  constraint types), the products of local outcomes span a space whose dimension
  equals the symmetric power dim = ∏_τ C(h(τ)+2, 2) ≤ (κ+1)^8. This is the
  irreducible mathematical content of the paper's §9 Theorem 92 (profile
  compression via symmetric powers of local interface spaces). -/

/-- The local interface dimension for Cook-Levin constraints. -/
def localDim : ℕ := 3

/-- The number of effective constraint types in Cook-Levin compilation. -/
def numTypes : ℕ := 4

/-- A profile histogram: for each of the 4 constraint types, how many
    derivative hits land on that type. -/
def ProfileHist (κ : ℕ) := { h : Fin numTypes → ℕ // ∑ i, h i ≤ κ }

/-- The within-profile dimension bound for a single type τ with h(τ) hits:
    dim(Sym^{h(τ)}(W_τ)) ≤ C(h(τ)+2, 2) ≤ (h(τ)+1)^2. -/
theorem within_type_dim_le (m : ℕ) : Nat.choose (m + 2) 2 ≤ (m + 1) ^ 2 :=
  sym_power_dim3_le m

/-- The product of within-type bounds over all 4 types gives ≤ (κ+1)^8
    when each h(τ) ≤ κ. -/
theorem within_profile_dim_le (κ : ℕ) (h : Fin numTypes → ℕ) (hle : ∀ i, h i ≤ κ) :
    (∏ i : Fin numTypes, (h i + 1) ^ 2) ≤ (κ + 1) ^ 8 := by
  unfold numTypes at h hle ⊢
  calc ∏ i : Fin 4, (h i + 1) ^ 2
      ≤ ∏ _i : Fin 4, (κ + 1) ^ 2 := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i _
          have hi := hle i
          exact Nat.pow_le_pow_left (by omega) 2
    _ = (κ + 1) ^ 8 := by
        simp [Finset.prod_const, Finset.card_fin]
        ring

/-- The combined profile bound: (κ+1)^4 × (κ+1)^8 = (κ+1)^12. -/
theorem combined_profile_le (κ : ℕ) : (κ + 1) ^ 4 * (κ + 1) ^ 8 = (κ + 1) ^ 12 := by ring

/-- The combined profile bound value (matches combinedProfileBound). -/
def combinedProfileBound (κ : ℕ) : ℕ := (κ + 1) ^ 4 * (κ + 1) ^ 8

/-- combinedProfileBound equals (κ+1)^12. -/
theorem combinedProfileBound_eq (κ : ℕ) : combinedProfileBound κ = (κ + 1) ^ 12 := by
  unfold combinedProfileBound; ring

/-! ## Part 3: Leibniz-based infrastructure for the profile generators

The compiled polynomial p = ∏ᵢ(1-Cᵢ) is a finite product.  By the
iterated Leibniz rule (Lemma 2, `iterDerivList_finset_prod_mem_span`),
every iterated derivative `iterDerivList S p` lies in the ℚ-span of
`distribDerivProds` — all products ∏ᵢ iterDerivList(hᵢ)(fᵢ) where
the derivative indices hᵢ draw from S.

This section provides helper lemmas connecting the Leibniz product rule
to the SPDP generator decomposition.  These are used by the downstream
profile compression argument. -/

/-- The multilinear projection composed with multiplication by a fixed
    polynomial is ℚ-linear, hence preserves span membership.

    If p ∈ span(S), then mlProj(m * p) ∈ span(mlProj(m * ·) '' S). -/
theorem mlProj_mul_mem_span_image {n : ℕ}
    (m : MvPolynomial (Fin n) ℚ)
    (S : Set (MvPolynomial (Fin n) ℚ))
    (p : MvPolynomial (Fin n) ℚ)
    (hp : p ∈ Submodule.span ℚ S) :
    mlProj (m * p) ∈ Submodule.span ℚ ((fun q => mlProj (m * q)) '' S) := by
  -- The map φ(q) = mlProj(m * q) is ℚ-linear.
  -- We define it as a composition of two ℚ-linear maps:
  --   q ↦ m * q (left multiplication by m)
  --   r ↦ mlProj r
  -- Then φ(span(S)) ⊆ span(φ '' S) since φ is linear.

  -- Define the ℚ-linear map φ(q) = mlProj(m * q) using comap/map.
  set T := Submodule.span ℚ ((fun q => mlProj (m * q)) '' S) with hT_def
  -- Define the preimage submodule L = { q | mlProj(m*q) ∈ T }
  -- L is a submodule because φ(q) = mlProj(m*q) is ℚ-linear.
  let mulm : MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ :=
    { toFun := fun q => m * q
      map_add' := fun x y => mul_add m x y
      map_smul' := fun c x => by
        change m * (c • x) = c • (m * x)
        rw [Algebra.mul_smul_comm] }
  let φ := (mlProjLinearMap (Fin n) ℚ).comp mulm
  set L := T.comap φ with hL_def
  -- S ⊆ L: for each x ∈ S, mlProj(m*x) ∈ T
  have hSL : S ⊆ ↑L := by
    intro x hx
    change φ x ∈ T
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  -- span(S) ≤ L
  have hspanL : Submodule.span ℚ S ≤ L := Submodule.span_le.mpr hSL
  -- p ∈ L → φ p ∈ T → mlProj(m*p) ∈ T
  exact hspanL hp

/-- Leibniz decomposition of SPDP generators.

For the compiled polynomial p = (factors).prod where factors are the
mapped constraints, each SPDP generator mlProj(m * iterDerivList S p)
lies in the span of { mlProj(m * g) | g ∈ distribDerivProds }.

This follows from Lemma 2 (iterDerivList_finset_prod_mem_span) and
the ℚ-linearity of mlProj ∘ (m * ·). -/
theorem spdp_generator_in_leibniz_span {n : ℕ}
    (B : BlockPartition n) (κ : ℕ)
    (factors : List (MvPolynomial (Fin n) ℚ))
    (S : List (Fin n))
    (m : MvPolynomial (Fin n) ℚ)
    (p : MvPolynomial (Fin n) ℚ)
    (hp : p = factors.prod) :
    mlProj (m * iterDerivList S p) ∈
      Submodule.span ℚ
        (mlProj ∘ (m * ·) '' distribDerivProds Finset.univ
          (fun i : Fin factors.length => factors[i.val]) S) := by
  -- Step 1: p = Finset.univ.prod (fun i => factors[i])
  have hprod : p = Finset.univ.prod (fun i : Fin factors.length => factors[i.val]) := by
    rw [hp]
    rw [← Fin.prod_univ_getElem]
  -- Step 2: iterDerivList S p ∈ span(distribDerivProds)
  rw [hprod]
  have hmem := iterDerivList_finset_prod_mem_span
    Finset.univ (fun i : Fin factors.length => factors[i.val]) S
  -- Step 3: mlProj(m * iterDerivList S p) ∈ span(mlProj(m*·) '' distribDerivProds)
  exact mlProj_mul_mem_span_image m _ _ hmem

/-! ## Part 3b: Profile generator axiom

The profile generator axiom encodes the profile compression claim:
after the Leibniz decomposition, the distribDerivProds can be classified
by constraint-type histogram, and within each histogram the contributions
span a subspace of bounded dimension via the symmetric power analysis.

The axiom provides explicit generators indexed by (profile, template) pairs
with the required cardinality bounds. -/

/-- Profile generator axiom: the SPDP subspace of the Cook-Levin compiled
polynomial is spanned by generators that can be indexed by profile class
and within-profile template index.

This is the paper's §9 Theorem 92 at the generator level: the Leibniz product
rule decomposes each SPDP generator into terms classified by constraint-type
histogram (profile). Within each profile, the contributions factor through
symmetric powers of local interface spaces of dimension ≤ 3, yielding
≤ (κ+1)^8 independent templates per profile and ≤ (κ+1)^4 profiles.

The Leibniz connection is established by `spdp_generator_in_leibniz_span`:
each SPDP generator mlProj(m * iterDerivList S p) decomposes via
`iterDerivList_finset_prod_mem_span` (Lemma 2) into distributed derivative
products, which are then classified by profile.

The axiom provides:
- numP ≤ (κ+1)^4 profile classes
- bound ≤ (κ+1)^8 generators per profile
- generators : Fin numP → Fin bound → polynomial
- The SPDP subspace is contained in span{generators i j | i, j}
-/
axiom spdp_profile_generators
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∃ (numP bound : ℕ)
      (generators : Fin numP → Fin bound →
        MvPolynomial (Fin (cook_levin_compilation M n hn htb hns).numVars) ℚ),
      numP ≤ (Nat.log 2 n + 1) ^ 4 ∧
      bound ≤ (Nat.log 2 n + 1) ^ 8 ∧
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn htb hns)) ≤
      Submodule.span ℚ (Set.range (fun (ij : Fin numP × Fin bound) =>
        generators ij.1 ij.2))

/-- The product Leibniz profile cover: for the cook_levin_compilation,
the SPDP subspace decomposes into profile subspaces of bounded finrank.

This is the paper's §9 Theorem 92 specialized to the specific compiled
polynomial. It encodes:
- The Leibniz decomposition of iterated derivatives of the product
- The profile classification of Leibniz terms
- The within-profile factorization through symmetric powers
- The resulting finrank bound per profile

Proved from `spdp_profile_generators` by taking the span of each profile's
generators as a submodule. Each profile submodule has finrank ≤ (κ+1)^8
(since it is spanned by ≤ (κ+1)^8 elements), and the union of all profile
submodules covers the SPDP subspace. -/
theorem product_leibniz_profile_cover
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∃ (numP : ℕ) (spaces : Fin numP → Submodule ℚ
        (MvPolynomial (Fin (cook_levin_compilation M n hn htb hns).numVars) ℚ)),
      numP ≤ (Nat.log 2 n + 1) ^ 4 ∧
      (∀ i, Module.Finite ℚ (spaces i)) ∧
      (∀ i, Module.finrank ℚ (spaces i) ≤ (Nat.log 2 n + 1) ^ 8) ∧
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn htb hns)) ≤ ⨆ i, spaces i := by
  obtain ⟨numP, bound, generators, hnumP, hbound, hcover⟩ :=
    spdp_profile_generators M n hn htb hns
  -- Define the profile subspaces as spans of each profile's generators
  let spaces : Fin numP → Submodule ℚ
      (MvPolynomial (Fin (cook_levin_compilation M n hn htb hns).numVars) ℚ) :=
    fun i => Submodule.span ℚ (Set.range (fun j : Fin bound => generators i j))
  refine ⟨numP, spaces, hnumP, ?_, ?_, ?_⟩
  -- (1) Each profile subspace is finite-dimensional
  · intro i
    apply Module.Finite.span_of_finite
    exact Set.finite_range _
  -- (2) Each profile subspace has finrank ≤ (κ+1)^8
  · intro i
    calc Module.finrank ℚ ↥(spaces i)
        = Module.finrank ℚ ↥(Submodule.span ℚ (Set.range (fun j : Fin bound => generators i j))) := rfl
      _ ≤ (Set.range (fun j : Fin bound => generators i j)).toFinset.card :=
          finrank_span_le_card _
      _ ≤ Fintype.card (Fin bound) := by
          rw [Set.toFinset_range]
          exact Finset.card_image_le
      _ = bound := Fintype.card_fin bound
      _ ≤ (Nat.log 2 n + 1) ^ 8 := hbound
  -- (3) The profile subspaces cover the SPDP subspace
  · calc mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (compiledPoly (cook_levin_compilation M n hn htb hns))
        ≤ Submodule.span ℚ (Set.range (fun ij : Fin numP × Fin bound =>
            generators ij.1 ij.2)) := hcover
      _ = Submodule.span ℚ (⋃ i : Fin numP,
            Set.range (fun j : Fin bound => generators i j)) := by
          congr 1
          ext x
          simp only [Set.mem_range, Set.mem_iUnion, Prod.exists]
      _ = ⨆ i : Fin numP, Submodule.span ℚ
            (Set.range (fun j : Fin bound => generators i j)) :=
          Submodule.span_iUnion _
      _ = ⨆ i, spaces i := rfl

/-! ## Part 4: Proving leibniz_symmetric_power_descent_bound

From the profile cover, we derive the finrank bound using:
- Submodule.finrank_mono (containment → finrank comparison)
- finrank_iSup_fin_le (finrank of sup ≤ sum of finranks)
- Arithmetic: numP * (κ+1)^8 ≤ (κ+1)^4 * (κ+1)^8 = (κ+1)^12 -/

/-- Helper: finrank of iSup is bounded by sum of finranks.
    Restated from SPDPDefs for convenient use. -/
private theorem finrank_iSup_le (m : ℕ)
    {n : ℕ}
    (U : Fin m → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    [∀ i, Module.Finite ℚ ↥(U i)] :
    Module.finrank ℚ ↥(⨆ i : Fin m, U i) ≤ ∑ i : Fin m, Module.finrank ℚ ↥(U i) :=
  finrank_iSup_fin_le m U

/-- The main theorem: the SPDP subspace of the compiled polynomial has
finrank ≤ combinedProfileBound(κ) = (κ+1)^12.

Proved from `product_leibniz_profile_cover` by:
1. Obtaining the profile cover (numP ≤ (κ+1)^4 subspaces, each finrank ≤ (κ+1)^8)
2. Using finrank_mono with the covering containment
3. Bounding finrank(⨆ spaces) ≤ Σ finrank(spaces i) ≤ numP × (κ+1)^8
4. Arithmetic: numP × (κ+1)^8 ≤ (κ+1)^4 × (κ+1)^8 = (κ+1)^12 -/
theorem leibniz_symmetric_power_descent_bound
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Module.finrank ℚ ↥(mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns)))
    ≤ combinedProfileBound (Nat.log 2 n) := by
  -- Obtain the profile decomposition
  obtain ⟨numP, spaces, hnumP, hfin, hbound, hcover⟩ :=
    product_leibniz_profile_cover M n hn htb hns
  -- Set κ for readability
  set κ := Nat.log 2 n
  -- The combined bound unfolds to (κ+1)^12
  have hcomb : combinedProfileBound κ = (κ + 1) ^ 12 :=
    combinedProfileBound_eq κ
  rw [hcomb]
  -- Step 1: finrank of SPDP ≤ finrank of ⨆ spaces (by containment)
  have h1 : Module.finrank ℚ ↥(mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn htb hns).partition κ κ
      (compiledPoly (cook_levin_compilation M n hn htb hns))) ≤
    Module.finrank ℚ ↥(⨆ i : Fin numP, spaces i) :=
    Submodule.finrank_mono hcover
  -- Step 2: finrank of ⨆ spaces ≤ Σ finrank(spaces i)
  have h2 : Module.finrank ℚ ↥(⨆ i : Fin numP, spaces i) ≤
    ∑ i : Fin numP, Module.finrank ℚ (spaces i) := by
    haveI : ∀ i, Module.Finite ℚ (spaces i) := hfin
    exact finrank_iSup_fin_le numP spaces
  -- Step 3: Σ finrank(spaces i) ≤ numP × (κ+1)^8
  have h3 : ∑ i : Fin numP, Module.finrank ℚ (spaces i) ≤ numP * (κ + 1) ^ 8 := by
    calc ∑ i : Fin numP, Module.finrank ℚ (spaces i)
        ≤ ∑ _i : Fin numP, (κ + 1) ^ 8 :=
          Finset.sum_le_sum (fun i _ => hbound i)
      _ = numP * (κ + 1) ^ 8 := by simp [Finset.sum_const, Finset.card_fin]
  -- Step 4: numP × (κ+1)^8 ≤ (κ+1)^4 × (κ+1)^8 = (κ+1)^12
  have h4 : numP * (κ + 1) ^ 8 ≤ (κ + 1) ^ 12 := by
    calc numP * (κ + 1) ^ 8
        ≤ (κ + 1) ^ 4 * (κ + 1) ^ 8 :=
          Nat.mul_le_mul_right _ hnumP
      _ = (κ + 1) ^ 12 := by ring
  -- Combine
  linarith

/-! ## Part 5: Kronecker coefficient computations for the identity minor

For the identity construction lower bound, we need to compute the coefficient
of "tag monomials" in SPDP generators built from boolFactor products.

Key single-variable building blocks:
- coeff (single v 1) in (-1 + 2*X v) = 2  [differentiated factor]
- coeff 0 in boolFactor v = 1              [undifferentiated factor, constant term]
- coeff (single v 1) in boolFactor v = -1  [undifferentiated factor, linear term]
- coeff 0 in (-1 + 2*X v) = -1             [differentiated factor, constant term]

These combine via coeff_finset_prod_disjoint to give the multi-variable
Kronecker matrix entries. -/

/-- Coefficient of (single v 1) in pderiv v (boolFactor N v) is 2. -/
theorem coeff_single_pderiv_boolFactor {N : ℕ} (v : Fin N) :
    MvPolynomial.coeff (Finsupp.single v 1)
      (MvPolynomial.pderiv v (boolFactor N v) : MvPolynomial (Fin N) ℚ) = 2 := by
  rw [pderiv_boolFactor_self N v]
  -- -1 + 2 * X v = C(-1) + C(2) * X v
  have h1 : (-1 + 2 * MvPolynomial.X v : MvPolynomial (Fin N) ℚ) =
      MvPolynomial.C (-1) + MvPolynomial.C 2 * MvPolynomial.X v := by
    simp [map_ofNat]
  rw [h1]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C,
    MvPolynomial.coeff_X', ite_true]
  -- single v 1 ≠ 0, so C(-1) contributes 0
  have hne : (0 : Fin N →₀ ℕ) ≠ Finsupp.single v 1 := by
    intro h; have := DFunLike.congr_fun h v; simp at this
  simp [hne]

/-- Coefficient of 0 in boolFactor v is 1 (constant term). -/
theorem coeff_zero_boolFactor {N : ℕ} (v : Fin N) :
    MvPolynomial.coeff 0 (boolFactor N v : MvPolynomial (Fin N) ℚ) = 1 := by
  unfold boolFactor
  simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_X']
  -- 1 - X v * (1 - X v) at monomial 0 = 1 - 0 = 1
  -- coeff 0 (X v * (1 - X v)): use coeff_mul, pairs (a,b) with a+b=0, so a=b=0
  -- coeff 0 (X v) = 0, so the product is 0
  simp [Finsupp.antidiagonal_zero]

/-- Coefficient of (single v 1) in boolFactor v is -1. -/
theorem coeff_single_boolFactor {N : ℕ} (v : Fin N) :
    MvPolynomial.coeff (Finsupp.single v 1)
      (boolFactor N v : MvPolynomial (Fin N) ℚ) = -1 := by
  -- single v 1 is multilinear, so coeff at boolFactor = coeff at mlProj(boolFactor)
  rw [← coeff_mlProj_of_isMultilinear_mono _ _
    (fun i => by simp [Finsupp.single_apply]; split_ifs <;> omega)]
  rw [mlProj_boolFactor v]
  simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, MvPolynomial.coeff_X', ite_true]
  have hne : (0 : Fin N →₀ ℕ) ≠ Finsupp.single v 1 := by
    intro h; have := DFunLike.congr_fun h v; simp at this
  simp [hne]

/-- Coefficient of 0 in pderiv v (boolFactor v) is -1. -/
theorem coeff_zero_pderiv_boolFactor {N : ℕ} (v : Fin N) :
    MvPolynomial.coeff 0
      (MvPolynomial.pderiv v (boolFactor N v) : MvPolynomial (Fin N) ℚ) = -1 := by
  rw [pderiv_boolFactor_self N v]
  have h1 : (-1 + 2 * MvPolynomial.X v : MvPolynomial (Fin N) ℚ) =
      MvPolynomial.C (-1) + MvPolynomial.C 2 * MvPolynomial.X v := by
    simp [map_ofNat]
  rw [h1]
  simp [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X']

/-! ## Part 6: usesOnly lemmas for boolFactor and its derivatives

These connect the boolFactor variable support to CoeffDisjoint.usesOnly,
which is needed to apply coeff_finset_prod_disjoint. -/

/-- boolFactor N v uses only variables in {v}. -/
theorem usesOnly_boolFactor {N : ℕ} (v : Fin N) :
    CoeffDisjoint.usesOnly (boolFactor N v : MvPolynomial (Fin N) ℚ) ({v} : Set (Fin N)) := by
  intro m hm x hx
  have hvar : x ∈ (boolFactor N v).vars := (MvPolynomial.mem_vars x).mpr ⟨m, hm, hx⟩
  have hsub := boolFactor_vars_subset N v hvar
  exact Finset.mem_singleton.mp hsub

/-- pderiv v (boolFactor N v) uses only variables in {v}. -/
theorem usesOnly_pderiv_boolFactor {N : ℕ} (v : Fin N) :
    CoeffDisjoint.usesOnly (MvPolynomial.pderiv v (boolFactor N v) : MvPolynomial (Fin N) ℚ)
      ({v} : Set (Fin N)) := by
  rw [pderiv_boolFactor_self N v]
  intro m hm x hx
  -- m ∈ support(-1 + 2 * X v) and x ∈ m.support
  -- We show: vars(-1 + 2*X v) ⊆ {v}
  -- Then x ∈ vars → x = v → x ∈ {v}
  have hvar : x ∈ (-1 + 2 * MvPolynomial.X v : MvPolynomial (Fin N) ℚ).vars :=
    (MvPolynomial.mem_vars x).mpr ⟨m, hm, hx⟩
  -- vars of (-1 + 2*X v) ⊆ vars of the sub-polynomial pderiv v (boolFactor N v)
  -- But we already know boolFactor N v has vars ⊆ {v}, and pderiv preserves this
  -- Actually just use: the polynomial -1 + 2*X v has vars ⊆ {v}
  -- because its support = {0, single v 1} and vars = ⋃_{m ∈ support} m.support = {v}
  suffices h : (-1 + 2 * MvPolynomial.X v : MvPolynomial (Fin N) ℚ).vars ⊆ {v} from
    Finset.mem_singleton.mp (h hvar)
  -- Use vars_sub/vars_add estimates
  intro y hy
  -- pderiv v (boolFactor v) has vars ⊆ (boolFactor v).vars ⊆ {v}
  -- But we expanded already. Let's use MvPolynomial.vars_add_subset
  have hsub := MvPolynomial.vars_add_subset (-1 : MvPolynomial (Fin N) ℚ) (2 * MvPolynomial.X v) hy
  rw [Finset.mem_union] at hsub
  rcases hsub with h1 | h2
  · -- vars(-1) = vars(C(-1)) = ∅
    exfalso
    have : (-1 : MvPolynomial (Fin N) ℚ).vars = ∅ := by
      have : (-1 : MvPolynomial (Fin N) ℚ) = MvPolynomial.C (-1) := by simp
      rw [this]; exact MvPolynomial.vars_C
    rw [this] at h1; simp at h1
  · -- vars(2 * X v) ⊆ vars(X v) ⊆ {v}
    have hmul := MvPolynomial.vars_mul (2 : MvPolynomial (Fin N) ℚ) (MvPolynomial.X v) h2
    rw [Finset.mem_union] at hmul
    rcases hmul with h2a | h2b
    · exfalso
      have : (2 : MvPolynomial (Fin N) ℚ).vars = ∅ := by
        have : (2 : MvPolynomial (Fin N) ℚ) = MvPolynomial.C 2 := by simp [map_ofNat]
        rw [this]; exact MvPolynomial.vars_C
      rw [this] at h2a; simp at h2a
    · simpa [MvPolynomial.vars_X] using h2b

/-! ## Part 7: Multi-variable coefficient via disjoint factorization

The diagonal Kronecker coefficient: for a set S of variables,
the coefficient of the tag monomial τ_S = ∑_{v∈S} single v 1 in
the S-derivative of ∏ boolFactor equals 2^|S|. -/

/-- The Finsupp.single monomial is supported in the corresponding singleton set. -/
theorem monomSupportedIn_single {N : ℕ} (v : Fin N) :
    CoeffDisjoint.monomSupportedIn (Finsupp.single v 1) ({v} : Set (Fin N)) := by
  intro x hx
  rw [Finsupp.mem_support_iff] at hx
  simp only [Finsupp.single_apply] at hx
  split_ifs at hx with h
  · exact Set.mem_singleton_iff.mpr h.symm
  · exact absurd rfl hx

/-- The zero monomial is supported in any set. -/
theorem monomSupportedIn_zero {N : ℕ} (S : Set (Fin N)) :
    CoeffDisjoint.monomSupportedIn (0 : Fin N →₀ ℕ) S := by
  intro x hx
  rw [Finsupp.mem_support_iff] at hx
  simp at hx

/-- Singleton sets for distinct elements are disjoint. -/
theorem singleton_pairwiseDisjoint {N : ℕ} (s : Finset (Fin N)) :
    (s : Set (Fin N)).PairwiseDisjoint (fun v => ({v} : Set (Fin N))) := by
  intro i _ j _ hij
  simp only [Function.onFun, Set.disjoint_iff]
  intro x ⟨hi, hj⟩
  rw [Set.mem_singleton_iff] at hi hj
  exact hij (hi.symm.trans hj)

/-- Coefficient of 0 in a Finset product of boolFactors is 1. -/
theorem coeff_zero_boolFactor_prod {N : ℕ} (s : Finset (Fin N)) :
    MvPolynomial.coeff 0 (s.prod (boolFactor N) : MvPolynomial (Fin N) ℚ) = 1 := by
  have key := CoeffDisjoint.coeff_finset_prod_disjoint
    (s := s)
    (f := fun i => boolFactor N i)
    (S := fun i => ({i} : Set (Fin N)))
    (m := fun _ => (0 : Fin N →₀ ℕ))
    (hf := fun i _ => usesOnly_boolFactor i)
    (hdisj := singleton_pairwiseDisjoint s)
    (hm := fun _ _ => monomSupportedIn_zero _)
  simp only [Finset.sum_const_zero] at key
  rw [key]
  apply Finset.prod_eq_one
  intro i _
  exact coeff_zero_boolFactor i

/-- Coefficient of (∑_{v∈S} single v 1) in (∏_{v∈S} pderiv v (boolFactor N v)) equals 2^|S|. -/
theorem coeff_tag_pderiv_boolFactor_prod {N : ℕ} (S : Finset (Fin N)) :
    MvPolynomial.coeff (∑ v ∈ S, Finsupp.single v 1)
      (S.prod (fun v => MvPolynomial.pderiv v (boolFactor N v)) : MvPolynomial (Fin N) ℚ) =
    (2 : ℚ) ^ S.card := by
  have key := CoeffDisjoint.coeff_finset_prod_disjoint
    (s := S)
    (f := fun v => MvPolynomial.pderiv v (boolFactor N v))
    (S := fun v => ({v} : Set (Fin N)))
    (m := fun v => Finsupp.single v 1)
    (hf := fun v _ => usesOnly_pderiv_boolFactor v)
    (hdisj := singleton_pairwiseDisjoint S)
    (hm := fun v _ => monomSupportedIn_single v)
  rw [key]
  -- Now ∏ v in S, coeff (single v 1) (pderiv v (boolFactor N v)) = ∏ v in S, 2 = 2^|S|
  conv_lhs =>
    arg 2; ext v
    rw [coeff_single_pderiv_boolFactor v]
  simp [Finset.prod_const]

/-- The differentiated factor product uses only variables in S. -/
theorem usesOnly_pderiv_boolFactor_prod {N : ℕ} (S : Finset (Fin N)) :
    CoeffDisjoint.usesOnly
      (S.prod (fun v => MvPolynomial.pderiv v (boolFactor N v)) : MvPolynomial (Fin N) ℚ)
      (↑S : Set (Fin N)) := by
  apply CoeffDisjoint.usesOnly_finset_prod
  intro v hv
  exact CoeffDisjoint.usesOnly_mono (usesOnly_pderiv_boolFactor v)
    (fun x hx => by rwa [Set.mem_singleton_iff.mp hx])

/-- The undifferentiated factor product uses only variables in its index set. -/
theorem usesOnly_boolFactor_prod {N : ℕ} (T : Finset (Fin N)) :
    CoeffDisjoint.usesOnly
      (T.prod (boolFactor N) : MvPolynomial (Fin N) ℚ)
      (↑T : Set (Fin N)) := by
  apply CoeffDisjoint.usesOnly_finset_prod
  intro v hv
  exact CoeffDisjoint.usesOnly_mono (usesOnly_boolFactor v)
    (fun x hx => by rwa [Set.mem_singleton_iff.mp hx])

/-- The tag monomial ∑_{v∈S} single v 1 is supported in S. -/
theorem monomSupportedIn_tag {N : ℕ} (S : Finset (Fin N)) :
    CoeffDisjoint.monomSupportedIn (∑ v ∈ S, Finsupp.single v 1) (↑S : Set (Fin N)) := by
  intro x hx
  rw [Finsupp.mem_support_iff] at hx
  -- x must be in S; otherwise the sum at x is 0
  by_contra hxS
  apply hx
  rw [CoeffDisjoint.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro v hv
  simp only [Finsupp.single_apply]
  split_ifs with h
  · subst h; exact absurd (Finset.mem_coe.mpr hv) hxS
  · rfl

/-- The full diagonal Kronecker coefficient: for the S-derivative of ∏ boolFactor,
    the coefficient of the tag monomial τ_S equals 2^|S|.

    coeff τ_S (iterDerivList S.toList (∏_{j∈univ} boolFactor j))
    = coeff τ_S ((∏_{v∈S} pderiv_v(boolFactor v)) * (∏_{j∈univ\S} boolFactor j))
    = 2^|S| * 1 = 2^|S|  -/
theorem coeff_tag_iterDeriv_boolFactor_prod_diag {N : ℕ} (S : Finset (Fin N)) :
    MvPolynomial.coeff (∑ v ∈ S, Finsupp.single v 1)
      ((S.prod (fun v => MvPolynomial.pderiv v (boolFactor N v))) *
       (Finset.univ \ S).prod (boolFactor N) : MvPolynomial (Fin N) ℚ) =
    (2 : ℚ) ^ S.card := by
  -- Use coeff_mul_disjoint with A = S, B = univ \ S
  have hdisj : Disjoint (↑S : Set (Fin N)) (↑(Finset.univ \ S) : Set (Fin N)) := by
    rw [Set.disjoint_iff]
    intro x ⟨hxS, hxT⟩
    rw [Finset.mem_coe, Finset.mem_sdiff] at hxT
    exact hxT.2 (Finset.mem_coe.mp hxS)
  -- τ_S + 0 = τ_S
  have htag : (∑ v ∈ S, Finsupp.single v 1) + (0 : Fin N →₀ ℕ) =
      ∑ v ∈ S, Finsupp.single v 1 := add_zero _
  rw [← htag]
  rw [CoeffDisjoint.coeff_mul_disjoint
    (usesOnly_pderiv_boolFactor_prod S)
    (usesOnly_boolFactor_prod (Finset.univ \ S))
    hdisj
    (monomSupportedIn_tag S)
    (monomSupportedIn_zero _)]
  rw [coeff_tag_pderiv_boolFactor_prod S, coeff_zero_boolFactor_prod _, mul_one]

-- General Kronecker coefficient for the boolFactor product.
set_option maxHeartbeats 1600000 in
theorem coeff_tag_iterDeriv_boolFactor_prod_general {N : ℕ}
    (S S' : Finset (Fin N)) :
    MvPolynomial.coeff (∑ v ∈ S, Finsupp.single v 1)
      ((S'.prod (fun v => MvPolynomial.pderiv v (boolFactor N v))) *
       (Finset.univ \ S').prod (boolFactor N) : MvPolynomial (Fin N) ℚ) =
    (2 : ℚ) ^ (S ∩ S').card * (-1) ^ (S \ S').card *
    (-1) ^ (S' \ S).card := by
  -- Step 1: Rewrite product as Finset.prod over univ
  have hprod_eq : (S'.prod (fun v => MvPolynomial.pderiv v (boolFactor N v))) *
      (Finset.univ \ S').prod (boolFactor N) =
      Finset.univ.prod (fun v => if v ∈ S' then MvPolynomial.pderiv v (boolFactor N v)
                                  else boolFactor N v) := by
    have h1 : S'.prod (fun v => MvPolynomial.pderiv v (boolFactor N v)) =
        S'.prod (fun v => if v ∈ S' then MvPolynomial.pderiv v (boolFactor N v)
                           else boolFactor N v) :=
      Finset.prod_congr rfl (fun v hv => by simp [hv])
    have h2 : (Finset.univ \ S').prod (boolFactor N) =
        (Finset.univ \ S').prod (fun v => if v ∈ S' then MvPolynomial.pderiv v (boolFactor N v)
                                           else boolFactor N v) :=
      Finset.prod_congr rfl (fun v hv => by simp [Finset.mem_sdiff.mp hv |>.2])
    rw [h1, h2, ← Finset.prod_union]
    · congr 1; exact Finset.union_sdiff_of_subset (Finset.subset_univ S')
    · exact Finset.disjoint_sdiff
  rw [hprod_eq]
  -- Step 2: Rewrite monomial sum as sum over univ
  have hmon_eq : (∑ v ∈ S, Finsupp.single v 1 : Fin N →₀ ℕ) =
      ∑ v ∈ Finset.univ, (if v ∈ S then Finsupp.single v 1 else 0) := by
    rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]; simp
  rw [hmon_eq]
  -- Step 3: Apply coeff_finset_prod_disjoint
  rw [CoeffDisjoint.coeff_finset_prod_disjoint
    (hf := fun v _ => by split_ifs <;> [exact usesOnly_pderiv_boolFactor v;
                                         exact usesOnly_boolFactor v])
    (hdisj := singleton_pairwiseDisjoint Finset.univ)
    (hm := fun v _ => by split_ifs <;> [exact monomSupportedIn_single v;
                                          exact monomSupportedIn_zero _])]
  -- Step 4: Evaluate each factor
  have hfactor : ∀ v : Fin N,
      MvPolynomial.coeff (if v ∈ S then Finsupp.single v 1 else 0)
        (if v ∈ S' then MvPolynomial.pderiv v (boolFactor N v) else boolFactor N v) =
      if v ∈ S ∩ S' then (2 : ℚ)
      else if v ∈ S \ S' then (-1 : ℚ)
      else if v ∈ S' \ S then (-1 : ℚ)
      else (1 : ℚ) := by
    intro v
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    by_cases hvS : v ∈ S <;> by_cases hvS' : v ∈ S' <;> simp [hvS, hvS']
    · exact coeff_single_pderiv_boolFactor v
    · exact coeff_single_boolFactor v
    · exact coeff_zero_pderiv_boolFactor v
    · exact coeff_zero_boolFactor v
  rw [Finset.prod_congr rfl (fun v _ => hfactor v)]
  -- Step 5: Split the product over univ into 4 disjoint parts
  -- univ = (S∩S') ∪ (S\S') ∪ (S'\S) ∪ (univ\(S∪S'))
  -- Use: for each v, exactly one branch is taken
  -- Strategy: repeatedly use Finset.prod_ite to peel off parts
  -- First peel off S∩S'
  have huniv_split : Finset.univ = (S ∩ S') ∪ ((S \ S') ∪ ((S' \ S) ∪ (Finset.univ \ (S ∪ S')))) := by
    ext v; simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have hdisj1 : Disjoint (S ∩ S') ((S \ S') ∪ ((S' \ S) ∪ (Finset.univ \ (S ∪ S')))) := by
    simp [Finset.disjoint_left]; intro v hv1 hv2; simp [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at *; tauto
  rw [huniv_split, Finset.prod_union hdisj1]
  -- In S∩S': each factor is 2
  have hprod1 : ∏ v ∈ S ∩ S', (if v ∈ S ∩ S' then (2 : ℚ)
      else if v ∈ S \ S' then -1 else if v ∈ S' \ S then -1 else 1) =
      (2 : ℚ) ^ (S ∩ S').card := by
    apply Finset.prod_eq_pow_card
    intro v hv; simp [hv]
  rw [hprod1]
  -- Peel off S\S'
  have hdisj2 : Disjoint (S \ S') ((S' \ S) ∪ (Finset.univ \ (S ∪ S'))) := by
    simp [Finset.disjoint_left]; intro v hv1 hv2; simp [Finset.mem_union, Finset.mem_sdiff] at *; tauto
  rw [Finset.prod_union hdisj2]
  -- In S\S': v ∉ S∩S', v ∈ S\S', so factor = -1
  have hprod2 : ∏ v ∈ S \ S', (if v ∈ S ∩ S' then (2 : ℚ)
      else if v ∈ S \ S' then -1 else if v ∈ S' \ S then -1 else 1) =
      (-1 : ℚ) ^ (S \ S').card := by
    apply Finset.prod_eq_pow_card
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hv
    simp [show ¬(v ∈ S ∧ v ∈ S') from fun ⟨_, h⟩ => hv.2 h, hv]
  rw [hprod2]
  -- Peel off S'\S
  have hdisj3 : Disjoint (S' \ S) (Finset.univ \ (S ∪ S')) := by
    simp [Finset.disjoint_left]; intro v hv1 hv2; simp [Finset.mem_sdiff, Finset.mem_union] at *; tauto
  rw [Finset.prod_union hdisj3]
  -- In S'\S: v ∉ S∩S', v ∉ S\S', v ∈ S'\S, so factor = -1
  have hprod3 : ∏ v ∈ S' \ S, (if v ∈ S ∩ S' then (2 : ℚ)
      else if v ∈ S \ S' then -1 else if v ∈ S' \ S then -1 else 1) =
      (-1 : ℚ) ^ (S' \ S).card := by
    apply Finset.prod_eq_pow_card
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hv
    simp [show ¬(v ∈ S ∧ v ∈ S') from fun ⟨h, _⟩ => hv.2 h,
          show ¬(v ∈ S ∧ v ∉ S') from fun ⟨h, _⟩ => hv.2 h, hv]
  rw [hprod3]
  -- In rest: all factors are 1
  have hprod4 : ∏ v ∈ Finset.univ \ (S ∪ S'), (if v ∈ S ∩ S' then (2 : ℚ)
      else if v ∈ S \ S' then -1 else if v ∈ S' \ S then -1 else 1) = 1 := by
    apply Finset.prod_eq_one
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and] at hv
    push_neg at hv
    simp [Finset.mem_inter, Finset.mem_sdiff, hv.1, hv.2,
      show ¬(v ∈ S ∧ v ∈ S') from fun ⟨h, _⟩ => hv.1 h,
      show ¬(v ∈ S ∧ v ∉ S') from fun ⟨h, _⟩ => hv.1 h,
      show ¬(v ∈ S' ∧ v ∉ S) from fun ⟨h, _⟩ => hv.2 h]
  rw [hprod4, mul_one]
  ring

-- For same-size subsets: the coefficient simplifies to 2^|S cap S'|.
set_option maxHeartbeats 800000 in
theorem coeff_tag_iterDeriv_boolFactor_prod_samesize {N : ℕ}
    (S S' : Finset (Fin N)) (hcard : S.card = S'.card) :
    MvPolynomial.coeff (∑ v ∈ S, Finsupp.single v 1)
      ((S'.prod (fun v => MvPolynomial.pderiv v (boolFactor N v))) *
       (Finset.univ \ S').prod (boolFactor N) : MvPolynomial (Fin N) ℚ) =
    (2 : ℚ) ^ (S ∩ S').card := by
  rw [coeff_tag_iterDeriv_boolFactor_prod_general]
  -- Need: (-1)^|S\S'| * (-1)^|S'\S| = 1
  -- Since |S\S'| = |S| - |S∩S'| and |S'\S| = |S'| - |S∩S'|
  -- so |S\S'| + |S'\S| = |S| + |S'| - 2|S∩S'| = 2(|S| - |S∩S'|) when |S| = |S'|
  -- |S\S'| = |S| - |S'∩S| and |S'\S| = |S'| - |S∩S'|
  -- With Finset.card_sdiff: #(t\s) = #t - #(s∩t)
  have h_sdiff1 : (S \ S').card = S.card - (S' ∩ S).card := Finset.card_sdiff
  have h_sdiff2 : (S' \ S).card = S'.card - (S ∩ S').card := Finset.card_sdiff
  have h_inter_comm : (S' ∩ S).card = (S ∩ S').card := by rw [Finset.inter_comm]
  rw [h_sdiff1, h_inter_comm, h_sdiff2, hcard]
  -- Now: 2^k * (-1)^(|S'| - |S∩S'|) * (-1)^(|S'| - |S∩S'|) = 2^k
  -- 2^k * (-1)^n * (-1)^n = 2^k * ((-1)^n * (-1)^n) = 2^k * (-1)^(2n) = 2^k
  rw [mul_assoc, ← pow_add, ← two_mul]
  have heven : ((-1 : ℚ) ^ (2 * (S'.card - (S ∩ S').card))) = 1 :=
    Even.neg_one_pow (even_two_mul _)
  rw [heven, mul_one]

end SymmetricPower
