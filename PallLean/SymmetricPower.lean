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

/-
  NOTE: The next honest frontier is to classify the possible multilinear projections of
  iterated derivatives of these local factors into a finite family of local outcome types,
  then assemble distributed Leibniz products into profile-indexed product spans.

  We deliberately avoid adding unverified local membership lemmas here until they are
  compile-checked. The proved infrastructure below starts from the Leibniz span reduction,
  and the remaining axiom `spdp_profile_generators` still packages the profile-compression
  cardinality bound.
-/

/-! ## Part 2: Symmetric Power Structure for Local Interface Spaces

Each Cook-Levin constraint type τ has a local interface space W_τ of dimension ≤ 3.
- Booleanity z(1-z): derivatives give {1-2z, 0} → W_bool ≅ span{1, z} → dim ≤ 3
- Adjacency z_i·z_{i+1}: derivatives give {z_{i+1}, z_i} → W_adj ≅ span{z_i, z_{i+1}} → dim ≤ 3
- Transition constraints: similar, dim ≤ 3

The m-th symmetric power Sym^m(W_τ) represents the space of "symmetric"
multilinear products of m elements from W_τ. Its dimension is C(m+2, 2). -/

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

end SymmetricPower
