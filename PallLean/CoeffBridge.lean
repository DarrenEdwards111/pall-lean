import PallLean.SPDPDefs
import Mathlib.Tactic
/-!
# Coefficient Bridge: Polynomial Subspaces ↔ Matrix Rank

This file establishes the equivalence between:
- `Module.finrank` of a span of polynomials (our SPDP definition)
- `Matrix.rank` of the coefficient matrix (the paper's working definition)

## Strategy

1. Fix a finite monomial index set `ι` (e.g., monomials of degree ≤ d in n vars)
2. Define coefficient extraction as a linear map `coeffVec : MvPolynomial σ F →ₗ[F] (ι → F)`
3. Show it is injective on bounded-degree polynomials
4. Conclude: `finrank (span S) = rank (coeffMatrix S)`
-/

namespace CoeffBridge

open MvPolynomial Finsupp

variable {σ : Type*} [DecidableEq σ] {F : Type*} [Field F]

/-! ## Step 1: Monomial Index Type

For polynomials in `MvPolynomial (Fin n) F` with total degree ≤ d,
the monomials are `Fin n →₀ ℕ` with `(Finsupp.sum · fun _ e => e) ≤ d`.

We use the full `σ →₀ ℕ` as our index type and work with `Finsupp.supported`
to restrict to relevant monomials. For finite σ, the set of monomials
of degree ≤ d is finite (already in mathlib). -/

-- We work with `p.support` directly as our monomial index set,
-- which is already a `Finset (σ →₀ ℕ)` in mathlib.

/-! ## Step 2: Coefficient Extraction as Linear Map

`MvPolynomial.coeff m p` extracts the coefficient of monomial `m` in `p`.
For a fixed `m`, this is already a linear map. We package the collection
over all `m` in a finite set as a vector. -/

/-- Coefficient vector: extract coefficients at a fixed list of monomials -/
noncomputable def coeffVecAt (monomials : Finset (σ →₀ ℕ)) :
    MvPolynomial σ F →ₗ[F] (monomials → F) where
  toFun p m := MvPolynomial.coeff m.val p
  map_add' p q := by ext m; simp [MvPolynomial.coeff_add]
  map_smul' r p := by ext m; simp [MvPolynomial.coeff_smul]

/-- If p.support ⊆ monomials, then coeffVecAt is injective on such polynomials -/
theorem coeffVecAt_injective_on_support (monomials : Finset (σ →₀ ℕ)) :
    ∀ p q : MvPolynomial σ F,
      p.support ⊆ monomials → q.support ⊆ monomials →
      coeffVecAt monomials p = coeffVecAt monomials q → p = q := by
  intro p q hp hq h
  ext m
  by_cases hm : m ∈ monomials
  · have := congr_fun h ⟨m, hm⟩
    exact this
  · have hp' : MvPolynomial.coeff m p = 0 := by
      by_contra hne
      exact hm (hp (Finsupp.mem_support_iff.mpr hne))
    have hq' : MvPolynomial.coeff m q = 0 := by
      by_contra hne
      exact hm (hq (Finsupp.mem_support_iff.mpr hne))
    rw [hp', hq']

/-! ## Step 3: Span Dimension = Image Dimension

Key fact: for a linear map `f` that is injective on a subspace `V`,
`finrank V = finrank (f '' V)`.

More precisely, if `f : M →ₗ[R] N` and `f` restricted to `span S` is
injective, then `finrank (span S) = finrank (span (f '' S))`.

In our case, `f = coeffVecAt` and `S` = generators of SPDP subspace. -/

/-- Image of span under linear map = span of image -/
theorem span_image_eq {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (S : Set M) :
    Submodule.map f (Submodule.span R S) = Submodule.span R (f '' S) :=
  Submodule.map_span f S

/-! ## Step 4: finrank of span = Matrix.rank of coefficient matrix

For a finite set of generators `{g₁, ..., gₘ}`, define the coefficient matrix
whose i-th row is `coeffVecAt monomials gᵢ`. Then:

  finrank(span{g₁,...,gₘ}) = Matrix.rank(coeffMatrix)

This follows from:
1. coeffVecAt is injective on the span (all generators have support ⊆ monomials)
2. finrank is preserved under linear equivalence
3. finrank of span of vectors in F^ι = rank of the matrix of those vectors -/

/-- The coefficient matrix: rows indexed by generators, columns by monomials -/
noncomputable def coeffMatrix {ι : Type*} [Fintype ι]
    (monomials : Finset (σ →₀ ℕ)) (generators : ι → MvPolynomial σ F) :
    Matrix ι monomials F :=
  fun i m => MvPolynomial.coeff m.val (generators i)

/-- The set of polynomials with support ⊆ S forms a submodule -/
def supportedSubmodule (monomials : Finset (σ →₀ ℕ)) :
    Submodule F (MvPolynomial σ F) where
  carrier := { p | p.support ⊆ monomials }
  add_mem' {a b} ha hb := by
    exact Finset.Subset.trans Finsupp.support_add (Finset.union_subset ha hb)
  zero_mem' := by simp [Finsupp.support_zero]
  smul_mem' c p hp := by
    exact Finset.Subset.trans Finsupp.support_smul hp

/-- span of generators with support ⊆ monomials is itself in supportedSubmodule -/
theorem span_le_supported (monomials : Finset (σ →₀ ℕ))
    (generators : Set (MvPolynomial σ F))
    (hsupport : ∀ g ∈ generators, (g).support ⊆ monomials) :
    Submodule.span F generators ≤ supportedSubmodule monomials := by
  apply Submodule.span_le.mpr
  intro g hg
  exact hsupport g hg

/-- coeffVecAt restricted to supportedSubmodule is injective -/
theorem coeffVecAt_injective_on_submodule (monomials : Finset (σ →₀ ℕ)) :
    Function.Injective
      ((coeffVecAt (F := F) monomials).domRestrict (supportedSubmodule (F := F) monomials)) := by
  intro ⟨p, hp⟩ ⟨q, hq⟩ h
  simp only [LinearMap.domRestrict_apply, Subtype.mk.injEq] at h ⊢
  exact coeffVecAt_injective_on_support monomials p q hp hq h

/-- Row of the coefficient matrix corresponds to coeffVecAt of generator -/
theorem coeffMatrix_row {ι : Type*} [Fintype ι]
    (monomials : Finset (σ →₀ ℕ))
    (generators : ι → MvPolynomial σ F) (i : ι) :
    (fun m : monomials => coeffMatrix monomials generators i m) =
    coeffVecAt monomials (generators i) := by
  ext m; rfl

theorem finrank_span_eq_matrix_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (monomials : Finset (σ →₀ ℕ))
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (generators i).support ⊆ monomials) :
    Module.finrank F (Submodule.span F (Set.range generators)) =
    (coeffMatrix monomials generators).rank := by
  -- The proof connects polynomial span ↔ coefficient vector span ↔ matrix rank.
  -- 1. coeffVecAt is injective on the span (all supports ⊆ monomials)
  -- 2. Image of span = span of image = span of rows of coeffMatrix
  -- 3. finrank preserved by injective linear map
  -- 4. finrank of row span = Matrix.rank
  -- Each step uses standard mathlib facts but the full connection requires
  -- careful type-matching between Submodule.map, Matrix.rank, and mulVecLin.
  sorry

/-! ## Application to SPDP Rank

Using the bridge lemma, we can now express blockedSpdpRank as a matrix rank,
enabling all the paper's coefficient-level proofs. -/

/-- The SPDP generators for a polynomial p at parameters (κ, ℓ) -/
noncomputable def spdpGenerators {n : ℕ} {F : Type*} [CommRing F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Set (MvPolynomial (Fin n) F) :=
  { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
      S.length = κ ∧ m.totalDegree ≤ ℓ ∧
      q = m * SPDP.iterDerivList S p }

/-- All SPDP generators have bounded total degree -/
theorem spdpGenerators_degree_bound {n : ℕ} {F : Type*} [CommRing F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    ∀ q ∈ spdpGenerators κ ℓ p,
      q.totalDegree ≤ ℓ + p.totalDegree := by
  intro q ⟨S, m, _, hdeg, hq⟩
  rw [hq]
  calc (m * SPDP.iterDerivList S p).totalDegree
      ≤ m.totalDegree + (SPDP.iterDerivList S p).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ ℓ + p.totalDegree := by
        apply Nat.add_le_add hdeg
        -- iterDerivList can only decrease degree
        sorry  -- standard but needs induction on derivative degree bound

/-- All SPDP generators have bounded support (contained in a finite set
    determined by the polynomial's support and the degree bound ℓ) -/
theorem spdpGenerators_support_bounded {n : ℕ} {F : Type*} [CommRing F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    ∃ (mono : Finset (Fin n →₀ ℕ)),
      ∀ q ∈ spdpGenerators κ ℓ p, q.support ⊆ mono := by
  sorry  -- the support of m * ∂_S p is contained in a computable finite set

end CoeffBridge
