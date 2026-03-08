import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Rank
/-!
# Coefficient Bridge: Polynomial Subspaces ↔ Matrix Rank

Bridge lemma: `finrank(span S) = Matrix.rank(coeffMatrix S)`

Strategy:
1. Fix finite monomial index `ι`
2. Coefficient extraction: `coeffVector p : ι → F`
3. Coefficient matrix: `coeffMatrix S : Matrix S ι F`
4. Bridge: `finrank(span S) = Matrix.rank(coeffMatrix S)`
-/

namespace CoeffBridge

open MvPolynomial

variable {σ : Type*} [DecidableEq σ] {F : Type*} [Field F]

/-! ## Step 1: Finite monomial index -/

-- We use `ι = monomials` (a `Finset (σ →₀ ℕ)`) as a subtype

/-! ## Step 2: Coefficient extraction as linear map -/

/-- Extract coefficient at monomial `m` — already linear in mathlib -/
noncomputable def coeffVector (monomials : Finset (σ →₀ ℕ))
    (p : MvPolynomial σ F) : monomials → F :=
  fun m => MvPolynomial.coeff m.val p

/-- coeffVector is F-linear -/
noncomputable def coeffVectorLin (monomials : Finset (σ →₀ ℕ)) :
    MvPolynomial σ F →ₗ[F] (monomials → F) where
  toFun := coeffVector monomials
  map_add' p q := by ext m; simp [coeffVector, MvPolynomial.coeff_add]
  map_smul' c p := by ext m; simp [coeffVector, MvPolynomial.coeff_smul]

/-- coeffVector is injective on polys with support ⊆ monomials -/
theorem coeffVector_injective (monomials : Finset (σ →₀ ℕ))
    (p q : MvPolynomial σ F)
    (hp : p.support ⊆ monomials) (hq : q.support ⊆ monomials)
    (h : coeffVector monomials p = coeffVector monomials q) : p = q := by
  ext m
  by_cases hm : m ∈ monomials
  · exact congr_fun h ⟨m, hm⟩
  · have : MvPolynomial.coeff m p = 0 := by
      by_contra hne; exact hm (hp (Finsupp.mem_support_iff.mpr hne))
    have : MvPolynomial.coeff m q = 0 := by
      by_contra hne; exact hm (hq (Finsupp.mem_support_iff.mpr hne))
    simp [*]

/-! ## Step 3: Coefficient matrix -/

/-- The coefficient matrix: rows = generators, columns = monomials -/
noncomputable def coeffMatrix {ι : Type*} [Fintype ι]
    (monomials : Finset (σ →₀ ℕ))
    (generators : ι → MvPolynomial σ F) :
    Matrix ι monomials F :=
  fun i m => MvPolynomial.coeff m.val (generators i)

/-! ## Step 4: Bridge Lemma -/

/-- Submodule of polynomials supported on `monomials` -/
def supportedSub (monomials : Finset (σ →₀ ℕ)) :
    Submodule F (MvPolynomial σ F) where
  carrier := { p | p.support ⊆ monomials }
  add_mem' ha hb := Finset.Subset.trans Finsupp.support_add (Finset.union_subset ha hb)
  zero_mem' := by simp [Finsupp.support_zero]
  smul_mem' c _ hp := Finset.Subset.trans Finsupp.support_smul hp

/-- span of supported generators lies in supportedSub -/
theorem span_in_supported (monomials : Finset (σ →₀ ℕ))
    (S : Set (MvPolynomial σ F))
    (h : ∀ g ∈ S, (g : MvPolynomial σ F).support ⊆ monomials) :
    Submodule.span F S ≤ supportedSub monomials :=
  Submodule.span_le.mpr h

/-- coeffVectorLin is injective on supportedSub -/
theorem coeffVectorLin_injOn (monomials : Finset (σ →₀ ℕ)) :
    Function.Injective
      ((coeffVectorLin (F := F) monomials).domRestrict (supportedSub monomials)) := by
  intro ⟨p, hp⟩ ⟨q, hq⟩ heq
  simp only [LinearMap.domRestrict_apply, Subtype.mk.injEq] at heq ⊢
  exact coeffVector_injective monomials p q hp hq heq

/-- The restricted linear map is a LinearEquiv onto its range -/
noncomputable def coeffEquiv (monomials : Finset (σ →₀ ℕ)) :
    (supportedSub (F := F) monomials) ≃ₗ[F]
    LinearMap.range ((coeffVectorLin (F := F) monomials).domRestrict (supportedSub monomials)) :=
  LinearEquiv.ofInjective _ (coeffVectorLin_injOn monomials)

/-- **Bridge Lemma**: finrank of span = Matrix.rank of coefficient matrix.

    Proof outline:
    1. coeffVectorLin restricted to span is injective (supports ⊆ monomials)
    2. Therefore span ≃ₗ image (LinearEquiv preserves finrank)
    3. Image = span of coefficient vectors = span of rows of coeffMatrix
    4. finrank(span of rows) = Matrix.rank (row rank = column rank)
-/
theorem finrank_span_eq_matrix_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (monomials : Finset (σ →₀ ℕ))
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (generators i).support ⊆ monomials) :
    Module.finrank F (Submodule.span F (Set.range generators)) =
    (coeffMatrix monomials generators).rank := by
  -- Let f = coeffVectorLin, V = span(range generators)
  let f := coeffVectorLin (σ := σ) (F := F) monomials
  -- V sits inside supportedSub
  have h_le := span_in_supported monomials _ (by
    intro g hg; rw [Set.mem_range] at hg; obtain ⟨i, rfl⟩ := hg; exact hsupport i)
  -- f is injective on V (since V ≤ supportedSub and f is injective there)
  have h_inj : Function.Injective (f.comp (Submodule.subtype
      (Submodule.span F (Set.range generators)))) := by
    intro ⟨p, hp⟩ ⟨q, hq⟩ heq
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Subtype.mk.injEq] at heq ⊢
    exact coeffVector_injective monomials p q (h_le hp) (h_le hq) heq
  -- Step 1: finrank(V) = finrank(f(V))
  -- Use: injective linear map gives LinearEquiv onto range, preserving finrank
  have step1 : Module.finrank F (Submodule.span F (Set.range generators)) =
      Module.finrank F (Submodule.map f (Submodule.span F (Set.range generators))) := by
    -- f restricted to V is injective → V ≃ₗ f(V)
    let fV := f.domRestrict (Submodule.span F (Set.range generators))
    have fV_inj : Function.Injective fV := by
      intro ⟨p, hp⟩ ⟨q, hq⟩ heq
      simp only [LinearMap.domRestrict_apply, Subtype.mk.injEq] at heq ⊢
      exact coeffVector_injective monomials p q (h_le hp) (h_le hq) heq
    -- LinearEquiv.ofInjective gives V ≃ₗ range(fV)
    let e := LinearEquiv.ofInjective fV fV_inj
    -- range(fV) = map f V
    have h_range : LinearMap.range fV = (Submodule.span F (Set.range generators)).map f := by
      ext x
      simp only [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨⟨a, ha⟩, rfl⟩; exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, rfl⟩
    rw [← h_range]
    exact (LinearEquiv.finrank_eq e)
  -- Step 2: f(V) = span(f '' generators) = span(rows of coeffMatrix)
  have step2 : Submodule.map f (Submodule.span F (Set.range generators)) =
      Submodule.span F (Set.range (fun i : ι => f (generators i))) := by
    rw [Submodule.map_span]; congr 1; ext v; simp [Set.mem_image, Set.mem_range]
  -- Step 3: rows of coeffMatrix = f(generators)
  have step3 : (fun i : ι => f (generators i)) =
      (fun i : ι => (fun m : monomials => (coeffMatrix monomials generators) i m)) := by
    ext i m; rfl
  -- Step 4: connect to Matrix.rank
  -- Matrix.rank A = finrank(span(range Aᵀ.col))
  -- Aᵀ.col i = row i of A = f(generators i)
  rw [step1, step2, step3]
  -- Goal: finrank(span(range (fun i => fun m => A i m))) = A.rank
  -- where A = coeffMatrix monomials generators
  let A := coeffMatrix monomials generators
  -- Matrix.rank_eq_finrank_span_cols: A.rank = finrank(span(range A.col))
  -- Matrix.rank_transpose: Aᵀ.rank = A.rank
  -- Aᵀ.col i = (fun m => A i m) = row i of A
  -- So: finrank(span(range (Aᵀ.col))) = Aᵀ.rank = A.rank
  rw [show (fun i : ι => (fun m : monomials => A i m)) =
      (fun i : ι => (Matrix.transpose A).col i) from by ext i m; simp [Matrix.transpose, Matrix.col]]
  rw [← Matrix.rank_eq_finrank_span_cols, Matrix.rank_transpose]

end CoeffBridge
