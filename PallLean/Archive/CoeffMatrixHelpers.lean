import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.RingTheory.TensorProduct.Finite

namespace CoeffMatrixHelpers

open MvPolynomial Matrix

variable {σ : Type*} [DecidableEq σ]
variable {F : Type*} [Field F]

/-- Coefficient vector of a polynomial restricted to a finite monomial set. -/
noncomputable def coeffVector (monomials : Finset (σ →₀ ℕ))
    (p : MvPolynomial σ F) : monomials → F :=
  fun m => MvPolynomial.coeff m.1 p

/-- The coefficient-vector map into the finitely supported monomial coordinates. -/
noncomputable def coeffVectorLin (monomials : Finset (σ →₀ ℕ)) :
    MvPolynomial σ F →ₗ[F] (monomials → F) where
  toFun := coeffVector monomials
  map_add' p q := by ext m; simp [coeffVector, MvPolynomial.coeff_add]
  map_smul' c p := by ext m; simp [coeffVector, MvPolynomial.coeff_smul]

/-- Coefficient matrix of a finite family of polynomials restricted to a finite monomial set. -/
noncomputable def coeffMatrix {ι : Type*}
    (monomials : Finset (σ →₀ ℕ)) (generators : ι → MvPolynomial σ F) :
    Matrix ι monomials F :=
  fun i m => MvPolynomial.coeff m.1 (generators i)

/-- Coefficient matrix indexed by an arbitrary family of chosen monomials from
an ambient finite monomial set. This packages column selections and repeated
columns without leaving the coefficient-matrix API. -/
noncomputable def coeffFamilyMatrix {ι μ : Type*}
    (monomials : Finset (σ →₀ ℕ))
    (chosenMonomials : μ → monomials)
    (generators : ι → MvPolynomial σ F) :
    Matrix ι μ F :=
  fun i j => MvPolynomial.coeff (chosenMonomials j).1 (generators i)

/-- Coefficient matrix indexed by arbitrary row and column families from an
ambient coefficient matrix. This packages simultaneous row selection and
column selection without leaving the coefficient-matrix API. -/
noncomputable def coeffBimatrix {ι κ μ : Type*}
    (monomials : Finset (σ →₀ ℕ))
    (rowMap : κ → ι)
    (chosenMonomials : μ → monomials)
    (generators : ι → MvPolynomial σ F) :
    Matrix κ μ F :=
  fun i j => MvPolynomial.coeff (chosenMonomials j).1 (generators (rowMap i))

/-- Column-action matrix induced by a linear map on monomial basis vectors. -/
noncomputable def monomialActionMatrix
    (src tgt : Finset (σ →₀ ℕ)) (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F) :
    Matrix src tgt F :=
  fun s t => MvPolynomial.coeff t.1 (φ (MvPolynomial.monomial s.1 (1 : F)))

theorem coeffVector_injective (monomials : Finset (σ →₀ ℕ))
    (p q : MvPolynomial σ F)
    (hp : p.support ⊆ monomials) (hq : q.support ⊆ monomials)
    (h : coeffVector monomials p = coeffVector monomials q) : p = q := by
  ext m
  by_cases hm : m ∈ monomials
  · exact congr_fun h ⟨m, hm⟩
  · have hp0 : MvPolynomial.coeff m p = 0 := by
      by_contra hne
      exact hm (hp (Finsupp.mem_support_iff.mpr hne))
    have hq0 : MvPolynomial.coeff m q = 0 := by
      by_contra hne
      exact hm (hq (Finsupp.mem_support_iff.mpr hne))
    simp [hp0, hq0]

omit [DecidableEq σ] in
theorem coeff_apply_eq_sum_monomialActionMatrix
    (src : Finset (σ →₀ ℕ))
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (p : MvPolynomial σ F)
    (hp : p.support ⊆ src)
    (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (φ p) =
      ∑ d : src, MvPolynomial.coeff d.1 p *
        MvPolynomial.coeff m (φ (MvPolynomial.monomial d.1 (1 : F))) := by
  calc
    MvPolynomial.coeff m (φ p)
        = MvPolynomial.coeff m
            (φ (p.support.sum fun d =>
              MvPolynomial.monomial d (MvPolynomial.coeff d p))) := by
              rw [← p.as_sum]
    _ = MvPolynomial.coeff m
          (p.support.sum fun d => φ (MvPolynomial.monomial d (MvPolynomial.coeff d p))) := by
            rw [map_sum]
    _ = MvPolynomial.coeff m
          (p.support.sum fun d => MvPolynomial.coeff d p •
            φ (MvPolynomial.monomial d (1 : F))) := by
            apply congrArg (MvPolynomial.coeff m)
            congr 1 with d
            rw [show MvPolynomial.monomial d (MvPolynomial.coeff d p) =
                MvPolynomial.coeff d p • MvPolynomial.monomial d (1 : F) by
                  rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
              map_smul]
    _ = p.support.sum (fun d => MvPolynomial.coeff d p *
          MvPolynomial.coeff m (φ (MvPolynomial.monomial d (1 : F)))) := by
            rw [MvPolynomial.coeff_sum]
            apply Finset.sum_congr rfl
            intro d hd
            rw [MvPolynomial.coeff_smul, smul_eq_mul]
    _ = src.sum (fun d => MvPolynomial.coeff d p *
          MvPolynomial.coeff m (φ (MvPolynomial.monomial d (1 : F)))) := by
            exact Finset.sum_subset hp (by
              intro d hdsrc hdnot
              rw [MvPolynomial.notMem_support_iff.mp hdnot, zero_mul])
    _ = ∑ d : src, MvPolynomial.coeff d.1 p *
          MvPolynomial.coeff m (φ (MvPolynomial.monomial d.1 (1 : F))) := by
            rw [← src.sum_attach (f := fun d =>
              MvPolynomial.coeff d p *
                MvPolynomial.coeff m (φ (MvPolynomial.monomial d (1 : F))))]
            rw [Finset.attach_eq_univ]

omit [DecidableEq σ] in
theorem coeffVector_apply_eq_sum_monomialActionMatrix
    (src tgt : Finset (σ →₀ ℕ))
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (p : MvPolynomial σ F)
    (hp : p.support ⊆ src) :
    coeffVector tgt (φ p) =
      fun t =>
        ∑ d : src, coeffVector src p d * monomialActionMatrix src tgt φ d t := by
  ext t
  simpa [coeffVector, monomialActionMatrix] using
    coeff_apply_eq_sum_monomialActionMatrix src φ p hp t.1

omit [DecidableEq σ] in
theorem coeffMatrix_map_eq_mul_monomialActionMatrix {ι : Type*} [Fintype ι]
    (src tgt : Finset (σ →₀ ℕ))
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (generators i).support ⊆ src) :
    coeffMatrix tgt (fun i => φ (generators i)) =
      coeffMatrix src generators * monomialActionMatrix src tgt φ := by
  ext i t
  simpa [coeffMatrix, monomialActionMatrix, Matrix.mul_apply] using
    coeff_apply_eq_sum_monomialActionMatrix src φ (generators i) (hsupport i) t.1

omit [DecidableEq σ] in
theorem rank_coeffMatrix_map_le {ι : Type*} [Fintype ι]
    (src tgt : Finset (σ →₀ ℕ))
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (generators i).support ⊆ src) :
    (coeffMatrix tgt (fun i => φ (generators i))).rank ≤
      (coeffMatrix src generators).rank := by
  rw [coeffMatrix_map_eq_mul_monomialActionMatrix src tgt φ generators hsupport]
  exact Matrix.rank_mul_le_left _ _

omit [DecidableEq σ] in
theorem coeffMatrix_submatrix_rows {ι κ : Type*}
    (monomials : Finset (σ →₀ ℕ))
    (generators : ι → MvPolynomial σ F)
    (rowMap : κ → ι) :
    coeffMatrix monomials (fun i : κ => generators (rowMap i)) =
      (coeffMatrix monomials generators).submatrix rowMap (Equiv.refl _) := by
  ext i m
  rfl

omit [DecidableEq σ] in
theorem coeffFamilyMatrix_eq_submatrix_cols {ι μ : Type*}
    (monomials : Finset (σ →₀ ℕ))
    (chosenMonomials : μ → monomials)
    (generators : ι → MvPolynomial σ F) :
    coeffFamilyMatrix monomials chosenMonomials generators =
      (coeffMatrix monomials generators).submatrix (Equiv.refl _) chosenMonomials := by
  ext i j
  rfl

omit [DecidableEq σ] in
theorem coeffBimatrix_eq_coeffFamilyMatrix {ι κ μ : Type*}
    (monomials : Finset (σ →₀ ℕ))
    (rowMap : κ → ι)
    (chosenMonomials : μ → monomials)
    (generators : ι → MvPolynomial σ F) :
    coeffBimatrix monomials rowMap chosenMonomials generators =
      coeffFamilyMatrix monomials chosenMonomials
        (fun i : κ => generators (rowMap i)) := by
  ext i j
  rfl

omit [DecidableEq σ] in
theorem coeffBimatrix_eq_submatrix {ι κ μ : Type*}
    (monomials : Finset (σ →₀ ℕ))
    (rowMap : κ → ι)
    (chosenMonomials : μ → monomials)
    (generators : ι → MvPolynomial σ F) :
    coeffBimatrix monomials rowMap chosenMonomials generators =
      (coeffMatrix monomials generators).submatrix rowMap chosenMonomials := by
  ext i j
  rfl

omit [DecidableEq σ] in
theorem coeffFamilyMatrix_map_eq_mul_submatrix_cols
    {ι μ : Type*} [Fintype ι]
    (src tgt : Finset (σ →₀ ℕ))
    (chosenMonomials : μ → tgt)
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (generators i).support ⊆ src) :
    coeffFamilyMatrix tgt chosenMonomials (fun i => φ (generators i)) =
      coeffMatrix src generators *
        (monomialActionMatrix src tgt φ).submatrix (Equiv.refl _) chosenMonomials := by
  ext i j
  simp [coeffFamilyMatrix, coeffMatrix, monomialActionMatrix, Matrix.mul_apply]
  exact coeff_apply_eq_sum_monomialActionMatrix src φ (generators i) (hsupport i)
    (chosenMonomials j).1

omit [DecidableEq σ] in
theorem coeffBimatrix_map_eq_mul_submatrix_cols
    {ι κ μ : Type*} [Fintype κ]
    (src tgt : Finset (σ →₀ ℕ))
    (rowMap : κ → ι)
    (chosenMonomials : μ → tgt)
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (generators i).support ⊆ src) :
    coeffBimatrix tgt rowMap chosenMonomials (fun i => φ (generators i)) =
      coeffMatrix src (fun i : κ => generators (rowMap i)) *
        (monomialActionMatrix src tgt φ).submatrix (Equiv.refl _) chosenMonomials := by
  rw [coeffBimatrix_eq_coeffFamilyMatrix]
  exact coeffFamilyMatrix_map_eq_mul_submatrix_cols src tgt chosenMonomials φ
    (fun i : κ => generators (rowMap i)) (fun i => hsupport (rowMap i))

omit [DecidableEq σ] in
theorem rank_coeffMatrix_subfamily_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (monomials : Finset (σ →₀ ℕ))
    (generators : ι → MvPolynomial σ F)
    (rowMap : κ → ι) :
    (coeffMatrix monomials (fun i : κ => generators (rowMap i))).rank ≤
      (coeffMatrix monomials generators).rank := by
  rw [coeffMatrix_submatrix_rows]
  simpa using
    Matrix.rank_submatrix_le (f := rowMap) (e := Equiv.refl monomials)
      (A := coeffMatrix monomials generators)

omit [DecidableEq σ] in
theorem rank_coeffMatrix_submatrix_cols_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (monomials : Finset (σ →₀ ℕ))
    (generators : ι → MvPolynomial σ F)
    (colMap : κ → monomials) :
    ((coeffMatrix monomials generators).submatrix (Equiv.refl _) colMap).rank ≤
      (coeffMatrix monomials generators).rank := by
  let A := coeffMatrix monomials generators
  have h :
      ((A.submatrix (Equiv.refl _) colMap)ᵀ).rank ≤ (Aᵀ).rank := by
    simpa [Matrix.transpose_submatrix] using
      Matrix.rank_submatrix_le (f := colMap) (e := Equiv.refl ι) (A := Aᵀ)
  calc
    (A.submatrix (Equiv.refl _) colMap).rank
      = ((A.submatrix (Equiv.refl _) colMap)ᵀ).rank := by
          symm
          exact Matrix.rank_transpose _
    _ ≤ (Aᵀ).rank := h
    _ = A.rank := Matrix.rank_transpose _

omit [DecidableEq σ] in
theorem rank_coeffFamilyMatrix_le {ι μ : Type*} [Fintype ι] [Fintype μ]
    (monomials : Finset (σ →₀ ℕ))
    (chosenMonomials : μ → monomials)
    (generators : ι → MvPolynomial σ F) :
    (coeffFamilyMatrix monomials chosenMonomials generators).rank ≤
      (coeffMatrix monomials generators).rank := by
  rw [coeffFamilyMatrix_eq_submatrix_cols]
  exact rank_coeffMatrix_submatrix_cols_le monomials generators chosenMonomials

omit [DecidableEq σ] in
theorem rank_coeffFamilyMatrix_map_le {ι μ : Type*} [Fintype ι] [Fintype μ]
    (src tgt : Finset (σ →₀ ℕ))
    (chosenMonomials : μ → tgt)
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (generators i).support ⊆ src) :
    (coeffFamilyMatrix tgt chosenMonomials (fun i => φ (generators i))).rank ≤
      (coeffMatrix src generators).rank := by
  rw [coeffFamilyMatrix_map_eq_mul_submatrix_cols src tgt chosenMonomials φ generators hsupport]
  exact Matrix.rank_mul_le_left _ _

omit [DecidableEq σ] in
theorem rank_coeffBimatrix_le {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (monomials : Finset (σ →₀ ℕ))
    (rowMap : κ → ι)
    (chosenMonomials : μ → monomials)
    (generators : ι → MvPolynomial σ F) :
    (coeffBimatrix monomials rowMap chosenMonomials generators).rank ≤
      (coeffMatrix monomials generators).rank := by
  have hcols :
      (coeffBimatrix monomials rowMap chosenMonomials generators).rank ≤
        (coeffMatrix monomials (fun i : κ => generators (rowMap i))).rank := by
    simpa [coeffBimatrix, coeffFamilyMatrix] using
      rank_coeffFamilyMatrix_le monomials chosenMonomials
        (fun i : κ => generators (rowMap i))
  have hrows :
      (coeffMatrix monomials (fun i : κ => generators (rowMap i))).rank ≤
        (coeffMatrix monomials generators).rank :=
    rank_coeffMatrix_subfamily_le monomials generators rowMap
  exact le_trans hcols hrows

omit [DecidableEq σ] in
theorem rank_coeffBimatrix_map_le {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (src tgt : Finset (σ →₀ ℕ))
    (rowMap : κ → ι)
    (chosenMonomials : μ → tgt)
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (generators i).support ⊆ src) :
    (coeffBimatrix tgt rowMap chosenMonomials (fun i => φ (generators i))).rank ≤
      (coeffMatrix src generators).rank := by
  have hmap :
      (coeffBimatrix tgt rowMap chosenMonomials (fun i => φ (generators i))).rank ≤
        (coeffMatrix src (fun i : κ => generators (rowMap i))).rank := by
    rw [coeffBimatrix_map_eq_mul_submatrix_cols src tgt rowMap chosenMonomials φ
      generators hsupport]
    exact Matrix.rank_mul_le_left _ _
  exact le_trans hmap (rank_coeffMatrix_subfamily_le src generators rowMap)

omit [DecidableEq σ] in
theorem rank_coeffMatrix_submatrix_le {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (monomials : Finset (σ →₀ ℕ))
    (generators : ι → MvPolynomial σ F)
    (rowMap : κ → ι)
    (colMap : ν → monomials) :
    ((coeffMatrix monomials generators).submatrix rowMap colMap).rank ≤
      (coeffMatrix monomials generators).rank := by
  let A := coeffMatrix monomials generators
  have hcols :
      ((A.submatrix rowMap (Equiv.refl _)).submatrix (Equiv.refl _) colMap).rank ≤
        (A.submatrix rowMap (Equiv.refl _)).rank := by
    simpa [A, Matrix.submatrix_submatrix] using
      rank_coeffMatrix_submatrix_cols_le monomials
        (fun i : κ => generators (rowMap i)) colMap
  have hrows : (A.submatrix rowMap (Equiv.refl _)).rank ≤ A.rank := by
    simpa [A] using
      Matrix.rank_submatrix_le (f := rowMap) (e := Equiv.refl monomials) (A := A)
  exact le_trans hcols hrows

def supportedSub (monomials : Finset (σ →₀ ℕ)) :
    Submodule F (MvPolynomial σ F) where
  carrier := { p | p.support ⊆ monomials }
  add_mem' ha hb := Finset.Subset.trans Finsupp.support_add (Finset.union_subset ha hb)
  zero_mem' := by simp
  smul_mem' c _ hp := Finset.Subset.trans Finsupp.support_smul hp

theorem span_in_supported (monomials : Finset (σ →₀ ℕ))
    (S : Set (MvPolynomial σ F))
    (h : ∀ g ∈ S, (g : MvPolynomial σ F).support ⊆ monomials) :
    Submodule.span F S ≤ supportedSub monomials :=
  Submodule.span_le.mpr h

theorem coeffVectorLin_injOn (monomials : Finset (σ →₀ ℕ)) :
    Function.Injective
      ((coeffVectorLin (F := F) monomials).domRestrict (supportedSub monomials)) := by
  intro ⟨p, hp⟩ ⟨q, hq⟩ heq
  simp only [LinearMap.domRestrict_apply, Subtype.mk.injEq] at heq ⊢
  exact coeffVector_injective monomials p q hp hq heq

theorem finrank_span_eq_matrix_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (monomials : Finset (σ →₀ ℕ))
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (generators i).support ⊆ monomials) :
    Module.finrank F (Submodule.span F (Set.range generators)) =
    (coeffMatrix monomials generators).rank := by
  let f := coeffVectorLin (σ := σ) (F := F) monomials
  have h_le := span_in_supported monomials _ (by
    intro g hg
    rw [Set.mem_range] at hg
    obtain ⟨i, rfl⟩ := hg
    exact hsupport i)
  have step1 : Module.finrank F (Submodule.span F (Set.range generators)) =
      Module.finrank F (Submodule.map f (Submodule.span F (Set.range generators))) := by
    let fV := f.domRestrict (Submodule.span F (Set.range generators))
    have fV_inj : Function.Injective fV := by
      intro ⟨p, hp⟩ ⟨q, hq⟩ heq
      simp only [Subtype.mk.injEq] at heq ⊢
      exact coeffVector_injective monomials p q (h_le hp) (h_le hq) heq
    let e := LinearEquiv.ofInjective fV fV_inj
    have h_range : LinearMap.range fV = (Submodule.span F (Set.range generators)).map f := by
      ext x
      simp only [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨⟨a, ha⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
    rw [← h_range]
    exact (LinearEquiv.finrank_eq e)
  have step2 : Submodule.map f (Submodule.span F (Set.range generators)) =
      Submodule.span F (Set.range (fun i : ι => f (generators i))) := by
    rw [Submodule.map_span]
    congr 1
    ext v
    simp [Set.mem_image, Set.mem_range]
  have step3 : (fun i : ι => f (generators i)) =
      (fun i : ι => (fun m : monomials => (coeffMatrix monomials generators) i m)) := by
    ext i m
    rfl
  rw [step1, step2, step3]
  let A := coeffMatrix monomials generators
  rw [show (fun i : ι => (fun m : monomials => A i m)) =
      (fun i : ι => (Matrix.transpose A).col i) from by
        ext i m
        simp [Matrix.transpose, Matrix.col]]
  rw [← Matrix.rank_eq_finrank_span_cols, Matrix.rank_transpose]

omit [DecidableEq σ] in
theorem map_span_range_eq_span_range {ι : Type*}
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (generators : ι → MvPolynomial σ F) :
    Submodule.map φ (Submodule.span F (Set.range generators)) =
      Submodule.span F (Set.range (fun i => φ (generators i))) := by
  rw [Submodule.map_span]
  congr 1
  ext v
  simp [Set.mem_image, Set.mem_range]

theorem finrank_map_span_eq_matrix_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (monomials : Finset (σ →₀ ℕ))
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (generators : ι → MvPolynomial σ F)
    (hsupport : ∀ i, (φ (generators i)).support ⊆ monomials) :
    Module.finrank F (Submodule.map φ (Submodule.span F (Set.range generators))) =
      (coeffMatrix monomials (fun i => φ (generators i))).rank := by
  rw [map_span_range_eq_span_range]
  exact finrank_span_eq_matrix_rank monomials (fun i => φ (generators i)) hsupport

theorem finrank_map_span_le_coeffMatrix_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src tgt : Finset (σ →₀ ℕ))
    (φ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (generators : ι → MvPolynomial σ F)
    (hsrc : ∀ i, (generators i).support ⊆ src)
    (htgt : ∀ i, (φ (generators i)).support ⊆ tgt) :
    Module.finrank F (Submodule.map φ (Submodule.span F (Set.range generators))) ≤
      (coeffMatrix src generators).rank := by
  calc
    Module.finrank F (Submodule.map φ (Submodule.span F (Set.range generators)))
      = (coeffMatrix tgt (fun i => φ (generators i))).rank :=
          finrank_map_span_eq_matrix_rank tgt φ generators htgt
    _ ≤ (coeffMatrix src generators).rank :=
        rank_coeffMatrix_map_le src tgt φ generators hsrc

/-! ### Coefficient vectors of products with disjoint support

For polynomials with disjoint variable supports, the coefficient vector of
the product factors as a product of per-factor coefficient vectors (in the
appropriate coordinate decomposition). This is the algebraic identity
underlying the Kronecker/tensor product structure of the SPDP matrix.

Concretely: if p_i have pairwise disjoint vars, then for any multilinear
monomial β = β_1 + ... + β_m (with supp(β_i) ⊆ vars(p_i)):
  coeff(β, ∏ p_i) = ∏ coeff(β_i, p_i)

This means the coefficient vector of the product is determined by the
per-factor coefficient vectors, and the rank of the product's coefficient
matrix is bounded by the product of per-factor ranks. Combined with
finrank_span_products_le, this gives the symmetric power collapse. -/

/-- For polynomials with disjoint variable support: the coefficient of a sum
    monomial in the product equals the product of individual coefficients.

    This is the Kronecker structure: coeff(α+β, p*q) = coeff(α,p) * coeff(β,q)
    when vars(p) ∩ vars(q) = ∅ and supp(α) ∩ supp(β) = ∅.

    Proof: by MvPolynomial.coeff_mul, coeff(γ, p*q) = Σ_{(a,b): a+b=γ} coeff(a,p)*coeff(b,q).
    When vars are disjoint: coeff(a,p) = 0 unless supp(a) ⊆ vars(p), and
    coeff(b,q) = 0 unless supp(b) ⊆ vars(q). With disjoint vars, the only
    contributing (a,b) pair in the antidiagonal sum for γ=α+β is (α,β) itself. -/
/- The coeff_mul_disjoint_vars theorem: for polynomials with disjoint vars,
   coeff(α+β, p*q) = coeff(α,p) * coeff(β,q) when supp(α) ∩ supp(β) = ∅.

   The proof expands coeff_mul as an antidiagonal sum and shows only the
   (α,β) term contributes. The Lean formalization hits timeout on the
   Finsupp antidiagonal API. The mathematical content is standard:
   in the antidiagonal decomposition of α+β, any (a,b) ≠ (α,β) with
   a+b = α+β forces a to have support overlapping with vars(q) (because
   supp(α) ∩ supp(β) = ∅ constrains the unique decomposition), making
   coeff(a,p) = 0.

   This is used to establish the Kronecker structure of the SPDP
   coefficient matrix for products with block-disjoint variable supports. -/
theorem coeff_mul_disjoint_vars
    (p q : MvPolynomial σ F)
    (hvars : Disjoint (MvPolynomial.vars p) (MvPolynomial.vars q))
    (α β : σ →₀ ℕ)
    (hα : α.support ⊆ p.vars) (hβ : β.support ⊆ q.vars)
    (hdisj : Disjoint α.support β.support) :
    MvPolynomial.coeff (α + β) (p * q) =
      MvPolynomial.coeff α p * MvPolynomial.coeff β q := by
  -- Key helper: for (a,b) ≠ (α,β) in antidiagonal(α+β),
  -- coeff(a,p) * coeff(b,q) = 0.
  have key : ∀ (a b : σ →₀ ℕ), a + b = α + β → (a, b) ≠ (α, β) →
      MvPolynomial.coeff a p * MvPolynomial.coeff b q = 0 := by
    intro a b hab hne
    -- Since (a,b) ≠ (α,β) and a+b = α+β: either a ≠ α or b ≠ β.
    -- Case a ≠ α: ∃ i with a(i) ≠ α(i), i ∈ supp(α) ⊆ vars(p).
    -- Then b(i) = (α+β)(i) - a(i). Since i ∈ supp(α), β(i) = 0 (disjoint supports).
    -- So (α+β)(i) = α(i). If a(i) < α(i): b(i) = α(i) - a(i) > 0.
    -- But i ∉ vars(q) (disjoint from vars(p)), so b ∉ q.support, coeff(b,q) = 0.
    -- If a(i) > α(i): impossible since a(i) + b(i) = α(i) and b(i) ≥ 0.
    -- Case b ≠ β: symmetric argument gives coeff(a,p) = 0.
    -- If coeff(a,p) * coeff(b,q) ≠ 0, then a ∈ p.support and b ∈ q.support.
    -- This gives supp(a) ⊆ vars(p) and supp(b) ⊆ vars(q).
    -- Since vars(p) ∩ vars(q) = ∅: supp(a) ∩ supp(b) = ∅.
    -- But also supp(α) ∩ supp(β) = ∅ and a+b = α+β.
    -- Two decompositions of the same Finsupp with disjoint supports must agree.
    -- Hence (a,b) = (α,β), contradicting hne.
    by_contra h0; push_neg at h0; apply hne
    have ha_supp : a.support ⊆ p.vars := fun j hj =>
      (MvPolynomial.mem_vars j).mpr ⟨a, Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul h0), hj⟩
    have hb_supp : b.support ⊆ q.vars := fun j hj =>
      (MvPolynomial.mem_vars j).mpr ⟨b, Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul h0), hj⟩
    have ha_eq : a = α := by
      ext i
      have hsum : a i + b i = α i + β i := by
        have := congr_fun (congr_arg Finsupp.toFun hab) i
        simpa [Finsupp.coe_add, Pi.add_apply] using this
      by_cases hia : i ∈ α.support
      · have hbi : b i = 0 := by
          by_contra hb_ne
          have hib : i ∈ b.support := Finsupp.mem_support_iff.mpr hb_ne
          exact Finset.disjoint_left.mp hvars (hα hia) (hb_supp hib)
        have hβi : β i = 0 := by
          by_contra hβ_ne
          exact absurd (Finsupp.mem_support_iff.mpr hβ_ne) (Finset.disjoint_left.mp hdisj hia)
        omega
      · have hαi : α i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hia
        by_cases hib : i ∈ β.support
        · have hai : a i = 0 := by
            by_contra ha_ne
            have hia' : i ∈ a.support := Finsupp.mem_support_iff.mpr ha_ne
            exact Finset.disjoint_left.mp hvars (ha_supp hia') (hβ hib)
          omega
        · have hβi : β i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hib
          omega
    have hb_eq : b = β := by
      have h : α + b = α + β := ha_eq ▸ hab
      exact add_left_cancel h
    exact Prod.ext ha_eq hb_eq
  classical
  rw [MvPolynomial.coeff_mul]
  -- The antidiagonal sum equals coeff(α,p)*coeff(β,q) + Σ_{(a,b)≠(α,β)} 0
  have hmem : (α, β) ∈ Finset.antidiagonal (α + β) :=
    Finset.mem_antidiagonal.mpr rfl
  rw [← Finset.add_sum_erase (Finset.antidiagonal (α + β)) _ hmem]
  have hrest : ∑ x ∈ (Finset.antidiagonal (α + β)).erase (α, β),
      MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q = 0 := by
    apply Finset.sum_eq_zero
    intro ⟨a, b⟩ hx
    rw [Finset.mem_erase] at hx
    exact key a b (Finset.mem_antidiagonal.mp hx.2) hx.1
  rw [hrest, add_zero]

/-! ### Kronecker product rank upper bound

rank(A ⊗ B) ≤ rank(A) × rank(B) for the Kronecker product.

The proof: the row space of A ⊗ B is spanned by products of rows of A
and rows of B. The span of such products has dimension ≤ rank(A) × rank(B)
because any product a ⊗ b lies in the image of the bilinear map
rowSpace(A) × rowSpace(B) → F^{columns}, and the image of a bilinear map
on spaces of dimensions r₁, r₂ has dimension ≤ r₁ × r₂.

For the SPDP application: the per-profile coefficient matrix factors as a
Kronecker product of per-type matrices, each with rank ≤ C(h(τ)+d_τ-1,d_τ-1).
So the per-profile rank ≤ ∏_τ C(h(τ)+d_τ-1, d_τ-1) ≤ (κ+1)^8. -/

/-- Upper bound on rank of Kronecker product: rank(A ⊗ B) ≤ rank(A) × rank(B).

    The matrix linear map of `A.kronecker B` is exactly `TensorProduct.map`
    of the matrix linear maps for `A` and `B`. Its range is contained in the
    image of `range f ⊗ range g`, whose finrank is the product of the two
    column-space finranks. -/
theorem rank_kronecker_le {R : Type*} [Field R]
    {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (A : Matrix l m R) (B : Matrix n p R) :
    (A.kronecker B).rank ≤ A.rank * B.rank := by
  classical
  let bl : Module.Basis l R (l → R) := Pi.basisFun R l
  let bm : Module.Basis m R (m → R) := Pi.basisFun R m
  let bn : Module.Basis n R (n → R) := Pi.basisFun R n
  let bp : Module.Basis p R (p → R) := Pi.basisFun R p
  let f : (m → R) →ₗ[R] (l → R) := Matrix.toLin bm bl A
  let g : (p → R) →ₗ[R] (n → R) := Matrix.toLin bp bn B
  have hA : A.rank = Module.finrank R (LinearMap.range f) := by
    simpa [f, bl, bm] using Matrix.rank_eq_finrank_range_toLin A bl bm
  have hB : B.rank = Module.finrank R (LinearMap.range g) := by
    simpa [g, bn, bp] using Matrix.rank_eq_finrank_range_toLin B bn bp
  have hAB :
      Matrix.toLin (bm.tensorProduct bp) (bl.tensorProduct bn) (A.kronecker B) =
        TensorProduct.map f g := by
    exact Matrix.toLin_kronecker (bM := bm) (bN := bp) (bM' := bl) (bN' := bn) A B
  rw [Matrix.rank_eq_finrank_range_toLin (A.kronecker B) (bl.tensorProduct bn)
    (bm.tensorProduct bp), hAB]
  have hRange :
      LinearMap.range (TensorProduct.map f g) =
        LinearMap.range (TensorProduct.mapIncl (LinearMap.range f) (LinearMap.range g)) := by
    exact (TensorProduct.range_map f g).trans
      (TensorProduct.range_mapIncl (LinearMap.range f) (LinearMap.range g)).symm
  calc
    Module.finrank R (LinearMap.range (TensorProduct.map f g))
        = Module.finrank R
            (LinearMap.range (TensorProduct.mapIncl (LinearMap.range f) (LinearMap.range g))) := by
          rw [hRange]
    _ ≤ Module.finrank R (TensorProduct R (LinearMap.range f) (LinearMap.range g)) := by
          exact LinearMap.finrank_range_le _
    _ = Module.finrank R (TensorProduct R (LinearMap.range f) (LinearMap.range g)) := rfl
    _ = Module.finrank R (LinearMap.range f) * Module.finrank R (LinearMap.range g) := by
          rw [Module.finrank_tensorProduct]
    _ = A.rank * B.rank := by rw [← hA, ← hB]

end CoeffMatrixHelpers
