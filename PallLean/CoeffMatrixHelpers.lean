import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Rank

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

end CoeffMatrixHelpers
