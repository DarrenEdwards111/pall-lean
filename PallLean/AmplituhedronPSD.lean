/-
  AmplituhedronPSD.lean — PSD operator infrastructure toward amplituhedron gauge

  Paper reference (p vs np1.pdf, §28.3 N-Frame Lagrangian, lines 7300-7330):
  The amplituhedron-style positive geometry uses PSD operators with positive
  principal minors:

    B(A) = -Σ_{J ∈ 𝒥} log det(A[J, J])

  where A ⪰ 0 is a compiled positive operator and 𝒥 is a fixed family of
  principal-minor index sets.

  This file builds preliminary Lean infrastructure:
  1. Principal submatrix of a PSD ℝ-matrix via arbitrary maps (wrapper for
     Mathlib's `PosSemidef.submatrix`).
  2. Non-negativity of principal-minor determinants (Mathlib's spectral thm).
  3. `TotallyNonnegativeMinorFamily` structure: a family of principal minors
     whose determinants are all non-negative for any PSD matrix.

  Specialized to ℝ (the paper's setting); extensible to ℂ via ComplexOrder.

  Contribution: first axiom-free infrastructure toward the amplituhedron
  gauge. Full gauge construction remains paper-deep (requires totally-
  positive Grassmannian / determinantal barrier calculus not in Mathlib).
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

namespace AmplituhedronPSD

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ## Section 1: PSD principal submatrix (over ℝ)

Principal submatrix of a PSD ℝ-matrix via an arbitrary map `e : m → n`. -/

/-- Principal-submatrix PSD: the submatrix via an arbitrary function of
a PSD ℝ-matrix is PSD (wrapper for Mathlib's `Matrix.PosSemidef.submatrix`). -/
theorem posSemidef_submatrix
    {M : Matrix n n ℝ} (hM : M.PosSemidef)
    (e : m → n) : (M.submatrix e e).PosSemidef :=
  hM.submatrix e

/-- **Non-negativity of PSD submatrix determinant**: combines Mathlib's
`PosSemidef.submatrix` with `PosSemidef.det_nonneg`. -/
theorem det_submatrix_nonneg_of_posSemidef
    {M : Matrix n n ℝ} (hM : M.PosSemidef) (e : m → n) :
    0 ≤ (M.submatrix e e).det :=
  (hM.submatrix e).det_nonneg

/-! ## Section 2: Totally Non-negative Minor family

A family of index sets `𝒥` over `n` induces a "barrier" structure when
each principal minor of a PSD matrix has non-negative determinant.

This is the basic amplituhedron positivity setup: a designated family
of principal submatrices whose determinants are the "observable"
coordinates in the positive geometry. -/

/-- A family of principal-minor selections. Each index picks out a
"shape" type (typically a subtype of `n`) and a selection function
(typically the inclusion). -/
structure TotallyNonnegativeMinorFamily
    (n : Type*) [Fintype n] [DecidableEq n] where
  /-- Index type for the family. -/
  index : Type*
  /-- Each index determines a "shape" type for the submatrix. -/
  shape : index → Type*
  /-- Each shape is finite. -/
  shape_fintype : ∀ i, Fintype (shape i) := by intros; infer_instance
  /-- Each shape has decidable equality. -/
  shape_decEq : ∀ i, DecidableEq (shape i) := by intros; infer_instance
  /-- The selection function for each index. -/
  select : (i : index) → shape i → n

/-- Applied to a PSD matrix, every minor in the family has non-negative
determinant. -/
theorem nonneg_minor_det_of_posSemidef
    (𝒥 : TotallyNonnegativeMinorFamily n)
    {M : Matrix n n ℝ} (hM : M.PosSemidef) (i : 𝒥.index) :
    letI := 𝒥.shape_fintype i
    letI := 𝒥.shape_decEq i
    0 ≤ (M.submatrix (𝒥.select i) (𝒥.select i)).det := by
  letI := 𝒥.shape_fintype i
  letI := 𝒥.shape_decEq i
  exact det_submatrix_nonneg_of_posSemidef hM (𝒥.select i)

/-! ## Section 3: specific families

Amplituhedron-style: the family of all "principal" minors indexed by
Finset subsets of `n`. -/

/-- The universal minor family: all finite subsets of `n`, viewed as
injections of their Finset-subtypes. -/
noncomputable def universalMinorFamily (n : Type*) [Fintype n]
    [DecidableEq n] : TotallyNonnegativeMinorFamily n where
  index := Finset n
  shape S := { i : n // i ∈ S }
  shape_fintype _ := inferInstance
  shape_decEq _ := Subtype.instDecidableEq
  select _ := Subtype.val

/-- Universal-family corollary: every principal minor of a PSD matrix has
non-negative determinant. -/
theorem nonneg_principal_minor_of_posSemidef
    {M : Matrix n n ℝ} (hM : M.PosSemidef) (S : Finset n) :
    0 ≤ (M.submatrix (Subtype.val : { i : n // i ∈ S } → n)
          (Subtype.val : { i : n // i ∈ S } → n)).det :=
  det_submatrix_nonneg_of_posSemidef hM _

/-! ## Section 4: PosDef principal minors — the positive case

For `PosDef` matrices (strict positive definite), Mathlib has
`PosDef.det_pos`. Combined with `PosDef → PosSemidef → submatrix PSD`,
we have non-negativity of submatrix determinants.

For STRICT positivity (PosDef.submatrix for injective e), we need
Finsupp/quadratic-form manipulation which we do below. -/

/-- Every `PosDef` matrix has strictly positive determinant (wrapper for
`Matrix.PosDef.det_pos`). -/
theorem det_pos_of_posDef {M : Matrix n n ℝ} (hM : M.PosDef) : 0 < M.det :=
  hM.det_pos

/-- Every `PosDef` matrix is `PosSemidef` (wrapper for
`Matrix.PosDef.posSemidef`). -/
theorem posSemidef_of_posDef {M : Matrix n n ℝ} (hM : M.PosDef) : M.PosSemidef :=
  hM.posSemidef

/-- Submatrices of `PosDef` matrices are at least `PosSemidef`, hence have
non-negative determinant. -/
theorem det_submatrix_nonneg_of_posDef
    {M : Matrix n n ℝ} (hM : M.PosDef) (e : m → n) :
    0 ≤ (M.submatrix e e).det :=
  det_submatrix_nonneg_of_posSemidef (posSemidef_of_posDef hM) e

/-- **Principal-submatrix `PosDef` via injective maps**: the submatrix
of a `PosDef` matrix via an injective function is `PosDef`.

Construction: given nonzero `x : m →₀ ℝ`, extend via `Finsupp.embDomain`
to `x_ext : n →₀ ℝ`. This extension is nonzero (by `embDomain_injective`)
and the quadratic forms match (by `Finsupp.sum_embDomain` applied twice).
Then `PosDef` of `M` applied to `x_ext` gives strict positivity. -/
theorem PosDef_submatrix_of_injective
    {M : Matrix n n ℝ} (hM : M.PosDef)
    {e : m → n} (he : Function.Injective e) :
    (M.submatrix e e).PosDef := by
  refine ⟨hM.1.submatrix e, ?_⟩
  intro x hx
  classical
  -- Embed x to n-indexed Finsupp via the injection e.
  let φ : m ↪ n := ⟨e, he⟩
  let x_ext : n →₀ ℝ := x.embDomain φ
  -- x_ext ≠ 0 (embDomain on an embedding is injective).
  have hx_ext : x_ext ≠ 0 := by
    intro hzero
    apply hx
    have h0 : (0 : m →₀ ℝ).embDomain φ = (0 : n →₀ ℝ) := by simp
    have : x.embDomain φ = (0 : m →₀ ℝ).embDomain φ := by
      rw [h0]; exact hzero
    exact Finsupp.embDomain_injective φ this
  -- Quadratic form identity.
  have h_quad : x.sum (fun i xi => x.sum fun j xj =>
      star xi * (M.submatrix e e) i j * xj) =
      x_ext.sum (fun i xi => x_ext.sum fun j xj =>
      star xi * M i j * xj) := by
    show x.sum (fun i xi => x.sum fun j xj =>
        star xi * (M.submatrix e e) i j * xj) = _
    -- x_ext.sum over β = x.sum over α via sum_embDomain.
    rw [show x_ext = x.embDomain φ from rfl]
    rw [Finsupp.sum_embDomain (f := φ)
        (g := fun i xi => (x.embDomain φ).sum fun j xj =>
          star xi * M i j * xj)]
    apply Finsupp.sum_congr
    intro a _
    -- Goal: (x.sum fun j xj => star (x a) * (M.submatrix e e) a j * xj) =
    --       (x.embDomain φ).sum fun j xj => star (x a) * M (φ a) j * xj
    rw [show (Finsupp.embDomain φ x).sum (fun j xj =>
          star (x a) * M (φ a) j * xj) =
        x.sum (fun b xb => star (x a) * M (φ a) (φ b) * xb) from
      Finsupp.sum_embDomain (f := φ)
        (g := fun j xj => star (x a) * M (φ a) j * xj)]
    rfl
  -- Apply PosDef of M to x_ext.
  rw [h_quad]
  exact hM.2 hx_ext

/-- `PosDef` principal minors via injective maps have STRICTLY positive
determinants. -/
theorem det_submatrix_pos_of_posDef
    {M : Matrix n n ℝ} (hM : M.PosDef)
    {e : m → n} (he : Function.Injective e) :
    0 < (M.submatrix e e).det :=
  (PosDef_submatrix_of_injective hM he).det_pos

/-! ## Section 5: Totally Positive Matrix

A matrix all of whose principal minors (indexed by Finsets of n) have
strictly positive determinants. For symmetric PSD matrices, this is
equivalent to being PosDef (via PosDef_submatrix_of_injective). -/

/-- A matrix whose principal minors (indexed by `Finset n`) all have
strictly positive determinants. -/
def TotallyPositivePrincipalMinors (M : Matrix n n ℝ) : Prop :=
  ∀ (S : Finset n),
    0 < (M.submatrix (Subtype.val : { i : n // i ∈ S } → n)
          (Subtype.val : { i : n // i ∈ S } → n)).det

/-- Every `PosDef` matrix has all principal minors strictly positive. -/
theorem totallyPositivePrincipalMinors_of_posDef
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    TotallyPositivePrincipalMinors M := by
  intro S
  exact det_submatrix_pos_of_posDef hM Subtype.val_injective

/-- From `PosDef`, `TotallyPositivePrincipalMinors` follows directly.
(Converse — recovering `PosDef` from `TotallyPositivePrincipalMinors` —
is Sylvester's criterion, requiring more advanced spectral theory.) -/
theorem posDef_implies_totallyPositive
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    TotallyPositivePrincipalMinors M :=
  totallyPositivePrincipalMinors_of_posDef hM

/-! ## Section 6: Determinantal barrier

The amplituhedron barrier function:
  B(A) := -Σ_{J ∈ 𝒥} log det(A[J, J])

Well-defined for PosDef matrices (all minor dets > 0). On the cone
of PSD matrices, this barrier → +∞ as A approaches the boundary
(singular PSD). -/

/-- The determinantal barrier with respect to a `TotallyNonnegativeMinorFamily`.

For `M : Matrix n n ℝ` and a family `𝒥` of principal-minor selections,
the barrier is defined as `-Σ_i log(det(M[𝒥_i, 𝒥_i]))`.

For `PosDef` matrices and `𝒥 = universalMinorFamily`, each log det is
well-defined and strictly positive. -/
noncomputable def determinantalBarrier (𝒥 : TotallyNonnegativeMinorFamily n)
    [Fintype 𝒥.index] (M : Matrix n n ℝ) : ℝ :=
  -∑ i : 𝒥.index,
    letI := 𝒥.shape_fintype i
    letI := 𝒥.shape_decEq i
    Real.log ((M.submatrix (𝒥.select i) (𝒥.select i)).det)

/-- Identity submatrix via injection = identity. -/
theorem submatrix_one_eq_one
    {m' : Type*} [Fintype m'] [DecidableEq m']
    {e : m' → n} (he : Function.Injective e) :
    ((1 : Matrix n n ℝ).submatrix e e) = 1 := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij]
  · have : e i ≠ e j := fun heq => hij (he heq)
    simp [hij, this]

/-- The determinant of an identity submatrix is 1. -/
theorem det_submatrix_one
    {m' : Type*} [Fintype m'] [DecidableEq m']
    {e : m' → n} (he : Function.Injective e) :
    ((1 : Matrix n n ℝ).submatrix e e).det = 1 := by
  rw [submatrix_one_eq_one he]
  exact Matrix.det_one

/-- `determinantalBarrier 𝒥 1 = 0`: the barrier vanishes at the identity.
(Each log det(I) = log 1 = 0; sum is 0.)

Requires each selection to be injective. -/
theorem determinantalBarrier_one (𝒥 : TotallyNonnegativeMinorFamily n)
    [Fintype 𝒥.index]
    (hselect : ∀ i, Function.Injective (𝒥.select i)) :
    determinantalBarrier 𝒥 (1 : Matrix n n ℝ) = 0 := by
  unfold determinantalBarrier
  rw [show
      (∑ i : 𝒥.index, letI := 𝒥.shape_fintype i; letI := 𝒥.shape_decEq i
        Real.log (((1 : Matrix n n ℝ).submatrix (𝒥.select i) (𝒥.select i)).det))
      = ∑ _i : 𝒥.index, (0 : ℝ) from by
    apply Finset.sum_congr rfl
    intro i _
    letI := 𝒥.shape_fintype i
    letI := 𝒥.shape_decEq i
    rw [det_submatrix_one (hselect i), Real.log_one]]
  simp

/-- **Barrier as negative log of determinant product**: for `PosDef`
matrices (where all dets are > 0), the barrier equals `-log(∏ det)`.

This follows from `Real.log_prod` (log of product = sum of logs). -/
theorem determinantalBarrier_eq_neg_log_prod
    (𝒥 : TotallyNonnegativeMinorFamily n) [Fintype 𝒥.index]
    {M : Matrix n n ℝ}
    (hpos : ∀ i : 𝒥.index,
      letI := 𝒥.shape_fintype i
      letI := 𝒥.shape_decEq i
      (M.submatrix (𝒥.select i) (𝒥.select i)).det ≠ 0) :
    determinantalBarrier 𝒥 M =
    - Real.log (∏ i : 𝒥.index,
      letI := 𝒥.shape_fintype i
      letI := 𝒥.shape_decEq i
      (M.submatrix (𝒥.select i) (𝒥.select i)).det) := by
  unfold determinantalBarrier
  congr 1
  have hne : ∀ i ∈ (Finset.univ : Finset 𝒥.index),
      (letI := 𝒥.shape_fintype i
       letI := 𝒥.shape_decEq i
       (M.submatrix (𝒥.select i) (𝒥.select i)).det) ≠ 0 :=
    fun i _ => hpos i
  exact (Real.log_prod hne).symm

/-- **Barrier is well-defined (finite) on totally positive matrices**: if
all principal minors have strictly positive determinant, the barrier is
a finite real number (each log is well-defined). -/
theorem determinantalBarrier_well_defined
    (𝒥 : TotallyNonnegativeMinorFamily n) [Fintype 𝒥.index]
    (hselect : ∀ i, Function.Injective (𝒥.select i))
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    ∀ i : 𝒥.index,
      letI := 𝒥.shape_fintype i
      letI := 𝒥.shape_decEq i
      (M.submatrix (𝒥.select i) (𝒥.select i)).det > 0 := by
  intro i
  letI := 𝒥.shape_fintype i
  letI := 𝒥.shape_decEq i
  exact det_submatrix_pos_of_posDef hM (hselect i)

/-! ## Section 7: Scalar barrier convexity

The function `-log` is convex on `(0, ∞)`. This is the 1-dimensional
case of the general log det convexity used in the amplituhedron
interior point construction.

Uses Mathlib's `Real.strictConcaveOn_log_Ioi`. -/

/-- The scalar barrier function `-log` is strictly convex on `(0, ∞)`. -/
theorem strictConvexOn_neg_log :
    StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => -Real.log x) :=
  StrictConcaveOn.neg strictConcaveOn_log_Ioi

/-- The scalar barrier function `-log` is convex on `(0, ∞)`. -/
theorem convexOn_neg_log :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => -Real.log x) :=
  strictConvexOn_neg_log.convexOn

/-- Concretely: for x, y > 0 and t ∈ [0, 1],
    `-log((1-t)x + ty) ≤ (1-t)(-log x) + t(-log y)`. -/
theorem neg_log_convex_inequality {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -Real.log ((1 - t) * x + t * y) ≤
    (1 - t) * (-Real.log x) + t * (-Real.log y) := by
  have h := convexOn_neg_log.2 (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy)
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring : (1 - t) + t = 1)
  simpa using h

/-! ## Section 8: Totally nonnegative/positive Grassmannian (matrix form)

For a k × n matrix A, a "Plücker coordinate" is a k × k minor indexed
by a size-k subset S ⊆ [n] (selecting columns of A). The **totally
nonnegative Grassmannian** `Gr+_{k,n}` is the image of rank-k matrices
all of whose Plücker coordinates (k × k minors) are ≥ 0.

This is the matrix-level view; the quotient by row operations gives
the geometric Grassmannian cell. We stay at the matrix level here
to keep the definition concrete. -/

/-- A k × n matrix is **totally nonnegative** if all k × k minors
(indexed by injective maps `e : Fin k → Fin n'` selecting k columns)
have non-negative determinants. -/
def IsTotallyNonnegativeMatrix {k n' : ℕ}
    (A : Matrix (Fin k) (Fin n') ℝ) : Prop :=
  ∀ (e : Fin k → Fin n'), Function.Injective e →
    0 ≤ (A.submatrix id e).det

/-- A k × n matrix is **totally positive** if all k × k minors have
STRICTLY positive determinants. -/
def IsTotallyPositiveMatrix {k n' : ℕ}
    (A : Matrix (Fin k) (Fin n') ℝ) : Prop :=
  ∀ (e : Fin k → Fin n'), Function.Injective e →
    0 < (A.submatrix id e).det

/-- Totally positive implies totally nonnegative. -/
theorem IsTotallyPositiveMatrix.isTotallyNonnegativeMatrix
    {k n' : ℕ} {A : Matrix (Fin k) (Fin n') ℝ}
    (hA : IsTotallyPositiveMatrix A) : IsTotallyNonnegativeMatrix A :=
  fun e he => (hA e he).le

/-- Scaling by a positive constant preserves total positivity.
For c > 0, the minor of c • A equals c^k times the minor of A. -/
theorem IsTotallyPositiveMatrix.smul_pos {k n' : ℕ}
    {A : Matrix (Fin k) (Fin n') ℝ} (hA : IsTotallyPositiveMatrix A)
    {c : ℝ} (hc : 0 < c) :
    IsTotallyPositiveMatrix (c • A) := by
  intro e he
  have hsub : ((c • A).submatrix id e) = c • (A.submatrix id e) := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.smul_apply]
  rw [hsub, Matrix.det_smul, Fintype.card_fin]
  exact mul_pos (pow_pos hc k) (hA e he)

/-- Totally nonneg matrices form the `Gr+_{k,n}` set (modulo row
operations, which we don't quotient here). -/
def TotallyNonnegativeGrassmannian (k n' : ℕ) : Set (Matrix (Fin k) (Fin n') ℝ) :=
  { A | IsTotallyNonnegativeMatrix A }

/-- Totally positive matrices form the INTERIOR of `Gr+_{k,n}` (positivity
of all k-minors — the top-dimensional cell). -/
def TotallyPositiveGrassmannianInterior (k n' : ℕ) :
    Set (Matrix (Fin k) (Fin n') ℝ) :=
  { A | IsTotallyPositiveMatrix A }

/-- The interior is contained in the whole. -/
theorem totallyPositive_subset_totallyNonnegative (k n' : ℕ) :
    TotallyPositiveGrassmannianInterior k n' ⊆
    TotallyNonnegativeGrassmannian k n' :=
  fun _ hA => hA.isTotallyNonnegativeMatrix

/-- Vacuous case: every `0 × n'` matrix is totally nonnegative (determinant
of the empty submatrix is `1 ≥ 0`). -/
theorem isTotallyNonnegativeMatrix_zero_rows {n' : ℕ}
    (A : Matrix (Fin 0) (Fin n') ℝ) : IsTotallyNonnegativeMatrix A := by
  intro e _
  simp [Matrix.det_isEmpty]

/-- Vacuous case: every `0 × n'` matrix is totally positive. -/
theorem isTotallyPositiveMatrix_zero_rows {n' : ℕ}
    (A : Matrix (Fin 0) (Fin n') ℝ) : IsTotallyPositiveMatrix A := by
  intro e _
  simp [Matrix.det_isEmpty]

/-! ## Section 9: Full rank from total positivity

A key structural fact: if `k ≤ n'` and `A : Matrix (Fin k) (Fin n') ℝ` is
totally positive, then `A` has full row rank.

The identity embedding `Fin k ↪ Fin n'` (via `Fin.castLE h` with `h : k ≤ n'`)
is injective, so the `k × k` submatrix picking out the first `k` columns has
strictly positive determinant, hence is invertible. This shows rank ≥ k, and
since A has only k rows, rank = k. -/

/-- For `k ≤ n'`, a totally positive `k × n'` matrix has a nonzero `k × k`
submatrix (obtained by selecting the first `k` columns via `Fin.castLE`). -/
theorem IsTotallyPositiveMatrix.exists_nonzero_minor {k n' : ℕ}
    (h : k ≤ n') {A : Matrix (Fin k) (Fin n') ℝ}
    (hA : IsTotallyPositiveMatrix A) :
    ∃ (e : Fin k → Fin n'), Function.Injective e ∧
      (A.submatrix id e).det ≠ 0 := by
  have hinj : Function.Injective (fun i : Fin k => Fin.castLE h i) :=
    Fin.castLE_injective h
  exact ⟨fun i => Fin.castLE h i, hinj, ne_of_gt (hA _ hinj)⟩

/-! ## Section 10: Finite sum of scalar `-log` is convex

Barrier convexity in the scalar coordinates: if we parameterize a family of
positive values `f : ι → ℝ≥0` and take the sum `∑ -log(f i)`, this is convex
in `f` on the positivity region. This is the "separable" / "coordinate-wise"
form of convexity that applies whenever the principal minors are independent
coordinates. -/

/-- The function `f ↦ ∑ i, -log(f i)` is convex on `{f | ∀ i, 0 < f i}`.
This is the finite-sum version of `convexOn_neg_log`. -/
theorem sum_neg_log_convexOn {ι : Type*} [Fintype ι] :
    ConvexOn ℝ {f : ι → ℝ | ∀ i, 0 < f i}
      (fun f : ι → ℝ => ∑ i, -Real.log (f i)) := by
  refine ⟨?_, ?_⟩
  · -- Convexity of the positivity region.
    intro x hx y hy a b ha hb hab i
    have hxi : 0 < x i := hx i
    have hyi : 0 < y i := hy i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases lt_or_eq_of_le ha with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hxi) (mul_nonneg hb hyi.le)
    · -- a = 0, so b = 1 by a + b = 1
      have hb' : (0 : ℝ) < b := by
        have : b = 1 := by linarith
        simp [this]
      exact add_pos_of_nonneg_of_pos (mul_nonneg ha hxi.le) (mul_pos hb' hyi)
  · -- Convexity inequality on the sum.
    intro x hx y hy a b ha hb hab
    have hxi : ∀ i, 0 < x i := hx
    have hyi : ∀ i, 0 < y i := hy
    have key : ∀ i : ι,
        -Real.log (a * x i + b * y i) ≤
          a * (-Real.log (x i)) + b * (-Real.log (y i)) := by
      intro i
      have h := convexOn_neg_log.2
        (Set.mem_Ioi.mpr (hxi i)) (Set.mem_Ioi.mpr (hyi i))
        ha hb hab
      simpa using h
    calc ∑ i, -Real.log (a * x i + b * y i)
        ≤ ∑ i, (a * (-Real.log (x i)) + b * (-Real.log (y i))) :=
          Finset.sum_le_sum (fun i _ => key i)
      _ = a * (∑ i, -Real.log (x i)) + b * (∑ i, -Real.log (y i)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = a • (∑ i, -Real.log (x i)) + b • (∑ i, -Real.log (y i)) := by
          simp [smul_eq_mul]

/-! ## Section 11: Barrier expressed via minor-valued map

The determinantal barrier is
    B(M) = ∑_i -log det(M[J_i, J_i])
By introducing the "minor vector" Φ(M) : 𝒥.index → ℝ,
    Φ_i(M) = det(M[J_i, J_i]),
we factor B = (∑ -log) ∘ Φ. This makes explicit that the barrier depends
on M only through the principal-minor values, and that its convexity
properties can be analyzed in the minor-vector coordinate. -/

/-- The principal-minor vector induced by a minor family. -/
def minorVector (𝒥 : TotallyNonnegativeMinorFamily n) [Fintype 𝒥.index]
    (M : Matrix n n ℝ) : 𝒥.index → ℝ :=
  fun i =>
    letI := 𝒥.shape_fintype i
    letI := 𝒥.shape_decEq i
    (M.submatrix (𝒥.select i) (𝒥.select i)).det

/-- Barrier factors through the minor vector:
    determinantalBarrier 𝒥 M = ∑_i -log (minorVector 𝒥 M i). -/
theorem determinantalBarrier_eq_sum_neg_log_minorVector
    (𝒥 : TotallyNonnegativeMinorFamily n) [Fintype 𝒥.index]
    (M : Matrix n n ℝ) :
    determinantalBarrier 𝒥 M =
      ∑ i : 𝒥.index, -Real.log (minorVector 𝒥 M i) := by
  unfold determinantalBarrier minorVector
  rw [← Finset.sum_neg_distrib]

/-- If `M` is `PosDef`, its minor vector has strictly positive entries. -/
theorem minorVector_pos_of_posDef
    (𝒥 : TotallyNonnegativeMinorFamily n) [Fintype 𝒥.index]
    (hselect : ∀ i, Function.Injective (𝒥.select i))
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    ∀ i, 0 < minorVector 𝒥 M i := by
  intro i
  unfold minorVector
  letI := 𝒥.shape_fintype i
  letI := 𝒥.shape_decEq i
  exact det_submatrix_pos_of_posDef hM (hselect i)

/-! ## Section 12: Positroid combinatorics (preliminary)

The **positroid** of a totally nonnegative matrix records which Plücker
coordinates (k×k minors) vanish. This is the combinatorial invariant
stratifying the totally-nonnegative Grassmannian (Postnikov).

Full positroid theory is paper-deep and lies outside Mathlib; here we give
the basic definition and trivial structural facts (e.g., the positroid
of a totally-positive matrix is the "top cell" — no vanishing minors). -/

/-- The **positroid** of a k × n' matrix A: the set of injective column
selections `e : Fin k → Fin n'` for which the corresponding k × k minor
is strictly positive. (For totally-nonnegative A, minors are ≥ 0, so this
records where they are > 0 versus = 0.) -/
def positroidSupport {k n' : ℕ} (A : Matrix (Fin k) (Fin n') ℝ) :
    Set {e : Fin k → Fin n' // Function.Injective e} :=
  { e | 0 < (A.submatrix id e.val).det }

/-- For totally positive matrices, every injective selection is in the
positroid support — the "top cell" of the stratification. -/
theorem positroidSupport_totallyPositive
    {k n' : ℕ} {A : Matrix (Fin k) (Fin n') ℝ}
    (hA : IsTotallyPositiveMatrix A) :
    positroidSupport A = Set.univ := by
  ext ⟨e, he⟩
  simp [positroidSupport, hA e he]

/-- For totally nonnegative matrices, the positroid support is a subset
of the universe. -/
theorem positroidSupport_subset_univ
    {k n' : ℕ} (A : Matrix (Fin k) (Fin n') ℝ) :
    positroidSupport A ⊆ Set.univ :=
  fun _ _ => Set.mem_univ _

/-! ## Section 13: Barrier monotonicity in minor coordinates

The sum-of-neg-log barrier is **antitone** (decreasing) in each minor
coordinate: larger principal minors ⇒ smaller barrier value. This is
the key qualitative property making it a usable barrier for interior-
point methods (barrier blows up on the boundary where a minor vanishes). -/

/-- `∑ -log` is antitone on the positivity region: if `v ≤ w` componentwise
and both are positive, then `∑ -log(w i) ≤ ∑ -log(v i)`. -/
theorem sum_neg_log_antitone {ι : Type*} [Fintype ι]
    {v w : ι → ℝ} (hv : ∀ i, 0 < v i) (_hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) :
    ∑ i, -Real.log (w i) ≤ ∑ i, -Real.log (v i) := by
  apply Finset.sum_le_sum
  intro i _
  have : Real.log (v i) ≤ Real.log (w i) :=
    Real.log_le_log (hv i) (hvw i)
  linarith

/-- If for each `i`, `v i ≤ w i` with equality not in every coordinate
(and all positive), then the inequality above is strict. (Strict version.) -/
theorem sum_neg_log_strictAnti_of_exists_lt {ι : Type*} [Fintype ι]
    {v w : ι → ℝ} (hv : ∀ i, 0 < v i) (_hw : ∀ i, 0 < w i)
    (hvw : ∀ i, v i ≤ w i) (i₀ : ι) (hlt : v i₀ < w i₀) :
    ∑ i, -Real.log (w i) < ∑ i, -Real.log (v i) := by
  apply Finset.sum_lt_sum
  · intro i _
    have : Real.log (v i) ≤ Real.log (w i) :=
      Real.log_le_log (hv i) (hvw i)
    linarith
  · refine ⟨i₀, Finset.mem_univ _, ?_⟩
    have : Real.log (v i₀) < Real.log (w i₀) :=
      Real.log_lt_log (hv i₀) hlt
    linarith

/-! ## Section 14: Algebraic closure properties of TNN/TP matrices

Scaling and basic preservation lemmas for the matrix-level TP/TNN
predicates. -/

/-- Scaling a totally nonnegative matrix by `c ≥ 0` yields a totally
nonnegative matrix. -/
theorem IsTotallyNonnegativeMatrix.smul_nonneg
    {k n' : ℕ} {A : Matrix (Fin k) (Fin n') ℝ}
    (hA : IsTotallyNonnegativeMatrix A) {c : ℝ} (hc : 0 ≤ c) :
    IsTotallyNonnegativeMatrix (c • A) := by
  intro e he
  have hsub : ((c • A).submatrix id e) = c • (A.submatrix id e) := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.smul_apply]
  rw [hsub, Matrix.det_smul, Fintype.card_fin]
  exact mul_nonneg (pow_nonneg hc k) (hA e he)

/-- The zero matrix is totally nonnegative (every k × k minor has
determinant 0, unless k = 0 in which case the determinant is 1). -/
theorem isTotallyNonnegativeMatrix_zero
    {k n' : ℕ} : IsTotallyNonnegativeMatrix (0 : Matrix (Fin k) (Fin n') ℝ) := by
  intro e _
  by_cases hk : k = 0
  · subst hk
    simp [Matrix.det_isEmpty]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have : (0 : Matrix (Fin k) (Fin n') ℝ).submatrix id e = 0 := by
      ext i j
      simp [Matrix.submatrix_apply]
    rw [this]
    rw [show (0 : Matrix (Fin k) (Fin k) ℝ).det = 0 from ?_]
    exact Matrix.det_zero ⟨⟨0, hkpos⟩⟩

/-- Rank-1 (single-row) case: a `1 × n'` matrix is totally positive iff
each entry is strictly positive (since each 1×1 minor is just an entry). -/
theorem isTotallyPositiveMatrix_one_row_iff {n' : ℕ}
    (A : Matrix (Fin 1) (Fin n') ℝ) :
    IsTotallyPositiveMatrix A ↔ ∀ j : Fin n', 0 < A 0 j := by
  constructor
  · intro hA j
    -- Build an injective e : Fin 1 → Fin n' mapping the unique element to j.
    have he : Function.Injective (fun _ : Fin 1 => j) := by
      intro a b _
      exact Subsingleton.elim a b
    have := hA (fun _ => j) he
    simp [Matrix.det_fin_one, Matrix.submatrix_apply] at this
    convert this using 1
  · intro hpos e _
    simp [Matrix.det_fin_one, Matrix.submatrix_apply]
    exact hpos (e 0)

end AmplituhedronPSD
