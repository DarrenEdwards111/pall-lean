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

end AmplituhedronPSD
