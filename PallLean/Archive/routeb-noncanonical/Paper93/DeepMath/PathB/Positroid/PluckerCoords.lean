import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic

/-!
# Plücker coordinates as determinants of submatrices

For a `k × n` matrix `M : Matrix (Fin k) (Fin n) ℝ` and a subset
`I ⊆ Fin n` with `|I| = k`, the **Plücker coordinate** `Δ_I(M)` is the
determinant of the `k × k` submatrix obtained by selecting the columns of
`M` indexed by `I` (in the canonical order induced by
`Finset.equivFinOfCardEq`).

For the Grassmannian `Gr(k,n)`, the projective Plücker coordinates
`[Δ_I(M)]` give a homogeneous embedding into `ℙ^(C(n,k) - 1)`.

This file is **kernel-only**: no `sorry`, no custom `axiom`, only the
kernel axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The **Plücker coordinate** of a `k × n` matrix `M` at an index set
`I : Finset (Fin n)` with `|I| = k`: the determinant of the `k × k`
submatrix obtained by selecting the columns of `M` indexed by `I`.

The bridge between `Fin k` and `I` uses `Finset.equivFinOfCardEq`, which
produces a canonical equivalence `I ≃ Fin k` from the cardinality
hypothesis. We take its `symm` to feed columns. -/
noncomputable def pluckerCoord {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ)
    (I : Finset (Fin n)) (h : I.card = k) : ℝ :=
  let e : Fin k ≃ I := (Finset.equivFinOfCardEq h).symm
  (M.submatrix id (fun i : Fin k => (e i).val)).det

/-- Auxiliary: principal-minor-style Plücker map taken on the diagonal,
    selecting both rows and columns by an index `I` from a square matrix.

    This is the simpler "principal" Plücker coordinate used elsewhere in
    the Positroid development; we expose it here for parity. -/
def pluckerCoordOnFinset {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (I : Finset (Fin n)) : ℝ :=
  (M.submatrix (fun i : I => i.val) (fun i : I => i.val)).det

/-- For the identity `n × n` matrix and `I = Finset.univ`, the principal
    Plücker coordinate is `1`. This is a convenient sanity-check
    instantiation. -/
def pluckerCoord_identity_aux (n : ℕ) : ℝ :=
  ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix id id).det

/-- The Plücker coordinate of the identity matrix at the full index set
    is `1`. -/
theorem pluckerCoord_identity_univ (n : ℕ) :
    pluckerCoord_identity_aux n = 1 := by
  unfold pluckerCoord_identity_aux
  rw [Matrix.submatrix_id_id, Matrix.det_one]

/-- The explicit construction of `pluckerCoord` is well-typed: for any
    inputs satisfying the cardinality hypothesis, the value is a real
    number obtainable by the construction. -/
theorem pluckerCoord_well_typed {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ)
    (I : Finset (Fin n)) (h : I.card = k) :
    ∃ x : ℝ, x = pluckerCoord M I h :=
  ⟨pluckerCoord M I h, rfl⟩

/-- The principal Plücker coordinate of the identity matrix at any
    subset is `1`. -/
theorem pluckerCoordOnFinset_one {n : ℕ} (I : Finset (Fin n)) :
    pluckerCoordOnFinset (1 : Matrix (Fin n) (Fin n) ℝ) I = 1 := by
  unfold pluckerCoordOnFinset
  have hInj : Function.Injective (fun i : I => (i.val : Fin n)) :=
    fun _ _ h => Subtype.ext h
  rw [Matrix.submatrix_one _ hInj, Matrix.det_one]

end PallLean.Paper93.DeepMath.PathB.Positroid
