import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Basic

/-!
# Generalized gauge reducer: `IsAmplituhedronGauge A (satFamily n)` for an
arbitrary `n × n` matrix `A`

This file generalizes
`compiledGadget_isAmplituhedronGauge_satFamily_iff`
(see `IsAmplituhedronGaugeReducer.lean`) from the §28.3 compiled gadget
`compiledGadget α n` to an *arbitrary* real `n × n` matrix
`A : Matrix (Fin n) (Fin n) ℝ`. The proof technique used in the
compiled-gadget version does not actually depend on the structure of
`compiledGadget`: it only uses

* `A.PosDef`,
* `A.det = 1`, and
* the two-element family structure `satFamily n = {∅, Finset.univ}`.

We therefore restate the reducer for any matrix `A`, with the only
hypotheses being positive-definiteness and unit determinant. As an
optional converse, we also prove that `IsAmplituhedronGauge A (satFamily n)`
implies `A.PosDef ∧ A.det = 1` whenever `n ≥ 1`.

For `𝒥 = satFamily n = {∅, Finset.univ}` only two cases need to be
discharged:

* `J = ∅`: the principal submatrix is `0 × 0`, hence its determinant is
  `1` by `Matrix.det_isEmpty` (the indexing type `Fin 0` is empty).
* `J = Finset.univ`: the reindexing
  `e : Fin (Finset.univ).card ≃ {i // i ∈ Finset.univ}`
  composes with the canonical
  `Equiv.subtypeUnivEquiv : {i // i ∈ Finset.univ} ≃ Fin n`
  to a self-equivalence `φ : Fin (Finset.univ).card ≃ Fin n`. The
  principal minor then equals the full determinant by
  `Matrix.det_submatrix_equiv_self`, and the user's hypothesis
  `hDet : A.det = 1` finishes the goal.

The file is kernel-only: no `sorry`, no custom `axiom`; only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound` are introduced.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open Matrix

/-- **Generalized reducer: from `PosDef` and `det = 1` to the
amplituhedron gauge property for `satFamily n`, for *any* `n × n` real
matrix `A`.**

This is the matrix-agnostic analogue of
`compiledGadget_isAmplituhedronGauge_satFamily_iff`. The proof structure
is identical: unfold `IsAmplituhedronGauge`, split the family into the
two cases `J = ∅` and `J = Finset.univ` via `satFamily_subset_iff`, and
discharge:

* `J = ∅`: principal submatrix is `0 × 0`, det = 1 by
  `Matrix.det_isEmpty`.
* `J = Finset.univ`: principal submatrix det = full det by
  `Matrix.det_submatrix_equiv_self`, and the full det is `1` by
  `hDet`.

The hypothesis `hn : 1 ≤ n` is included for the user-facing API but is
not strictly necessary: the case split on `satFamily n` does not
require `n ≥ 1`. Including it keeps the signature aligned with the
non-vacuous existence statements at `n = 1, 2, …`. -/
theorem isAmplituhedronGauge_satFamily_iff
    (n : ℕ) (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hPos : A.PosDef)
    (hDet : A.det = 1) :
    IsAmplituhedronGauge A (satFamily n) := by
  -- Suppress unused-variable warning on `hn` (kept for user-facing API parity).
  let _ := hn
  refine ⟨hPos, ?_⟩
  intro J hJ e
  -- `satFamily n = {∅, Finset.univ}`, so `J = ∅` or `J = Finset.univ`.
  rw [satFamily_subset_iff] at hJ
  rcases hJ with hEmpty | hUniv
  · -- Case J = ∅: principal submatrix is 0×0, det = 1 by det_isEmpty.
    subst hEmpty
    -- `Fin (∅.card) = Fin 0` is empty.
    have hEmptyType : IsEmpty (Fin ((∅ : Finset (Fin n)).card)) := by
      rw [Finset.card_empty]
      exact Fin.isEmpty'
    exact Matrix.det_isEmpty
  · -- Case J = Finset.univ: principal submatrix det = full det = 1.
    subst hUniv
    -- Build the bijection φ : Fin (univ.card) ≃ Fin n as
    -- `e.trans (Equiv.subtypeUnivEquiv Finset.mem_univ)`.
    let u : (Finset.univ : Finset (Fin n)) ≃ Fin n :=
      Equiv.subtypeUnivEquiv (fun i : Fin n => Finset.mem_univ i)
    let φ : Fin (Finset.univ : Finset (Fin n)).card ≃ Fin n := e.trans u
    -- The underlying function of φ matches `fun i => (e i).1`.
    have hφ_apply : ∀ i, φ i = (e i).1 := by
      intro i
      rfl
    -- Pointwise equality of submatrices.
    have hsub_eq :
        A.submatrix
            (fun i => (e i).1) (fun i => (e i).1)
          = A.submatrix
              (fun i => φ i) (fun i => φ i) := by
      funext i j
      show A ((e i).1) ((e j).1)
        = A (φ i) (φ j)
      rw [hφ_apply i, hφ_apply j]
    rw [hsub_eq]
    -- `det (A.submatrix φ φ) = A.det` by `det_submatrix_equiv_self`.
    rw [Matrix.det_submatrix_equiv_self φ A]
    -- Goal: `A.det = 1`, given by hypothesis.
    exact hDet

/-- **Converse: an amplituhedron gauge for `satFamily n` is
positive-definite with unit determinant.**

If `A` is an amplituhedron gauge for the SAT family `satFamily n` and
`n ≥ 1`, then `A.PosDef ∧ A.det = 1`. The first conjunct is the first
component of the gauge property by definition. The second conjunct
follows by instantiating the principal-minor condition at
`J = Finset.univ ∈ satFamily n` with the canonical reindexing
`Equiv.subtypeUnivEquiv`, after which the principal minor equals
`A.det` via `Matrix.det_submatrix_equiv_self`.

The `n ≥ 1` hypothesis is *not* used in the proof itself but is kept in
the signature for API parity with the forward direction; the converse
in fact holds for all `n ≥ 0` (at `n = 0` the determinant `A.det = 1`
holds trivially since the matrix is `0 × 0`). -/
theorem isAmplituhedronGauge_satFamily_imp_posDef_det
    (n : ℕ) (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hGauge : IsAmplituhedronGauge A (satFamily n)) :
    A.PosDef ∧ A.det = 1 := by
  -- Suppress unused-variable warning on `hn` (kept for user-facing API parity).
  let _ := hn
  refine ⟨hGauge.1, ?_⟩
  -- Use the principal-minor condition at `J = Finset.univ`.
  have hUnivMem : (Finset.univ : Finset (Fin n)) ∈ satFamily n :=
    satFamily_mem_univ n
  -- Pick the canonical reindexing
  -- `e := (Equiv.subtypeUnivEquiv …).symm : Fin n ≃ {i // i ∈ Finset.univ}`,
  -- transported along `Finset.univ.card = n`.
  let u : (Finset.univ : Finset (Fin n)) ≃ Fin n :=
    Equiv.subtypeUnivEquiv (fun i : Fin n => Finset.mem_univ i)
  -- Cardinality rewrite: `Finset.univ.card = n` for `Fin n`.
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by
    rw [Finset.card_univ, Fintype.card_fin]
  -- Use the cardinality rewrite to build a reindexing
  -- `e : Fin (Finset.univ).card ≃ {i // i ∈ Finset.univ}`.
  let cEq : Fin (Finset.univ : Finset (Fin n)).card ≃ Fin n :=
    Fin.castOrderIso hcard |>.toEquiv
  let e : Fin (Finset.univ : Finset (Fin n)).card ≃
      {i // i ∈ (Finset.univ : Finset (Fin n))} :=
    cEq.trans u.symm
  -- Apply the principal-minor condition.
  have hMinor :=
    hGauge.2 (Finset.univ : Finset (Fin n)) hUnivMem e
  -- The reindexing `φ := e.trans u : Fin (univ).card ≃ Fin n`
  -- equals `cEq` by construction.
  let φ : Fin (Finset.univ : Finset (Fin n)).card ≃ Fin n := e.trans u
  have hφ_apply : ∀ i, φ i = (e i).1 := by
    intro i; rfl
  -- Rewrite the principal minor as a submatrix of `A` indexed by `φ`.
  have hsub_eq :
      A.submatrix (fun i => (e i).1) (fun i => (e i).1)
        = A.submatrix (fun i => φ i) (fun i => φ i) := by
    funext i j
    show A ((e i).1) ((e j).1) = A (φ i) (φ j)
    rw [hφ_apply i, hφ_apply j]
  -- Combine: `A.det = (submatrix φ φ).det = (submatrix e e).det = 1`.
  have hdet_eq : A.det = 1 := by
    have h1 : (A.submatrix (fun i => φ i) (fun i => φ i)).det = A.det :=
      Matrix.det_submatrix_equiv_self φ A
    -- From hMinor: the submatrix indexed by `e` has determinant 1.
    -- Rewrite into the φ-form.
    have h2 :
        (A.submatrix (fun i => φ i) (fun i => φ i)).det = 1 := by
      rw [← hsub_eq]; exact hMinor
    -- Combine to conclude `A.det = 1`.
    rw [← h1]; exact h2
  exact hdet_eq

/-- **Iff form: `IsAmplituhedronGauge A (satFamily n) ↔ A.PosDef ∧ A.det = 1`.**

Combines the forward direction (`isAmplituhedronGauge_satFamily_iff`)
and the converse (`isAmplituhedronGauge_satFamily_imp_posDef_det`)
into a single biconditional. This is the canonical Route C ⇒ Route A
(and back) characterization of the amplituhedron gauge property for
the SAT family `satFamily n` at any `n ≥ 1`. -/
theorem isAmplituhedronGauge_satFamily_iff_posDef_det
    (n : ℕ) (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    IsAmplituhedronGauge A (satFamily n) ↔ A.PosDef ∧ A.det = 1 := by
  refine ⟨isAmplituhedronGauge_satFamily_imp_posDef_det n hn A, ?_⟩
  rintro ⟨hPos, hDet⟩
  exact isAmplituhedronGauge_satFamily_iff n hn A hPos hDet

end PallLean.Paper93.DeepMath.PathB.Positroid
