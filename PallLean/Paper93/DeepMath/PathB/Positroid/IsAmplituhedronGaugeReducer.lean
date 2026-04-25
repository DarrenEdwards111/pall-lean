import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Basic

/-!
# Reducer: `IsAmplituhedronGauge (compiledGadget α n) (satFamily n)` from
positive-definiteness and unit-determinant

This kernel-only file packages the boilerplate reduction:

```
compiledGadget α n is PosDef ∧ (compiledGadget α n).det = 1
   ⇒  IsAmplituhedronGauge (compiledGadget α n) (satFamily n)
```

The `satFamily` is the two-element family `{∅, Finset.univ}` defined in
`SatFamilyDefinition.lean`, and `IsAmplituhedronGauge A 𝒥` (defined in
`GaugePropertyDef.lean`) is the conjunction:

* `A.PosDef`;
* For every `J ∈ 𝒥` and every reindexing `e : Fin J.card ≃ {i // i ∈ J}`,
  the principal minor
  `(A.submatrix (fun i => (e i).1) (fun i => (e i).1)).det` equals `1`.

For `𝒥 = satFamily n = {∅, Finset.univ}` only two cases need to be
discharged:

* `J = ∅`: the principal submatrix is `0×0`, hence its determinant is
  `1` by `Matrix.det_isEmpty` (the indexing type `Fin 0` is empty).
* `J = Finset.univ`: the reindexing
  `e : Fin (Finset.univ).card ≃ {i // i ∈ Finset.univ}`
  composes with the canonical
  `Equiv.subtypeUnivEquiv : {i // i ∈ Finset.univ} ≃ Fin n`
  to a self-equivalence `φ : Fin n ≃ Fin n` (after rewriting
  `Finset.univ.card = n`). The principal minor then equals the full
  determinant by `Matrix.det_submatrix_equiv_self`, and the user's
  hypothesis `hDet : (compiledGadget α n).det = 1` finishes the goal.

This reducer is the canonical "Route C ⇒ Route A" boilerplate for the
truncated NS / SAT decider gadget at any `n ≥ 1`: the hard work is
positive definiteness and the closed-form unit determinant; everything
else is the two-case split on `satFamily n`.

The file is kernel-only: no `sorry`, no custom `axiom`; only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound` are introduced.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **Reducer: from `PosDef` and `det = 1` to the amplituhedron gauge
property for `satFamily n`.**

Given `n ≥ 1`, if the §28.3 compiled gadget `compiledGadget α n` is
positive definite and has determinant `1`, then it is an amplituhedron
gauge for the SAT family `satFamily n = {∅, Finset.univ}`.

The proof unfolds `IsAmplituhedronGauge`, splits the family into the two
cases `J = ∅` and `J = Finset.univ` via `satFamily_subset_iff`, and
discharges:

* `J = ∅`: principal submatrix is `0×0`, det = 1 by
  `Matrix.det_isEmpty`.
* `J = Finset.univ`: principal submatrix det = full det by
  `Matrix.det_submatrix_equiv_self`, and the full det is `1` by
  `hDet`.

The hypothesis `hn : 1 ≤ n` is included for the user-facing API but is
not strictly necessary for the proof: the case split on `satFamily n`
does not require `n ≥ 1`. Including it keeps the lemma signature aligned
with the non-vacuous existence statements at `n = 1, 2, …`. -/
theorem compiledGadget_isAmplituhedronGauge_satFamily_iff
    (α : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hPos : (compiledGadget α n).PosDef)
    (hDet : (compiledGadget α n).det = 1) :
    IsAmplituhedronGauge (compiledGadget α n) (satFamily n) := by
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
        (compiledGadget α n).submatrix
            (fun i => (e i).1) (fun i => (e i).1)
          = (compiledGadget α n).submatrix
              (fun i => φ i) (fun i => φ i) := by
      funext i j
      show compiledGadget α n ((e i).1) ((e j).1)
        = compiledGadget α n (φ i) (φ j)
      rw [hφ_apply i, hφ_apply j]
    rw [hsub_eq]
    -- `det (A.submatrix φ φ) = A.det` by `det_submatrix_equiv_self`.
    rw [Matrix.det_submatrix_equiv_self φ (compiledGadget α n)]
    -- Goal: `(compiledGadget α n).det = 1`, given by hypothesis.
    exact hDet

end PallLean.Paper93.DeepMath.PathB.Positroid
