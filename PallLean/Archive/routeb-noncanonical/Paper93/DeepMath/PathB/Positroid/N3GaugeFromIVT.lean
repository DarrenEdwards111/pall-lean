import PallLean.Paper93.DeepMath.PathB.Positroid.N3IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.PrincipalMinorAtUniv
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# A non-identity gauge witness for `satFamily 3` from the IVT

This file combines the existence result `exists_alpha_n3_det_one`
(which provides, via the Intermediate Value Theorem, a positive `α`
with `α (α + 3)² = 1`) with three structural facts about the §28.3
compiled gadget at `n = 3`:

* `compiledGadget_3x3_det`: the closed-form determinant
  `(compiledGadget α 3).det = α * (α + 3)^2`;
* `compiledGadget_posDef`: positive-definiteness of `compiledGadget α n`
  for `α > 0` and `n ≥ 1`;
* `compiledGadget_ne_identity`: the compiled gadget is never equal to
  the identity matrix for `n ≥ 2`.

Combined, these yield, for `n = 3`, the existence of a positive coupling
`α` such that `compiledGadget α 3` is a non-identity positive-definite
matrix with determinant `1`. This is the structural ingredient for a
non-trivial gauge witness for `satFamily 3 = {∅, Finset.univ}`: positive
definiteness handles the gauge `PosDef` clause, the empty principal
minor is automatically `1`, and the full principal minor coincides with
the determinant.

## Main theorems

* `exists_nonidentity_posDef_det_one_n3_ivt`: existence of a positive
  `α` and a matrix `A = compiledGadget α 3` which is `PosDef`, has
  `det A = 1`, and is not the identity.
* `exists_nontrivial_gauge_satFamily_n3`: the corollary forgetting the
  explicit witness `α` — there exists a non-identity positive-definite
  matrix on `Fin 3` with determinant `1`.

All results are kernel-only (axioms: `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **For `n = 3`, there exists a non-identity `PosDef` matrix with
determinant `1`, given concretely by `compiledGadget α 3` at the IVT
witness `α > 0`.**

Proof:

1. Apply `exists_alpha_n3_det_one` (IVT on `f(α) = α (α + 3)^2` over
   `[0, 1]`) to obtain `α > 0` with `α (α + 3)² = 1`.
2. Take `A := compiledGadget α 3`.
3. `PosDef`: `compiledGadget_posDef α 3 hα_pos (by norm_num : 1 ≤ 3)`.
4. `det A = 1`: rewrite by `compiledGadget_3x3_det` (giving
   `α * (α + 3)^2`) and apply the IVT equation `α (α + 3)² = 1`.
5. `A ≠ 1`: `compiledGadget_ne_identity α 3 (by norm_num : 2 ≤ 3)` —
   the off-diagonal `(0, 1)` entry of the compiled gadget is `-1`,
   regardless of `α`. -/
theorem exists_nonidentity_posDef_det_one_n3_ivt :
    ∃ (α : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ),
      0 < α ∧ A = compiledGadget α 3 ∧
      A.PosDef ∧ A.det = 1 ∧ A ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨α, hα_pos, _, hα_eq⟩ := exists_alpha_n3_det_one
  refine ⟨α, compiledGadget α 3, hα_pos, rfl, ?_, ?_, ?_⟩
  · exact compiledGadget_posDef α 3 hα_pos (by norm_num : (1 : ℕ) ≤ 3)
  · rw [compiledGadget_3x3_det]; exact hα_eq
  · exact compiledGadget_ne_identity α 3 (by norm_num : (2 : ℕ) ≤ 3)

/-- **Existence of a non-identity gauge witness for `satFamily 3`
(kernel-only, via the IVT).**

Forgetting the explicit witness `α`, there exists a `PosDef` matrix on
`Fin 3` with determinant `1` that is not the identity. Together with
the principal-minor structure of `satFamily 3 = {∅, Finset.univ}`
(empty minor is the vacuous determinant `1`; full minor is the matrix
determinant `= 1`), this gives the structural ingredient for a
non-trivial amplituhedron gauge witness at `n = 3`. -/
theorem exists_nontrivial_gauge_satFamily_n3 :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ,
      A.PosDef ∧ A.det = 1 ∧ A ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨α, A, _, _, hA_pd, hA_det, hA_ne⟩ :=
    exists_nonidentity_posDef_det_one_n3_ivt
  exact ⟨A, hA_pd, hA_det, hA_ne⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
