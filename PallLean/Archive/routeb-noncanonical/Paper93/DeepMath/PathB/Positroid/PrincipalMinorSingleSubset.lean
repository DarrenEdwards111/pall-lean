import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract
import PallLean.Paper93.DeepMath.PathB.PrincipalMinorAtUniv
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Structural facts about principal minors at a single subset

This kernel-only file collects three structural facts about the principal
minor map `principalMinor` defined in
`PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract`:

* `principalMinor_zero_at_nonempty` — the principal minor of the zero
  matrix at any non-empty subset `J` is `0`, since the corresponding
  principal submatrix is the zero matrix on the non-empty index type
  `↥J`, whose determinant is `0` by `Matrix.det_zero`.

* `principalMinor_zero_at_empty` — the principal minor of the zero
  matrix at the empty subset is `1`, recovering `principalMinor_empty`
  applied to the zero matrix.

* `identity_principalMinor_unit` — the principal minor of the identity
  matrix at any subset `J` is `1`, recovering `principalMinor_one`.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The principal minor of the zero matrix at any non-empty `J` is `0`. -/
theorem principalMinor_zero_at_nonempty {n : ℕ} (J : Finset (Fin n)) (hJ : J.Nonempty) :
    principalMinor (0 : Matrix (Fin n) (Fin n) ℝ) J = 0 := by
  unfold principalMinor
  -- The submatrix of the zero matrix at any `J` is definitionally the zero
  -- matrix on `↥J`, which has determinant `0` whenever `↥J` is non-empty.
  rw [show (0 : Matrix (Fin n) (Fin n) ℝ).submatrix
        (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n)) =
       (0 : Matrix J J ℝ) from rfl]
  obtain ⟨i, hi⟩ := hJ
  have : Nonempty J := ⟨⟨i, hi⟩⟩
  exact Matrix.det_zero this

/-- The principal minor of the zero matrix at the empty subset is `1`. -/
theorem principalMinor_zero_at_empty (n : ℕ) :
    principalMinor (0 : Matrix (Fin n) (Fin n) ℝ) ∅ = 1 :=
  principalMinor_empty 0

/-- The principal minor of the identity matrix at any subset is `1`. -/
theorem identity_principalMinor_unit {n : ℕ} (J : Finset (Fin n)) :
    principalMinor (1 : Matrix (Fin n) (Fin n) ℝ) J = 1 :=
  principalMinor_one J

end PallLean.Paper93.DeepMath.PathB.Positroid
