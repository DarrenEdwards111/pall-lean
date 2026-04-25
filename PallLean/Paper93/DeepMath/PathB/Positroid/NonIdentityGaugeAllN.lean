import PallLean.Paper93.DeepMath.PathB.Positroid.R70DetGeneral
import PallLean.Paper93.DeepMath.PathB.Positroid.IVTGeneralN
import PallLean.Paper93.DeepMath.PathB.Positroid.IsAmplituhedronGaugeReducer
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import Mathlib.Tactic.Linarith

/-!
# Non-identity amplituhedron gauges for all `n >= 2`

The general determinant formula

`(compiledGadget α n).det = α * (α + n)^(n - 1)`

combines with the general IVT root

`α * (α + n)^(n - 1) = 1`

to produce a non-identity gauge witness for `satFamily n` at every
dimension `n >= 2`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **All-`n` non-identity gauge witness for `satFamily n`.**

For every `n >= 2`, there exists a real `n x n` matrix which is an
amplituhedron gauge for `satFamily n` and is not the identity.

The witness is `compiledGadget α n`, where `α` is the IVT-supplied
positive root of `α * (α + n)^(n - 1) = 1`. -/
theorem nonIdentity_gauge_all_n (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      IsAmplituhedronGauge A (satFamily n) ∧
        A ≠ (1 : Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨α, hα_pos, _hα_le, hα_eq⟩ := exists_alpha_general_n_det_one n hn
  refine ⟨compiledGadget α n, ?_, ?_⟩
  · have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℕ) ≤ 2) hn
    have hPos : (compiledGadget α n).PosDef :=
      compiledGadget_posDef α n hα_pos hn1
    have hDet : (compiledGadget α n).det = 1 := by
      rw [compiledGadget_det_general α n hn1]
      exact hα_eq
    exact compiledGadget_isAmplituhedronGauge_satFamily_iff
      α n hn1 hPos hDet
  · exact compiledGadget_ne_identity α n hn

/-- Explicit coupling form of `nonIdentity_gauge_all_n`. -/
theorem exists_alpha_nonIdentity_gauge_all_n (n : ℕ) (hn : 2 ≤ n) :
    ∃ (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ),
      0 < α ∧ A = compiledGadget α n ∧
        IsAmplituhedronGauge A (satFamily n) ∧
          A ≠ (1 : Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨α, hα_pos, _hα_le, hα_eq⟩ := exists_alpha_general_n_det_one n hn
  refine ⟨α, compiledGadget α n, hα_pos, rfl, ?_, ?_⟩
  · have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℕ) ≤ 2) hn
    have hPos : (compiledGadget α n).PosDef :=
      compiledGadget_posDef α n hα_pos hn1
    have hDet : (compiledGadget α n).det = 1 := by
      rw [compiledGadget_det_general α n hn1]
      exact hα_eq
    exact compiledGadget_isAmplituhedronGauge_satFamily_iff
      α n hn1 hPos hDet
  · exact compiledGadget_ne_identity α n hn

#print axioms nonIdentity_gauge_all_n

end PallLean.Paper93.DeepMath.PathB.Positroid
