import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.Positroid.IsAmplituhedronGaugeReducer
import PallLean.Paper93.DeepMath.PathB.Positroid.IVTGeneralN
import Mathlib.Tactic

/-!
# R70: all-`n` SAT-family gauges from algebraic conditions

This file packages the SAT-family gauge reduction needed by the R70 branch.
The substantive reducer is already proved in
`IsAmplituhedronGaugeReducer`: for `satFamily n`, positive-definiteness and
unit determinant are exactly the two algebraic facts needed to discharge the
two principal-minor constraints `∅` and `Finset.univ`.

We add two all-`n` wrappers:

* an algebraic theorem for any `α` and `n ≥ 1`; the nonidentity hypothesis is
  carried as part of the nontrivial compiled-gadget package, but the gauge
  proof itself only uses `PosDef` and `det = 1`;
* an IVT-based existence theorem for every `n ≥ 2`, conditional on the
  standard determinant formula
  `(compiledGadget α n).det = α * (α + n)^(n - 1)`.

The final theorem includes the `n = 1` endpoint, where the determinant-one
compiled gadget witness is `α = 1`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Algebraic all-`n` gauge theorem for the compiled gadget.

For `satFamily n`, the nonidentity fact is orthogonal to the principal-minor
proof: `PosDef` and `det = 1` imply the amplituhedron gauge property. The
nonidentity hypothesis is retained in the API so callers can pass the full
nontrivial compiled-gadget algebraic package without repacking it. -/
theorem compiledGadget_satFamily_gauge_of_posDef_det_nonidentity
    (α : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hPos : (compiledGadget α n).PosDef)
    (hDet : (compiledGadget α n).det = 1)
    (_hNonId : compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) :
    IsAmplituhedronGauge (compiledGadget α n) (satFamily n) :=
  compiledGadget_isAmplituhedronGauge_satFamily_iff α n hn hPos hDet

/-- Bundled form preserving the nonidentity conclusion. -/
theorem compiledGadget_satFamily_nonidentity_gauge_of_posDef_det_nonidentity
    (α : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hPos : (compiledGadget α n).PosDef)
    (hDet : (compiledGadget α n).det = 1)
    (hNonId : compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) :
    IsAmplituhedronGauge (compiledGadget α n) (satFamily n) ∧
      compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ) := by
  exact ⟨compiledGadget_satFamily_gauge_of_posDef_det_nonidentity
      α n hn hPos hDet hNonId,
    hNonId⟩

/-- IVT plus the determinant formula gives a nonidentity SAT-family gauge for
every `n ≥ 2`.

The IVT theorem supplies a positive root of
`α * (α + n)^(n - 1) = 1`. Under the determinant formula hypothesis, that root
has compiled-gadget determinant `1`; positive `α` gives `PosDef`, and
`n ≥ 2` gives nonidentity by the off-diagonal entry argument. -/
theorem exists_nonidentity_compiledGadget_satFamily_gauge_of_ivt_det_formula
    (n : ℕ) (hn : 2 ≤ n)
    (hDetFormula :
      ∀ α : ℝ, (compiledGadget α n).det = α * (α + n) ^ (n - 1)) :
    ∃ α : ℝ,
      0 < α ∧
      α ≤ 1 ∧
      IsAmplituhedronGauge (compiledGadget α n) (satFamily n) ∧
      compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ) ∧
      (compiledGadget α n).det = 1 := by
  obtain ⟨α, hα_pos, hα_le_one, hα_poly⟩ :=
    exists_alpha_general_n_det_one n hn
  have hn1 : 1 ≤ n := by omega
  have hPos : (compiledGadget α n).PosDef :=
    compiledGadget_posDef α n hα_pos hn1
  have hDet : (compiledGadget α n).det = 1 := by
    rw [hDetFormula α]
    exact hα_poly
  have hNonId : compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ) :=
    compiledGadget_ne_identity α n hn
  have hGauge : IsAmplituhedronGauge (compiledGadget α n) (satFamily n) :=
    compiledGadget_satFamily_gauge_of_posDef_det_nonidentity
      α n hn1 hPos hDet hNonId
  exact ⟨α, hα_pos, hα_le_one, hGauge, hNonId, hDet⟩

/-- All nonempty dimensions have a SAT-family compiled-gadget gauge, provided
the standard determinant formula is available in every `n ≥ 2`.

At `n = 1`, the witness is `α = 1`. At `n ≥ 2`, the witness is obtained by
the IVT theorem and the supplied determinant formula. This theorem does not
claim nonidentity at `n = 1`; determinant one forces the 1×1 compiled-gadget
witness to be the identity matrix. -/
theorem exists_compiledGadget_satFamily_gauge_all_n_of_ivt_det_formula
    (n : ℕ) (hn : 1 ≤ n)
    (hDetFormula :
      2 ≤ n →
        ∀ α : ℝ, (compiledGadget α n).det = α * (α + n) ^ (n - 1)) :
    ∃ α : ℝ,
      0 < α ∧
      α ≤ 1 ∧
      IsAmplituhedronGauge (compiledGadget α n) (satFamily n) ∧
      (compiledGadget α n).det = 1 := by
  by_cases hn2 : 2 ≤ n
  · obtain ⟨α, hα_pos, hα_le_one, hGauge, _hNonId, hDet⟩ :=
      exists_nonidentity_compiledGadget_satFamily_gauge_of_ivt_det_formula
        n hn2 (hDetFormula hn2)
    exact ⟨α, hα_pos, hα_le_one, hGauge, hDet⟩
  · have hn_eq_one : n = 1 := by omega
    subst n
    refine ⟨1, by norm_num, by norm_num, ?_, compiledGadget_1x1_det_one_at_alpha_one⟩
    exact compiledGadget_isAmplituhedronGauge_satFamily_iff
      1 1 (by norm_num)
      (compiledGadget_posDef 1 1 (by norm_num) (by norm_num))
      compiledGadget_1x1_det_one_at_alpha_one

end PallLean.Paper93.DeepMath.PathB.Positroid
