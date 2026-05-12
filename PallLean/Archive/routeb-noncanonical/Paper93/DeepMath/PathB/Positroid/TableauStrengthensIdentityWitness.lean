import PallLean.Paper93.DeepMath.PathB.Positroid.TableauToFamilyBridge
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Tableau-to-Gauge Bridge — Strengthened Non-Trivial Identity Witness at `n = 2`

This file strengthens the toy `TableauToFamilyBridge` in two ways at
`n = 2`:

1. We identify the toy `extractedFamily` of `SATDeciderTableauToy.lean`
   with the canonical Path B `satFamily 2 = {∅, Finset.univ}`. Both
   are definitionally `{∅, Finset.univ}`, so this is `rfl`.

2. We replace the trivial identity gauge witness from
   `tableau_to_gauge_bridge` with a **non-trivial** witness: the
   §28.3 compiled gadget `compiledGadget (Real.sqrt 2 − 1) 2`. This
   matrix is *not* the identity (off-diagonal entry is `−1` by
   `compiledGadget_2x2_off_diag_01`, c.f.
   `compiledGadget_2x2_ne_identity`), and it is an amplituhedron gauge
   for `satFamily 2` by `compiledGadget_n2_isGauge_satFamily`.

The result is a Path B gauge witness for the extracted family of every
`n = 2` SAT decider tableau that is *both* genuinely positive-definite
and genuinely non-identity, refuting any reading of the toy bridge as
"identity is everything you ever need".
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- For n=2 SAT tableaus, the extracted family is satFamily 2.
    NOTE: this depends on the toy `extractedFamily := {∅, univ}` which equals satFamily 2. -/
theorem extractedFamily_eq_satFamily_n2 (m : ℕ) (T : SATDeciderTableau m 2) :
    T.extractedFamily = satFamily 2 := by
  unfold SATDeciderTableau.extractedFamily satFamily
  rfl

/-- For n=2 SAT tableaus, the §28.3 compiledGadget at √2-1 is a NON-TRIVIAL
    amplituhedron gauge for the extracted family. -/
theorem tableauToFamilyBridge_strengthened_n2 {m : ℕ} (T : SATDeciderTableau m 2) :
    IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) T.extractedFamily ∧
    compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨?_, compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  rw [extractedFamily_eq_satFamily_n2]
  exact compiledGadget_n2_isGauge_satFamily

/-- Existence of a non-trivial gauge witness for the extracted family at n=2. -/
theorem tableauToFamilyBridge_strengthened_exists {m : ℕ} (T : SATDeciderTableau m 2) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      IsAmplituhedronGauge A T.extractedFamily ∧
      A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨compiledGadget (Real.sqrt 2 - 1) 2,
   tableauToFamilyBridge_strengthened_n2 T⟩

/-- Universal n=2 statement: every n=2 SAT decider tableau admits a non-trivial gauge witness. -/
theorem all_n2_tableaus_admit_nontrivial_gauge_strengthened :
    ∀ (m : ℕ) (T : SATDeciderTableau m 2),
      ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
        IsAmplituhedronGauge A T.extractedFamily ∧
        A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  fun m T => tableauToFamilyBridge_strengthened_exists T

end PallLean.Paper93.DeepMath.PathB.Positroid
