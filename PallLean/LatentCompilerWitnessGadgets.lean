import PallLean.LatentCompilerExtraction
import Mathlib.Tactic

/-!
# LatentCompilerWitnessGadgets

The previous latent compiler placeholders extracted to constants. This file makes the
next big correction: a new latent gadget family whose selector-layer extraction is
**nontrivial** and yields an explicit product on the base variable space.

This still does not claim the full paper compiler is done. It does, however, replace
"trivial extraction" by a concrete extraction-visible witness layer on the corrected
latent architecture.
-/

namespace LatentCompilerWitnessGadgets

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompilerRoute

section WitnessGadgets

variable (M : DTM) (n : ℕ)

/-- A selector-visible latent gadget: survives selector extraction as `1 - X i`. -/
def selectorWitnessGadget (i : Fin (latentBaseVars M n)) :
    MvPolynomial (LatentVar M n) ℚ :=
  1 - Xsel M n i

/-- A machine-visible latent gadget: survives machine extraction as `1 - X i`. -/
def machineWitnessGadget (i : Fin (latentBaseVars M n)) :
    MvPolynomial (LatentVar M n) ℚ :=
  1 - Xmach M n i

/-- Latent witness sheet on the selector layer. -/
noncomputable def selectorWitnessSheet :
    MvPolynomial (LatentVar M n) ℚ :=
  ∏ i : Fin (latentBaseVars M n), selectorWitnessGadget M n i

/-- Latent machine sheet on the machine layer. -/
noncomputable def machineWitnessSheet :
    MvPolynomial (LatentVar M n) ℚ :=
  ∏ i : Fin (latentBaseVars M n), machineWitnessGadget M n i

/-- Improved latent compiled polynomial: keep the local machine and consistency sheets,
but replace the extraction-trivial selector sheet by an extraction-visible witness sheet. -/
noncomputable def latentCompiledPolyW :
    MvPolynomial (LatentVar M n) ℚ :=
  machineSheet M n + consistencySheet M n + selectorWitnessSheet M n

end WitnessGadgets

section BasicFacts

variable (M : DTM) (n : ℕ)

/-- Each selector-visible witness gadget is strictly local. -/
theorem selectorWitnessGadget_vars_card_le_one
    (i : Fin (latentBaseVars M n)) :
    (selectorWitnessGadget M n i).vars.card ≤ 1 := by
  simp [selectorWitnessGadget, Xsel]

/-- Each machine-visible witness gadget is strictly local. -/
theorem machineWitnessGadget_vars_card_le_one
    (i : Fin (latentBaseVars M n)) :
    (machineWitnessGadget M n i).vars.card ≤ 1 := by
  simp [machineWitnessGadget, Xmach]

@[simp] theorem extractSelectorLayer_selectorWitnessGadget
    (i : Fin (latentBaseVars M n)) :
    extractSelectorLayer M n (selectorWitnessGadget M n i) =
      (1 - X i : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [extractSelectorLayer, selectorWitnessGadget, Xsel]

@[simp] theorem extractMachineLayer_machineWitnessGadget
    (i : Fin (latentBaseVars M n)) :
    extractMachineLayer M n (machineWitnessGadget M n i) =
      (1 - X i : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [extractMachineLayer, machineWitnessGadget, Xmach]

@[simp] theorem extractMachineLayer_selectorWitnessGadget
    (i : Fin (latentBaseVars M n)) :
    extractMachineLayer M n (selectorWitnessGadget M n i) =
      (1 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [extractMachineLayer, selectorWitnessGadget, Xsel]

@[simp] theorem extractSelectorLayer_machineWitnessGadget
    (i : Fin (latentBaseVars M n)) :
    extractSelectorLayer M n (machineWitnessGadget M n i) =
      (1 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [extractSelectorLayer, machineWitnessGadget, Xmach]

end BasicFacts

section SheetExtraction

variable (M : DTM) (n : ℕ)

/-- Selector extraction of the new witness sheet is a concrete base-space product. -/
theorem extractSelectorLayer_selectorWitnessSheet :
    extractSelectorLayer M n (selectorWitnessSheet M n) =
      ∏ i : Fin (latentBaseVars M n),
        (1 - X i : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [selectorWitnessSheet]

/-- Machine extraction of the machine witness sheet is the analogous product. -/
theorem extractMachineLayer_machineWitnessSheet :
    extractMachineLayer M n (machineWitnessSheet M n) =
      ∏ i : Fin (latentBaseVars M n),
        (1 - X i : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [machineWitnessSheet]

/-- The improved latent compiled object no longer extracts to a constant on the selector side:
it extracts to the witness product plus two constant sheets. -/
theorem extractSelectorLayer_latentCompiledPolyW :
    extractSelectorLayer M n (latentCompiledPolyW M n) =
      (2 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) +
      ∏ i : Fin (latentBaseVars M n), (1 - X i : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [latentCompiledPolyW, extractSelectorLayer_selectorWitnessSheet,
    extractSelectorLayer_consistencySheet, machineSheet]

/-- Likewise on the machine side. -/
theorem extractMachineLayer_latentCompiledPolyW :
    extractMachineLayer M n (latentCompiledPolyW M n) =
      (2 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) +
      ∏ i : Fin (latentBaseVars M n), (1 - X i : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [latentCompiledPolyW, extractMachineLayer_machineSheet,
    extractMachineLayer_consistencySheet, selectorWitnessSheet]

end SheetExtraction

end LatentCompilerWitnessGadgets
