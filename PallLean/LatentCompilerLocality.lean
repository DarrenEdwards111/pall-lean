import PallLean.LatentCompilerRoute
import Mathlib.Tactic

/-!
# LatentCompilerLocality

Small, genuinely proved facts for the corrected latent compiler route.

These do not finish the paper's holographic compiler, but they establish that the
raw latent object really is assembled from tiny local gadgets and that the simple
layer projections behave as intended.
-/

namespace LatentCompilerLocality

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompilerRoute

section GadgetLocality

/-- Each machine local gadget mentions at most two variables. -/
theorem machineLocalGadget_vars_card_le_two (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    (machineLocalGadget M n i).vars.card ≤ 2 := by
  simp [machineLocalGadget, Xmach, Xcopy]

/-- Each consistency local gadget mentions at most two variables. -/
theorem consistencyLocalGadget_vars_card_le_two (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    (consistencyLocalGadget M n i).vars.card ≤ 2 := by
  simp [consistencyLocalGadget, Xcopy, Xcon]

/-- Each selector local gadget mentions at most two variables. -/
theorem selectorLocalGadget_vars_card_le_two (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    (selectorLocalGadget M n i).vars.card ≤ 2 := by
  simp [selectorLocalGadget, Xsel, Xcon]

end GadgetLocality

section PartitionFacts

@[simp] theorem latentPartition_assign_machine
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    (latentPartition M n).assign (LatentLayer.machine, i) = ⟨i.1, i.2⟩ := rfl

@[simp] theorem latentPartition_assign_copy
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    (latentPartition M n).assign (LatentLayer.copy, i) = ⟨i.1, i.2⟩ := rfl

@[simp] theorem latentPartition_assign_selector
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    (latentPartition M n).assign (LatentLayer.selector, i) = ⟨i.1, i.2⟩ := rfl

@[simp] theorem latentPartition_assign_consistency
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    (latentPartition M n).assign (LatentLayer.consistency, i) = ⟨i.1, i.2⟩ := rfl

/-- All four layer copies of one base index lie in the same block. -/
theorem same_base_same_block_all_layers
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    (latentPartition M n).assign (LatentLayer.machine, i) = (latentPartition M n).assign (LatentLayer.copy, i) ∧
    (latentPartition M n).assign (LatentLayer.machine, i) = (latentPartition M n).assign (LatentLayer.selector, i) ∧
    (latentPartition M n).assign (LatentLayer.machine, i) = (latentPartition M n).assign (LatentLayer.consistency, i) := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

end PartitionFacts

section ExtractionFacts

@[simp] theorem extractSelectorLayer_Xcopy_zero
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    extractSelectorLayer M n (Xcopy M n i) = 0 := by
  simp [extractSelectorLayer, Xcopy]

@[simp] theorem extractSelectorLayer_Xcon_zero
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    extractSelectorLayer M n (Xcon M n i) = 0 := by
  simp [extractSelectorLayer, Xcon]

@[simp] theorem extractMachineLayer_Xcopy_zero
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    extractMachineLayer M n (Xcopy M n i) = 0 := by
  simp [extractMachineLayer, Xcopy]

@[simp] theorem extractMachineLayer_Xcon_zero
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    extractMachineLayer M n (Xcon M n i) = 0 := by
  simp [extractMachineLayer, Xcon]

@[simp] theorem extractSelectorLayer_selectorLocalGadget
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    extractSelectorLayer M n (selectorLocalGadget M n i) = (1 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [selectorLocalGadget, extractSelectorLayer, Xsel, Xcon]

@[simp] theorem extractMachineLayer_machineLocalGadget
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    extractMachineLayer M n (machineLocalGadget M n i) = (1 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [machineLocalGadget, extractMachineLayer, Xmach, Xcopy]

end ExtractionFacts

end LatentCompilerLocality
