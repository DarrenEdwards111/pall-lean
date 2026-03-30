import PallLean.LatentCompilerLocality
import Mathlib.Tactic

/-!
# LatentCompilerExtraction

This file proves the exact behavior of the **current** latent compiler under the
simple layer extractions. The result is important:

*with the present placeholder gadgets, extraction is trivial.*

That is not failure; it precisely identifies the next real development target:
replace the selector/consistency gadgets by paper-style local gadgets whose
specialization recovers a nontrivial witness polynomial.
-/

namespace LatentCompilerExtraction

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompilerRoute
open LatentCompilerLocality

section SheetExtraction

/-- Under machine-layer extraction, every machine local gadget becomes `1`. -/
@[simp] theorem extractMachineLayer_machineLocalGadget
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    extractMachineLayer M n (machineLocalGadget M n i) =
      (1 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [machineLocalGadget, extractMachineLayer, Xmach, Xcopy]

/-- Under machine-layer extraction, every consistency local gadget becomes `1`. -/
@[simp] theorem extractMachineLayer_consistencyLocalGadget
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    extractMachineLayer M n (consistencyLocalGadget M n i) =
      (1 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [consistencyLocalGadget, extractMachineLayer, Xcopy, Xcon]

/-- Under selector-layer extraction, every consistency local gadget becomes `1`. -/
@[simp] theorem extractSelectorLayer_consistencyLocalGadget
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    extractSelectorLayer M n (consistencyLocalGadget M n i) =
      (1 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [consistencyLocalGadget, extractSelectorLayer, Xcopy, Xcon]

/-- Under selector-layer extraction, every selector local gadget becomes `1`. -/
@[simp] theorem extractSelectorLayer_selectorLocalGadget
    (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    extractSelectorLayer M n (selectorLocalGadget M n i) =
      (1 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [selectorLocalGadget, extractSelectorLayer, Xsel, Xcon]

/-- Hence the machine sheet collapses to `1` under machine extraction. -/
theorem extractMachineLayer_machineSheet
    (M : DTM) (n : ℕ) :
    extractMachineLayer M n (machineSheet M n) =
      (1 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [machineSheet]

/-- The consistency sheet also collapses to `1` under machine extraction. -/
theorem extractMachineLayer_consistencySheet
    (M : DTM) (n : ℕ) :
    extractMachineLayer M n (consistencySheet M n) =
      (1 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [consistencySheet]

/-- The selector sheet collapses to `1` under selector extraction. -/
theorem extractSelectorLayer_selectorSheet
    (M : DTM) (n : ℕ) :
    extractSelectorLayer M n (selectorSheet M n) =
      (1 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [selectorSheet]

/-- The consistency sheet also collapses to `1` under selector extraction. -/
theorem extractSelectorLayer_consistencySheet
    (M : DTM) (n : ℕ) :
    extractSelectorLayer M n (consistencySheet M n) =
      (1 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [consistencySheet]

end SheetExtraction

section CompiledPolyExtraction

/-- Current latent compiler under machine extraction is just the constant `3`. -/
theorem extractMachineLayer_latentCompiledPoly
    (M : DTM) (n : ℕ) :
    extractMachineLayer M n (latentCompiledPoly M n) =
      (3 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [latentCompiledPoly, extractMachineLayer_machineSheet,
    extractMachineLayer_consistencySheet, selectorSheet]

/-- Current latent compiler under selector extraction is also just the constant `3`. -/
theorem extractSelectorLayer_latentCompiledPoly
    (M : DTM) (n : ℕ) :
    extractSelectorLayer M n (latentCompiledPoly M n) =
      (3 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) := by
  simp [latentCompiledPoly, extractSelectorLayer_selectorSheet,
    extractSelectorLayer_consistencySheet, machineSheet]

/-- Consequence: the present placeholder latent compiler does **not** yet reveal a
nontrivial witness polynomial under extraction. This is the exact next replacement target. -/
theorem current_latent_extraction_is_trivial
    (M : DTM) (n : ℕ) :
    extractMachineLayer M n (latentCompiledPoly M n) =
      extractSelectorLayer M n (latentCompiledPoly M n) := by
  rw [extractMachineLayer_latentCompiledPoly, extractSelectorLayer_latentCompiledPoly]

end CompiledPolyExtraction

end LatentCompilerExtraction
