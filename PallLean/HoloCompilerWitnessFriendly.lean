import PallLean.HoloCompilerDistinctPartition
import Mathlib.Tactic

/-!
# HoloCompilerWitnessFriendly

The first distinct holographic scaffold separated variables into layers, but its
simple factors were too weak: under verifier-layer extraction they collapsed to
constants. This file introduces a more witness-friendly local gadget family.

The purpose is not to claim completion of the paper's compiler, but to move from
"distinct but extraction-trivial" gadgets to "distinct and extraction-nontrivial"
gadgets that can plausibly support the paper's extraction route.
-/

namespace HoloCompilerWitnessFriendly

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open HoloCompilerDistinct
open HoloCompilerDistinctPartition

/-- A witness-friendly verifier factor: keeps a genuine verifier-layer term under extraction. -/
def wfVerifierFactor (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) : MvPolynomial (HoloVar M n) ℚ :=
  1 - Xver M n i

/-- A witness-friendly machine factor: keeps a genuine machine-layer term under extraction. -/
def wfMachineFactor (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) : MvPolynomial (HoloVar M n) ℚ :=
  1 - Xmach M n i

/-- Witness-friendly verifier sheet. -/
noncomputable def wfVerifierSheet (M : DTM) (n : ℕ) :
    MvPolynomial (HoloVar M n) ℚ :=
  ∏ i : Fin (holoBaseVars M n), wfVerifierFactor M n i

/-- Witness-friendly machine sheet. -/
noncomputable def wfMachineSheet (M : DTM) (n : ℕ) :
    MvPolynomial (HoloVar M n) ℚ :=
  ∏ i : Fin (holoBaseVars M n), wfMachineFactor M n i

/-- Witness-friendly distinct compiled object. -/
noncomputable def wfCompiledPoly (M : DTM) (n : ℕ) :
    MvPolynomial (HoloVar M n) ℚ :=
  wfVerifierSheet M n + wfMachineSheet M n

@[simp] theorem extractVerifierLayer_wfVerifierFactor (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    extractVerifierLayer M n (wfVerifierFactor M n i) = (1 - X i : MvPolynomial (Fin (holoBaseVars M n)) ℚ) := by
  simp [extractVerifierLayer, wfVerifierFactor, projectVerifier, Xver]

@[simp] theorem extractMachineLayer_wfMachineFactor (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    extractMachineLayer M n (wfMachineFactor M n i) = (1 - X i : MvPolynomial (Fin (holoBaseVars M n)) ℚ) := by
  simp [extractMachineLayer, wfMachineFactor, projectMachine, Xmach]

@[simp] theorem extractVerifierLayer_wfMachineFactor (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    extractVerifierLayer M n (wfMachineFactor M n i) = (1 : MvPolynomial (Fin (holoBaseVars M n)) ℚ) := by
  simp [extractVerifierLayer, wfMachineFactor, projectVerifier, Xmach]

@[simp] theorem extractMachineLayer_wfVerifierFactor (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    extractMachineLayer M n (wfVerifierFactor M n i) = (1 : MvPolynomial (Fin (holoBaseVars M n)) ℚ) := by
  simp [extractMachineLayer, wfVerifierFactor, projectMachine, Xver]

/-- Each witness-friendly verifier factor is strictly local: one duplicated variable only. -/
theorem wfVerifierFactor_vars_card_le_one (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    (wfVerifierFactor M n i).vars.card ≤ 1 := by
  simp [wfVerifierFactor]

/-- Each witness-friendly machine factor is strictly local: one duplicated variable only. -/
theorem wfMachineFactor_vars_card_le_one (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    (wfMachineFactor M n i).vars.card ≤ 1 := by
  simp [wfMachineFactor]

/-- Under verifier-layer extraction, the distinct verifier sheet becomes a concrete base-space product. -/
theorem extractVerifierLayer_wfVerifierSheet (M : DTM) (n : ℕ) :
    extractVerifierLayer M n (wfVerifierSheet M n) =
      ∏ i : Fin (holoBaseVars M n), (1 - X i : MvPolynomial (Fin (holoBaseVars M n)) ℚ) := by
  simp [wfVerifierSheet]

/-- Under machine-layer extraction, the distinct machine sheet becomes the analogous base-space product. -/
theorem extractMachineLayer_wfMachineSheet (M : DTM) (n : ℕ) :
    extractMachineLayer M n (wfMachineSheet M n) =
      ∏ i : Fin (holoBaseVars M n), (1 - X i : MvPolynomial (Fin (holoBaseVars M n)) ℚ) := by
  simp [wfMachineSheet]

end HoloCompilerWitnessFriendly
