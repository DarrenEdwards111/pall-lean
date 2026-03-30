import PallLean.HoloCompilerDistinctPartition
import Mathlib.Tactic

/-!
# HoloCompilerWitnessFriendly — Distinct-layer witness-friendly gadgets

Uses the `Fin (distinctNumVars M n)` encoding from HoloCompilerDistinctPartition.
Defines verifier/machine factors on the distinct variable space and proves
basic extraction/locality lemmas.
-/

namespace HoloCompilerWitnessFriendly

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open HoloCompilerDistinctPartition

/-- Witness-friendly verifier factor: (1 - X_{ver(i)}) on distinct space. -/
noncomputable def wfVerifierFactor (M : DTM) (n : ℕ)
    (i : Fin (HoloCompilerDistinct.holoBaseVars M n)) :
    MvPolynomial (Fin (distinctNumVars M n)) ℚ :=
  1 - XVer M n i

/-- Witness-friendly machine factor: (1 - X_{mach(i)}) on distinct space. -/
noncomputable def wfMachineFactor (M : DTM) (n : ℕ)
    (i : Fin (HoloCompilerDistinct.holoBaseVars M n)) :
    MvPolynomial (Fin (distinctNumVars M n)) ℚ :=
  1 - XMach M n i

/-- Witness-friendly verifier sheet: product of all verifier factors. -/
noncomputable def wfVerifierSheet (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (distinctNumVars M n)) ℚ :=
  ∏ i : Fin (HoloCompilerDistinct.holoBaseVars M n), wfVerifierFactor M n i

/-- Witness-friendly machine sheet: product of all machine factors. -/
noncomputable def wfMachineSheet (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (distinctNumVars M n)) ℚ :=
  ∏ i : Fin (HoloCompilerDistinct.holoBaseVars M n), wfMachineFactor M n i

/-- Witness-friendly compiled polynomial on distinct variable space. -/
noncomputable def wfCompiledPoly (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (distinctNumVars M n)) ℚ :=
  wfVerifierSheet M n + wfMachineSheet M n

/-- Verifier extraction sends verifier factor to (1 - X_i) on base space. -/
theorem extractVer_wfVerifierFactor (M : DTM) (n : ℕ)
    (i : Fin (HoloCompilerDistinct.holoBaseVars M n)) :
    extractVerifierLayer M n (wfVerifierFactor M n i) =
      (1 - X i : MvPolynomial (Fin (HoloCompilerDistinct.holoBaseVars M n)) ℚ) := by
  unfold wfVerifierFactor
  rw [map_sub, map_one, extractVerifierLayer_XVer]

/-- Verifier extraction kills machine factor (sends to 1). -/
theorem extractVer_wfMachineFactor (M : DTM) (n : ℕ)
    (i : Fin (HoloCompilerDistinct.holoBaseVars M n)) :
    extractVerifierLayer M n (wfMachineFactor M n i) =
      (1 : MvPolynomial (Fin (HoloCompilerDistinct.holoBaseVars M n)) ℚ) := by
  unfold wfMachineFactor
  rw [map_sub, map_one, extractVerifierLayer_XMach, sub_zero]

/-- Each verifier factor touches exactly 1 variable (locality). -/
theorem wfVerifierFactor_vars_le (M : DTM) (n : ℕ)
    (i : Fin (HoloCompilerDistinct.holoBaseVars M n)) :
    (wfVerifierFactor M n i).vars.card ≤ 1 := by
  simp [wfVerifierFactor, XVer, verSlot]

/-- Each machine factor touches exactly 1 variable (locality). -/
theorem wfMachineFactor_vars_le (M : DTM) (n : ℕ)
    (i : Fin (HoloCompilerDistinct.holoBaseVars M n)) :
    (wfMachineFactor M n i).vars.card ≤ 1 := by
  simp [wfMachineFactor, XMach, machSlot]

end HoloCompilerWitnessFriendly
