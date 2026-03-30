import PallLean.HoloCompilerDistinctLocality
import Mathlib.Tactic

/-!
# HoloCompilerWitnessFriendly

Witness-friendly base-space gadget family used by the distinct-route scaffold.

This module provides concrete base-space polynomials over `Fin (holoBaseVars M n)`
that serve as extraction targets for the Fin-indexed distinct-layer compiled object.
-/

namespace HoloCompilerWitnessFriendly

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open HoloCompilerDistinct
open HoloCompilerDistinctPartition
open HoloCompilerDistinctLocality

/-- Witness-friendly verifier factor on the base variable space. -/
noncomputable def wfVerifierFactor (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) : MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  1 - X i

/-- Witness-friendly machine factor on the base variable space. -/
noncomputable def wfMachineFactor (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) : MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  1 - X i

/-- Witness-friendly verifier sheet. -/
noncomputable def wfVerifierSheet (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  ∏ i : Fin (holoBaseVars M n), wfVerifierFactor M n i

/-- Witness-friendly machine sheet. -/
noncomputable def wfMachineSheet (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  ∏ i : Fin (holoBaseVars M n), wfMachineFactor M n i

/-- Witness-friendly compiled object. -/
noncomputable def wfCompiledPoly (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  wfVerifierSheet M n + wfMachineSheet M n

/-- Locality of each factor (single variable). -/
theorem wfVerifierFactor_vars_card_le_one (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    (wfVerifierFactor M n i).vars.card ≤ 1 := by
  simp [wfVerifierFactor]

/-- Locality of each factor (single variable). -/
theorem wfMachineFactor_vars_card_le_one (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    (wfMachineFactor M n i).vars.card ≤ 1 := by
  simp [wfMachineFactor]

end HoloCompilerWitnessFriendly
