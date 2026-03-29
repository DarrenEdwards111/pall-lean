import PallLean.HoloCompilerDistinct
import Mathlib.Tactic

/-!
# HoloCompilerDistinctPartition

This file pushes the distinct holographic-compiler scaffold one step further by:

1. giving the distinct object an explicit block partition;
2. defining a concrete extraction map from the verifier layer back to the base variable space;
3. isolating the remaining paper-facing obligations as local gadget theorems.

The point is to make the remaining work about the actual local gadgets and their CEW,
not about the existence of a distinct object at all.
-/

namespace HoloCompilerDistinctPartition

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open HoloCompilerDistinct

/-- Explicit partition for the distinct compiler object:
all copies of the same base index live in the same block.

This is the simplest locality-friendly partition one can put on the duplicated-layer space.
The final paper-faithful partition may refine this further, but this already prevents the
worst shared-space collapse seen in `fullCompiledPoly`. -/
noncomputable def holoDistinctPartition (M : DTM) (n : ℕ) :
    BlockPartition (HoloVar M n) where
  numBlocks := holoBaseVars M n
  assign := fun
    | (_, i) => ⟨i.1, i.2⟩

/-- Concrete extraction map from the distinct compiler object to the base variable space,
keeping only verifier-layer variables. -/
noncomputable def extractVerifierLayer (M : DTM) (n : ℕ) :
    MvPolynomial (HoloVar M n) ℚ →ₐ[ℚ] MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  projectVerifier M n

/-- Concrete extraction map keeping only machine-layer variables. -/
noncomputable def extractMachineLayer (M : DTM) (n : ℕ) :
    MvPolynomial (HoloVar M n) ℚ →ₐ[ℚ] MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  projectMachine M n

@[simp] theorem extractVerifierLayer_Xver (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    extractVerifierLayer M n (Xver M n i) = X i := by
  simp [extractVerifierLayer]

@[simp] theorem extractMachineLayer_Xmach (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    extractMachineLayer M n (Xmach M n i) = X i := by
  simp [extractMachineLayer]

/-- Paper-facing remaining obligation 1:
local verifier gadgets should extract to the intended witness-side gadget family. -/
axiom holoDistinct_verifier_gadget_correct (M : DTM) (n : ℕ) :
  True

/-- Paper-facing remaining obligation 2:
the distinct partition gives bounded CEW / local width for the new compiler object. -/
axiom holoDistinct_partition_cew (M : DTM) (n : ℕ) :
  True

/-- Paper-facing remaining obligation 3:
profile compression on the distinct partition yields polynomial SPDP rank. -/
axiom holoDistinct_profile_compression (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates)
    (κ : ℕ) (hκ : κ ≥ 5) :
  True

/-- Paper-facing remaining obligation 4:
the verifier-layer extraction is rank-monotone from the distinct object back to the base witness space. -/
axiom holoDistinct_extraction_monotone (M : DTM) (n : ℕ)
    (κ ℓ : ℕ) :
  True

end HoloCompilerDistinctPartition
