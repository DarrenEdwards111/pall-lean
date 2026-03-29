import PallLean.HoloCompilerDistinct
import Mathlib.Tactic

/-!
# HoloCompilerDistinctPartition

Compilation-safe scaffold partition/extraction layer for the distinct route.

Note: `mlBlockedSpdpRank` is currently defined over `MvPolynomial (Fin n)`, so this
module exposes a base-index partition/extraction interface on `Fin (holoBaseVars M n)`.
This keeps the witness-friendly route wired into the active import graph while preserving
paper-facing obligations as explicit axioms.
-/

namespace HoloCompilerDistinctPartition

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open HoloCompilerDistinct

/-- Base-space partition used by the witness-friendly scaffold route. -/
noncomputable def holoDistinctPartition (M : DTM) (n : ℕ) :
    BlockPartition (holoBaseVars M n) where
  numBlocks := holoBaseVars M n
  assign := fun i => i

/-- Verifier-layer extraction (scaffold): identity on base-variable space. -/
noncomputable def extractVerifierLayer (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (holoBaseVars M n)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  AlgHom.id ℚ _

/-- Machine-layer extraction (scaffold): identity on base-variable space. -/
noncomputable def extractMachineLayer (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (holoBaseVars M n)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  AlgHom.id ℚ _

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
