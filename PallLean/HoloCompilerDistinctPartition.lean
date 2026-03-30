import PallLean.HoloCompilerDistinct
import Mathlib.Tactic

/-!
# HoloCompilerDistinctPartition

Fin-indexed partition and extraction layer for the distinct holographic compiler route.

The `mlBlockedSpdpRank` API requires `BlockPartition n` and `MvPolynomial (Fin n)`.
This module provides:
- A block partition on `Fin (holoDistinctVars M n)` grouping each triple
  `{machSlot i, verSlot i, auxSlot i}` into block `i`.
- Extraction algebra homomorphisms that project individual layers to the base
  variable space `Fin (holoBaseVars M n)`.
- Simp lemmas for extraction applied to each slot type.
-/

namespace HoloCompilerDistinctPartition

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open HoloCompilerDistinct

/-- Partition on the Fin-indexed distinct variable space:
groups `{3i, 3i+1, 3i+2}` into block `i`. -/
def holoDistinctPartitionFin (M : DTM) (n : ℕ) :
    BlockPartition (holoDistinctVars M n) where
  numBlocks := holoBaseVars M n
  assign := slotBase M n

/-- Extract machine layer to base variable space:
maps `machSlot i ↦ X i`, all other slots to `0`. -/
noncomputable def extractMachineLayerFin (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (holoDistinctVars M n)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  MvPolynomial.aeval (fun j : Fin (holoDistinctVars M n) =>
    if slotLayer M n j = .machine then X (slotBase M n j) else 0)

/-- Extract verifier layer to base variable space:
maps `verSlot i ↦ X i`, all other slots to `0`. -/
noncomputable def extractVerifierLayerFin (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (holoDistinctVars M n)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  MvPolynomial.aeval (fun j : Fin (holoDistinctVars M n) =>
    if slotLayer M n j = .verifier then X (slotBase M n j) else 0)

section ExtractionLemmas

variable (M : DTM) (n : ℕ)

@[simp] theorem extractMachineLayerFin_X_machSlot (i : Fin (holoBaseVars M n)) :
    extractMachineLayerFin M n (X (machSlot M n i)) = X i := by
  unfold extractMachineLayerFin
  simp

@[simp] theorem extractMachineLayerFin_X_verSlot (i : Fin (holoBaseVars M n)) :
    extractMachineLayerFin M n (X (verSlot M n i)) = 0 := by
  unfold extractMachineLayerFin
  simp

@[simp] theorem extractMachineLayerFin_X_auxSlot (i : Fin (holoBaseVars M n)) :
    extractMachineLayerFin M n (X (auxSlot M n i)) = 0 := by
  unfold extractMachineLayerFin
  simp

@[simp] theorem extractVerifierLayerFin_X_verSlot (i : Fin (holoBaseVars M n)) :
    extractVerifierLayerFin M n (X (verSlot M n i)) = X i := by
  unfold extractVerifierLayerFin
  simp

@[simp] theorem extractVerifierLayerFin_X_machSlot (i : Fin (holoBaseVars M n)) :
    extractVerifierLayerFin M n (X (machSlot M n i)) = 0 := by
  unfold extractVerifierLayerFin
  simp

@[simp] theorem extractVerifierLayerFin_X_auxSlot (i : Fin (holoBaseVars M n)) :
    extractVerifierLayerFin M n (X (auxSlot M n i)) = 0 := by
  unfold extractVerifierLayerFin
  simp

end ExtractionLemmas

section PaperObligations

/-- Paper-facing remaining obligation:
local verifier gadgets should extract to the intended witness-side gadget family. -/
axiom holoDistinct_verifier_gadget_correct (M : DTM) (n : ℕ) :
  True

/-- Paper-facing remaining obligation:
the distinct partition gives bounded CEW / local width for the new compiler object. -/
axiom holoDistinct_partition_cew (M : DTM) (n : ℕ) :
  True

/-- Paper-facing remaining obligation:
profile compression on the distinct partition yields polynomial SPDP rank. -/
axiom holoDistinct_profile_compression (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates)
    (κ : ℕ) (hκ : κ ≥ 5) :
  True

/-- Paper-facing remaining obligation:
the verifier-layer extraction is rank-monotone from the distinct object
back to the base witness space. -/
axiom holoDistinct_extraction_monotone (M : DTM) (n : ℕ)
    (κ ℓ : ℕ) :
  True

end PaperObligations

end HoloCompilerDistinctPartition
