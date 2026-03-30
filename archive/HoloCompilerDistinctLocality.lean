import PallLean.HoloCompilerDistinctPartition
import Mathlib.Tactic

/-!
# HoloCompilerDistinctLocality

Locality and structural facts for the Fin-indexed distinct holographic compiler.

This file proves that the slot constructors respect the partition structure:
all three slots for a given base index land in the same partition block.
It also establishes injectivity and distinctness of the slot embeddings.
-/

namespace HoloCompilerDistinctLocality

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open HoloCompilerDistinct
open HoloCompilerDistinctPartition

/-! ### Partition block assignment -/

theorem partition_machSlot (M : DTM) (n : ℕ) (i : Fin (holoBaseVars M n)) :
    (holoDistinctPartitionFin M n).assign (machSlot M n i) = i := by
  change slotBase M n (machSlot M n i) = i
  simp

theorem partition_verSlot (M : DTM) (n : ℕ) (i : Fin (holoBaseVars M n)) :
    (holoDistinctPartitionFin M n).assign (verSlot M n i) = i := by
  change slotBase M n (verSlot M n i) = i
  simp

theorem partition_auxSlot (M : DTM) (n : ℕ) (i : Fin (holoBaseVars M n)) :
    (holoDistinctPartitionFin M n).assign (auxSlot M n i) = i := by
  change slotBase M n (auxSlot M n i) = i
  simp

/-! ### Slot injectivity -/

theorem machSlot_injective (M : DTM) (n : ℕ) : Function.Injective (machSlot M n) := by
  intro i j h
  have hv := congr_arg Fin.val h
  simp only [machSlot, Fin.val_mk] at hv
  ext; omega

theorem verSlot_injective (M : DTM) (n : ℕ) : Function.Injective (verSlot M n) := by
  intro i j h
  have hv := congr_arg Fin.val h
  simp only [verSlot, Fin.val_mk] at hv
  ext; omega

theorem auxSlot_injective (M : DTM) (n : ℕ) : Function.Injective (auxSlot M n) := by
  intro i j h
  have hv := congr_arg Fin.val h
  simp only [auxSlot, Fin.val_mk] at hv
  ext; omega

/-! ### Slot distinctness -/

theorem machSlot_ne_verSlot (M : DTM) (n : ℕ) (i j : Fin (holoBaseVars M n)) :
    machSlot M n i ≠ verSlot M n j := by
  intro h
  have hv := congr_arg Fin.val h
  simp only [machSlot, verSlot, Fin.val_mk] at hv
  omega

theorem machSlot_ne_auxSlot (M : DTM) (n : ℕ) (i j : Fin (holoBaseVars M n)) :
    machSlot M n i ≠ auxSlot M n j := by
  intro h
  have hv := congr_arg Fin.val h
  simp only [machSlot, auxSlot, Fin.val_mk] at hv
  omega

theorem verSlot_ne_auxSlot (M : DTM) (n : ℕ) (i j : Fin (holoBaseVars M n)) :
    verSlot M n i ≠ auxSlot M n j := by
  intro h
  have hv := congr_arg Fin.val h
  simp only [verSlot, auxSlot, Fin.val_mk] at hv
  omega

end HoloCompilerDistinctLocality
