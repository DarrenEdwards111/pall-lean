import PallLean.MultilinearSPDP
import PallLean.NPWitness
import PallLean.Compiler
import Mathlib.Tactic

/-!
# HoloCompilerDistinctPartition — Fin-indexed distinct-layer encoding

Encodes machine/verifier/aux layers into `Fin (3 * baseN)`:
- Machine  slot i = 3*i
- Verifier slot i = 3*i + 1
- Aux      slot i = 3*i + 2

This gives a `Fin n` variable space compatible with `mlBlockedSpdpRank`.
-/

namespace HoloCompilerDistinctPartition

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial

/-- Base variable count (from existing machine-side index space). -/
def holoBaseVars (M : DTM) (n : ℕ) : ℕ := numVars M n (Nat.log 2 n)

/-- Total variable count for distinct-layer encoding: 3 copies per base variable. -/
def distinctNumVars (M : DTM) (n : ℕ) : ℕ := 3 * holoBaseVars M n

private theorem three_i_lt (M : DTM) (n : ℕ) (i : Fin (holoBaseVars M n)) :
    3 * i.val < distinctNumVars M n := by
  unfold distinctNumVars; omega

private theorem three_i_plus_one_lt (M : DTM) (n : ℕ) (i : Fin (holoBaseVars M n)) :
    3 * i.val + 1 < distinctNumVars M n := by
  unfold distinctNumVars; omega

private theorem three_i_plus_two_lt (M : DTM) (n : ℕ) (i : Fin (holoBaseVars M n)) :
    3 * i.val + 2 < distinctNumVars M n := by
  unfold distinctNumVars; omega

private theorem div3_lt (M : DTM) (n : ℕ) (j : Fin (distinctNumVars M n)) :
    j.val / 3 < holoBaseVars M n := by
  have := j.isLt; unfold distinctNumVars at this; omega

/-- Machine slot for base index i. -/
def machSlot (M : DTM) (n : ℕ) (i : Fin (holoBaseVars M n)) :
    Fin (distinctNumVars M n) :=
  ⟨3 * i.val, three_i_lt M n i⟩

/-- Verifier slot for base index i. -/
def verSlot (M : DTM) (n : ℕ) (i : Fin (holoBaseVars M n)) :
    Fin (distinctNumVars M n) :=
  ⟨3 * i.val + 1, three_i_plus_one_lt M n i⟩

/-- Aux slot for base index i. -/
def auxSlot (M : DTM) (n : ℕ) (i : Fin (holoBaseVars M n)) :
    Fin (distinctNumVars M n) :=
  ⟨3 * i.val + 2, three_i_plus_two_lt M n i⟩

/-- Machine-layer variable polynomial. -/
noncomputable def XMach (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) : MvPolynomial (Fin (distinctNumVars M n)) ℚ :=
  X (machSlot M n i)

/-- Verifier-layer variable polynomial. -/
noncomputable def XVer (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) : MvPolynomial (Fin (distinctNumVars M n)) ℚ :=
  X (verSlot M n i)

/-- Aux-layer variable polynomial. -/
noncomputable def XAux (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) : MvPolynomial (Fin (distinctNumVars M n)) ℚ :=
  X (auxSlot M n i)

/-- Block partition: group all 3 copies of base index i into block i. -/
noncomputable def holoDistinctPartition (M : DTM) (n : ℕ) :
    BlockPartition (distinctNumVars M n) where
  numBlocks := holoBaseVars M n
  assign := fun j => ⟨j.val / 3, div3_lt M n j⟩

/-- Verifier-layer extraction: project verifier slots to base vars, kill others. -/
noncomputable def extractVerifierLayer (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (distinctNumVars M n)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  aeval (fun j : Fin (distinctNumVars M n) =>
    if j.val % 3 = 1 then X ⟨j.val / 3, div3_lt M n j⟩ else 0)

/-- Machine-layer extraction: project machine slots to base vars, kill others. -/
noncomputable def extractMachineLayer (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (distinctNumVars M n)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  aeval (fun j : Fin (distinctNumVars M n) =>
    if j.val % 3 = 0 then X ⟨j.val / 3, div3_lt M n j⟩ else 0)

/-- Extraction sends verifier variable to base variable. -/
theorem extractVerifierLayer_XVer (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    extractVerifierLayer M n (XVer M n i) = X i := by
  unfold extractVerifierLayer XVer verSlot
  simp only [aeval_X]
  have h3 : (3 * i.val + 1) % 3 = 1 := by omega
  simp only [ite_true, h3]
  congr 1; exact Fin.ext (by simp; omega)

/-- Extraction kills machine variable. -/
theorem extractVerifierLayer_XMach (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    extractVerifierLayer M n (XMach M n i) = 0 := by
  unfold extractVerifierLayer XMach machSlot
  simp only [aeval_X]
  have h3 : ¬ ((3 * i.val) % 3 = 1) := by omega
  simp [h3]

/-- Extraction kills aux variable. -/
theorem extractVerifierLayer_XAux (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    extractVerifierLayer M n (XAux M n i) = 0 := by
  unfold extractVerifierLayer XAux auxSlot
  simp only [aeval_X]
  have h3 : ¬ ((3 * i.val + 2) % 3 = 1) := by omega
  simp [h3]

/-- Machine extraction sends machine variable to base variable. -/
theorem extractMachineLayer_XMach (M : DTM) (n : ℕ)
    (i : Fin (holoBaseVars M n)) :
    extractMachineLayer M n (XMach M n i) = X i := by
  unfold extractMachineLayer XMach machSlot
  simp only [aeval_X]
  have h3 : (3 * i.val) % 3 = 0 := by omega
  simp [h3]

/-- Paper-facing remaining obligations (placeholders). -/
axiom holoDistinct_verifier_gadget_correct (M : DTM) (n : ℕ) : True
axiom holoDistinct_partition_cew (M : DTM) (n : ℕ) : True
axiom holoDistinct_profile_compression (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates) (κ : ℕ) (hκ : κ ≥ 5) : True
axiom holoDistinct_extraction_monotone (M : DTM) (n : ℕ) (κ ℓ : ℕ) : True

end HoloCompilerDistinctPartition
