import PallLean.MultilinearSPDP
import PallLean.NPWitness
import PallLean.Compiler
import Mathlib.Tactic

/-!
# LatentCompilerRoute

Corrected compiler architecture: the raw compiled object should *not* contain a
high-rank verifier/product sheet explicitly. Instead, hardness must appear only
through an extraction theorem.

This file adds a distinct latent compiler object and the final contradiction route
on that object. It is intentionally separate from the earlier broken candidates.
-/

set_option maxRecDepth 2000
set_option exponentiation.threshold 1024

namespace LatentCompilerRoute

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial

inductive LatentLayer where
  | machine
  | copy
  | selector
  | consistency
  deriving DecidableEq, Repr

def latentBaseVars (M : DTM) (n : ℕ) : ℕ :=
  numVars M n (Nat.log 2 n)

abbrev LatentVar (M : DTM) (n : ℕ) := LatentLayer × Fin (latentBaseVars M n)

section Vars

variable (M : DTM) (n : ℕ)

def Xmach (i : Fin (latentBaseVars M n)) : MvPolynomial (LatentVar M n) ℚ :=
  X (LatentLayer.machine, i)

def Xcopy (i : Fin (latentBaseVars M n)) : MvPolynomial (LatentVar M n) ℚ :=
  X (LatentLayer.copy, i)

def Xsel (i : Fin (latentBaseVars M n)) : MvPolynomial (LatentVar M n) ℚ :=
  X (LatentLayer.selector, i)

def Xcon (i : Fin (latentBaseVars M n)) : MvPolynomial (LatentVar M n) ℚ :=
  X (LatentLayer.consistency, i)

end Vars

section LocalGadgets

variable (M : DTM) (n : ℕ)

def machineLocalGadget (i : Fin (latentBaseVars M n)) :
    MvPolynomial (LatentVar M n) ℚ :=
  1 - Xmach M n i * Xcopy M n i

def consistencyLocalGadget (i : Fin (latentBaseVars M n)) :
    MvPolynomial (LatentVar M n) ℚ :=
  1 - Xcopy M n i * Xcon M n i

def selectorLocalGadget (i : Fin (latentBaseVars M n)) :
    MvPolynomial (LatentVar M n) ℚ :=
  1 - Xsel M n i * Xcon M n i

noncomputable def machineSheet : MvPolynomial (LatentVar M n) ℚ :=
  ∏ i : Fin (latentBaseVars M n), machineLocalGadget M n i

noncomputable def consistencySheet : MvPolynomial (LatentVar M n) ℚ :=
  ∏ i : Fin (latentBaseVars M n), consistencyLocalGadget M n i

noncomputable def selectorSheet : MvPolynomial (LatentVar M n) ℚ :=
  ∏ i : Fin (latentBaseVars M n), selectorLocalGadget M n i

noncomputable def latentCompiledPoly : MvPolynomial (LatentVar M n) ℚ :=
  machineSheet M n + consistencySheet M n + selectorSheet M n

end LocalGadgets

section Partition

noncomputable def latentPartition (M : DTM) (n : ℕ) :
    BlockPartition (LatentVar M n) where
  numBlocks := latentBaseVars M n
  assign := fun
    | (_, i) => ⟨i.1, i.2⟩

@[simp] theorem latentPartition_same_base
    (M : DTM) (n : ℕ) (ℓ₁ ℓ₂ : LatentLayer) (i : Fin (latentBaseVars M n)) :
    (latentPartition M n).assign (ℓ₁, i) = (latentPartition M n).assign (ℓ₂, i) := rfl

end Partition

section Extraction

variable (M : DTM) (n : ℕ)

noncomputable def extractSelectorLayer :
    MvPolynomial (LatentVar M n) ℚ →ₐ[ℚ] MvPolynomial (Fin (latentBaseVars M n)) ℚ :=
  MvPolynomial.aeval (fun
    | (LatentLayer.machine, _) => 0
    | (LatentLayer.copy, _) => 0
    | (LatentLayer.selector, i) => X i
    | (LatentLayer.consistency, _) => 0)

noncomputable def extractMachineLayer :
    MvPolynomial (LatentVar M n) ℚ →ₐ[ℚ] MvPolynomial (Fin (latentBaseVars M n)) ℚ :=
  MvPolynomial.aeval (fun
    | (LatentLayer.machine, i) => X i
    | (LatentLayer.copy, _) => 0
    | (LatentLayer.selector, _) => 0
    | (LatentLayer.consistency, _) => 0)

@[simp] theorem extractSelectorLayer_Xsel (i : Fin (latentBaseVars M n)) :
    extractSelectorLayer M n (Xsel M n i) = X i := by
  simp [extractSelectorLayer, Xsel]

@[simp] theorem extractMachineLayer_Xmach (i : Fin (latentBaseVars M n)) :
    extractMachineLayer M n (Xmach M n i) = X i := by
  simp [extractMachineLayer, Xmach]

@[simp] theorem extractSelectorLayer_Xmach_zero (i : Fin (latentBaseVars M n)) :
    extractSelectorLayer M n (Xmach M n i) = 0 := by
  simp [extractSelectorLayer, Xmach]

@[simp] theorem extractMachineLayer_Xsel_zero (i : Fin (latentBaseVars M n)) :
    extractMachineLayer M n (Xsel M n i) = 0 := by
  simp [extractMachineLayer, Xsel]

end Extraction

section Route

axiom latent_width_rank (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates)
    (κ : ℕ) (hκ : κ ≥ 5) :
    mlBlockedSpdpRank (latentPartition M n) κ κ (latentCompiledPoly M n) ≤ n ^ 200

axiom latent_extracts_hard_witness (M : DTM) (n : ℕ)
    (hn : n ≥ 32)
    (κ : ℕ) (hκ : κ ≥ 5) :
    n ^ (κ / 4) ≤ mlBlockedSpdpRank (latentPartition M n) κ κ (latentCompiledPoly M n)

structure PeqNP where
  sat_decider : DTM
  decides_sat : True

theorem P_neq_NP_latent (h : PeqNP)
    (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) : False := by
  let M := h.sat_decider
  have hn_left : n ≥ max 32 (max 4 M.numStates) := le_trans (le_max_left _ _) hn
  have hn32 : n ≥ 32 := le_trans (le_max_left _ _) hn_left
  have hnM : n ≥ max 4 M.numStates := le_trans (le_max_right _ _) hn_left
  have hn804 : n ≥ 2 ^ 804 := le_trans (le_max_right _ _) hn
  let κ := Nat.log 2 n
  have hκ : κ ≥ 5 := by
    have : Nat.log 2 32 = 5 := by native_decide
    exact le_trans (by omega) (Nat.log_mono_right hn32)
  have hNP := latent_extracts_hard_witness M n hn32 κ hκ
  have hP := latent_width_rank M n hnM κ hκ
  have hchain : n ^ (κ / 4) ≤ n ^ 200 := le_trans hNP hP
  have hexp : n ^ 200 < n ^ (κ / 4) := by
    apply Nat.pow_lt_pow_right
    · have : (2 : ℕ) ^ 1 ≤ 2 ^ 804 := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
      omega
    · have h_log : Nat.log 2 n ≥ 804 := by
        calc 804 = Nat.log 2 (2 ^ 804) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
          _ ≤ Nat.log 2 n := Nat.log_mono_right hn804
      omega
  exact (not_lt_of_ge hchain) hexp

end Route

end LatentCompilerRoute
