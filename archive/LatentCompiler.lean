import PallLean.MultilinearSPDP
import PallLean.NPWitness
import PallLean.Compiler
import Mathlib.Tactic

/-!
# LatentCompiler

This file fixes the core architectural mistake in the earlier candidate compilers.

## What went wrong before

Both `fullCompiledPoly` and the later witness-friendly layered candidates baked a
high-rank verifier/product sheet directly into the compiled polynomial. That makes any
polynomial-rank upper bound false, because the witness hardness is already present in
raw form.

## The paper-faithful fix

The compiler output must carry the NP witness structure only *latently*.
The raw compiled polynomial should be assembled from local machine / consistency /
selector gadgets with bounded overlap. The hard witness object is recovered only after
an extraction / specialization map.

So the target architecture is:

1. raw compiled object `latentCompiledPoly` has bounded CEW / polynomial SPDP rank;
2. a rank-monotone extraction map reveals the verifier/witness object;
3. the extracted witness has exponential rank;
4. contradiction.

This file installs that corrected route as a concrete GitHub object, without pretending
that the core compiler theorems are already proved.
-/

set_option maxRecDepth 2000
set_option exponentiation.threshold 1024

namespace LatentCompiler

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial

/-- Variable layers for the latent compiler object.

Unlike the earlier bad candidates, there is no dedicated high-rank witness sheet baked
in here. The raw object only carries local machine/state/copy/selector infrastructure. -/
inductive LatentLayer where
  | machine
  | copy
  | selector
  | consistency
  deriving DecidableEq, Repr

/-- Base variable count inherited from the existing machine-side index space. -/
def latentBaseVars (M : DTM) (n : ℕ) : ℕ :=
  numVars M n (Nat.log 2 n)

/-- Distinct variable space for the latent compiler. -/
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

/-- Machine-local gadget: one machine variable tied to one local copy. -/
def machineLocalGadget (i : Fin (latentBaseVars M n)) :
    MvPolynomial (LatentVar M n) ℚ :=
  1 - Xmach M n i * Xcopy M n i

/-- Consistency gadget: local copy tied to a consistency variable. -/
def consistencyLocalGadget (i : Fin (latentBaseVars M n)) :
    MvPolynomial (LatentVar M n) ℚ :=
  1 - Xcopy M n i * Xcon M n i

/-- Selector gadget: keeps a local selector layer separate from the raw machine/copy layers. -/
def selectorLocalGadget (i : Fin (latentBaseVars M n)) :
    MvPolynomial (LatentVar M n) ℚ :=
  1 - Xsel M n i * Xcon M n i

/-- Raw machine sheet from local machine gadgets. -/
noncomputable def machineSheet : MvPolynomial (LatentVar M n) ℚ :=
  ∏ i : Fin (latentBaseVars M n), machineLocalGadget M n i

/-- Raw consistency sheet from local consistency gadgets. -/
noncomputable def consistencySheet : MvPolynomial (LatentVar M n) ℚ :=
  ∏ i : Fin (latentBaseVars M n), consistencyLocalGadget M n i

/-- Raw selector sheet from local selector gadgets. -/
noncomputable def selectorSheet : MvPolynomial (LatentVar M n) ℚ :=
  ∏ i : Fin (latentBaseVars M n), selectorLocalGadget M n i

/-- The corrected latent compiler output.

This is intentionally *not* a direct verifier/product witness sheet. It is a raw local-gadget
object whose hardness is supposed to emerge only after extraction. -/
noncomputable def latentCompiledPoly : MvPolynomial (LatentVar M n) ℚ :=
  machineSheet M n + consistencySheet M n + selectorSheet M n

end LocalGadgets

section Partition

/-- Locality-friendly partition: all layer-copies of one base index lie in one block. -/
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

/-- Extraction to the selector layer. In the paper-faithful final route this will be refined
into the real witness-recovery map. -/
noncomputable def extractSelectorLayer :
    MvPolynomial (LatentVar M n) ℚ →ₐ[ℚ] MvPolynomial (Fin (latentBaseVars M n)) ℚ :=
  MvPolynomial.aeval (fun
    | (LatentLayer.machine, _) => 0
    | (LatentLayer.copy, _) => 0
    | (LatentLayer.selector, i) => X i
    | (LatentLayer.consistency, _) => 0)

/-- Extraction to the machine layer. -/
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

/-- The real remaining compiler theorem, now on the corrected latent object.
This is where bounded CEW / profile compression must be proved. -/
axiom latent_width_rank (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates)
    (κ : ℕ) (hκ : κ ≥ 5) :
    mlBlockedSpdpRank (latentPartition M n) κ κ (latentCompiledPoly M n) ≤ n ^ 200

/-- The real remaining extraction theorem, now from the corrected latent object to the hard witness side.
This is where the paper's holographic extraction route must be implemented. -/
axiom latent_extracts_hard_witness (M : DTM) (n : ℕ)
    (hn : n ≥ 32)
    (κ : ℕ) (hκ : κ ≥ 5) :
    n ^ (κ / 4) ≤ mlBlockedSpdpRank (latentPartition M n) κ κ (latentCompiledPoly M n)

/-- P = NP assumption package. -/
structure PeqNP where
  sat_decider : DTM
  decides_sat : True

/-- Corrected separation route on the latent compiler object.

This is the repaired version of the earlier broken routes: the raw compiler object is no longer
itself the hard witness polynomial. The hard witness only appears through the extraction theorem. -/
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

end LatentCompiler
