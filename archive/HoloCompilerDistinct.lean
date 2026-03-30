import PallLean.MultilinearSPDP
import PallLean.NPWitness
import PallLean.Compiler
import Mathlib.Tactic

/-!
# HoloCompilerDistinct

A **genuinely distinct** compiler object from `fullCompiledPoly`.

This file does not pretend to finish the paper's full holographic compiler.
What it does is put a concrete, separate polynomial object into the repo whose
variable space is explicitly duplicated into layers, matching the paper's need
for a bounded-CEW / locality-friendly encoding rather than the already-proved
high-rank object `fullCompiledPoly`.

## Design idea

The current `fullCompiledPoly` lives on a single shared variable space and has
been verified to have the same SPDP rank as the Tseitin verifier sheet.
So it cannot be the paper's bounded-CEW compiler object.

Here we introduce a new variable type with duplicated layers:
- `machine`   : machine-side local copies
- `verifier`  : verifier-side local copies
- `aux`       : local glue / consistency variables

This makes the output *definitionally distinct* from `fullCompiledPoly` and is
closer in spirit to the paper's holographic compiler, where locality comes from
how variables are grouped and duplicated, not just from the Boolean function.

## Important

This is a **concrete scaffold**, not yet the full §40 / Appendix B compiler.
The next work is to replace the simple layer-local factors below by the paper's
actual clause / transition gadgets, and then prove the CEW / Width⇒Rank theorem
on the resulting object.
-/

namespace HoloCompilerDistinct

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial

/-- Three variable layers for the distinct holographic compiler output. -/
inductive HoloLayer where
  | machine
  | verifier
  | aux
  deriving DecidableEq, Repr

/-- Base variable count reused from the existing machine-side index space. -/
def holoBaseVars (M : DTM) (n : ℕ) : ℕ :=
  numVars M n (Nat.log 2 n)

/-- Distinct variable type: each base index gets three separate copies. -/
abbrev HoloVar (M : DTM) (n : ℕ) := HoloLayer × Fin (holoBaseVars M n)

section Vars

variable (M : DTM) (n : ℕ)

/-- Machine-layer variable. -/
noncomputable def Xmach (i : Fin (holoBaseVars M n)) : MvPolynomial (HoloVar M n) ℚ :=
  X (HoloLayer.machine, i)

/-- Verifier-layer variable. -/
noncomputable def Xver (i : Fin (holoBaseVars M n)) : MvPolynomial (HoloVar M n) ℚ :=
  X (HoloLayer.verifier, i)

/-- Auxiliary local variable. -/
noncomputable def Xaux (i : Fin (holoBaseVars M n)) : MvPolynomial (HoloVar M n) ℚ :=
  X (HoloLayer.aux, i)

end Vars

section LocalFactors

variable (M : DTM) (n : ℕ)

/-- A tiny machine-side local factor: depends only on one machine copy and one aux copy. -/
noncomputable def holoMachineFactor (i : Fin (holoBaseVars M n)) :
    MvPolynomial (HoloVar M n) ℚ :=
  1 - Xmach M n i * Xaux M n i

/-- A tiny verifier-side local factor: depends only on one verifier copy and one aux copy. -/
noncomputable def holoVerifierFactor (i : Fin (holoBaseVars M n)) :
    MvPolynomial (HoloVar M n) ℚ :=
  1 - Xver M n i * Xaux M n i

/-- Machine sheet assembled from local machine factors. -/
noncomputable def holoMachineSheet : MvPolynomial (HoloVar M n) ℚ :=
  ∏ i : Fin (holoBaseVars M n), holoMachineFactor M n i

/-- Verifier sheet assembled from local verifier factors. -/
noncomputable def holoVerifierSheet : MvPolynomial (HoloVar M n) ℚ :=
  ∏ i : Fin (holoBaseVars M n), holoVerifierFactor M n i

/-- A concrete distinct compiled polynomial with duplicated layers.

This is not the final paper object, but it is a genuinely distinct candidate
bounded-CEW compiler output: the machine-side and verifier-side interactions are
forced to live on different variable layers, instead of sharing one rank-hard
space as in `fullCompiledPoly`.
-/
noncomputable def holoCompiledPolyDistinct : MvPolynomial (HoloVar M n) ℚ :=
  holoVerifierSheet M n + holoMachineSheet M n

end LocalFactors

section Projections

variable (M : DTM) (n : ℕ)

/-- Forget all but the machine layer. -/
noncomputable def projectMachine :
    MvPolynomial (HoloVar M n) ℚ →ₐ[ℚ] MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  MvPolynomial.aeval (fun
    | (HoloLayer.machine, i) => X i
    | (HoloLayer.verifier, _) => 0
    | (HoloLayer.aux, _) => 0)

/-- Forget all but the verifier layer. -/
noncomputable def projectVerifier :
    MvPolynomial (HoloVar M n) ℚ →ₐ[ℚ] MvPolynomial (Fin (holoBaseVars M n)) ℚ :=
  MvPolynomial.aeval (fun
    | (HoloLayer.machine, _) => 0
    | (HoloLayer.verifier, i) => X i
    | (HoloLayer.aux, _) => 0)

@[simp] theorem projectMachine_Xmach (i : Fin (holoBaseVars M n)) :
    projectMachine M n (Xmach M n i) = X i := by
  simp [projectMachine, Xmach]

@[simp] theorem projectVerifier_Xver (i : Fin (holoBaseVars M n)) :
    projectVerifier M n (Xver M n i) = X i := by
  simp [projectVerifier, Xver]

end Projections

section BridgeScaffold

/-- The paper-faithful next theorem to prove for the distinct compiler object:
its SPDP rank is polynomial under the appropriate local partition. -/
axiom holoDistinct_width_rank (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates)
    (κ : ℕ) (hκ : κ ≥ 5) :
    True

/-- The paper-faithful next theorem to prove: the distinct compiler object admits
an extraction map recovering the NP witness structure in rank-monotone form. -/
axiom holoDistinct_extracts_witness (M : DTM) (n : ℕ)
    (hn : n ≥ 32)
    (κ ℓ : ℕ) (hκ : κ ≥ 5) :
    True

end BridgeScaffold

/-! ## Fin-indexed encoding for mlBlockedSpdpRank compatibility

The `mlBlockedSpdpRank` API requires `MvPolynomial (Fin n)` and `BlockPartition n`.
We encode the three-layer variable space as `Fin (3 * holoBaseVars M n)` with
machine/verifier/aux slots interleaved at stride 3.
-/

/-- Total Fin-indexed variable count: three copies of each base variable. -/
def holoDistinctVars (M : DTM) (n : ℕ) : ℕ := 3 * holoBaseVars M n

section SlotArithmetic

variable (M : DTM) (n : ℕ)

/-- Machine-layer slot: base index i maps to Fin position 3*i. -/
def machSlot (i : Fin (holoBaseVars M n)) : Fin (holoDistinctVars M n) :=
  ⟨3 * i.val, by unfold holoDistinctVars; omega⟩

/-- Verifier-layer slot: base index i maps to Fin position 3*i + 1. -/
def verSlot (i : Fin (holoBaseVars M n)) : Fin (holoDistinctVars M n) :=
  ⟨3 * i.val + 1, by unfold holoDistinctVars; omega⟩

/-- Auxiliary-layer slot: base index i maps to Fin position 3*i + 2. -/
def auxSlot (i : Fin (holoBaseVars M n)) : Fin (holoDistinctVars M n) :=
  ⟨3 * i.val + 2, by unfold holoDistinctVars; omega⟩

/-- Layer classification of a Fin-indexed variable. -/
def slotLayer (j : Fin (holoDistinctVars M n)) : HoloLayer :=
  if j.val % 3 = 0 then .machine
  else if j.val % 3 = 1 then .verifier
  else .aux

/-- Base index of a Fin-indexed variable. -/
def slotBase (j : Fin (holoDistinctVars M n)) : Fin (holoBaseVars M n) :=
  ⟨j.val / 3, by have := j.isLt; unfold holoDistinctVars at *; omega⟩

@[simp] theorem slotLayer_machSlot (i : Fin (holoBaseVars M n)) :
    slotLayer M n (machSlot M n i) = .machine := by
  simp only [slotLayer, machSlot, Fin.val_mk]
  split
  · rfl
  · omega

@[simp] theorem slotLayer_verSlot (i : Fin (holoBaseVars M n)) :
    slotLayer M n (verSlot M n i) = .verifier := by
  simp only [slotLayer, verSlot, Fin.val_mk]
  split
  · omega
  · split
    · rfl
    · omega

@[simp] theorem slotLayer_auxSlot (i : Fin (holoBaseVars M n)) :
    slotLayer M n (auxSlot M n i) = .aux := by
  simp only [slotLayer, auxSlot, Fin.val_mk]
  split
  · omega
  · split
    · omega
    · rfl

@[simp] theorem slotBase_machSlot (i : Fin (holoBaseVars M n)) :
    slotBase M n (machSlot M n i) = i := by
  ext; simp only [slotBase, machSlot, Fin.val_mk]; omega

@[simp] theorem slotBase_verSlot (i : Fin (holoBaseVars M n)) :
    slotBase M n (verSlot M n i) = i := by
  ext; simp only [slotBase, verSlot, Fin.val_mk]; omega

@[simp] theorem slotBase_auxSlot (i : Fin (holoBaseVars M n)) :
    slotBase M n (auxSlot M n i) = i := by
  ext; simp only [slotBase, auxSlot, Fin.val_mk]; omega

end SlotArithmetic

section FinIndexedPolys

variable (M : DTM) (n : ℕ)

/-- Machine-side local factor on the Fin-indexed space. -/
noncomputable def holoMachineFactorFin (i : Fin (holoBaseVars M n)) :
    MvPolynomial (Fin (holoDistinctVars M n)) ℚ :=
  1 - X (machSlot M n i) * X (auxSlot M n i)

/-- Verifier-side local factor on the Fin-indexed space. -/
noncomputable def holoVerifierFactorFin (i : Fin (holoBaseVars M n)) :
    MvPolynomial (Fin (holoDistinctVars M n)) ℚ :=
  1 - X (verSlot M n i) * X (auxSlot M n i)

/-- Machine sheet on the Fin-indexed space. -/
noncomputable def holoMachineSheetFin :
    MvPolynomial (Fin (holoDistinctVars M n)) ℚ :=
  ∏ i : Fin (holoBaseVars M n), holoMachineFactorFin M n i

/-- Verifier sheet on the Fin-indexed space. -/
noncomputable def holoVerifierSheetFin :
    MvPolynomial (Fin (holoDistinctVars M n)) ℚ :=
  ∏ i : Fin (holoBaseVars M n), holoVerifierFactorFin M n i

/-- Compiled polynomial on the Fin-indexed space, compatible with mlBlockedSpdpRank. -/
noncomputable def holoCompiledPolyFin :
    MvPolynomial (Fin (holoDistinctVars M n)) ℚ :=
  holoVerifierSheetFin M n + holoMachineSheetFin M n

end FinIndexedPolys

end HoloCompilerDistinct
