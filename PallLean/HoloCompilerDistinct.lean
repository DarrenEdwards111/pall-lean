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
def Xmach (i : Fin (holoBaseVars M n)) : MvPolynomial (HoloVar M n) ℚ :=
  X (HoloLayer.machine, i)

/-- Verifier-layer variable. -/
def Xver (i : Fin (holoBaseVars M n)) : MvPolynomial (HoloVar M n) ℚ :=
  X (HoloLayer.verifier, i)

/-- Auxiliary local variable. -/
def Xaux (i : Fin (holoBaseVars M n)) : MvPolynomial (HoloVar M n) ℚ :=
  X (HoloLayer.aux, i)

end Vars

section LocalFactors

variable (M : DTM) (n : ℕ)

/-- A tiny machine-side local factor: depends only on one machine copy and one aux copy. -/
def holoMachineFactor (i : Fin (holoBaseVars M n)) :
    MvPolynomial (HoloVar M n) ℚ :=
  1 - Xmach M n i * Xaux M n i

/-- A tiny verifier-side local factor: depends only on one verifier copy and one aux copy. -/
def holoVerifierFactor (i : Fin (holoBaseVars M n)) :
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

end HoloCompilerDistinct
