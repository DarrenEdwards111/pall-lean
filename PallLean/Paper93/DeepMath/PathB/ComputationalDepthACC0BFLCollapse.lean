import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CollapseIngredients
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0KarpLiptonCollapse

/-!
# The Babai–Fortnow–Lund / IKW collapse — `NEXP = MIP` + guessable prover, structure exposed (proved glue)

Entry 202 decomposed `KarpLiptonCollapse` (`NEXP ⊆ ACC⁰ ⟹ NEXP = MA`) into `NexpSubsetMA_ofCircuits` (the deep inclusion
`NEXP ⊆ ACC⁰ ⟹ NEXP ⊆ MA`, socketed) + the trivial `MA ⊆ NEXP` + antisymmetry.  This file opens up that deep inclusion
into its genuine **Babai–Fortnow–Lund / IKW** structure and proves the composition glue.

The structure.  The collapse goes through interactive proofs: **`NEXP = MIP`** (Babai–Fortnow–Lund 1991, the
multi-prover IP characterisation of `NEXP`), and **circuits ⟹ the `MIP` prover's strategy is a small circuit, which
Arthur guesses** (so `MIP ⊆ MA` under the circuit hypothesis).  Composing: `NEXP = MIP ⊆ MA`, hence `NEXP ⊆ MA`.

## What is proved (clean axioms, no `sorry`)

* **`NexpEqMIP NEXP MIP := NEXP = MIP`** — the Babai–Fortnow–Lund `MIP = NEXP` theorem (named socket).
* **`MIPSubsetMA_ofCircuits MIP ACC0 MA := MIP ⊆ ACC0 → MIP ⊆ MA`** — under circuits, the `MIP` prover is guessable, so
  `MIP ⊆ MA` (named socket).
* **`nexpSubsetMA_via_MIP`** — the composition glue: `NexpEqMIP` + `MIPSubsetMA_ofCircuits` ⇒ the entry-202
  `NexpSubsetMA_ofCircuits` (the deep BFL inclusion), by `fun hsub => heq ▸ guessable (heq ▸ hsub)`.
* **`karpLiptonCollapse_via_MIP`** — the full `KarpLiptonCollapse` from the BFL-IKW ingredients (`NexpEqMIP`,
  `MIPSubsetMA_ofCircuits`, the trivial `MASubsetNexp`), via entry-202's antisymmetry.

## Honest scope

This **exposes the BFL-IKW structure** of the deep Karp–Lipton inclusion — that `NEXP ⊆ ACC⁰ ⟹ NEXP ⊆ MA` factors as
`NEXP = MIP` (Babai–Fortnow–Lund) composed with "circuits ⟹ guessable `MIP` prover ⟹ `MIP ⊆ MA`" — and proves the
*composition* (`NEXP = MIP ⊆ MA` by rewriting along the equality).  The two genuine classical theorems remain named
sub-sockets: **`NexpEqMIP`** (the `MIP = NEXP` theorem — the multilinearity/sum-check machinery) and
**`MIPSubsetMA_ofCircuits`** (the guessable-prover collapse — that a `P/poly` prover strategy turns the interactive
proof into a Merlin–Arthur one).  Each requires interactive-proof infrastructure absent here.  This proves the
*structure and composition* of the BFL-IKW collapse, not its two deep ingredients.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BFLCollapse

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonCollapse (KarpLiptonCollapse)
open PallLean.Paper93.DeepMath.PathB.ACC0CollapseIngredients
  (NexpSubsetMA_ofCircuits MASubsetNexp karpLiptonCollapse_discharge)

/-- **The `MIP = NEXP` socket (Babai–Fortnow–Lund 1991).**  `NEXP` equals the multi-prover interactive-proof class
`MIP`.  Stated, not proved (the sum-check / multilinearity machinery). -/
def NexpEqMIP (NEXP MIP : CClass) : Prop := NEXP = MIP

/-- **The guessable-prover socket.**  Under the circuit hypothesis (`MIP ⊆ ACC⁰`), the `MIP` prover's optimal strategy
is a small circuit, which Arthur guesses — collapsing `MIP ⊆ MA`.  Stated, not proved. -/
def MIPSubsetMA_ofCircuits (MIP ACC0 MA : CClass) : Prop := MIP ⊆ ACC0 → MIP ⊆ MA

/-- **The deep BFL inclusion, factored through `MIP` (PROVED glue).**  `NEXP = MIP` (`NexpEqMIP`) and the guessable-prover
collapse (`MIPSubsetMA_ofCircuits`) compose to the entry-202 deep inclusion `NexpSubsetMA_ofCircuits`
(`NEXP ⊆ ACC⁰ ⟹ NEXP ⊆ MA`): a circuit hypothesis `hsub : NEXP ⊆ ACC⁰` becomes `MIP ⊆ ACC⁰` (rewrite along
`NEXP = MIP`), yields `MIP ⊆ MA` (guessable), and rewrites back to `NEXP ⊆ MA`. -/
theorem nexpSubsetMA_via_MIP (NEXP MIP ACC0 MA : CClass)
    (heq : NexpEqMIP NEXP MIP) (guessable : MIPSubsetMA_ofCircuits MIP ACC0 MA) :
    NexpSubsetMA_ofCircuits NEXP ACC0 MA :=
  fun hsub => heq ▸ guessable (heq ▸ hsub)

/-- **`KarpLiptonCollapse` from the BFL-IKW ingredients (PROVED glue).**  `NexpEqMIP` + `MIPSubsetMA_ofCircuits` + the
trivial `MASubsetNexp` give `KarpLiptonCollapse NEXP ACC0 MA` (`NEXP ⊆ ACC⁰ ⟹ NEXP = MA`), via the deep inclusion
(`nexpSubsetMA_via_MIP`) and entry-202's antisymmetry (`karpLiptonCollapse_discharge`). -/
theorem karpLiptonCollapse_via_MIP (NEXP MIP ACC0 MA : CClass)
    (heq : NexpEqMIP NEXP MIP) (guessable : MIPSubsetMA_ofCircuits MIP ACC0 MA)
    (triv : MASubsetNexp MA NEXP) :
    KarpLiptonCollapse NEXP ACC0 MA :=
  karpLiptonCollapse_discharge NEXP ACC0 MA
    (nexpSubsetMA_via_MIP NEXP MIP ACC0 MA heq guessable) triv

end PallLean.Paper93.DeepMath.PathB.ACC0BFLCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BFLCollapse.nexpSubsetMA_via_MIP
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BFLCollapse.karpLiptonCollapse_via_MIP
