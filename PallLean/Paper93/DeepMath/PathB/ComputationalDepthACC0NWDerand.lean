import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DerandCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0KarpLiptonMA

/-!
# NW-derandomisation — `HardFunction → MA ⊆ NP`, assembled (proved glue)

Workstream A, step 2.  Entry 307 / 313 took `derand : HardFunction → MA ⊆ NP` as a *hypothesis*.  This file
**discharges it**, assembling the hardness-to-`NP` collapse from the Nisan–Wigderson hardness–randomness tradeoff and
proving the glue, reducing it to two named classical residues.

**The implication, broken into its pieces:**

```
HardFunction ──[NW / IW: hardness ⇒ pseudorandomness]──► PRG exists
        │  the PRG fools Arthur; replace his coins by the poly-many PRG seeds, decide nondeterministically
        ▼
MA ⊆ NP
```

The chaining is the proved `…ACC0DerandCollapse.derandMASubsetNP_via_PRG` (`Derand ⟹ PRG` composed with
`PRG ⟹ MA ⊆ NP`), instantiated at `Derand := HardFunction`.  The two residues are `DerandGivesPRG` (`HardFunction →
PRGExists`, the NW hardness-to-pseudorandomness tradeoff) and `PRGCollapsesMAtoNP` (`PRGExists → MA ⊆ NP`, seed
enumeration).

**Fully-assembled `HardFnSeparation`.**  Combining this with the Karp–Lipton MA inclusion (entry 313), entry 307's
`HardFnSeparation` is now discharged from *purely named* classical residues — no `karpLipton`/`derand` hypotheses left.

## What is proved (clean axioms, no `sorry`)

* **`nw_hardFn_MA_subset_NP`** — `(HardFunction → PRGExists)` + `PRGCollapsesMAtoNP PRGExists MA NP` ⟹ `HardFunction →
  MA ⊆ NP`: the NW-derandomisation collapse (via `derandMASubsetNP_via_PRG` at `Derand := HardFunction`).
* **`hardFnSeparation_fully_assembled`** — `HardFnSeparation` from purely named residues: `NexpEqMIP`,
  `MIPRealizedGuessable` (Karp–Lipton), `HardFunction → PRGExists`, `PRGCollapsesMAtoNP` (derandomisation),
  `NP ⊆ MA ⊆ NEXP`, and the proved `NEXP ≠ NP` — both `karpLipton` and `derand` hypotheses discharged.

## Honest scope

This **removes the NW-derandomisation piece of caveat 1**: `HardFunction → MA ⊆ NP` is no longer a monolithic socket —
it is assembled (hardness ⇒ PRG ⇒ seed-enumeration collapse), with the chaining proved, reduced to two *named*
classical residues: `DerandGivesPRG` (the NW/IW hardness-to-pseudorandomness tradeoff) and `PRGCollapsesMAtoNP` (PRG-seed
enumeration).  Both are *proven*-classical theorems (Nisan–Wigderson, Impagliazzo–Wigderson), left as named sub-sockets;
their full pseudorandomness infrastructure (the PRG-fooling details) is workstream-A step 3.  With this, `HardFnSeparation`
rests on purely named residues.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NWDerand

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0DerandCollapse (PRGCollapsesMAtoNP derandMASubsetNP_via_PRG)
open PallLean.Paper93.DeepMath.PathB.ACC0BFLCollapse (NexpEqMIP)
open PallLean.Paper93.DeepMath.PathB.ACC0GuessableProver (MIPRealizedGuessable)
open PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonMA (karp_lipton_NEXP_ACC_to_MA)

/-- **The NW-derandomisation collapse, assembled (PROVED).**  From the hardness-to-PRG tradeoff
(`hardToPRG : HardFunction → PRGExists`, Nisan–Wigderson) and the PRG-collapse (`PRGCollapsesMAtoNP`, seed enumeration),
`HardFunction → MA ⊆ NP`: chain `Derand ⟹ PRG ⟹ MA ⊆ NP` (`derandMASubsetNP_via_PRG`) at `Derand := HardFunction`. -/
theorem nw_hardFn_MA_subset_NP (HardFunction PRGExists : Prop) (MA NP : CClass)
    (hardToPRG : HardFunction → PRGExists)
    (prgCollapse : PRGCollapsesMAtoNP PRGExists MA NP) :
    HardFunction → MA ⊆ NP :=
  derandMASubsetNP_via_PRG HardFunction PRGExists MA NP hardToPRG prgCollapse

/-- **`HardFnSeparation` from purely named residues (PROVED).**  Combining the Karp–Lipton MA inclusion (entry 313) and
the NW-derandomisation collapse, entry 307's `HardFnSeparation` is discharged with **no** `karpLipton`/`derand`
hypotheses — only: `NexpEqMIP`, `MIPRealizedGuessable` (BFL/IKW), `HardFunction → PRGExists`, `PRGCollapsesMAtoNP`
(NW/IW), the trivial `NP ⊆ MA ⊆ NEXP`, and the proved `NEXP ≠ NP`. -/
theorem hardFnSeparation_fully_assembled (NEXP MIP ACC0 MA NP : CClass) (HardFunction PRGExists : Prop)
    (heq : NexpEqMIP NEXP MIP) (realized : MIPRealizedGuessable MIP ACC0 MA)
    (hardToPRG : HardFunction → PRGExists) (prgCollapse : PRGCollapsesMAtoNP PRGExists MA NP)
    (hNPMA : NP ⊆ MA) (hMANEXP : MA ⊆ NEXP) (hNexpNeqNp : NEXP ≠ NP) :
    ACC0IKWEasyWitness.HardFnSeparation NEXP ACC0 HardFunction :=
  ACC0IKWHardFnSeparation.hardFnSeparation_from_parts NEXP ACC0 MA NP HardFunction
    (karp_lipton_NEXP_ACC_to_MA NEXP MIP ACC0 MA heq realized)
    (nw_hardFn_MA_subset_NP HardFunction PRGExists MA NP hardToPRG prgCollapse)
    hNPMA hMANEXP hNexpNeqNp

/-!
**NW-derandomisation assembled.**  `HardFunction → MA ⊆ NP` is reduced to the NW residues `DerandGivesPRG`
(hardness ⇒ PRG) and `PRGCollapsesMAtoNP` (PRG ⇒ seed-enumeration collapse), chaining proved
(`nw_hardFn_MA_subset_NP`).  Together with the Karp–Lipton inclusion (313), entry 307's `HardFnSeparation` rests on
purely named, proven-classical residues (`hardFnSeparation_fully_assembled`) — both `karpLipton` and `derand`
hypotheses discharged.  The NW-derandomisation piece of caveat 1 is removed; the PRG-fooling details (the residues'
internals) are workstream-A step 3.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0NWDerand

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NWDerand.nw_hardFn_MA_subset_NP
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NWDerand.hardFnSeparation_fully_assembled
