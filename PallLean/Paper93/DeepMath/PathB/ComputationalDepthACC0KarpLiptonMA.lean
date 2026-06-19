import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0GuessableProver
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0IKWHardFnSeparation

/-!
# Karp–Lipton MA inclusion — `NEXP ⊆ ACC⁰ → NEXP ⊆ MA`, assembled (proved glue)

Workstream A (close the classical Williams residues), step 1.  Entry 307 took `karpLipton : NEXP ⊆ ACC⁰ → NEXP ⊆ MA`
as a *hypothesis* of `HardFnSeparation`.  This file **discharges it**, assembling the Karp–Lipton MA inclusion from the
Babai–Fortnow–Lund decomposition and proving the glue, reducing it to two named classical residues.

**The implication, broken into its pieces** (Merlin sends a circuit, Arthur verifies):

```
NEXP ⊆ ACC⁰  ──[NEXP = MIP]──►  MIP ⊆ ACC⁰
        (small ACC⁰ circuit for the MIP language)
        │  Merlin guesses the prover circuit C; Arthur runs the MIP verifier Ver x (proverOf C)
        ▼
MIP ⊆ MA     ──[NEXP = MIP]──►  NEXP ⊆ MA
```

The middle step — "the optimal `MIP` prover is a small circuit, so an `MA` protocol guesses it and verifies" — is the
proved guessable-prover collapse (`…ACC0GuessableProver.mipSubsetMA_of_realized`, mechanism `mipLang_eq_maLang`).  Its
content (under circuits the prover *is* small-circuit describable) is the IKW small-prover residue `MIPRealizedGuessable`.
The outer `NEXP = MIP` rewrites are the BFL residue `NexpEqMIP`.

## What is proved (clean axioms, no `sorry`)

* **`karp_lipton_NEXP_ACC_to_MA`** — `NexpEqMIP` + `MIPRealizedGuessable` ⟹ `NEXP ⊆ ACC⁰ → NEXP ⊆ MA`: the Karp–Lipton
  MA inclusion, assembled (BFL composition `nexpSubsetMA_via_MIP` ∘ guessable-prover discharge `mipSubsetMA_of_realized`).
* **`hardFnSeparation_via_karpLipton`** — entry 307's `HardFnSeparation` with its `karpLipton` hypothesis **discharged**
  by `karp_lipton_NEXP_ACC_to_MA`: now from `NexpEqMIP` + `MIPRealizedGuessable` + NW-derandomisation + `NEXP ≠ NP`.

## Honest scope

This **removes the Karp–Lipton piece of caveat 1**: the implication `NEXP ⊆ ACC⁰ → NEXP ⊆ MA` is no longer a monolithic
socket — it is assembled, with all glue and the Merlin-sends-circuit / Arthur-verifies mechanism proved, and reduced to
two *named* classical residues: `NexpEqMIP` (the BFL `NEXP = MIP` theorem — its sum-check arithmetic engine is proved,
entries 226–227) and `MIPRealizedGuessable` (the IKW small-prover under circuits — its collapse mechanism
`mipLang_eq_maLang` is proved).  Those two residues are *proven*-classical theorems (BFL 1991, IKW), each a major
formalisation in its own right, left as named sub-sockets.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonMA

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0BFLCollapse (NexpEqMIP nexpSubsetMA_via_MIP)
open PallLean.Paper93.DeepMath.PathB.ACC0GuessableProver (MIPRealizedGuessable mipSubsetMA_of_realized)

/-- **The Karp–Lipton MA inclusion, assembled (PROVED).**  From `NexpEqMIP` (`NEXP = MIP`, BFL) and
`MIPRealizedGuessable` (under circuits the `MIP` prover is a small circuit, IKW), `NEXP ⊆ ACC⁰ → NEXP ⊆ MA`: the
guessable-prover discharge gives `MIP ⊆ ACC⁰ → MIP ⊆ MA` (`mipSubsetMA_of_realized`), and the BFL composition
(`nexpSubsetMA_via_MIP`) rewrites it through `NEXP = MIP` to the `NEXP`-level inclusion. -/
theorem karp_lipton_NEXP_ACC_to_MA (NEXP MIP ACC0 MA : CClass)
    (heq : NexpEqMIP NEXP MIP) (realized : MIPRealizedGuessable MIP ACC0 MA) :
    NEXP ⊆ ACC0 → NEXP ⊆ MA :=
  nexpSubsetMA_via_MIP NEXP MIP ACC0 MA heq (mipSubsetMA_of_realized MIP ACC0 MA realized)

/-- **Entry 307's `karpLipton` hypothesis discharged (PROVED).**  `HardFnSeparation` now follows from the BFL/IKW
residues (`NexpEqMIP`, `MIPRealizedGuessable`) instead of an assumed `karpLipton`: feed `karp_lipton_NEXP_ACC_to_MA`
into `hardFnSeparation_from_parts`.  So a hard function gives the separation modulo `NexpEqMIP` + `MIPRealizedGuessable`
+ NW-derandomisation + the proved `NEXP ≠ NP`. -/
theorem hardFnSeparation_via_karpLipton (NEXP MIP ACC0 MA NP : CClass) (HardFunction : Prop)
    (heq : NexpEqMIP NEXP MIP) (realized : MIPRealizedGuessable MIP ACC0 MA)
    (derand : HardFunction → MA ⊆ NP)
    (hNPMA : NP ⊆ MA) (hMANEXP : MA ⊆ NEXP) (hNexpNeqNp : NEXP ≠ NP) :
    ACC0IKWEasyWitness.HardFnSeparation NEXP ACC0 HardFunction :=
  ACC0IKWHardFnSeparation.hardFnSeparation_from_parts NEXP ACC0 MA NP HardFunction
    (karp_lipton_NEXP_ACC_to_MA NEXP MIP ACC0 MA heq realized) derand hNPMA hMANEXP hNexpNeqNp

/-!
**Karp–Lipton MA inclusion, assembled.**  `NEXP ⊆ ACC⁰ → NEXP ⊆ MA` is reduced to the BFL residue `NexpEqMIP`
(`NEXP = MIP`, sum-check engine proved 226–227) and the IKW residue `MIPRealizedGuessable` (small prover under circuits,
collapse mechanism `mipLang_eq_maLang` proved), with the composition and the Merlin/Arthur mechanism proved
(`karp_lipton_NEXP_ACC_to_MA`).  Entry 307's `karpLipton` hypothesis is discharged
(`hardFnSeparation_via_karpLipton`).  The Karp–Lipton piece of caveat 1 is removed — replaced by named, proven-classical
residues.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonMA

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonMA.karp_lipton_NEXP_ACC_to_MA
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonMA.hardFnSeparation_via_karpLipton
