import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EasyWitness

/-!
# The IKW easy-witness lemma — proof architecture (contrapositive glue proved, deep steps socketed)

The Impagliazzo–Kabanets–Wigderson easy-witness lemma — `NEXP ⊆ ACC⁰ ⇒ accepting `NTIME[2ⁿ]` computations have small
`ACC⁰` witness circuits` (`SmallWitnessCircuits`) — is the deepest Williams ingredient.  This file formalises its
**proof architecture** (the standard *contrapositive*) and proves the **glue**, reducing it to two genuinely-deep
sub-lemmas that remain sockets:

1. **No easy witness ⇒ a hard function** (`NoEasyWitnessHardFn`): if witnesses are *not* small-circuit describable,
   their truth tables are *hard* (no small circuits).
2. **A hard function ⇒ the separation** (`HardFnSeparation`): a hard function derandomises (Nisan–Wigderson) and, with
   a Karp–Lipton-style collapse, contradicts `NEXP ⊆ ACC⁰`.

The contrapositive: assuming `NEXP ⊆ ACC⁰`, witnesses *must* be easy (else (1)+(2) refute the assumption).

## What is proved (clean axioms, no `sorry`)

* **`NoEasyWitnessHardFn`**, **`HardFnSeparation`** — the two deep sub-lemmas, as named sockets.
* **`easyWitness_from_parts`** — the contrapositive glue: (1) ∧ (2) ⇒ `ACC0EasyWitness.EasyWitnessLemma`.
* **`nexp_not_acc0_full`** — the full Williams chain with IKW decomposed: (1) ∧ (2) ∧ guess-verify ∧ time hierarchy ∧
  a SAT speedup ⇒ `¬ (NEXP ⊆ ACC⁰)`.

## Honest scope

Only the contrapositive composition is proved.  The hard-function extraction and the derandomisation-to-separation —
the actual IKW content — are the named sockets; formalising them needs circuit lower bounds, Nisan–Wigderson
derandomisation, and a Karp–Lipton collapse (a major project).  This **does not** prove the easy-witness lemma.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0IKWEasyWitness

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)

/-- **Sub-socket 1 — no easy witness ⇒ a hard function.**  If witnesses are not small-circuit describable, their
truth tables have no small circuits (a hard function).  Stated, not proved. -/
def NoEasyWitnessHardFn (SmallWitnessCircuits HardFunction : Prop) : Prop :=
  ¬ SmallWitnessCircuits → HardFunction

/-- **Sub-socket 2 — a hard function ⇒ the separation.**  A hard function derandomises (Nisan–Wigderson) and, with a
Karp–Lipton-style collapse, contradicts `NEXP ⊆ ACC⁰`.  Stated, not proved. -/
def HardFnSeparation (NEXP ACC0 : CClass) (HardFunction : Prop) : Prop :=
  HardFunction → ¬ (NEXP ⊆ ACC0)

/-- **The IKW contrapositive glue (proved): (1) ∧ (2) ⇒ the easy-witness lemma.**  Assuming `NEXP ⊆ ACC⁰`, witnesses
must be easy: were they not, the hard function (1) would refute the assumption via (2). -/
theorem easyWitness_from_parts (NEXP ACC0 : CClass) (SmallWitnessCircuits HardFunction : Prop)
    (h1 : NoEasyWitnessHardFn SmallWitnessCircuits HardFunction)
    (h2 : HardFnSeparation NEXP ACC0 HardFunction) :
    ACC0EasyWitness.EasyWitnessLemma NEXP ACC0 SmallWitnessCircuits :=
  fun hsub => Classical.byContradiction (fun hns => h2 (h1 hns) hsub)

/-- **The full Williams chain with IKW decomposed (proved glue): `¬ (NEXP ⊆ ACC⁰)`.**  The two IKW sub-lemmas give the
easy-witness lemma; with guess-and-verify, the nondeterministic time hierarchy, and a SAT speedup, the separation
follows.  Reduces `NEXP ⊄ ACC⁰` to `{NoEasyWitnessHardFn, HardFnSeparation, GuessVerify, NondetTimeHierarchy}`. -/
theorem nexp_not_acc0_full (NEXP ACC0 NTIME2n NTIME2nFast : CClass)
    (ACC0SatSpeedup SmallWitnessCircuits HardFunction : Prop)
    (h1 : NoEasyWitnessHardFn SmallWitnessCircuits HardFunction)
    (h2 : HardFnSeparation NEXP ACC0 HardFunction)
    (gv : ACC0EasyWitness.GuessVerify NTIME2n NTIME2nFast ACC0SatSpeedup SmallWitnessCircuits)
    (hierarchy : ACC0WilliamsMetaTheorem.NondetTimeHierarchy NTIME2n NTIME2nFast)
    (speedup : ACC0SatSpeedup) :
    ¬ (NEXP ⊆ ACC0) :=
  ACC0EasyWitness.nexp_not_acc0_from_witness_parts NEXP ACC0 NTIME2n NTIME2nFast
    ACC0SatSpeedup SmallWitnessCircuits
    (easyWitness_from_parts NEXP ACC0 SmallWitnessCircuits HardFunction h1 h2) gv hierarchy speedup

end PallLean.Paper93.DeepMath.PathB.ACC0IKWEasyWitness

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IKWEasyWitness.easyWitness_from_parts
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IKWEasyWitness.nexp_not_acc0_full
