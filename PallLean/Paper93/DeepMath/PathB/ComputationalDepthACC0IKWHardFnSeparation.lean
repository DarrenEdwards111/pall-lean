import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0IKWEasyWitness

/-!
# IKW, sub-socket 2 — a hard function ⇒ the separation, decomposed (proved glue)

Target 3 of the Williams socket elimination (IKW easy-witness, the deepest).  `…ACC0IKWEasyWitness` reduced the
easy-witness lemma to two sub-sockets: (1) `NoEasyWitnessHardFn` (no easy witness ⇒ a hard function) — *already
discharged* for the concrete `Circ` predicates (entry 150, `…ACC0NisanWigdersonEasyWitness`); and (2)
`HardFnSeparation` (a hard function ⇒ the separation).  This file **decomposes (2)** into the standard classical chain
and proves the glue:

```
HardFunction ──[NW derandomisation]──► MA ⊆ NP
NEXP ⊆ ACC⁰ ──[Karp–Lipton]──► NEXP ⊆ MA           ⊆ NP        (compose)
                                                    │
                          NP ⊆ MA ⊆ NEXP            ▼
                          ───────────────────► NEXP = NP   — contradicts  NEXP ≠ NP (entry 200, PROVED)
```

So a hard function, with `NEXP ⊆ ACC⁰`, collapses `NEXP = NP`, contradicting the nondeterministic time hierarchy's
`NEXP ≠ NP` (already proved by diagonalisation, `…ACC0NondetTimeHierarchy`).  This reduces IKW's last deep atom to the
**Karp–Lipton** circuit-collapse and the **NW-derandomisation** `MA ⊆ NP` — both classical, both decomposed elsewhere
in the corpus (entries 199/202/221/222/229) — with `NEXP ≠ NP` proved.

## What is proved (clean axioms, no `sorry`)

* **`hardFnSeparation_from_parts`** — `HardFnSeparation` from: Karp–Lipton (`NEXP ⊆ ACC⁰ → NEXP ⊆ MA`),
  NW-derandomisation (`HardFunction → MA ⊆ NP`), the trivial inclusions `NP ⊆ MA ⊆ NEXP`, and `NEXP ≠ NP` (entry 200).
* **`ikw_from_parts`** — the full IKW easy-witness lemma assembled: `NoEasyWitnessHardFn` (1, discharged) + the
  decomposition of (2) ⇒ `EasyWitnessLemma`.

## Honest scope

This decomposes IKW's deepest remaining atom (`HardFnSeparation`) into the Karp–Lipton collapse + NW-derandomisation +
the *proved* `NEXP ≠ NP`, and proves the composition — so IKW reduces to exactly those two classical sub-sockets, both
already isolated/decomposed in the corpus.  The proof is pure inclusion-chasing + antisymmetry against the proved time
hierarchy.  The two sub-sockets (Karp–Lipton, NW-derandomisation) are *proven*-classical theorems (formalised to their
own deep cores elsewhere), not open obstructions (`NEXP ⊄ ACC⁰` is Williams 2011).  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0IKWHardFnSeparation

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0IKWEasyWitness (HardFnSeparation NoEasyWitnessHardFn easyWitness_from_parts)

/-- **IKW sub-socket 2, decomposed (PROVED).**  A hard function gives the separation, via the classical chain: Karp–Lipton
(`NEXP ⊆ ACC⁰ → NEXP ⊆ MA`) and NW-derandomisation (`HardFunction → MA ⊆ NP`) compose to `NEXP ⊆ NP`; the trivial
`NP ⊆ MA ⊆ NEXP` give `NP ⊆ NEXP`; antisymmetry yields `NEXP = NP`, contradicting the proved `NEXP ≠ NP` (entry 200).
So `HardFunction → ¬ (NEXP ⊆ ACC⁰)`. -/
theorem hardFnSeparation_from_parts (NEXP ACC0 MA NP : CClass) (HardFunction : Prop)
    (karpLipton : NEXP ⊆ ACC0 → NEXP ⊆ MA)
    (derand : HardFunction → MA ⊆ NP)
    (hNPMA : NP ⊆ MA) (hMANEXP : MA ⊆ NEXP)
    (hNexpNeqNp : NEXP ≠ NP) :
    HardFnSeparation NEXP ACC0 HardFunction := by
  intro hHard hsub
  have hNexpNP : NEXP ⊆ NP := fun L hL => derand hHard (karpLipton hsub hL)
  have hNPNexp : NP ⊆ NEXP := fun L hL => hMANEXP (hNPMA hL)
  exact hNexpNeqNp (Set.Subset.antisymm hNexpNP hNPNexp)

/-- **The IKW easy-witness lemma assembled (PROVED).**  Combining sub-socket 1 (`NoEasyWitnessHardFn`, discharged at
entry 150) with the decomposition of sub-socket 2 gives the full easy-witness lemma.  IKW now rests on exactly the
Karp–Lipton collapse and the NW-derandomisation `MA ⊆ NP`, plus the proved `NEXP ≠ NP`. -/
theorem ikw_from_parts (NEXP ACC0 MA NP : CClass) (SmallWitnessCircuits HardFunction : Prop)
    (h1 : NoEasyWitnessHardFn SmallWitnessCircuits HardFunction)
    (karpLipton : NEXP ⊆ ACC0 → NEXP ⊆ MA)
    (derand : HardFunction → MA ⊆ NP)
    (hNPMA : NP ⊆ MA) (hMANEXP : MA ⊆ NEXP)
    (hNexpNeqNp : NEXP ≠ NP) :
    ACC0EasyWitness.EasyWitnessLemma NEXP ACC0 SmallWitnessCircuits :=
  easyWitness_from_parts NEXP ACC0 SmallWitnessCircuits HardFunction h1
    (hardFnSeparation_from_parts NEXP ACC0 MA NP HardFunction karpLipton derand hNPMA hMANEXP hNexpNeqNp)

/-!
**IKW, reduced to two classical sub-sockets.**  Sub-socket 1 (`NoEasyWitnessHardFn`) is discharged (entry 150); this
file decomposes sub-socket 2 (`HardFnSeparation`) into Karp–Lipton + NW-derandomisation + the *proved* `NEXP ≠ NP`
(`hardFnSeparation_from_parts`), and assembles the full easy-witness lemma (`ikw_from_parts`).  So the deepest Williams
ingredient now rests on exactly the Karp–Lipton circuit-collapse and the NW-derandomisation `MA ⊆ NP` — proven-classical
theorems decomposed elsewhere (entries 199/202/221/222/229), not open obstructions.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0IKWHardFnSeparation

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IKWHardFnSeparation.hardFnSeparation_from_parts
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IKWHardFnSeparation.ikw_from_parts
