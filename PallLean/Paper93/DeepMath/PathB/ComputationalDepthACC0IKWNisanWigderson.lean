import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0IKWEasyWitness

/-!
# IKW, refined — exposing the Nisan–Wigderson derandomisation socket

Entry 150 decomposed the IKW easy-witness lemma into two sub-sockets: `NoEasyWitnessHardFn` (no easy witness ⇒ a hard
function) and `HardFnSeparation` (a hard function ⇒ `¬ (NEXP ⊆ ACC⁰)`).  That second socket *bundles* the two genuinely
distinct classical steps — the **Nisan–Wigderson derandomisation** (hardness ⇒ a PRG defeating `ACC⁰`) and the
**Karp–Lipton collapse** (derandomisation + the circuit upper bound ⇒ the separation).  This file refines it: it exposes
the NW derandomisation as its own named socket and proves the glue `NW + Karp–Lipton ⇒ HardFnSeparation`, so the IKW
chain now names NW explicitly.

## What is proved (clean axioms, no `sorry`)

* **`NWDerandomization`** — the Nisan–Wigderson socket: a hard function yields a derandomisation (PRG defeating `ACC⁰`).
* **`DerandKarpLiptonSeparation`** — the collapse socket: derandomisation ⇒ `¬ (NEXP ⊆ ACC⁰)` (Karp–Lipton style).
* **`hardFnSeparation_from_NW`** — the refinement glue: `NWDerandomization` + `DerandKarpLiptonSeparation` ⇒ the entry-150
  socket `HardFnSeparation`.
* **`easyWitness_from_NW`** — IKW from the *refined* ingredients: `NoEasyWitnessHardFn` + NW + Karp–Lipton ⇒
  `EasyWitnessLemma`, with NW exposed.

## Honest scope

This refines the IKW socket of entry 150 by *naming the Nisan–Wigderson derandomisation* as its own ingredient; the glue
(NW + Karp–Lipton ⇒ HardFnSeparation, and the full IKW assembly) is proved.  The three classical pieces — the
no-easy-witness-to-hardness step, **Nisan–Wigderson** (hardness ⇒ PRG), and the **Karp–Lipton** derandomisation-to-
separation collapse — remain named sub-sockets; each is a *proven classical theorem* requiring circuit-complexity /
pseudorandomness infrastructure absent here.  This does **not** prove IKW or NW — both are proven theorems — but exposes
the NW core in the formalisation architecture; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0IKWNisanWigderson

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0IKWEasyWitness
  (NoEasyWitnessHardFn HardFnSeparation easyWitness_from_parts)

/-- **The Nisan–Wigderson derandomisation socket.**  A hard Boolean function yields a derandomisation — a pseudorandom
generator defeating `ACC⁰` (the NW / Impagliazzo–Wigderson generator).  Stated, not proved. -/
def NWDerandomization (HardFunction Derandomization : Prop) : Prop :=
  HardFunction → Derandomization

/-- **The Karp–Lipton collapse socket.**  A derandomisation, together with the circuit upper bound, collapses to the
separation `¬ (NEXP ⊆ ACC⁰)` (Karp–Lipton style).  Stated, not proved. -/
def DerandKarpLiptonSeparation (NEXP ACC0 : CClass) (Derandomization : Prop) : Prop :=
  Derandomization → ¬ (NEXP ⊆ ACC0)

/-- **Refinement glue (proved): NW + Karp–Lipton ⇒ `HardFnSeparation`.**  A hard function derandomises
(`NWDerandomization`), and that derandomisation collapses to the separation (`DerandKarpLiptonSeparation`) — composing to
the entry-150 socket `HardFnSeparation` (hard function ⇒ `¬ (NEXP ⊆ ACC⁰)`), now with NW named. -/
theorem hardFnSeparation_from_NW (NEXP ACC0 : CClass) (HardFunction Derandomization : Prop)
    (nw : NWDerandomization HardFunction Derandomization)
    (kl : DerandKarpLiptonSeparation NEXP ACC0 Derandomization) :
    HardFnSeparation NEXP ACC0 HardFunction :=
  fun hf => kl (nw hf)

/-- **IKW from the refined ingredients (proved glue): with NW exposed.**  The no-easy-witness-to-hardness step, the NW
derandomisation, and the Karp–Lipton collapse together give the IKW easy-witness lemma — composing
`hardFnSeparation_from_NW` into the entry-150 contrapositive `easyWitness_from_parts`. -/
theorem easyWitness_from_NW (NEXP ACC0 : CClass)
    (SmallWitnessCircuits HardFunction Derandomization : Prop)
    (h1 : NoEasyWitnessHardFn SmallWitnessCircuits HardFunction)
    (nw : NWDerandomization HardFunction Derandomization)
    (kl : DerandKarpLiptonSeparation NEXP ACC0 Derandomization) :
    ACC0EasyWitness.EasyWitnessLemma NEXP ACC0 SmallWitnessCircuits :=
  easyWitness_from_parts NEXP ACC0 SmallWitnessCircuits HardFunction h1
    (hardFnSeparation_from_NW NEXP ACC0 HardFunction Derandomization nw kl)

end PallLean.Paper93.DeepMath.PathB.ACC0IKWNisanWigderson

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IKWNisanWigderson.hardFnSeparation_from_NW
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IKWNisanWigderson.easyWitness_from_NW
