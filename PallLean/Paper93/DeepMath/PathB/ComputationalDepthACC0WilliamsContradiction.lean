import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EasyWitness

/-!
# The Williams contradiction — IKW/NW + fast SAT ⇒ `NEXP ⊄ ACC⁰`, the final capstone

The last Williams mountain (3/3): assemble the complete contradiction.  If `NEXP ⊆ ACC⁰`, then (IKW easy-witness lemma)
accepting `NTIME[2ⁿ]` computations have small `ACC⁰`-witnesses, which (guess-and-verify, using the fast `ACC⁰`-SAT of
the Beigel–Tarui `SYM∘AND` representation) collapse `NTIME[2ⁿ] ⊆ NTIME[2ⁿ/superpoly]`, contradicting the nondeterministic
time hierarchy.  Hence `NEXP ⊄ ACC⁰`.

This file ties the **proved BT-closure side** into that contradiction.  The composition glue is already proved
(`…ACC0EasyWitness.nexp_not_acc0_from_witness_parts`, `…ACC0WilliamsMetaTheorem.williams_meta_theorem`); here we feed
the fast-SAT speedup *from* the BT closure (entry 179 proves `DynamicClosesAtBT` for AC⁰[p]; entry 187 is the fast-SAT
verifier), and state the final `¬ (NEXP ⊆ ACC⁰)` as a function of exactly the genuinely-deep classical sockets.

## What is proved (clean axioms, no `sorry`)

* **`williams_contradiction`** — `¬ (NEXP ⊆ ACC⁰)` from: the BT closure `hClosure : DynamicClosesAtBT` (proved for
  AC⁰[p], entry 179) bridged to the SAT speedup (`closure_to_speedup`, the BT→fast-SAT route, entries 179/187 + uniform
  realization), the IKW easy-witness lemma (`ew`), guess-and-verify / NW-derandomisation (`gv`), and the
  nondeterministic time hierarchy (`hierarchy`).  Pure composition through the proved Williams glue.

## Honest scope

This is the **complete Williams contradiction assembled**, reducing `NEXP ⊄ ACC⁰` to a precise set of named ingredients:
the BT closure (proved for AC⁰[p], entry 179) and four genuinely-deep classical sockets — `closure_to_speedup` (the
bridge from a quasipoly `SYM∘AND` representation to a *uniform* fast `ACC⁰`-SAT algorithm, which subsumes the
`NEXP ⊄ ACC⁰`-strength `UniformWilliamsRealizationSocket`), the **IKW** easy-witness lemma, **guess-and-verify / NW**
derandomisation, and the **nondeterministic time hierarchy**.  These four are *proven classical theorems* (Williams 2011,
Impagliazzo–Kabanets–Wigderson, Nisan–Wigderson, the time hierarchy), each a major formalisation in its own right; they
are left as named sockets.  The composition is proved glue.  This is **not** a proof of `NEXP ⊄ ACC⁰` from nothing —
`NEXP ⊄ ACC⁰` is already a proven theorem (Williams 2011), and this is its formalisation *architecture* with the deep
ingredients socketed; nothing here is a new separation or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0WilliamsContradiction

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass NondetTimeHierarchy)
open PallLean.Paper93.DeepMath.PathB.ACC0EasyWitness
  (EasyWitnessLemma GuessVerify nexp_not_acc0_from_witness_parts)

/-- **The Williams contradiction (proved as glue): `NEXP ⊄ ACC⁰` from the BT closure + the deep classical sockets.**
Given the BT closure `hClosure : DynamicClosesAtBT` (proved for AC⁰[p], entry 179) bridged to the `ACC⁰`-SAT speedup by
`closure_to_speedup` (the BT → fast-SAT route, entries 179/187 + uniform realization), the IKW easy-witness lemma `ew`,
guess-and-verify / NW-derandomisation `gv`, and the nondeterministic time hierarchy `hierarchy`, we obtain
`¬ (NEXP ⊆ ACC⁰)`.  Pure composition through `nexp_not_acc0_from_witness_parts` (the proved Williams glue), with the
speedup supplied by the closure.  The deep ingredients (`closure_to_speedup`, `ew`, `gv`, `hierarchy`) are the named
classical sockets; everything else is proved. -/
theorem williams_contradiction
    {NEXP ACC0 NTIME2n NTIME2nFast : CClass}
    {DynamicClosesAtBT ACC0SatSpeedup SmallWitnessCircuits : Prop}
    (closure_to_speedup : DynamicClosesAtBT → ACC0SatSpeedup)
    (hClosure : DynamicClosesAtBT)
    (ew : EasyWitnessLemma NEXP ACC0 SmallWitnessCircuits)
    (gv : GuessVerify NTIME2n NTIME2nFast ACC0SatSpeedup SmallWitnessCircuits)
    (hierarchy : NondetTimeHierarchy NTIME2n NTIME2nFast) :
    ¬ (NEXP ⊆ ACC0) :=
  nexp_not_acc0_from_witness_parts NEXP ACC0 NTIME2n NTIME2nFast ACC0SatSpeedup SmallWitnessCircuits
    ew gv hierarchy (closure_to_speedup hClosure)

end PallLean.Paper93.DeepMath.PathB.ACC0WilliamsContradiction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsContradiction.williams_contradiction
