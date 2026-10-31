import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsMetaTheorem

/-!
# The easy-witness collapse — proof architecture (glue proved, IKW + guess-verify socketed)

`EasyWitnessCollapse` — *a fast `ACC⁰`-SAT algorithm together with `NEXP ⊆ ACC⁰` simulates `NTIME[2ⁿ]` within
`NTIME[2ⁿ/superpoly]`* — was the second deep socket of the Williams meta-theorem.  This file formalises its **internal
architecture** and proves the **glue**, reducing it to its two genuinely-deep ingredients (which remain sockets):

1. **The easy-witness lemma (IKW)** — `NEXP ⊆ ACC⁰` ⇒ accepting `NTIME[2ⁿ]` computations have *small* (`ACC⁰`-circuit
   encodable) witnesses.  Impagliazzo–Kabanets–Wigderson.
2. **Guess-and-verify** — small witness circuits together with the `ACC⁰`-SAT speedup ⇒ `NTIME[2ⁿ] ⊆
   NTIME[2ⁿ/superpoly]` (a nondeterministic machine guesses the small witness circuit and verifies it with the fast
   SAT algorithm, running faster).

The composition `(1) ∘ (2)` is `EasyWitnessCollapse`; the glue is proved, the two ingredients are named hypotheses.

## What is proved (clean axioms, no `sorry`)

* **`EasyWitnessLemma`**, **`GuessVerify`** — the two ingredients, over the complexity-class framework.
* **`easyWitnessCollapse_from_parts`** — the glue: `EasyWitnessLemma` ∧ `GuessVerify` ⇒
  `ACC0WilliamsMetaTheorem.EasyWitnessCollapse`.
* **`nexp_not_acc0_from_witness_parts`** — fused with the hierarchy: the two ingredients + `NondetTimeHierarchy` +
  `ACC0SatSpeedup` ⇒ `¬ (NEXP ⊆ ACC⁰)` (Williams, with `EasyWitnessCollapse` unpacked one level).

## Honest scope

Only the composition glue is proved.  The easy-witness lemma (IKW) and the guess-and-verify simulation — the actual
mathematical content — are the named sockets `EasyWitnessLemma` / `GuessVerify`; formalising them needs circuit
complexity and nondeterministic-simulation infrastructure (a separate major project).  This **does not** prove
`EasyWitnessCollapse`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EasyWitness

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass)

/-- **Ingredient 1 — the easy-witness lemma (IKW, socket).**  `NEXP ⊆ ACC⁰` ⇒ accepting `NTIME[2ⁿ]` computations have
small (`ACC⁰`-encodable) witnesses (`SmallWitnessCircuits`).  Stated, not proved. -/
def EasyWitnessLemma (NEXP ACC0 : CClass) (SmallWitnessCircuits : Prop) : Prop :=
  NEXP ⊆ ACC0 → SmallWitnessCircuits

/-- **Ingredient 2 — guess-and-verify (socket).**  Small witness circuits together with the `ACC⁰`-SAT speedup ⇒
`NTIME[2ⁿ] ⊆ NTIME[2ⁿ/superpoly]` (guess the small circuit, verify with fast SAT).  Stated, not proved. -/
def GuessVerify (NTIME2n NTIME2nFast : CClass) (ACC0SatSpeedup SmallWitnessCircuits : Prop) : Prop :=
  SmallWitnessCircuits → ACC0SatSpeedup → NTIME2n ⊆ NTIME2nFast

/-- **The easy-witness collapse glue (proved): IKW ∘ guess-verify = `EasyWitnessCollapse`.**  Given the easy-witness
lemma and guess-and-verify, a fast `ACC⁰`-SAT algorithm plus `NEXP ⊆ ACC⁰` yields the `NTIME` collapse: extract small
witnesses (IKW), then guess-and-verify them with the speedup. -/
theorem easyWitnessCollapse_from_parts
    (NEXP ACC0 NTIME2n NTIME2nFast : CClass) (ACC0SatSpeedup SmallWitnessCircuits : Prop)
    (ew : EasyWitnessLemma NEXP ACC0 SmallWitnessCircuits)
    (gv : GuessVerify NTIME2n NTIME2nFast ACC0SatSpeedup SmallWitnessCircuits) :
    ACC0WilliamsMetaTheorem.EasyWitnessCollapse NEXP ACC0 NTIME2n NTIME2nFast ACC0SatSpeedup :=
  fun speedup hsub => gv (ew hsub) speedup

/-- **Williams with the collapse unpacked (proved glue): `¬ (NEXP ⊆ ACC⁰)` from the two ingredients + hierarchy.**  The
easy-witness lemma and guess-and-verify compose to the collapse, which with the nondeterministic time hierarchy and a
SAT speedup forces the separation.  Reduces `NEXP ⊄ ACC⁰` to `{EasyWitnessLemma, GuessVerify, NondetTimeHierarchy}`. -/
theorem nexp_not_acc0_from_witness_parts
    (NEXP ACC0 NTIME2n NTIME2nFast : CClass) (ACC0SatSpeedup SmallWitnessCircuits : Prop)
    (ew : EasyWitnessLemma NEXP ACC0 SmallWitnessCircuits)
    (gv : GuessVerify NTIME2n NTIME2nFast ACC0SatSpeedup SmallWitnessCircuits)
    (hierarchy : ACC0WilliamsMetaTheorem.NondetTimeHierarchy NTIME2n NTIME2nFast)
    (speedup : ACC0SatSpeedup) :
    ¬ (NEXP ⊆ ACC0) :=
  ACC0WilliamsMetaTheorem.williams_meta_theorem NEXP ACC0 NTIME2n NTIME2nFast ACC0SatSpeedup
    (easyWitnessCollapse_from_parts NEXP ACC0 NTIME2n NTIME2nFast ACC0SatSpeedup
      SmallWitnessCircuits ew gv)
    hierarchy speedup

end PallLean.Paper93.DeepMath.PathB.ACC0EasyWitness

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EasyWitness.easyWitnessCollapse_from_parts
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EasyWitness.nexp_not_acc0_from_witness_parts
