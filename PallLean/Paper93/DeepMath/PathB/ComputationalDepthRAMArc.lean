import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMBeigelTaruiAxiom
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMSimDeciderSynthesis
import Mathlib.Tactic

/-!
# The RAM lazy-diagonal arc — capstone index and axiom audit

This file is the table of contents for the RAM lazy-diagonal-decider arc and a single-place audit of exactly
what every headline theorem rests on.  It imports the whole arc; the `#print axioms` block at the bottom is the
honest dependency ledger.

## The arc, step by step (all constructive parts `sorry`-free)

* **Step 1 — RAM memo-DP interpreter.**  A genuine RAM machine (`Mem = ℕ → ℕ`, indirect addressing the Kleene
  `Code` model lacks): `cellCopy` → indexed table access (`tableGet`/`tableSet`) → a verified clocked loop
  (`countLoop`, exact iteration count) → the memo DP fused into the loop (`dpLoop`, fills the table).

* **Step 2 — the lazy diagonal decider, as one integrated machine.**  decode/dispatch (`decodeDispatch`) →
  clock-to-a-bound (`clockedDecider`) → content-dependent universal simulation (`uSim`/`uSim2`, fetch–decode–
  dispatch each opcode) → the **full composition** `simDecider` (decode → dispatch → simulate / complement, in
  one program with relocated absolute pcs).  Plus the diagonalisation core: `ramDiag`, `ramDiag_not_mem` (the
  diagonal escapes the class — *unconditional*).

* **Step 3 — bit-cost discharged to proved value bounds (no hidden unit-cost cheating).**  The abstract
  bit-width hypothesis is reduced to a concrete value bound (`runCost_value_le`, `step_mem_le`, `step_acc_le`),
  then that value bound is *proved* for every reachable state of `simDecider`: the init phase, the **complement
  branch** (`simDecider_complement_cost`, unconditional), and the **simulator loop** — the genuinely hard part:
  intra-tick crux (`tick_intra_valueBounded`) composed over ticks (`loop_valueBounded`) and glued with the
  prefix into the **copy-branch cost** (`simDecider_copy_cost_mixed`, for *any* simulated program).

* **Step 6 — the target shape, reduced to two cited axioms.**  `NEXP_not_subset_ACC0_fromAxioms` proves
  `¬ (WilliamsNEXP ⊆ DesignatedACC0)` from exactly two named, cited classical axioms (the structural
  well-formedness facts are *proved* from concrete definitions): `beigelTarui_faithful` (Beigel–Tarui `SYM∘AND`
  quasipoly; budget domination = `ACC⁰` membership) and `williams_decider_in_NEXP` (the Williams fast-`SAT`
  speed-up).

* **Synthesis (step 3 ⋈ step 6).**  `simDecider_realises_ramDiag_efficient`: the same concrete machine computes
  the diagonal value `ramDiag sim x` **and** does so in proved poly bit-cost — correctness, efficiency, and the
  diagonal-realisation cohere on one `simDecider`.

## What this is and is not

It **is** a complete, machine-checked formalisation of the *implication* "Williams' two ingredients ⟹
`NEXP ⊄ ACC⁰`", with all constructive machinery (the RAM decider, its correctness, its polynomial bit-cost, and
the diagonalisation core) proved and `sorry`-free, and the entire separation-strength content isolated in two
explicit, cited axioms.

It **is not** a proof of `NEXP ⊄ ACC⁰`: discharging `beigelTarui_faithful` and `williams_decider_in_NEXP` *is*
the full Williams theorem (a real ACC-`SAT` algorithm + the Beigel–Tarui normal form + the nondeterministic
time hierarchy), which is barrier-respecting and not done here.  The two axioms are visible in every audit
below — nothing is hidden behind `sorry`, `Classical.choose`, or a vacuous `Prop`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

end PallLean.Paper93.DeepMath.PathB.RAM

/-! ### Axiom ledger — the honest dependency audit -/

-- The target separation: rests on exactly the two cited Williams-strength axioms (+ standard logic).
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.NEXP_not_subset_ACC0_fromAxioms

-- The diagonalisation core: unconditional (no custom axioms at all).
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.ramDiag_not_mem

-- The integrated decider computes the diagonal in proved poly bit-cost: no Williams axioms (pure constructive).
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_realises_ramDiag_efficient

-- Step 3 costs, both branches: pure constructive (no Williams axioms).
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_complement_cost
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_copy_cost_mixed

-- The reusable bit-cost reduction (value bound ⇒ poly bit-cost).
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.runCost_value_le
