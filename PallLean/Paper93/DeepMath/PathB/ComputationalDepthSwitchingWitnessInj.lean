import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessReconstruct
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reconstruction

/-!
# Håstad switching lemma — the confound broken, operationally: unconditional witness injectivity

Attacking the confound directly.  The confound is `hinj`: the injection `ρ ↦ (leaf, label)` is
injective on the bad set, equivalently the decoder recovers `ρ` from the leaf + label.  The four
earlier routes all needed `hnf` because their decoders **recompute** the active term from the leaf and
cannot tell a `ρ`-falsified term from a path-falsified one.

The **witness** decoder breaks exactly that: it does not recompute — the label records each step's
active-term **index** in `cs` (and the literal position), so `witDecode` reads the selected variable
off `cs[clauseIdx].lits[pos]` directly, with no scan and no `hnf` (`witDecode_deepestWitSeq`, already
in the codebase).  Combined with `deepestEnd_inj`, this gives **unconditional** injectivity:

  `deepest_witness_inj` — `ρ ↦ (deepestEnd cs F ρ, deepestWitSeq cs F ρ)` is injective, for **all** `ρ`
  (no `hnf`, no confound).

## Honest reading — what this costs

This discharges `hinj` for the general regime — the operational confound-break — but the witness label
is `(position, clause-index)` per step, so its count is `(w·|cs|)^s` (an extra `|cs|^s` factor), not
the tight `(2w)^s`.  The `|cs|` factor is the price of *naming* the active term instead of recomputing
it: the witness sidesteps the confound by recording the live clause, which the tight `(2w)^s` bound
specifically refuses to do.  So this is genuine unconditional injectivity (the confound *is* broken
here), at a non-tight count.  The tight `(2w)^s` general bound still requires recomputation
(= the confound proper).

## What is proved (clean axioms, no `sorry`)

* `deepest_witness_inj` — unconditional injectivity of the witness injection (the confound, broken).

## Honest scope

`hinj` discharged unconditionally via the witness (clause-index) decoder — general `ρ`, no `hnf`.  The
cost is the `|cs|` label factor (non-tight count).  AC⁰/depth-3; `Depth3CollapseModel.collapse` and
P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The confound, broken operationally.**  The witness injection `ρ ↦ (deepestEnd cs F ρ,
deepestWitSeq cs F ρ)` is injective for **every** `ρ` — no `hnf`.  The witness names each step's active
clause, so `witDecode` recovers the selected set without recomputation (`witDecode_deepestWitSeq`,
`hnf`-free), and `deepestEnd_inj` recovers `ρ`. -/
theorem deepest_witness_inj (cs : List (Clause n)) (F : ℕ) {ρ σ : Restriction n}
    (hE : deepestEnd cs F ρ = deepestEnd cs F σ)
    (hW : deepestWitSeq cs F ρ = deepestWitSeq cs F σ) :
    ρ = σ := by
  refine deepestEnd_inj cs F hE ?_
  rw [← witDecode_deepestWitSeq cs F ρ, ← witDecode_deepestWitSeq cs F σ, hW]

/-!
**Confound broken (operationally), unconditionally.**  The witness injection is injective for all
`ρ` — `hinj` discharged with no `hnf`.  The witness records the active clause index, so the count
carries the `|cs|` factor (non-tight); the tight `(2w)^s` general bound still needs the
recomputation-based decoder (the confound proper).  Genuine, not faked.  AC⁰/depth-3; collapse + P≠NP
untouched.
-/

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_witness_inj
