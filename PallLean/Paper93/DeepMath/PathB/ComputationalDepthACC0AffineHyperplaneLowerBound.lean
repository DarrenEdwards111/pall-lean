import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CrossFieldCountCore

/-!
# Affine hyperplane lower bound — the honest negative: the fire-count is EASY, refining the hard hypothesis

The focused program asked to prove `affineHyperplane_fireCount_modq_hard` for the entry-258 family
`gates i x = decide (∑ⱼ xⱼ = targets i)`.  Attacking it directly reveals the opposite, and the finding is important:

> **The affine (parallel) hyperplane fire-count is trivially EASY, not hard.**

Parallel hyperplanes `{x : ∑ⱼ xⱼ = targets i}` (fixed all-ones direction, distinct targets) are **disjoint**: any
input has a *single* coordinate-sum value, so it lies on **at most one** hyperplane.  Hence the fire-count is `≤ 1`
(`affineHyperplane_fireCount_le_one`) and the mod-`q` fire-count is `≤ 1` (`affineHyperplane_crossFieldCount_le_one`) —
a trivial 2-cell observer computes it.  So `affineHyperplane_fireCount_modq_hard` is **false** for this family.

**Why this matters (the refinement).**  Entry 258 proved this family is `AlgExpander` (linearly-independent
indicators, full rank).  So we now have a clean theorem-level fact: **`AlgExpander` (indicator rank) is NOT sufficient
for count-hardness** — the parallel affine family is a full-rank algebraic expander whose fire-count is trivial.  The
count-hardness needs something `AlgExpander` does not capture: the gates must **co-fire** in rich patterns
(simultaneously, in many-sized subsets).  Parallel/disjoint families never co-fire (`≤ 1` fires).  So:

* indicator-rank / `AlgExpander` (entries 256–258) — *necessary*, governs whether the indicators are independent;
* **co-firing richness** (overlapping, *varying-direction* gates that fire together in complex patterns) — the *extra*
  ingredient the count lower bound actually needs.

This also means the proposed bridge `AlgExpanderCountObstruction → NEXP ⊄ ACC⁰` with the *naive* `AlgExpander` hypothesis
is **unsound** (this family is a counterexample); the genuine upstream condition is co-firing-rich count-hardness — the
Razborov–Smolensky lower bound, proved in-arc for the (co-firing) `MOD_q` family (`Layer4.mod_q_indicators_false`).

⚠️ **No crossing, no faked target.**  The easy-ness facts are proved.  The *correct* hard family
(varying-direction hyperplanes / co-firing gates) and the lower bound on it remain the Smolensky-strength socket.

## What is proved (clean axioms, no `sorry`)

* **`affineHyperplane_fireCount_le_one`** (PROVED) — for injective `targets`, `#{i : ∑ⱼ xⱼ = targets i} ≤ 1`: parallel
  hyperplanes are disjoint (at most one fires; `Finset.card_le_one` + injectivity).
* **`affineHyperplane_crossFieldCount_le_one`** (PROVED) — the mod-`q` fire-count of the parallel affine family is
  `≤ 1` (`Nat.mod_le` + the above): trivially easy, refuting `affineHyperplane_fireCount_modq_hard`.

## The refined hard hypothesis (named, not proved)

The count lower bound needs **co-firing richness**, not just indicator independence: a family whose gates fire
*simultaneously* in many distinct patterns (overlapping, varying-direction).  The varying-direction hyperplane family
`{⟨aᵢ, x⟩ = bᵢ}` with distinct directions `aᵢ` is the candidate hard family (inputs satisfy many simultaneously).  The
lower bound on it is the entry-256/257 socket with the *corrected* (co-firing) hypothesis — Razborov–Smolensky,
proved in-arc for `MOD_q` (`Layer4.mod_q_indicators_false`).  Not proved here.

## Honest scope

This proves the affine *parallel* hyperplane fire-count is easy (`≤ 1`), refuting the proposed lower-bound target for
this family, and thereby establishes the theorem-level fact that `AlgExpander` is *not* sufficient for count-hardness
(co-firing richness is the missing ingredient).  It does **not** prove the lower bound for the corrected (co-firing)
family — the Smolensky-strength socket.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplaneLowerBound

open PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCountCore

/-- **Parallel affine hyperplanes are disjoint — fire-count `≤ 1` (PROVED).**  For injective `targets`, at most one of
the parallel hyperplanes `{∑ⱼ xⱼ = targets i}` contains a given `x` (it has a single coordinate-sum value).  So the
fire-count is `≤ 1`: trivially easy. -/
theorem affineHyperplane_fireCount_le_one {p n s : ℕ} (targets : Fin s → ZMod p)
    (hinj : Function.Injective targets) (x : Fin (n + 1) → ZMod p) :
    (Finset.univ.filter (fun i => decide ((∑ j, x j) = targets i) = true)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, decide_eq_true_eq] at ha hb
  exact hinj (ha.2.symm.trans hb.2)

/-- **The mod-`q` fire-count of the parallel affine family is `≤ 1` (PROVED).**  From `fireCount ≤ 1` and `Nat.mod_le`:
the cross-field count is `≤ 1`, computed by a trivial 2-cell observer.  This **refutes**
`affineHyperplane_fireCount_modq_hard` — the family is `AlgExpander` (entry 258) yet count-easy, so indicator rank is
*not* sufficient for count-hardness. -/
theorem affineHyperplane_crossFieldCount_le_one {p n s : ℕ} (q : ℕ) (targets : Fin s → ZMod p)
    (hinj : Function.Injective targets) (x : Fin (n + 1) → ZMod p) :
    crossFieldCount q
      (fun (i : Fin s) (x : Fin (n + 1) → ZMod p) => decide ((∑ j, x j) = targets i)) x ≤ 1 := by
  unfold crossFieldCount
  exact le_trans (Nat.mod_le _ _) (affineHyperplane_fireCount_le_one targets hinj x)

/-!
**The refined hard hypothesis (named).**  Indicator rank / `AlgExpander` (entries 256–258) is necessary but *not*
sufficient for count-hardness: the parallel affine family is `AlgExpander` (entry 258) yet count-easy
(`affineHyperplane_crossFieldCount_le_one`).  The count lower bound needs **co-firing richness** — gates that fire
*simultaneously* in many distinct patterns (overlapping, varying-direction), which parallel/disjoint families lack.  The
varying-direction hyperplane family `{⟨aᵢ, x⟩ = bᵢ}` is the candidate hard family; the lower bound on it is the
entry-256/257 socket with the corrected co-firing hypothesis (Razborov–Smolensky, proved in-arc for `MOD_q`,
`Layer4.mod_q_indicators_false`).  Consequently the naive bridge `AlgExpander ⇒ NEXP ⊄ ACC⁰` is unsound; the genuine
upstream condition is co-firing-rich count-hardness.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplaneLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplaneLowerBound.affineHyperplane_fireCount_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplaneLowerBound.affineHyperplane_crossFieldCount_le_one
