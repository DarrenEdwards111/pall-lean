import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# The derandomization core of the RS constructive wrapper

The RS switching-lemma wrapper builds a low-degree polynomial approximating an AC⁰[p] gate by Razborov's
*probabilistic* method: a random polynomial (from random subsets) approximates well *on average*, then
one derandomizes to a fixed good polynomial.  The probabilistic error bound is a genuine landmark
calculation — but the **derandomization step** it feeds is a clean averaging fact, discharged here.

* If a finite family of candidate approximators (indexed by seeds `r`) has *total* error below
  `|R| · ε`, then *some* seed has error below `ε`.  "Good on average ⟹ a specific good one exists."

This is the deterministic heart that makes the probabilistic construction constructive.

## What is proved

* **`exists_good_approximation`** — `∑_r err(r) < |R| · ε ⟹ ∃ r, err(r) < ε`.  (If every seed had error
  `≥ ε`, the total would be `≥ |R| · ε`.)

## Honest scope

The averaging *derandomization* is proved and axiom-clean.  What it does **not** supply is the
probabilistic input — that the random-subset polynomial family actually *has* average error below the
threshold (Razborov's calculation), the degree bound, and the depth-`d` composition.  Those, together
with the extension-field spreading, are the research-level remainder of the two constructive wrappers,
socketed not faked.  `AC⁰[p]`-restricted; nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RSDerandomization

/-- **The derandomization core (proved).**  Over a finite, nonempty family of seeds, if the total error
is below `|R| · ε`, some seed's error is below `ε`.  This is the averaging step that makes Razborov's
probabilistic polynomial construction constructive: good-on-average yields a specific good approximator. -/
theorem exists_good_approximation {R : Type*} [Fintype R] (err : R → ℕ) (ε : ℕ)
    (havg : ∑ r, err r < Fintype.card R * ε) :
    ∃ r, err r < ε := by
  by_contra h
  push_neg at h
  have hle : Fintype.card R * ε ≤ ∑ r, err r := by
    calc Fintype.card R * ε = ∑ _r : R, ε := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ r, err r := Finset.sum_le_sum (fun r _ => h r)
  omega

end PallLean.Paper93.DeepMath.PathB.RSDerandomization

#print axioms PallLean.Paper93.DeepMath.PathB.RSDerandomization.exists_good_approximation
