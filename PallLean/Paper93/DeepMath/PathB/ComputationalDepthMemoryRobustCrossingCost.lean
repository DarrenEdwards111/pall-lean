import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDirectSumCrossingEnergy

/-!
# Memory-robust crossing cost

Quadratic crossing energy alone can be reduced by exposing more reusable
boundary memory.  This file charges that escape explicitly.  For an observer
with `passes` crossings and `bits` visible bits, define

```text
reuseCost = passes² + bits².
```

Correctness on `equalityCNF` gives `n ≤ passes * bits`; the elementary square
inequality `2 * passes * bits ≤ passes² + bits²` therefore yields

```text
2n ≤ reuseCost.
```

This is memory-robust in the precise restricted-model sense: reducing crossing
energy by increasing reusable visible memory merely transfers cost into the
memory term.  The result also adds across independent blocks.

The bound is linear, not super-polynomial.  It closes the memory-absorption
loophole for this combined restricted resource; it does not imply a SAT time
lower bound for unrestricted machines or prove `P != NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MemoryRobustCrossingCost

open SATDepthMachine
open PvsNPMultiPassCoupling
open PvsNPSATBoundaryFoolingWidthLB
open UniformContextualReconstructionDepth
open BoundedPassCrossingEnergy
open DirectSumCrossingEnergy

/-- Quadratic crossing energy plus the quadratic reusable-memory charge. -/
def observerReuseCost {n passes bits : ℕ}
    (O : ReconstructionObserver n passes bits) : ℕ :=
  observerCrossingEnergy O + bits ^ 2

/-- **Memory-robust single-block lower bound.** Correctness forces either
crossing energy or reusable visible memory to carry linear combined cost. -/
theorem equalityCNF_reuseCost_lower_bound
    {n passes bits : ℕ} (O : ReconstructionObserver n passes bits)
    (hSAT : ∀ a b,
      O.decider.eval a b = true ↔ Satisfiable (equalityCNF a b)) :
    2 * n ≤ observerReuseCost O := by
  have hdepth : n ≤ passes * bits :=
    equalityCNF_contextualReconstructionDepth_lower_bound O hSAT
  have hsquare : 2 * (passes * bits) ≤ passes ^ 2 + bits ^ 2 := by
    simpa [mul_assoc] using (two_mul_le_add_sq passes bits)
  unfold observerReuseCost observerCrossingEnergy
  omega

/-- Total memory-robust cost across independent blocks.  The shared bit ceiling
is charged once per independently serviced block. -/
def totalReuseCost {blocks m bits : ℕ}
    (O : DirectSumObserver blocks m bits) : ℕ :=
  ∑ i, observerReuseCost (O.component i)

/-- **Direct-sum memory-robust lower bound.** Independent correct components
contribute additively even if every component chooses a different pass count. -/
theorem equalityCNF_directSum_reuseCost_lower_bound
    {blocks m bits : ℕ} (O : DirectSumObserver blocks m bits)
    (hcorrect : Correct O) :
    blocks * (2 * m) ≤ totalReuseCost O := by
  calc
    blocks * (2 * m) = ∑ _i : Fin blocks, 2 * m := by simp
    _ ≤ ∑ i : Fin blocks, observerReuseCost (O.component i) := by
      apply Finset.sum_le_sum
      intro i _
      exact equalityCNF_reuseCost_lower_bound (O.component i) (hcorrect i)
    _ = totalReuseCost O := rfl

/-- Below the additive reuse-cost threshold, at least one independent block
must be decided incorrectly. -/
theorem no_directSum_observer_below_reuseCost
    {blocks m bits : ℕ} (O : DirectSumObserver blocks m bits)
    (hsmall : totalReuseCost O < blocks * (2 * m)) :
    ¬ Correct O := by
  intro hcorrect
  exact Nat.not_le_of_lt hsmall
    (equalityCNF_directSum_reuseCost_lower_bound O hcorrect)

end PallLean.Paper93.DeepMath.PathB.MemoryRobustCrossingCost

#print axioms PallLean.Paper93.DeepMath.PathB.MemoryRobustCrossingCost.equalityCNF_reuseCost_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.MemoryRobustCrossingCost.equalityCNF_directSum_reuseCost_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.MemoryRobustCrossingCost.no_directSum_observer_below_reuseCost
