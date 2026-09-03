import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniformContextualReconstructionDepth

/-!
# Crossing-energy lower bound for bounded-pass contextual observers

The unrestricted crossing-energy lower bound for SAT is separation-strength.
This file proves the next honest rung: a quantitative energy lower bound for
the bounded-pass, bounded-visible-state observers already used by uniform
contextual reconstruction depth.

A `passes`-crossing observer has one-cut crossing energy `passes²`. If its
visible state has at most `bits` bits, correctness on the explicit
`equalityCNF` SAT family implies

```text
n² ≤ bits² · crossingEnergy.
```

Thus constant-bit observers require quadratic crossing energy. More generally,
the theorem is an exact time-space-energy tradeoff: increasing visible boundary
memory is the only way this restricted model can reduce the required energy.

This is an unconditional restricted-model theorem. It is not a lower bound
against arbitrary polynomial-time machines and does not prove `P != NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundedPassCrossingEnergy

open SATDepthMachine
open PvsNPMultiPassCoupling
open PvsNPSATBoundaryFoolingWidthLB
open UniformContextualReconstructionDepth

/-- One-cut quadratic crossing energy for a `passes`-crossing observer. -/
def observerCrossingEnergy {n passes bits : ℕ}
    (_ : ReconstructionObserver n passes bits) : ℕ :=
  passes ^ 2

/-- **Bounded-pass crossing-energy tradeoff.** Correctness on the explicit
equality-CNF SAT family forces `n² ≤ bits² * energy`. -/
theorem equalityCNF_crossingEnergy_tradeoff
    {n passes bits : ℕ} (O : ReconstructionObserver n passes bits)
    (hSAT : ∀ a b,
      O.decider.eval a b = true ↔ Satisfiable (equalityCNF a b)) :
    n ^ 2 ≤ bits ^ 2 * observerCrossingEnergy O := by
  have hdepth : n ≤ passes * bits :=
    equalityCNF_contextualReconstructionDepth_lower_bound O hSAT
  have hsquare : n ^ 2 ≤ (passes * bits) ^ 2 := Nat.pow_le_pow_left hdepth 2
  simpa [observerCrossingEnergy, mul_pow, Nat.mul_comm] using hsquare

/-- At most one visible bit per crossing forces quadratic energy `n²`. -/
theorem equalityCNF_oneBit_crossingEnergy_lower_bound
    {n passes : ℕ} (O : ReconstructionObserver n passes 1)
    (hSAT : ∀ a b,
      O.decider.eval a b = true ↔ Satisfiable (equalityCNF a b)) :
    n ^ 2 ≤ observerCrossingEnergy O := by
  simpa using equalityCNF_crossingEnergy_tradeoff O hSAT

/-- No one-bit observer with energy below `n²` decides every member of the
equality-CNF family. -/
theorem no_oneBit_equalityCNF_observer_below_energy
    {n passes : ℕ} (O : ReconstructionObserver n passes 1)
    (hsmall : observerCrossingEnergy O < n ^ 2) :
    ¬ ∀ a b, O.decider.eval a b = true ↔ Satisfiable (equalityCNF a b) := by
  intro hSAT
  exact Nat.not_le_of_lt hsmall
    (equalityCNF_oneBit_crossingEnergy_lower_bound O hSAT)

end PallLean.Paper93.DeepMath.PathB.BoundedPassCrossingEnergy

#print axioms PallLean.Paper93.DeepMath.PathB.BoundedPassCrossingEnergy.equalityCNF_crossingEnergy_tradeoff
#print axioms PallLean.Paper93.DeepMath.PathB.BoundedPassCrossingEnergy.equalityCNF_oneBit_crossingEnergy_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.BoundedPassCrossingEnergy.no_oneBit_equalityCNF_observer_below_energy
