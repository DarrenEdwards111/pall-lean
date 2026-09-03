import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundedPassCrossingEnergy

/-!
# Direct-sum crossing-energy amplification

The single-block bounded-pass theorem gives

```text
m² ≤ bits² · energy.
```

This file proves that the cost adds across independent equality-CNF SAT
blocks.  Each block may use its own number of passes, but all blocks share the
same visible-memory ceiling `bits`.  Correctness on every block forces

```text
blocks · m² ≤ bits² · totalEnergy.
```

This rules out amortizing several independent residual distinctions through a
single low-energy ledger in the bounded-pass model.  The memory factor remains:
the theorem does not yet prevent polynomially growing visible memory from
absorbing the lower bound, and therefore does not prove a lower bound for all
polynomial-time machines.
-/

namespace PallLean.Paper93.DeepMath.PathB.DirectSumCrossingEnergy

open SATDepthMachine
open PvsNPMultiPassCoupling
open PvsNPSATBoundaryFoolingWidthLB
open UniformContextualReconstructionDepth
open BoundedPassCrossingEnergy

/-- A family of independent bounded-pass observers.  The pass count may vary
by block; the visible-state bit ceiling is shared. -/
structure DirectSumObserver (blocks m bits : ℕ) where
  passes : Fin blocks → ℕ
  component : ∀ i, ReconstructionObserver m (passes i) bits

/-- Total quadratic crossing energy, summed over independent blocks. -/
def totalCrossingEnergy {blocks m bits : ℕ}
    (O : DirectSumObserver blocks m bits) : ℕ :=
  ∑ i, observerCrossingEnergy (O.component i)

/-- Correctness of every component on its equality-CNF SAT block. -/
def Correct {blocks m bits : ℕ}
    (O : DirectSumObserver blocks m bits) : Prop :=
  ∀ i a b,
    (O.component i).decider.eval a b = true ↔
      Satisfiable (equalityCNF a b)

/-- **Direct-sum energy lower bound.** Independent SAT blocks contribute
additively even when their pass budgets differ. -/
theorem equalityCNF_directSum_crossingEnergy_lower_bound
    {blocks m bits : ℕ} (O : DirectSumObserver blocks m bits)
    (hcorrect : Correct O) :
    blocks * m ^ 2 ≤ bits ^ 2 * totalCrossingEnergy O := by
  have hsum : (∑ _i : Fin blocks, m ^ 2) ≤
      ∑ i : Fin blocks, bits ^ 2 * observerCrossingEnergy (O.component i) := by
    apply Finset.sum_le_sum
    intro i _
    exact equalityCNF_crossingEnergy_tradeoff (O.component i) (hcorrect i)
  calc
    blocks * m ^ 2 = ∑ _i : Fin blocks, m ^ 2 := by simp
    _ ≤ ∑ i : Fin blocks, bits ^ 2 * observerCrossingEnergy (O.component i) := hsum
    _ = bits ^ 2 * totalCrossingEnergy O := by
      simp [totalCrossingEnergy, Finset.mul_sum]

/-- With one visible bit, direct-sum energy is at least `blocks * m²`. -/
theorem equalityCNF_directSum_oneBit_lower_bound
    {blocks m : ℕ} (O : DirectSumObserver blocks m 1)
    (hcorrect : Correct O) :
    blocks * m ^ 2 ≤ totalCrossingEnergy O := by
  simpa using equalityCNF_directSum_crossingEnergy_lower_bound O hcorrect

/-- No one-bit direct-sum observer below the additive energy threshold is
correct on every independent block. -/
theorem no_oneBit_directSum_observer_below_energy
    {blocks m : ℕ} (O : DirectSumObserver blocks m 1)
    (hsmall : totalCrossingEnergy O < blocks * m ^ 2) :
    ¬ Correct O := by
  intro hcorrect
  exact Nat.not_le_of_lt hsmall
    (equalityCNF_directSum_oneBit_lower_bound O hcorrect)

end PallLean.Paper93.DeepMath.PathB.DirectSumCrossingEnergy

#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumCrossingEnergy.equalityCNF_directSum_crossingEnergy_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumCrossingEnergy.equalityCNF_directSum_oneBit_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.DirectSumCrossingEnergy.no_oneBit_directSum_observer_below_energy
