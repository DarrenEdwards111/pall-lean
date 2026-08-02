import PallLean.Paper93.DeepMath.PathB.ComputationalDepthContextualDynamicalWorkFrontier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPMultiPassCoupling

/-!
# Uniform contextual reconstruction depth

This file isolates the time-sensitive observer invariant suggested jointly by
the N-Frame account of sequential epistemic reconstruction and the
No-Fixed-Structure-Amortization frontier.

The observer is allowed to retain the complete CNF syntax.  Hence syntax
transport remains cheap, exactly as proved by the contextual dynamical-work
calibration.  What is charged here is observer-time interaction: a restricted
observer has `passes` opportunities to cross a contextual boundary and at most
`bits` bits of state at each crossing.  Its **uniform contextual reconstruction
depth** is the time-space action `passes * bits`.

For the genuine `equalityCNF` SAT family, the existing crossing-transcript
fooling theorem gives an unconditional restricted-model lower bound:

```text
correctness  ->  n <= passes * bits.
```

Thus contextual reconstruction cannot be amortized below `n` bits of total
observer-time action in this bounded-pass model.  The result permits rereading
through several passes and makes no charge for storing exact CNF syntax.

## Honest scope

This is a time-space tradeoff for bounded-pass crossing observers, not a lower
bound against arbitrary polynomial-time machines.  When both `passes` and
`bits` are polynomial, `n <= passes * bits` is easily satisfied.  The final
section proves that asking for the corresponding unrestricted evaluator lower
bound is exactly `SATDecisionInP` negated.  No `P != NP` claim is made.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniformContextualReconstructionDepth

open CNFSelfReduction
open SATDepthMachine
open ContextualSummaryInvalidationFrontier
open ContextualDynamicalWorkFrontier
open PvsNPMultiPassCoupling
open PvsNPSATBoundaryFoolingWidthLB

/-! ## Genuine CNF restriction traces -/

/-- A nested-bubble path together with an explicit per-transition fresh-work
ledger.  The ledger is deliberately separate from syntax size: an observer may
retain the whole current CNF for free and still incur semantic work. -/
structure ContextualReconstructionTrace (n : ℕ) where
  start : CNF n
  path : List (RestrictionStep n)
  freshWork : List ℕ
  workAligned : freshWork.length = path.length

namespace ContextualReconstructionTrace

/-- Total fresh reconstruction work recorded along observer-time. -/
def totalFreshWork {n : ℕ} (T : ContextualReconstructionTrace n) : ℕ :=
  T.freshWork.sum

/-- The exact syntax retained after the nested restriction path. -/
def finalSyntax {n : ℕ} (T : ContextualReconstructionTrace n) : CNF n :=
  restrictAlong T.start T.path

/-- Retaining exact syntax realizes precisely the final contextual bubble. -/
theorem finalSyntax_eq_exact_cache {n : ℕ}
    (T : ContextualReconstructionTrace n) :
    (exactSyntaxSummaryScheme n).realize
      ((exactSyntaxSummaryScheme n).advanceAlong
        ((exactSyntaxSummaryScheme n).summarize T.start) T.path) =
      T.finalSyntax := by
  exact exact_cache_after_path T.start T.path

/-- Exact syntax maintenance remains polynomially cheap on every path whose
length is bounded by the original traversal size.  UCRD therefore does not
smuggle representation growth into the fresh-work ledger. -/
theorem exact_syntax_maintenance_quadratic {n : ℕ}
    (T : ContextualReconstructionTrace n)
    (hpath : T.path.length ≤ cnfTraversalSize T.start) :
    restrictionPathWork T.start T.path ≤ cnfTraversalSize T.start ^ 2 := by
  exact restrictionPathWork_quadratic T.start T.path hpath

end ContextualReconstructionTrace

/-! ## Bounded-pass UCRD observers -/

/-- A bounded-pass contextual observer with at most `2^bits` boundary states.
The underlying multi-pass decider may use a different transition at every
pass; the only restriction is the observer-visible state bound. -/
structure ReconstructionObserver (n passes bits : ℕ) where
  decider : MultiPassDecider n n passes
  stateCard_le :
    @Fintype.card decider.State decider.fintype ≤ 2 ^ bits

/-- Observer-time action: boundary bits times the number of contextual
crossings. -/
def contextualReconstructionDepth {n passes bits : ℕ}
    (_ : ReconstructionObserver n passes bits) : ℕ :=
  passes * bits

/-- A `bits`-bit state observed over `passes` crossings has at most
`2^(bits*passes)` possible transcripts. -/
theorem transcript_card_le_two_pow_depth {n passes bits : ℕ}
    (O : ReconstructionObserver n passes bits) :
    (@Fintype.card O.decider.State O.decider.fintype) ^ passes ≤
      2 ^ contextualReconstructionDepth O := by
  have h := Nat.pow_le_pow_left O.stateCard_le passes
  calc
    (@Fintype.card O.decider.State O.decider.fintype) ^ passes
        ≤ (2 ^ bits) ^ passes := h
    _ = 2 ^ (bits * passes) := by rw [pow_mul]
    _ = 2 ^ (passes * bits) := by rw [Nat.mul_comm bits passes]
    _ = 2 ^ contextualReconstructionDepth O := rfl

/-- **Restricted UCRD lower bound.**  Every bounded-pass observer correct on
the genuine equality-CNF SAT family pays at least `n` total observer-time bits.

This is the promised non-amortization theorem on the first restricted rung:
several passes may reuse state, but their complete transcript still must carry
all `n` independent distinctions. -/
theorem equalityCNF_contextualReconstructionDepth_lower_bound
    {n passes bits : ℕ} (O : ReconstructionObserver n passes bits)
    (hSAT : ∀ a b,
      O.decider.eval a b = true ↔ Satisfiable (equalityCNF a b)) :
    n ≤ contextualReconstructionDepth O := by
  have hlower : 2 ^ n ≤
      (@Fintype.card O.decider.State O.decider.fintype) ^ passes :=
    equalitySAT_multipass_lower_bound n passes O.decider hSAT
  have hpow : 2 ^ n ≤ 2 ^ contextualReconstructionDepth O :=
    hlower.trans (transcript_card_le_two_pow_depth O)
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1 hpow

/-- Equivalently, no observer whose contextual action is below `n` can be
correct on every member of the equality-CNF family. -/
theorem no_equalityCNF_observer_below_depth
    {n passes bits : ℕ} (O : ReconstructionObserver n passes bits)
    (hsmall : contextualReconstructionDepth O < n) :
    ¬ ∀ a b, O.decider.eval a b = true ↔ Satisfiable (equalityCNF a b) := by
  intro hSAT
  exact (Nat.not_le_of_lt hsmall)
    (equalityCNF_contextualReconstructionDepth_lower_bound O hSAT)

/-- With one visible bit per crossing, at least `n` observer-time crossings are
required. -/
theorem oneBit_requires_n_passes {n passes : ℕ}
    (O : ReconstructionObserver n passes 1)
    (hSAT : ∀ a b,
      O.decider.eval a b = true ↔ Satisfiable (equalityCNF a b)) :
    n ≤ passes := by
  simpa [contextualReconstructionDepth] using
    (equalityCNF_contextualReconstructionDepth_lower_bound O hSAT)

/-- With one crossing, the observer must expose at least `n` bits. -/
theorem onePass_requires_n_bits {n bits : ℕ}
    (O : ReconstructionObserver n 1 bits)
    (hSAT : ∀ a b,
      O.decider.eval a b = true ↔ Satisfiable (equalityCNF a b)) :
    n ≤ bits := by
  simpa [contextualReconstructionDepth] using
    (equalityCNF_contextualReconstructionDepth_lower_bound O hSAT)

/-! ## The unrestricted endpoint -/

/-- The unrestricted UCRD target: cheap exact contextual dynamics exist, but
no polynomial uniform evaluator does.  This definition deliberately allows the
exact-syntax cache and all polynomial context maintenance proved above. -/
def GeneralUCRDLowerBound (U : MachineModel) : Prop :=
  ¬ PolynomialContextDynamicsWithEvaluator U

/-- **Exact frontier calibration.**  A general UCRD lower bound is precisely
the absence of a polynomial-budget SAT decider.  The restricted theorem above
is unconditional; this unrestricted statement is the open separation endpoint,
not a further mechanical lemma. -/
theorem generalUCRDLowerBound_iff_no_SATDecisionInP (U : MachineModel) :
    GeneralUCRDLowerBound U ↔ ¬ SATDecisionInP U := by
  exact no_polynomialContextDynamicsWithEvaluator_iff_no_SATDecisionInP U

end PallLean.Paper93.DeepMath.PathB.UniformContextualReconstructionDepth

#print axioms PallLean.Paper93.DeepMath.PathB.UniformContextualReconstructionDepth.ContextualReconstructionTrace.finalSyntax_eq_exact_cache
#print axioms PallLean.Paper93.DeepMath.PathB.UniformContextualReconstructionDepth.ContextualReconstructionTrace.exact_syntax_maintenance_quadratic
#print axioms PallLean.Paper93.DeepMath.PathB.UniformContextualReconstructionDepth.transcript_card_le_two_pow_depth
#print axioms PallLean.Paper93.DeepMath.PathB.UniformContextualReconstructionDepth.equalityCNF_contextualReconstructionDepth_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.UniformContextualReconstructionDepth.no_equalityCNF_observer_below_depth
#print axioms PallLean.Paper93.DeepMath.PathB.UniformContextualReconstructionDepth.generalUCRDLowerBound_iff_no_SATDecisionInP
