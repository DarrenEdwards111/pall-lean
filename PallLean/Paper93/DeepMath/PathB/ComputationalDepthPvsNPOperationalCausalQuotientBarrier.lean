import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPRunIndexedFaithfulTPhi

/-!
# Operational causal quotients: the representation-independent barrier

The run-indexed `TΦ` audit showed that the final SAT decision itself supplies a
canonical Boolean causal quotient.  This file packages arbitrary exact decision
factorizations and proves a sharp barrier: every deterministic decision run has an
exact factorization through a two-state feature space at every time.

Consequently no representation-independent theorem can force *every* exact causal
quotient to have rank/cardinality greater than two.  Any useful SPDP/holonomy lower
bound must restrict which operational observations are admissible and must prove that
the restriction follows from the concrete machine model.  Merely requiring exact
recovery of the final decision is insufficient.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPOperationalCausalQuotientBarrier

open PallLean.Paper93.DeepMath.PathB.PvsNPRunIndexedFaithfulTPhi

variable {Input State Feature : Type*}

/-- A feature extracted at one time of a real run, together with an exact decoder of
the final Boolean decision. -/
structure DecisionFactorization
    (R : ActualDecisionRun Input State) (time : Nat) where
  Feature : Type
  [featureFintype : Fintype Feature]
  extract : Input → Feature
  decode : Feature → Bool
  correct : ∀ x, decode (extract x) = R.finalAnswer x

namespace DecisionFactorization

/-- The canonical factorization through the run-indexed causal quotient.  It uses the
actual trajectory suffix, not an appended sheet. -/
def canonical (R : ActualDecisionRun Input State) (time : Nat)
    (htime : time ≤ R.steps) : DecisionFactorization R time where
  Feature := Bool
  extract := R.causalTPhi time
  decode := id
  correct := by
    intro x
    simpa using R.causalTPhi_eq_finalAnswer time htime x

/-- The canonical exact operational quotient has exactly two available states. -/
theorem canonical_card_eq_two (R : ActualDecisionRun Input State)
    (time : Nat) (htime : time ≤ R.steps) :
    @Fintype.card (canonical R time htime).Feature
      (canonical R time htime).featureFintype = 2 := by
  rfl

/-- Therefore an exact-decision requirement alone cannot force all causal
factorizations to have three or more states. -/
theorem not_three_le_every_exact_factorization
    (R : ActualDecisionRun Input State) (time : Nat) (htime : time ≤ R.steps) :
    ¬ (∀ F : DecisionFactorization R time,
      3 ≤ @Fintype.card F.Feature F.featureFintype) := by
  intro hall
  have h := hall (canonical R time htime)
  rw [canonical_card_eq_two] at h
  omega

/-- More generally, any proposed universal rank demand above two is refuted by the
canonical actual-run quotient. -/
theorem not_lower_le_every_exact_factorization
    (R : ActualDecisionRun Input State) (time : Nat) (htime : time ≤ R.steps)
    {lower : Nat} (hlower : 3 ≤ lower) :
    ¬ (∀ F : DecisionFactorization R time,
      lower ≤ @Fintype.card F.Feature F.featureFintype) := by
  intro hall
  have h := hall (canonical R time htime)
  rw [canonical_card_eq_two] at h
  omega

end DecisionFactorization

/-! ## What an operational theorem must add -/

/-- An explicit admissibility predicate for operational observations.  The point is
that the mathematical content must live in `Admissible`; exact decision recovery is
already present in `DecisionFactorization`. -/
structure OperationalObservationLaw
    (R : ActualDecisionRun Input State) (time : Nat) where
  Admissible : DecisionFactorization R time → Prop
  requiredRank : Nat
  rank_lower : ∀ F, Admissible F →
    requiredRank ≤ @Fintype.card F.Feature F.featureFintype

/-- Any law demanding rank above two must reject the canonical Boolean causal quotient.
This is the exact proof obligation hidden by a solver-independent SPDP claim. -/
theorem canonical_not_admissible_of_rank_gt_two
    (R : ActualDecisionRun Input State) (time : Nat) (htime : time ≤ R.steps)
    (L : OperationalObservationLaw R time) (hlarge : 3 ≤ L.requiredRank) :
    ¬ L.Admissible (DecisionFactorization.canonical R time htime) := by
  intro hadm
  have h := L.rank_lower _ hadm
  rw [DecisionFactorization.canonical_card_eq_two] at h
  omega

/-- In particular, a law that declares every exact factorization operationally
admissible cannot demand rank above two. -/
theorem requiredRank_le_two_of_all_admissible
    (R : ActualDecisionRun Input State) (time : Nat) (htime : time ≤ R.steps)
    (L : OperationalObservationLaw R time)
    (hall : ∀ F, L.Admissible F) :
    L.requiredRank ≤ 2 := by
  simpa [DecisionFactorization.canonical_card_eq_two] using
    L.rank_lower (DecisionFactorization.canonical R time htime)
      (hall (DecisionFactorization.canonical R time htime))

/-!
## Honest endpoint

The next P≠NP bridge cannot be a theorem about all exact decision factorizations:
the canonical two-state factorization refutes it.  One must define an operationally
restricted observation class (local accesses, bounded fan-in updates, justified cuts,
or a similarly concrete machine-dependent condition), prove every polynomial-time SAT
run yields an admissible observation in that class, and then prove a superpolynomial
SPDP/holonomy lower bound inside the same class.  Those two substantive claims remain
open.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPOperationalCausalQuotientBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPOperationalCausalQuotientBarrier.DecisionFactorization.canonical_card_eq_two
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPOperationalCausalQuotientBarrier.DecisionFactorization.not_three_le_every_exact_factorization
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPOperationalCausalQuotientBarrier.canonical_not_admissible_of_rank_gt_two
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPOperationalCausalQuotientBarrier.requiredRank_le_two_of_all_admissible
