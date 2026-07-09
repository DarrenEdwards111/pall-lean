import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPResidualObserverNoGo

/-!
# Dynamic SPDP: transcript/state structure is the next observer, not residual truth

This file formalizes the refinement forced by the residual-observer no-go.

The static residual-truth observer has only a Boolean boundary (`sat`/`unsat`) and therefore cannot carry the
exponential residual distinctions required by the toy H4 pigeonhole core.  The replacement object must be dynamic:
transcripts/states/search paths, not a single residual truth bit.

What is proved here:

* a full transcript observer `dynamicTranscriptObserver` that records the branch bits is injective on all `2^n` branches;
* therefore its boundary has exactly/exponentially `2^n` states;
* any polynomially-bounded dynamic observer that is full-branch distinguishing contradicts `n^k < 2^n` by the existing
  H4 core;
* static Boolean projection cannot be the full-distinguishing observer once `2^n` exceeds the chosen polynomial bound.

This is not `P ≠ NP`.  It proves the design correction: H4 must be a theorem about dynamic transcript/state/fooling-set
structure, not residual SAT truth.
-/

namespace PallLean.Paper93.DeepMath.PathB.DynamicSPDP

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserverNoGo
open SATDepthMachine

/-- A dynamic transcript for the full branch of length `n`: here, just the sequence of branch bits itself. -/
abbrev FullTranscript (n : ℕ) := Assignment n

/-- The canonical dynamic transcript observer: record the whole branch. -/
def dynamicTranscriptObserver (n : ℕ) : BoundaryObserver n (FullTranscript n) :=
  id

/-- Dynamic transcripts distinguish all full branches. -/
theorem dynamicTranscriptObserver_injective (n : ℕ) :
    Function.Injective (dynamicTranscriptObserver n) := by
  intro a b h
  exact h

/-- The dynamic full-transcript boundary has exactly `2^n` states. -/
theorem dynamicTranscript_card (n : ℕ) :
    Fintype.card (FullTranscript n) = 2 ^ n := by
  exact card_assignment n

/-- Dynamic transcripts satisfy the exponential lower bound required by the H4 core. -/
theorem dynamicTranscript_boundary_ge_exp (n : ℕ) :
    2 ^ n ≤ Fintype.card (FullTranscript n) := by
  rw [dynamicTranscript_card]

/-- Any dynamic observer that fully distinguishes branches and also has polynomial boundary contradicts the exponential
scale gap.  This is the reusable dynamic-SPDP H4 socket. -/
theorem dynamic_full_distinction_contradicts_poly_boundary {n k : ℕ} {α : Type} [Fintype α]
    (obs : BoundaryObserver n α)
    (hdyn : Function.Injective obs)
    (hpoly : Fintype.card α ≤ n ^ k)
    (hgap : n ^ k < 2 ^ n) : False := by
  exact residual_distinguishing_contradicts_poly_boundary obs hdyn hpoly hgap

/-- A static Boolean observer with polynomial-size boundary cannot be the full dynamic transcript observer whenever the
scale gap holds. -/
theorem bool_static_cannot_be_dynamic_full_distinguishing {n k : ℕ}
    (obs : BoundaryObserver n Bool)
    (htwo : 2 ≤ n ^ k) (hgap : n ^ k < 2 ^ n) :
    ¬ Function.Injective obs := by
  have hpoly : Fintype.card Bool ≤ n ^ k := by
    simpa using htwo
  exact poly_boundary_not_residual_distinguishing obs hpoly hgap

/-- The canonical dynamic transcript observer cannot be polynomial-bounded below the exponential scale. -/
theorem dynamicTranscript_not_poly_below_exp {n k : ℕ}
    (hgap : n ^ k < 2 ^ n) :
    ¬ Fintype.card (FullTranscript n) ≤ n ^ k := by
  intro hpoly
  exact dynamic_full_distinction_contradicts_poly_boundary
    (dynamicTranscriptObserver n)
    (dynamicTranscriptObserver_injective n)
    hpoly hgap

/-- Static residual truth is a sound Boolean observer, but the dynamic transcript is the object that carries branch
identity.  This theorem packages the design correction: truth-soundness and full dynamic distinction are different
properties. -/
theorem truth_sound_does_not_supply_dynamic_distinction
    (Q : CNF → RawAssignment → Bool) (hQ : PrefixOracleCorrect Q) :
    ResidualTruthSound (boolPrefixObserver Q) ∧
      ∀ {n k : ℕ} (φ : CNF), 2 ≤ n ^ k → n ^ k < 2 ^ n →
        ¬ FullResidualDistinguishing (n := n) (boolPrefixObserver Q) φ := by
  constructor
  · exact prefix_oracle_truth_sound Q hQ
  · intro n k φ htwo hgap
    exact (bool_prefix_observer_poly_but_not_full_distinguishing Q φ htwo hgap).2

/-!
Interpretation:

```text
static residual truth:      Bool boundary, truth-sound, not full-distinguishing

dynamic transcript/state:   records branch/search path, can distinguish 2^n branches,
                            and therefore has exponential boundary unless compressed by a nontrivial theorem
```

So the corrected H4 target is dynamic SPDP:

```text
P-side:  polynomial dynamic transcript/state boundary induced by a P-time solver
NP-side: many inequivalent dynamic transcripts/states forced by a hard SAT/search family
```

The missing theorem is now about transcript/state/fooling-set complexity, not about residual truth.
-/

end PallLean.Paper93.DeepMath.PathB.DynamicSPDP

#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDP.dynamicTranscriptObserver_injective
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDP.dynamicTranscript_card
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDP.dynamic_full_distinction_contradicts_poly_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDP.bool_static_cannot_be_dynamic_full_distinguishing
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDP.dynamicTranscript_not_poly_below_exp
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDP.truth_sound_does_not_supply_dynamic_distinction
