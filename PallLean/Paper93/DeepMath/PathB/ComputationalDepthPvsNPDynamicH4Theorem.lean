import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPTranscriptObserver

/-!
# Dynamic H4 theorem shape for P vs NP

This file closes the current dynamic-SPDP/H4 pipeline into one exact conditional theorem.

Previous modules proved the reusable lower-bound machinery:

* static residual truth is too weak (`ComputationalDepthPvsNPResidualObserverNoGo.lean`);
* dynamic transcript/state observers can carry exponential distinctions (`ComputationalDepthDynamicSPDP.lean`);
* a sound transcript observer on a `2^m` fooling residual family has at least `2^m` boundary states
  (`ComputationalDepthPvsNPTranscriptObserver.lean`);
* the schema fires on concrete forced-assignment CNFs, but those are easy
  (`ComputationalDepthPvsNPForcedAssignmentFamily.lean`).

Here we name the real missing theorem as `DynamicH4ForPTimeSAT`:

```text
Every polynomial-time SAT decider induces, for some hard residual family,
a sound transcript observer whose boundary is polynomially bounded below an exponential gap.
```

Together with the already-proved fooling-set lower bound, that is contradictory.  Therefore:

```text
DynamicH4ForPTimeSAT U ⇒ ¬ SATDecisionInP U.
```

This is **not** an unconditional proof of `P ≠ NP`; it is the exact theorem-shaped H4 bridge.  The remaining open work is
proving `DynamicH4ForPTimeSAT` for a genuine hard SAT/search residual family.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPDynamicH4Theorem

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver

/-- A dynamic H4 witness extracted from one claimed polynomial-time SAT decider.

It consists of:

* `m` residual bits, hence `2^m` candidate labels;
* a finite transcript/state boundary `α`;
* a transcript observer `obs`;
* a fooling residual family `fam` indexed by `2^m` branches;
* soundness of `obs` on `fam`;
* polynomial boundary size `|α| ≤ m^k`;
* the exponential scale gap `m^k < 2^m`.

The lower-bound theorem from `ComputationalDepthPvsNPTranscriptObserver.lean` says these fields are jointly
inconsistent. -/
structure DynamicH4Witness where
  m : ℕ
  k : ℕ
  α : Type
  fintypeα : Fintype α
  obs : TranscriptObserver α
  fam : FoolingResidualFamily m
  sound : SoundOnFoolingFamily obs fam
  polyBoundary : Fintype.card α ≤ m ^ k
  expGap : m ^ k < 2 ^ m

/-- The real missing H4 theorem, stated against the repository's abstract SAT machine semantics:
any correct polynomial-time SAT decider yields a dynamic H4 witness.

This is data-producing (`Type`), not merely propositional, because the bridge must actually exhibit the fooling family,
observer, boundary, and bounds extracted from the claimed decider. -/
abbrev DynamicH4ForPTimeSAT (U : MachineModel) : Type 1 :=
  ∀ (D : DecisionMachine U), DecidesSAT U D → DynamicH4Witness

/-- A dynamic H4 witness is impossible: the transcript/fooling lower bound forces `2^m ≤ |α|`, while the witness also
claims `|α| ≤ m^k < 2^m`. -/
theorem dynamicH4Witness_impossible (W : DynamicH4Witness) : False := by
  letI : Fintype W.α := W.fintypeα
  exact transcript_fooling_contradicts_poly_boundary
    W.obs W.fam W.sound W.polyBoundary W.expGap

/-- **Conditional P-vs-NP theorem shape.**  If the dynamic H4 bridge holds for polynomial-time SAT deciders, then SAT has
no polynomial-time decider in this machine model. -/
theorem no_SATDecisionInP_of_DynamicH4 {U : MachineModel}
    (hH4 : DynamicH4ForPTimeSAT U) :
    ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact dynamicH4Witness_impossible (hH4 D hD)

/-- Equivalent phrasing: under dynamic H4, SAT search is deep whenever the standard decision-to-search self-reduction is
available in the machine model. -/
theorem deepSATSearch_of_DynamicH4_with_selfReduction {U : MachineModel}
    (R : DecisionToSearchSelfReduction U)
    (hH4 : DynamicH4ForPTimeSAT U) :
    DeepSATSearch U := by
  have hNoDec : ¬ SATDecisionInP U := no_SATDecisionInP_of_DynamicH4 hH4
  exact (deepSATSearch_iff_no_decider_with_selfReduction R).mpr hNoDec

/-!
Current exact path:

```text
Prove DynamicH4ForPTimeSAT U
  = every P-time SAT decider yields a polynomial-boundary sound transcript observer
    on a hard 2^m fooling residual SAT family.

Then no_SATDecisionInP_of_DynamicH4 gives SAT ∉ P in the abstract machine model.
```

So the remaining theorem is no longer vague H4.  It is precisely `DynamicH4ForPTimeSAT`.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPDynamicH4Theorem

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicH4Theorem.dynamicH4Witness_impossible
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicH4Theorem.no_SATDecisionInP_of_DynamicH4
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicH4Theorem.deepSATSearch_of_DynamicH4_with_selfReduction
