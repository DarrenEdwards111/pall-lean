import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGlobalGodMoveLowActionBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGlobalGodMoveCapacity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthStrictPortStandardBridge

/-!
# Theorem 207 frontier obligations

This file keeps the frontier theorem surface honest.

The earlier global coverage target

```lean
forall c, forall strict observer Ls,
  exists low-action Ll, Ll.k <= c ∧ same live-boundary-rank trajectory
```

is too strong: taking `c = 0` would force every strict observer to have an
equivalent trajectory bounded by `n^0 = 1`.

The calibration-correct replacement is per-observer coverage: every strict
observer has some low-action representative with the same live-boundary-rank
trajectory, carrying its own polynomial exponent `Ll.k`.  The strict port can
then be queried at that exponent.

No new route is introduced here.  The former stubs are converted into explicit
prose→Lean obligation records and field-by-field bridge theorems.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- One line of the corrected C2 prose obligation for a fixed strict observer
`Ls`: exhibit a low-action representative and prove pointwise equality of the
live-boundary-rank trajectory.  The exponent is carried by the low-action
observer itself; it is not required to fit an arbitrary external calibration. -/
structure StrictObserverLowActionGodMoveCoverageDatum
    (enc : ThreeCNFEncoding)
    (Ls : StrictDynamicNFrameLagrangianObserver enc) : Type 1 where
  lowActionObserver : LowActionStrictDynamicNFrameLagrangianObserver enc
  liveBoundaryRank_eq :
    forall n : Nat,
      forall input : Fin n -> Bool,
      forall time : Nat,
        Ls.toTrajectory.liveBoundaryRank n input time =
          lowActionObserver.base.toTrajectory.liveBoundaryRank n input time

/-- Calibration-correct per-observer God-Move coverage. -/
def PerObserverStrictLowActionGodMoveCoverage
    (enc : ThreeCNFEncoding) : Prop :=
  forall Ls : StrictDynamicNFrameLagrangianObserver enc,
    exists Ll : LowActionStrictDynamicNFrameLagrangianObserver enc,
      forall n : Nat,
        forall input : Fin n -> Bool,
        forall time : Nat,
          Ls.toTrajectory.liveBoundaryRank n input time =
            Ll.base.toTrajectory.liveBoundaryRank n input time

/-- Corrected C2 obligation package: every strict observer has the datum above. -/
structure StrictObserverLowActionGodMoveCoverageObligations
    (enc : ThreeCNFEncoding) : Type 1 where
  coverageDatum :
    forall Ls : StrictDynamicNFrameLagrangianObserver enc,
      StrictObserverLowActionGodMoveCoverageDatum enc Ls

/-- Corrected frontier theorem C2.  This is the line-by-line conversion of the
per-observer prose obligation into the Lean coverage predicate. -/
theorem strictObserverLowActionGodMoveCoverage_theorem
    (enc : ThreeCNFEncoding)
    (O : StrictObserverLowActionGodMoveCoverageObligations enc) :
    PerObserverStrictLowActionGodMoveCoverage enc := by
  intro Ls
  let d := O.coverageDatum Ls
  exact ⟨d.lowActionObserver, d.liveBoundaryRank_eq⟩

/-- Per-observer coverage is enough for the strict-port no-decider endpoint:
for the strict observer supplied by a hypothetical SAT decider, choose its
low-action representative, query the strict port at that representative's own
exponent, then contradict the low-action Book-1 obstruction. -/
theorem no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_perObserverCoverage
    (enc : ThreeCNFEncoding)
    (Hport : Theorem207StrictLiveBoundaryPort enc)
    (Hcov : PerObserverStrictLowActionGodMoveCoverage enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) := by
  intro hdec
  have hL : Nonempty (StrictDynamicNFrameLagrangianObserver enc) :=
    strictObserver_nonempty_of_DTMDecidesSATWithEncoding hdec
  rcases hL with ⟨Ls⟩
  rcases Hcov Ls with ⟨Ll, hrank⟩
  rcases Hport Ll.k with ⟨n, hn20, hlog, HextractAt⟩
  rcases HextractAt Ls with ⟨minor⟩
  have hbudget :
      Ll.base.toTrajectory.liveBoundaryRank n minor.input minor.time <
        Nat.choose (n / 3) (Nat.log 2 n) :=
    universalBook1BoundaryBudgetObstructionLowAction_theorem enc
      Ll.k n hn20 hlog Ll (Nat.le_refl Ll.k) minor.input minor.time
  have hbudgetLs :
      Ls.toTrajectory.liveBoundaryRank n minor.input minor.time <
        Nat.choose (n / 3) (Nat.log 2 n) := by
    simpa [hrank n minor.input minor.time] using hbudget
  have hlower :
      Nat.choose (n / 3) (Nat.log 2 n) <=
        Ls.toTrajectory.liveBoundaryRank n minor.input minor.time := by
    rw [← minor.liveActionRank_eq_boundary]
    exact minor.rank_lower
  exact (Nat.not_le_of_lt hbudgetLs) hlower

/-- Obligation-package version of the corrected C2 closure. -/
theorem no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_provedCoverage
    (enc : ThreeCNFEncoding)
    (O : StrictObserverLowActionGodMoveCoverageObligations enc)
    (Hport : Theorem207StrictLiveBoundaryPort enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) :=
  no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_perObserverCoverage
    enc Hport (strictObserverLowActionGodMoveCoverage_theorem enc O)

/-- E2 obligation package for the intended standard model.  The bridge is split
into the proposition itself plus the two directions of equivalence with the
repository's encoded-DTM SAT lower-bound endpoint. -/
structure StandardPvsNPBridgeObligations
    (enc : ThreeCNFEncoding) : Type 1 where
  standardPvsNP : Prop
  standardPvsNP_implies_no_encodedSATDecider :
    standardPvsNP ->
      Not (exists M : TuringMachine.DTM,
        DTMDecidesSATWithEncoding enc M)
  no_encodedSATDecider_implies_standardPvsNP :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) ->
      standardPvsNP

/-- E2 bridge instance, converted from prose into explicit Lean obligations. -/
def standardPvsNPBridge_instance
    (enc : ThreeCNFEncoding)
    (O : StandardPvsNPBridgeObligations enc) :
    StandardPvsNPBridge enc where
  standardPvsNP := O.standardPvsNP
  standardPvsNP_iff_no_encodedSATDecider := by
    constructor
    · exact O.standardPvsNP_implies_no_encodedSATDecider
    · exact O.no_encodedSATDecider_implies_standardPvsNP

/-- Final exported standard statement from strict port + standard-model bridge
obligations. -/
theorem standardPvsNP_of_theorem207StrictPort_and_frontier
    (enc : ThreeCNFEncoding)
    (Ostd : StandardPvsNPBridgeObligations enc)
    (Hport : Theorem207StrictLiveBoundaryPort enc) :
    (standardPvsNPBridge_instance enc Ostd).standardPvsNP :=
  standardPvsNP_of_theorem207StrictPort
    (standardPvsNPBridge_instance enc Ostd) Hport

/-- Final exported standard statement from strict port + both corrected C2 and
E2 obligation packages.  `Ocov` exposes the corrected coverage payload in the
signature; the standard readout itself is through `Hport` and `Ostd`. -/
theorem standardPvsNP_of_theorem207StrictPort_and_all_frontier_obligations
    (enc : ThreeCNFEncoding)
    (_Ocov : StrictObserverLowActionGodMoveCoverageObligations enc)
    (Ostd : StandardPvsNPBridgeObligations enc)
    (Hport : Theorem207StrictLiveBoundaryPort enc) :
    (standardPvsNPBridge_instance enc Ostd).standardPvsNP := by
  exact standardPvsNP_of_theorem207StrictPort_and_frontier enc Ostd Hport

#print axioms strictObserverLowActionGodMoveCoverage_theorem
#print axioms no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_perObserverCoverage
#print axioms no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_provedCoverage
#print axioms standardPvsNPBridge_instance
#print axioms standardPvsNP_of_theorem207StrictPort_and_frontier
#print axioms standardPvsNP_of_theorem207StrictPort_and_all_frontier_obligations

end PallLean.Paper93.DeepMath.PathB
