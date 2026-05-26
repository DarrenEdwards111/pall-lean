import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheorem207StrictPort

/-!
# Global grid-move bridge to low-action Book-1 obstruction

This file isolates the exact missing global-grid move theorem shape:
coverage of strict observers by low-action observers at each calibration level.

With that coverage, the already-proved non-vacuous low-action obstruction lifts
to the original strict observer class, and the strict-port no-decider endpoint
follows directly.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Global grid-move coverage hypothesis:
for every calibration exponent `c`, every strict observer can be represented by
some low-action observer with exponent `k ≤ c` and pointwise-equal live boundary
rank trajectory. -/
def StrictObserverLowActionCoverage
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat,
    forall Ls : StrictDynamicNFrameLagrangianObserver enc,
      exists Ll : LowActionStrictDynamicNFrameLagrangianObserver enc,
        Ll.k <= c /\
        (forall n : Nat,
          forall input : Fin n -> Bool,
          forall time : Nat,
            Ls.toTrajectory.liveBoundaryRank n input time =
              Ll.base.toTrajectory.liveBoundaryRank n input time)

/-- If strict observers are covered by low-action observers, then Book-1
universal boundary-budget obstruction lifts from the low-action class to the
strict class. -/
theorem universalBook1BoundaryBudgetObstruction_of_lowActionCoverage
    (enc : ThreeCNFEncoding)
    (Hcov : StrictObserverLowActionCoverage enc) :
    UniversalBook1BoundaryBudgetObstruction enc := by
  intro c n hn20 hlog Ls input time
  rcases Hcov c Ls with ⟨Ll, hk, hrank⟩
  have hlow :
      Ll.base.toTrajectory.liveBoundaryRank n input time <
        Nat.choose (n / 3) (Nat.log 2 n) :=
    universalBook1BoundaryBudgetObstructionLowAction_theorem enc
      c n hn20 hlog Ll hk input time
  simpa [hrank n input time] using hlow

/-- Global-grid move closure:
strict port plus low-action coverage implies no encoded SAT-deciding DTM. -/
theorem no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_lowActionCoverage
    (enc : ThreeCNFEncoding)
    (Hport : Theorem207StrictLiveBoundaryPort enc)
    (Hcov : StrictObserverLowActionCoverage enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) :=
  no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_universalBook1Obstruction
    enc
    (universalBook1BoundaryBudgetObstruction_of_lowActionCoverage enc Hcov)
    Hport

/-! ## Kernel-only axiom trace -/

#print axioms universalBook1BoundaryBudgetObstruction_of_lowActionCoverage
#print axioms no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_lowActionCoverage

end PallLean.Paper93.DeepMath.PathB
