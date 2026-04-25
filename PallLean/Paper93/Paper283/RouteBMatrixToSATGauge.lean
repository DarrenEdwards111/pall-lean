import PallLean.Paper93.Paper283.RouteBToSATGaugeBridge
import PallLean.Paper93.Paper283.PiStarSpectralRank
import PallLean.Paper93.Concrete.ProjectionRank
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRankMonotoneCriterion
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugePSideBridge
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeNPBridge

/-!
# Route B matrix/rank packages to SAT gauge fields

This file narrows the old `RouteBMatrixRankToSATGaugeHypothesis`.
The checked Route B analytic theorem gives a matrix/rank surface.  The SAT
frontier asks for three fields on a concrete `SATDeciderGaugeMap`.

The remaining mathematical content is isolated below as functoriality facts:

* the NFrame projection has SPDP image-containment for the Cook-Levin
  partition;
* the Route B matrix rank package transports to the unprojected flat P-side
  Cook-Levin rank bound;
* the same package transports the NP identity-minor lower bound through the
  selected projection.

Everything after those facts is checked packaging.  No profile-collapse route
and no `keepFOB` projection is used here.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- Matrix-side column-span control for the real Π⋆ matrix action.  This is
the concrete linear-algebra fact proved in `PiStarSpectralRank`, named here in
the Route B bridge vocabulary. -/
def RouteBMatrixColumnSpanControl {N : Nat}
    (P : Matrix (Fin N) (Fin N) Real) : Prop :=
  LinearMap.range (piStarFromMatrix P) ≤
    Submodule.span Real (Set.range (fun i => P.mulVec (Pi.single i 1)))

/-- Every real projection matrix has the Route B column-span control used by
the matrix-side rank story. -/
theorem routeBMatrixColumnSpanControl_of_matrix {N : Nat}
    (P : Matrix (Fin N) (Fin N) Real) :
    RouteBMatrixColumnSpanControl P :=
  piStarFromMatrix_range_le P

/-- The identity matrix action has full range in the matrix-side Route B
vocabulary. -/
theorem routeBMatrixColumnSpanControl_identity_range_top
    (N : Nat) [Nonempty (Fin N)] :
    LinearMap.range (piStarFromMatrix (1 : Matrix (Fin N) (Fin N) Real)) =
      ⊤ :=
  piStarFromMatrix_identity_range_top N

/-- The concrete rank compatibility needed to relate the Route B matrix rank
`rankA` to the selected NFrame projection.  This is deliberately only a
rank-comparison surface; it does not claim any SAT/SPDP functoriality. -/
def RouteBProjectionRankCompatible
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Prop :=
  PallLean.Paper93.Concrete.projectionRank Pi ≤ (rankA : Real)

/-- The rank compatibility immediately supplies the nonnegative concrete rank
side condition used by downstream real-valued comparisons. -/
theorem projectionRank_nonneg_of_routeBProjectionRankCompatible
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (_hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi) :
    0 ≤ PallLean.Paper93.Concrete.projectionRank Pi :=
  PallLean.Paper93.Concrete.projectionRank_nonneg

/-- The P-side flat Cook-Levin rank statement that the Route B matrix package
must transport to before rank monotonicity projects it. -/
def RouteBSATUnprojectedPSideRankBound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  mlBlockedSpdpRank
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200

/-- The projected NP lower-bound statement needed to discharge the flat
`SATDeciderGaugeNPIdentityMinorPreservation` field. -/
def RouteBSATProjectedNPIdentityMinorLowerBound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop :=
  Nat.choose (n / 3) (Nat.log 2 n) ≤
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)))

/-- The exact functoriality still needed after Route B supplies its checked
matrix/rank output.

The first field is a projection functoriality fact on SPDP subspaces.  The
second and third fields are the remaining transports from the Route B analytic
rank surface, together with concrete projection-rank compatibility, to the
flat Cook-Levin P-side and NP-side rank statements. -/
structure RouteBMatrixToSATGaugeFunctoriality {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Prop where
  spdp_image_containment :
    SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
  pSide_of_routeB_rank :
    RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA ->
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi ->
        RouteBSATUnprojectedPSideRankBound M n hn2 htb hns
  npIdentityMinor_of_routeB_rank :
    RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA ->
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi ->
        RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
          (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)

/-- Matrix/rank package owned by the Route B-to-SAT bridge: a selected NFrame
projection, its matrix-rank compatibility, the checked Route B analytic rank
surface, and the three explicit functoriality facts above. -/
structure RouteBMatrixProjectionRankPackage {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat) where
  Pi : PallLean.Paper93.NFrame.CandidateGauge
    (RouteBCookLevinDim M n hn2 htb hns)
  admissible : PallLean.Paper93.NFrame.AdmissibleGauge Pi
  analytic :
    RouteBAnalyticRankCoreOutput
      alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA
  rank_compatible :
    RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi
  functoriality :
    RouteBMatrixToSATGaugeFunctoriality
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA Pi

/-- The functoriality package gives the SAT rank-monotonicity field. -/
theorem satDeciderGaugeRankMonotonicity_of_routeBMatrixFunctoriality {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA Pi) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  satDeciderGaugeRankMonotonicity_of_spdpSubspaceImageContainment
    M n hn2 htb hns
    (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
    hfun.spdp_image_containment

/-- The functoriality package gives the projected SAT P-side field once the
checked Route B rank output and projection-rank compatibility are supplied. -/
theorem satDeciderGaugePSideBound_of_routeBMatrixFunctoriality {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hanalytic :
      RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA Pi) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  satDeciderGaugePSideBound_of_rankMonotone_of_unprojected_bound
    M n hn2 htb hns
    (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
    (satDeciderGaugeRankMonotonicity_of_routeBMatrixFunctoriality
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA Pi hfun)
    (hfun.pSide_of_routeB_rank hanalytic hcompat)

/-- The functoriality package gives the SAT NP identity-minor preservation
field once the checked Route B rank output and projection-rank compatibility
are supplied. -/
theorem satDeciderGaugeNPIdentityMinorPreservation_of_routeBMatrixFunctoriality
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hanalytic :
      RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA Pi) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
    M n hn2 htb hns
    (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
    (hfun.npIdentityMinor_of_routeB_rank hanalytic hcompat)

/-- The narrowed matrix/rank functoriality facts discharge the full SAT
subgoal package for the selected Route B NFrame projection. -/
theorem routeBNFrameGaugeSubgoals_of_routeBMatrixFunctoriality {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hanalytic :
      RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA Pi) :
    RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi :=
  ⟨satDeciderGaugeRankMonotonicity_of_routeBMatrixFunctoriality
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA Pi hfun,
    satDeciderGaugePSideBound_of_routeBMatrixFunctoriality
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA Pi hanalytic hcompat hfun,
    satDeciderGaugeNPIdentityMinorPreservation_of_routeBMatrixFunctoriality
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA Pi hanalytic hcompat hfun⟩

/-- The new explicit functoriality package implies the old broad
`RouteBMatrixRankToSATGaugeHypothesis`. -/
theorem routeBMatrixRankToSATGaugeHypothesis_of_functoriality {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA Pi) :
    RouteBMatrixRankToSATGaugeHypothesis
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA Pi := by
  intro hanalytic
  exact routeBNFrameGaugeSubgoals_of_routeBMatrixFunctoriality
    M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
    capacity delta rankA Pi hanalytic hcompat hfun

/-- Package-level bridge from the narrowed Route B matrix/rank package to the
existing NFrame gauge package vocabulary. -/
theorem routeBNFrameGaugePackage_of_routeBMatrixProjectionRankPackage
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (hpkg :
      RouteBMatrixProjectionRankPackage
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA) :
    RouteBNFrameGaugePackage M n hn2 htb hns := by
  refine ⟨hpkg.Pi, hpkg.admissible, ?_⟩
  exact routeBNFrameGaugeSubgoals_of_routeBMatrixFunctoriality
    M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
    capacity delta rankA hpkg.Pi hpkg.analytic hpkg.rank_compatible
    hpkg.functoriality

/-- Package-level bridge from the narrowed Route B matrix/rank package to the
existing Cook-Levin rich projection target. -/
theorem cookLevinRichProjectionTarget_of_routeBMatrixProjectionRankPackage
    {N d : Nat}
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (hpkg :
      RouteBMatrixProjectionRankPackage
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_routeBNFrameGaugePackage
    M n hn hn2 htb hns
    (routeBNFrameGaugePackage_of_routeBMatrixProjectionRankPackage
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA hpkg)

/-- Direct bridge from the narrowed Route B matrix/rank functoriality package
to the existing Cook-Levin rich projection target. -/
theorem cookLevinRichProjectionTarget_of_routeBMatrixFunctoriality {N d : Nat}
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hanalytic :
      RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA Pi) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_routeBNFrameGaugeSubgoals
    M n hn hn2 htb hns Pi
    (routeBNFrameGaugeSubgoals_of_routeBMatrixFunctoriality
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA Pi hanalytic hcompat hfun)

/-- Direct theorem-hypothesis version: if Route B analytic hypotheses prove the
checked matrix/rank surface and the narrowed functoriality package is supplied,
then the selected NFrame projection satisfies the SAT subgoal package without
using the profile-collapse route. -/
theorem routeBNFrameGaugeSubgoals_of_routeBAnalyticCore_functoriality
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (halpha0 : 0 < alpha0)
    (hGadgetRank :
      ∀ v : Fin N,
        alpha0 <= localEnergy alpha beta G chi Phi v ->
          kappa <= (gadgetFamily v).rank)
    {logDet capacity delta : Real} {rankA : Nat}
    (hcapacity : 0 < capacity)
    (hLogLower :
      delta *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <= logDet)
    (hLogUpper : logDet <= (rankA : Real) * capacity)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA Pi) :
    RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi := by
  exact routeBNFrameGaugeSubgoals_of_routeBMatrixFunctoriality
    M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
    capacity delta rankA Pi
    (routeBAnalyticRankCoreOutput_of_hypotheses
      alpha beta alpha0 kappa G chi Phi gadgetFamily halpha0 hGadgetRank
      hcapacity hLogLower hLogUpper)
    hcompat hfun

/-! ## Axiom audit anchors -/

#print axioms routeBMatrixColumnSpanControl_of_matrix
#print axioms routeBMatrixColumnSpanControl_identity_range_top
#print axioms projectionRank_nonneg_of_routeBProjectionRankCompatible
#print axioms satDeciderGaugeRankMonotonicity_of_routeBMatrixFunctoriality
#print axioms satDeciderGaugePSideBound_of_routeBMatrixFunctoriality
#print axioms satDeciderGaugeNPIdentityMinorPreservation_of_routeBMatrixFunctoriality
#print axioms routeBNFrameGaugeSubgoals_of_routeBMatrixFunctoriality
#print axioms routeBMatrixRankToSATGaugeHypothesis_of_functoriality
#print axioms routeBNFrameGaugePackage_of_routeBMatrixProjectionRankPackage
#print axioms cookLevinRichProjectionTarget_of_routeBMatrixProjectionRankPackage
#print axioms cookLevinRichProjectionTarget_of_routeBMatrixFunctoriality
#print axioms routeBNFrameGaugeSubgoals_of_routeBAnalyticCore_functoriality

end PallLean.Paper93.Paper283
