import PallLean.Paper93.Paper283.FullChain283
import PallLean.Paper93.NFrame.PiStarExistence
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget

/-!
# Route B matrix-rank to SAT gauge bridge

This file is only an interface layer.  The checked Route B analytic core in
`FullChain283` produces matrix/local-rank inequalities, while the Path B SAT
frontier consumes a `SATDeciderGaugeMap` with three exact SPDP/SAT fields.

The genuinely missing mathematical step is the conversion from the Route B
matrix-rank output, together with an NFrame candidate gauge, to those three SAT
fields.  We expose that conversion as an explicit `Prop` hypothesis and prove
the definitional/packaging implications around it.

No profile-template collapse and no `keepFOB` projection is used here.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- The Cook-Levin ambient dimension used by the Route B-to-SAT bridge. -/
noncomputable abbrev RouteBCookLevinDim
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Nat :=
  (cook_levin_compilation M n hn2 htb hns).numVars

/-- View an NFrame candidate at the Cook-Levin dimension as the exact
SAT-decider gauge map consumed by the Path B frontier. -/
abbrev routeBNFrameCandidateAsSATGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  Pi.projection

/-- Route B's NFrame-to-SAT gauge obligation: the candidate projection must
satisfy the three existing SAT-decider SPDP subgoals. -/
def RouteBNFrameGaugeSubgoals
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Prop :=
  SATDeciderGaugeSubgoals M n hn2 htb hns
    (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)

/-- The Route B NFrame gauge obligation is definitionally the existing
rank/P-side/NP-preservation triple. -/
theorem routeBNFrameGaugeSubgoals_iff_fields
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) :
    RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi ↔
      SATDeciderGaugeRankMonotonicity M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) ∧
        SATDeciderGaugePSideBound M n hn2 htb hns
          (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) ∧
          SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
            (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) := by
  rfl

/-- The same obligation, repackaged as the bundled Global God-Move gauge
surface.  This is a packaging equivalence only. -/
theorem routeBNFrameGaugeSubgoals_iff_isAmplituhedronGauge
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) :
    RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi ↔
      GlobalGodMoveGauge.IsAmplituhedronGauge M n hn hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  satDeciderGaugeSubgoals_iff_isAmplituhedronGauge
    M n hn hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)

/-- A Route B NFrame gauge package at the exact Cook-Levin ambient dimension. -/
def RouteBNFrameGaugePackage
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns),
    PallLean.Paper93.NFrame.AdmissibleGauge Pi ∧
      RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi

/-- Forgetting the NFrame wrapper gives the existing SAT subgoal package. -/
theorem satDeciderGaugeSubgoals_of_routeBNFrameGaugeSubgoals
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hPi : RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi) :
    SATDeciderGaugeSubgoals M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  hPi

/-- Any Route B NFrame candidate whose projection has the three SAT fields
gives the existing Cook-Levin rich projection target. -/
theorem cookLevinRichProjectionTarget_of_routeBNFrameGaugeSubgoals
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hPi : RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  ⟨routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi, hPi⟩

/-- Package-level version of the Route B NFrame-to-SAT bridge. -/
theorem cookLevinRichProjectionTarget_of_routeBNFrameGaugePackage
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hpackage : RouteBNFrameGaugePackage M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns := by
  rcases hpackage with ⟨Pi, _hAdm, hPi⟩
  exact cookLevinRichProjectionTarget_of_routeBNFrameGaugeSubgoals
    M n hn hn2 htb hns Pi hPi

/-- The checked Route B analytic core output, named as the matrix-rank surface
that still has to be related to SAT/SPDP gauge fields. -/
def RouteBAnalyticRankCoreOutput {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat) : Prop :=
  (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
      kappa <=
    ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
      (gadgetFamily v).rank
  ∧
  (delta / capacity) *
      ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
        Real) <=
    (rankA : Real)

/-- Route B's checked analytic theorem supplies the named matrix-rank surface. -/
theorem routeBAnalyticRankCoreOutput_of_hypotheses {N d : Nat}
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
    (hLogUpper : logDet <= (rankA : Real) * capacity) :
    RouteBAnalyticRankCoreOutput
      alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA :=
  routeB_analytic_rank_core
    alpha beta alpha0 kappa G chi Phi gadgetFamily halpha0 hGadgetRank
    hcapacity hLogLower hLogUpper

/-- The genuinely missing Route B matrix-rank-to-SAT/SPDP conversion.

Given the checked analytic rank output and an NFrame candidate gauge at the
Cook-Levin dimension, this hypothesis asserts exactly the three SAT-decider
gauge subgoals for the candidate's projection. -/
def RouteBMatrixRankToSATGaugeHypothesis {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Prop :=
  RouteBAnalyticRankCoreOutput
      alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA ->
    RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi

/-- Consuming Route B's checked analytic core plus the explicit missing
matrix-rank-to-SAT/SPDP mapping gives the SAT gauge subgoals. -/
theorem routeBNFrameGaugeSubgoals_of_routeBAnalyticRankCore {N d : Nat}
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
    (hmap :
      RouteBMatrixRankToSATGaugeHypothesis
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA Pi) :
    RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi :=
  hmap (routeBAnalyticRankCoreOutput_of_hypotheses
    alpha beta alpha0 kappa G chi Phi gadgetFamily halpha0 hGadgetRank
    hcapacity hLogLower hLogUpper)

/-- End-to-end Route B bridge to the existing Cook-Levin rich projection target,
conditional only on the explicit missing matrix-rank-to-SAT/SPDP mapping. -/
theorem cookLevinRichProjectionTarget_of_routeBAnalyticRankCore {N d : Nat}
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
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
    (_hAdm : PallLean.Paper93.NFrame.AdmissibleGauge Pi)
    (hmap :
      RouteBMatrixRankToSATGaugeHypothesis
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA Pi) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_routeBNFrameGaugeSubgoals
    M n hn hn2 htb hns Pi
      (routeBNFrameGaugeSubgoals_of_routeBAnalyticRankCore
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        halpha0 hGadgetRank hcapacity hLogLower hLogUpper Pi hmap)

/-! ## Axiom audit anchors -/

#print axioms routeBNFrameGaugeSubgoals_iff_fields
#print axioms routeBNFrameGaugeSubgoals_iff_isAmplituhedronGauge
#print axioms satDeciderGaugeSubgoals_of_routeBNFrameGaugeSubgoals
#print axioms cookLevinRichProjectionTarget_of_routeBNFrameGaugeSubgoals
#print axioms cookLevinRichProjectionTarget_of_routeBNFrameGaugePackage
#print axioms routeBAnalyticRankCoreOutput_of_hypotheses
#print axioms routeBNFrameGaugeSubgoals_of_routeBAnalyticRankCore
#print axioms cookLevinRichProjectionTarget_of_routeBAnalyticRankCore

end PallLean.Paper93.Paper283
