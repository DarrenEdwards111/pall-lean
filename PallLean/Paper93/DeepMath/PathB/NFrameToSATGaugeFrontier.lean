import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget
import PallLean.Paper93.NFrame.PiStarExistence
import PallLean.Paper93.Paper283.PiStarFromStationarity

/-!
# NFrame/PiStar to SAT-decider gauge frontier

This file is intentionally only a bridge.  The existing NFrame/Paper283
stationarity route supplies an admissible `NFrame.CandidateGauge`, but it does
not currently supply the three exact `SATDeciderGauge` fields required by the
Cook-Levin frontier.  We therefore isolate the minimal missing interface:
whenever a stationarity or Π⋆ package produces a SAT gauge together with those
three fields, it discharges the existing `CookLevinRichProjectionTarget`.

No theorem below asserts that the final SAT-decider gauge exists.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- The NFrame ambient dimension matching the exact Cook-Levin compilation. -/
noncomputable abbrev CookLevinNFrameDim
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Nat :=
  (cook_levin_compilation M n hn2 htb hns).numVars

/-- View an NFrame candidate gauge at the Cook-Levin dimension as the exact
`SATDeciderGaugeMap` used by the Path B frontier. -/
abbrev nframeCandidateAsSATGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (CookLevinNFrameDim M n hn2 htb hns)) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  Pi.projection

/-- Per-instance missing interface for an NFrame candidate: its projection must
prove exactly the three SAT-decider gauge fields.  This is deliberately a
`Prop`; it records the content not supplied by the present NFrame/Paper283
stationarity witnesses. -/
def NFrameCandidateSATGaugeFields
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (CookLevinNFrameDim M n hn2 htb hns)) : Prop :=
  SATDeciderGaugeSubgoals M n hn2 htb hns
    (nframeCandidateAsSATGauge M n hn2 htb hns Pi)

/-- The NFrame candidate-field interface is definitionally the explicit
rank/P-side/NP-preservation triple. -/
theorem nframeCandidateSATGaugeFields_iff
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (CookLevinNFrameDim M n hn2 htb hns)) :
    NFrameCandidateSATGaugeFields M n hn2 htb hns Pi ↔
      SATDeciderGaugeRankMonotonicity M n hn2 htb hns
        (nframeCandidateAsSATGauge M n hn2 htb hns Pi) ∧
        SATDeciderGaugePSideBound M n hn2 htb hns
          (nframeCandidateAsSATGauge M n hn2 htb hns Pi) ∧
          SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
            (nframeCandidateAsSATGauge M n hn2 htb hns Pi) := by
  rfl

/-- A candidate-gauge package in the NFrame vocabulary, specialised to the
exact Cook-Levin ambient space.  The admissibility witness is retained because
it is what the NFrame/Paper283 route currently produces; the load-bearing part
is `NFrameCandidateSATGaugeFields`. -/
def NFrameCandidateSATGaugePackage
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ Pi : PallLean.Paper93.NFrame.CandidateGauge
      (CookLevinNFrameDim M n hn2 htb hns),
    PallLean.Paper93.NFrame.AdmissibleGauge Pi ∧
      NFrameCandidateSATGaugeFields M n hn2 htb hns Pi

/-- Any NFrame candidate whose projection supplies the three SAT-decider gauge
fields gives the per-instance Cook-Levin rich projection target. -/
theorem cookLevinRichProjectionTarget_of_nframeCandidateSATGaugeFields
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (CookLevinNFrameDim M n hn2 htb hns))
    (hPi : NFrameCandidateSATGaugeFields M n hn2 htb hns Pi) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  ⟨nframeCandidateAsSATGauge M n hn2 htb hns Pi, hPi⟩

/-- Package-level version of the NFrame candidate bridge. -/
theorem cookLevinRichProjectionTarget_of_nframeCandidateSATGaugePackage
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hpackage : NFrameCandidateSATGaugePackage M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns := by
  rcases hpackage with ⟨Pi, _hAdm, hfields⟩
  exact cookLevinRichProjectionTarget_of_nframeCandidateSATGaugeFields
    M n hn hn2 htb hns Pi hfields

/-- What the present Paper283 stationarity bridge actually supplies: an
admissible NFrame candidate at the Cook-Levin dimension.  This theorem is
included to make the remaining gap explicit: it does not produce
`NFrameCandidateSATGaugeFields`. -/
theorem paper283Stationarity_supplies_admissible_nframeCandidate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {d : Nat} (α β lam : ℝ) (hα : 0 < α) (hβ : 0 < β) (hlam : 0 < lam)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed
      (CookLevinNFrameDim M n hn2 htb hns) d)
    (χ : PallLean.Paper93.Paper283.TseitinCharge
      (CookLevinNFrameDim M n hn2 htb hns))
    (Φ : Fin (CookLevinNFrameDim M n hn2 htb hns) → ℝ)
    (A : Matrix (Fin (CookLevinNFrameDim M n hn2 htb hns))
      (Fin (CookLevinNFrameDim M n hn2 htb hns)) ℝ)
    (hΦ : PallLean.Paper93.Paper283.StationaryPhi
      (N := CookLevinNFrameDim M n hn2 htb hns) (d := d) α β G χ Φ)
    (hA : PallLean.Paper93.Paper283.StationaryA lam A) :
    ∃ Pi : PallLean.Paper93.NFrame.CandidateGauge
        (CookLevinNFrameDim M n hn2 htb hns),
      PallLean.Paper93.NFrame.AdmissibleGauge Pi :=
  PallLean.Paper93.Paper283.piStar_exists_from_stationarity
    α β lam hα hβ hlam G χ Φ A hΦ hA

/-- Stationarity-level missing interface: a Paper283 stationary pair is useful
for the SAT-decider frontier exactly when it also yields an NFrame candidate
whose projection has the three SAT fields. -/
def Paper283StationaritySATGaugePackage
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {d : Nat} (α β lam : ℝ)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed
      (CookLevinNFrameDim M n hn2 htb hns) d)
    (χ : PallLean.Paper93.Paper283.TseitinCharge
      (CookLevinNFrameDim M n hn2 htb hns))
    (Φ : Fin (CookLevinNFrameDim M n hn2 htb hns) → ℝ)
    (A : Matrix (Fin (CookLevinNFrameDim M n hn2 htb hns))
      (Fin (CookLevinNFrameDim M n hn2 htb hns)) ℝ) : Prop :=
  PallLean.Paper93.Paper283.StationaryPhi
      (N := CookLevinNFrameDim M n hn2 htb hns) (d := d) α β G χ Φ →
    PallLean.Paper93.Paper283.StationaryA lam A →
      NFrameCandidateSATGaugePackage M n hn2 htb hns

/-- If a Paper283 stationarity package supplies the missing SAT fields, it
bridges to the per-instance Cook-Levin rich projection target. -/
theorem cookLevinRichProjectionTarget_of_paper283StationaritySATGaugePackage
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {d : Nat} (α β lam : ℝ)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed
      (CookLevinNFrameDim M n hn2 htb hns) d)
    (χ : PallLean.Paper93.Paper283.TseitinCharge
      (CookLevinNFrameDim M n hn2 htb hns))
    (Φ : Fin (CookLevinNFrameDim M n hn2 htb hns) → ℝ)
    (A : Matrix (Fin (CookLevinNFrameDim M n hn2 htb hns))
      (Fin (CookLevinNFrameDim M n hn2 htb hns)) ℝ)
    (hΦ : PallLean.Paper93.Paper283.StationaryPhi
      (N := CookLevinNFrameDim M n hn2 htb hns) (d := d) α β G χ Φ)
    (hA : PallLean.Paper93.Paper283.StationaryA lam A)
    (hpackage :
      Paper283StationaritySATGaugePackage M n hn2 htb hns α β lam G χ Φ A) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_nframeCandidateSATGaugePackage
    M n hn hn2 htb hns (hpackage hΦ hA)

/-- Global NFrame-candidate frontier: every SAT-decider instance receives an
admissible NFrame candidate whose projection satisfies the three exact SAT
gauge fields.  This is stronger than the minimal frontier because it insists
on the NFrame `CandidateGauge` structure. -/
def NFrameCandidateSATGaugeFrontier : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    NFrameCandidateSATGaugePackage M n hn2 htb hns

/-- The NFrame-candidate frontier discharges the existing Cook-Levin rich
projection discharge. -/
theorem cookLevinRichProjectionDischarge_of_nframeCandidateSATGaugeFrontier
    (hfrontier : NFrameCandidateSATGaugeFrontier) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns hdec
  exact cookLevinRichProjectionTarget_of_nframeCandidateSATGaugePackage
    M n hn hn2 htb hns (hfrontier M n hn hn2 htb hns hdec)

/-- Minimal per-instance interface after forgetting the NFrame structural
source: a SAT gauge and the three explicit fields. -/
def NFrameToSATGaugeInstanceInterface
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ gauge : SATDeciderGaugeMap M n hn2 htb hns,
    SATDeciderGaugeSubgoals M n hn2 htb hns gauge

/-- The minimal instance interface is definitionally the existing target. -/
theorem nframeToSATGaugeInstanceInterface_iff_cookLevinRichProjectionTarget
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    NFrameToSATGaugeInstanceInterface M n hn2 htb hns ↔
      CookLevinRichProjectionTarget M n hn hn2 htb hns := by
  rfl

/-- Minimal global interface required of any NFrame/Paper283/PiStar route after
translation to the SAT-decider vocabulary. -/
def NFrameToSATGaugeDischargeInterface : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    NFrameToSATGaugeInstanceInterface M n hn2 htb hns

/-- The minimal global interface is exactly the existing Cook-Levin rich
projection discharge. -/
theorem nframeToSATGaugeDischargeInterface_iff_cookLevinRichProjectionDischarge :
    NFrameToSATGaugeDischargeInterface ↔ CookLevinRichProjectionDischarge := by
  rfl

/-- Forgetting the NFrame structure turns the NFrame-candidate frontier into
the minimal global interface. -/
theorem nframeToSATGaugeDischargeInterface_of_nframeCandidateSATGaugeFrontier
    (hfrontier : NFrameCandidateSATGaugeFrontier) :
    NFrameToSATGaugeDischargeInterface := by
  intro M n hn hn2 htb hns hdec
  rcases hfrontier M n hn hn2 htb hns hdec with ⟨Pi, _hAdm, hfields⟩
  exact ⟨nframeCandidateAsSATGauge M n hn2 htb hns Pi, hfields⟩

/-! ## Axiom audit anchors -/

#print axioms nframeCandidateSATGaugeFields_iff
#print axioms cookLevinRichProjectionTarget_of_nframeCandidateSATGaugeFields
#print axioms cookLevinRichProjectionTarget_of_nframeCandidateSATGaugePackage
#print axioms paper283Stationarity_supplies_admissible_nframeCandidate
#print axioms cookLevinRichProjectionTarget_of_paper283StationaritySATGaugePackage
#print axioms cookLevinRichProjectionDischarge_of_nframeCandidateSATGaugeFrontier
#print axioms nframeToSATGaugeInstanceInterface_iff_cookLevinRichProjectionTarget
#print axioms nframeToSATGaugeDischargeInterface_iff_cookLevinRichProjectionDischarge
#print axioms nframeToSATGaugeDischargeInterface_of_nframeCandidateSATGaugeFrontier

end PallLean.Paper93.DeepMath.PathB
