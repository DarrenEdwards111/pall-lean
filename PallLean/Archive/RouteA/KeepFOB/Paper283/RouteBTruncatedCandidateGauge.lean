import PallLean.Archive.RouteA.KeepFOB.DeepMath.PathB.SATDeciderGaugeKeepFOB

/-!
# Truncated Route B candidate gauge surface

The N-frame `CandidateGauge` asks for finite rank of the whole projection
range.  That is too strong for the Cook-Levin first-of-block projection: the
projection keeps infinitely many monomials in the kept variables.  This file
records the finite-window version actually used by the Route B SAT interface:
the gauge is a `SATDeciderGaugeMap`, is idempotent, and has finite-dimensional
image on the relevant Cook-Levin SPDP window.

No P-side bound, NP-side preservation, or final gauge existence theorem is
asserted here.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The derivative order used by the finite Cook-Levin SPDP window. -/
def routeBTruncatedWindowKappa (n : Nat) : Nat :=
  Nat.log 2 n

/-- The shift degree used by the finite Cook-Levin SPDP window. -/
def routeBTruncatedWindowShift (n : Nat) : Nat :=
  Nat.log 2 n

/-- The SPDP subspace at the finite Cook-Levin window. -/
noncomputable abbrev routeBTruncatedWindowSubspace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns) :=
  mlBlockedSpdpSubspace
    (cook_levin_compilation M n hn2 htb hns).partition
    (routeBTruncatedWindowKappa n)
    (routeBTruncatedWindowShift n)
    p

/-- The image of the finite Cook-Levin SPDP window under a SAT-decider gauge. -/
noncomputable abbrev routeBTruncatedWindowImage
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns) :=
  Submodule.map gauge
    (routeBTruncatedWindowSubspace M n hn2 htb hns p)

/-- Finite-dimensionality of the image side of the finite window.  This is the
truncated replacement for asking that the whole projection range be finite
rank. -/
def RouteBFiniteWindowImage
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop :=
  ∀ p : SATDeciderGaugeSpace M n hn2 htb hns,
    Module.Finite Rat
      (routeBTruncatedWindowImage M n hn2 htb hns gauge p)

/-- Any linear SAT-decider gauge has finite-dimensional image on the finite
SPDP window, because the source window itself is finite-dimensional. -/
theorem routeBFiniteWindowImage_of_satDeciderGaugeMap
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) :
    RouteBFiniteWindowImage M n hn2 htb hns gauge := by
  intro p
  infer_instance

/-- Image rank on the finite window cannot exceed the original finite-window
rank. -/
theorem routeBTruncatedWindowImage_finrank_le
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    Module.finrank Rat
        (routeBTruncatedWindowImage M n hn2 htb hns gauge p) ≤
      Module.finrank Rat
        (routeBTruncatedWindowSubspace M n hn2 htb hns p) :=
  Submodule.finrank_map_le gauge
    (routeBTruncatedWindowSubspace M n hn2 htb hns p)

/-- Refined Route B gauge surface on the finite Cook-Levin window.  The
`spdpImageContainment` field is stronger than rank monotonicity and is the
existing criterion used by the concrete `keepFOB` projection. -/
structure RouteBTruncatedCandidateGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  /-- The exact SAT-decider gauge map consumed downstream. -/
  gauge : SATDeciderGaugeMap M n hn2 htb hns
  /-- Structural projection/idempotence. -/
  isProjection : GaugeMonotonicity.IsProjectionGauge gauge
  /-- Strong SPDP image containment, hence rank monotonicity. -/
  spdpImageContainment :
    SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns gauge
  /-- Finite-dimensional image on the finite Cook-Levin SPDP window. -/
  finiteWindowImage :
    RouteBFiniteWindowImage M n hn2 htb hns gauge

/-- The truncated surface implies the existing SAT-decider rank-monotonicity
field. -/
theorem RouteBTruncatedCandidateGauge.rankMonotonicity
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (G : RouteBTruncatedCandidateGauge M n hn2 htb hns) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns G.gauge :=
  satDeciderGaugeRankMonotonicity_of_spdpSubspaceImageContainment
    M n hn2 htb hns G.gauge G.spdpImageContainment

/-- Window-level rank monotonicity, expanded as a finrank comparison between
the concrete SPDP subspaces. -/
theorem RouteBTruncatedCandidateGauge.windowRankMonotonicity
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (G : RouteBTruncatedCandidateGauge M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    Module.finrank Rat
        (routeBTruncatedWindowSubspace M n hn2 htb hns (G.gauge p)) ≤
      Module.finrank Rat
        (routeBTruncatedWindowSubspace M n hn2 htb hns p) := by
  calc
    Module.finrank Rat
        (routeBTruncatedWindowSubspace M n hn2 htb hns (G.gauge p))
        ≤
      Module.finrank Rat
        (routeBTruncatedWindowImage M n hn2 htb hns G.gauge p) :=
        Submodule.finrank_mono
          (G.spdpImageContainment
            (routeBTruncatedWindowKappa n)
            (routeBTruncatedWindowShift n) p)
    _ ≤ Module.finrank Rat
        (routeBTruncatedWindowSubspace M n hn2 htb hns p) :=
        routeBTruncatedWindowImage_finrank_le M n hn2 htb hns G.gauge p

/-- The concrete `keepFOB` projection is idempotent. -/
theorem satDeciderGaugeKeepFOBProjection_isProjectionGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    GaugeMonotonicity.IsProjectionGauge
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) := by
  unfold satDeciderGaugeKeepFOBProjection
  exact PiStarConcrete.piZero_isProjectionGauge PiStarConcrete.keepFOB

/-- The concrete first-of-block gauge as a truncated Route B candidate. -/
noncomputable def routeBTruncatedKeepFOBGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBTruncatedCandidateGauge M n hn2 htb hns where
  gauge := satDeciderGaugeKeepFOBProjection M n hn2 htb hns
  isProjection :=
    satDeciderGaugeKeepFOBProjection_isProjectionGauge M n hn2 htb hns
  spdpImageContainment :=
    satDeciderGaugeKeepFOBProjection_spdpSubspaceImageContainment
      M n hn2 htb hns
  finiteWindowImage :=
    routeBFiniteWindowImage_of_satDeciderGaugeMap M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns)

/-- The package's underlying map is exactly the existing `keepFOB`
SAT-decider projection. -/
theorem routeBTruncatedKeepFOBGauge_gauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (routeBTruncatedKeepFOBGauge M n hn2 htb hns).gauge =
      satDeciderGaugeKeepFOBProjection M n hn2 htb hns :=
  rfl

/-- Structural and rank-monotone fields for the concrete `keepFOB`
truncated candidate. -/
noncomputable def satDeciderGaugeKeepFOBProjection_routeBTruncatedCandidate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBTruncatedCandidateGauge M n hn2 htb hns :=
  routeBTruncatedKeepFOBGauge M n hn2 htb hns

/-- Rank monotonicity for the concrete truncated `keepFOB` package, obtained
from the existing keepFOB SPDP image-containment lemma. -/
theorem routeBTruncatedKeepFOBGauge_rankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) :=
  (routeBTruncatedKeepFOBGauge M n hn2 htb hns).rankMonotonicity

/-- Finite-dimensional image on the finite Cook-Levin window for the concrete
`keepFOB` projection. -/
theorem satDeciderGaugeKeepFOBProjection_finiteWindowImage
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBFiniteWindowImage M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) :=
  (routeBTruncatedKeepFOBGauge M n hn2 htb hns).finiteWindowImage

end PallLean.Paper93.Paper283
