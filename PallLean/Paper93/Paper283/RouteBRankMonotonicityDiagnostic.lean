import PallLean.Paper93.Paper283.RouteBProjectedLogWindowFinalCertificate
import PallLean.Paper93.Paper283.RouteBProjectionLogWindowContainmentProgress

/-!
# Route B rank-monotonicity diagnostic

This file isolates the optional old-target field
`SATDeciderGaugeRankMonotonicity` for the selected PiPhi/head-span projection.
The corrected projected contradiction consumer does not need this field.

The checked PiPhi/head-span SPDP containment is a log-window statement:
it controls only `(κ, ℓ) = (Nat.log 2 n, Nat.log 2 n)`.  The old
`CookLevinRichProjectionTarget` remains stronger because its rank field asks
for all `(κ, ℓ)` and all polynomials.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Rank monotonicity only at the canonical Route B log window. -/
def SATDeciderGaugeLogWindowRankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop :=
  forall (p : SATDeciderGaugeSpace M n hn2 htb hns),
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) (gauge p) <=
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) p

/-- The complementary off-window part of the old rank-monotonicity field. -/
def SATDeciderGaugeOffWindowRankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop :=
  forall (kappa ell : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns),
    (kappa ≠ Nat.log 2 n \/ ell ≠ Nat.log 2 n) ->
      mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          kappa ell (gauge p) <=
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          kappa ell p

/-- Log-window subspace containment proves exactly the log-window rank
inequality, by the same `Submodule.map` finrank argument used by the global
SPDP containment criterion. -/
theorem satDeciderGaugeLogWindowRankMonotonicity_of_routeBLogWindowContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcontain :
      RouteBRicherGaugeSPDPLogWindowSubspaceContainment
        M n hn2 htb hns Pi) :
    SATDeciderGaugeLogWindowRankMonotonicity M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) := by
  intro p
  unfold mlBlockedSpdpRank
  exact
    finrank_le_of_submodule_le_map
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
      (mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) p)
      (mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) p))
      (hcontain p)

/-- The old global rank-monotonicity field is exactly the conjunction of the
log-window rank inequality and all off-window rank inequalities. -/
theorem satDeciderGaugeRankMonotonicity_iff_logWindow_and_offWindow
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge <->
      SATDeciderGaugeLogWindowRankMonotonicity M n hn2 htb hns gauge /\
        SATDeciderGaugeOffWindowRankMonotonicity M n hn2 htb hns gauge := by
  constructor
  · intro hrank
    constructor
    · intro p
      exact hrank (Nat.log 2 n) (Nat.log 2 n) p
    · intro kappa ell p _hoff
      exact hrank kappa ell p
  · rintro ⟨hlog, hoff⟩ kappa ell p
    by_cases hk : kappa = Nat.log 2 n
    · by_cases hell : ell = Nat.log 2 n
      · subst kappa
        subst ell
        exact hlog p
      · exact hoff kappa ell p (Or.inr hell)
    · exact hoff kappa ell p (Or.inl hk)

/-- Diagnostic specialization to the selected PiPhi/head-span projection:
checked log-window containment leaves exactly the off-window rank inequalities
as the missing content for the old `SATDeciderGaugeRankMonotonicity` field. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_rankMonotonicity_iff_offWindow_of_logWindowContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcontain :
      RouteBRicherGaugeSPDPLogWindowSubspaceContainment M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns)) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns) <->
      SATDeciderGaugeOffWindowRankMonotonicity M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns) := by
  have hlog :
      SATDeciderGaugeLogWindowRankMonotonicity M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns) := by
    simpa [routeBPaperFaithfulPiPhiHeadSpanProjection] using
      satDeciderGaugeLogWindowRankMonotonicity_of_routeBLogWindowContainment
        M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns)
        hcontain
  constructor
  · intro hrank
    exact
      (satDeciderGaugeRankMonotonicity_iff_logWindow_and_offWindow
        M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)).mp
        hrank |>.2
  · intro hoff
    exact
      (satDeciderGaugeRankMonotonicity_iff_logWindow_and_offWindow
        M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)).mpr
        ⟨hlog, hoff⟩

/-- With direct projected P-side and NP-side fields fixed for the selected
PiPhi/head-span projection, the old SAT subgoal package is still equivalent
to the off-window rank-monotonicity obligation.  This is the precise
obstruction: the projected final consumer avoids this package, while
`CookLevinRichProjectionTarget` still contains it through
`SATDeciderGaugeRankMonotonicity`. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_oldSATSubgoals_iff_offWindow_of_projectedFields
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcontain :
      RouteBRicherGaugeSPDPLogWindowSubspaceContainment M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns))
    (hP :
      SATDeciderGaugePSideBound M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns))
    (hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)) :
    SATDeciderGaugeSubgoals M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns) <->
      SATDeciderGaugeOffWindowRankMonotonicity M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns) := by
  constructor
  · intro hsub
    exact
      (routeBPaperFaithfulPiPhiHeadSpan_rankMonotonicity_iff_offWindow_of_logWindowContainment
        M n hn2 htb hns hcontain).mp hsub.1
  · intro hoff
    exact
      ⟨(routeBPaperFaithfulPiPhiHeadSpan_rankMonotonicity_iff_offWindow_of_logWindowContainment
          M n hn2 htb hns hcontain).mpr hoff,
        hP,
        satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
          M n hn2 htb hns
          (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
          hNP⟩

/-! ## Axiom audit anchors -/

#print axioms SATDeciderGaugeLogWindowRankMonotonicity
#print axioms SATDeciderGaugeOffWindowRankMonotonicity
#print axioms satDeciderGaugeLogWindowRankMonotonicity_of_routeBLogWindowContainment
#print axioms satDeciderGaugeRankMonotonicity_iff_logWindow_and_offWindow
#print axioms routeBPaperFaithfulPiPhiHeadSpan_rankMonotonicity_iff_offWindow_of_logWindowContainment
#print axioms routeBPaperFaithfulPiPhiHeadSpan_oldSATSubgoals_iff_offWindow_of_projectedFields

end PallLean.Paper93.Paper283
