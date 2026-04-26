import PallLean.Paper93.Paper283.RouteBRicherGaugePSideTransport
import PallLean.Paper93.Paper283.RouteBTransportPSideBound

/-!
# Route B richer-gauge P-window finite-span covers

This file packages the Cook-Levin P-window rank surface as the finite-span
cover object consumed by `RouteBRicherGaugePSideTransport`.  The main bridge is
kernel-only: once the flat unprojected P-side rank inequality is known, the
P-window subspace itself is an explicit finite span cover, using the existing
`mlBlockedSpdpSubspace` finite-dimensional instance.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP
open TuringMachine
open WithinProfileBound
open PallLean.Paper93.DeepMath.PathB

/-- Build a richer-gauge unprojected P-window finite-span cover from any
explicit finite submodule containing the P-window and satisfying the required
rank bound. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_submodule
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (coverSpan :
      Submodule Rat
        (MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat))
    (hfinite : Module.Finite Rat coverSpan)
    (hcontains :
      routeBRicherGaugeUnprojectedPWindowSubspace M n hn2 htb hns <=
        coverSpan)
    (hrank : Module.finrank Rat coverSpan <= n ^ 200) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns where
  span := coverSpan
  finite := hfinite
  contains := hcontains
  rank_bound := hrank

/-- The existing flat unprojected P-side rank inequality gives a finite-span
cover by taking the cover span to be the P-window subspace itself. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_rankBound
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hrank : RouteBSATUnprojectedPSideRankBound M n hn2 htb hns) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns where
  span := routeBRicherGaugeUnprojectedPWindowSubspace M n hn2 htb hns
  finite := by
    unfold routeBRicherGaugeUnprojectedPWindowSubspace
    infer_instance
  contains := le_rfl
  rank_bound := by
    simpa [RouteBSATUnprojectedPSideRankBound, mlBlockedSpdpRank,
      routeBRicherGaugeUnprojectedPWindowSubspace] using hrank

/-- The exact compiled-family within-profile theorem gives the richer-gauge
unprojected P-window finite-span cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_exactWithinProfileLemma
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hexact : CookLevinExactWithinProfileFinrankLemma M n hn2 htb hns) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_rankBound
    M n hn2 htb hns
    (routeBSATUnprojectedPSideRankBound_of_exactWithinProfileLemma
      M n hn2 htb hns hexact)

/-- A bounded-profile common-span theorem gives the richer-gauge unprojected
P-window finite-span cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_boundedProfileCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hspan : CookLevinBoundedProfileCommonSpanLemma M n hn2 htb hns) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_rankBound
    M n hn2 htb hns
    (routeBSATUnprojectedPSideRankBound_of_boundedProfileCommonSpan
      M n hn2 htb hns hspan)

/-- The all-bounded per-profile common-span theorem gives the richer-gauge
unprojected P-window finite-span cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hspan : CookLevinAllBoundedProfileCommonSpanLemma M n hn2 htb hns) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_rankBound
    M n hn2 htb hns
    (routeBSATUnprojectedPSideRankBound_of_allBoundedProfileCommonSpan
      M n hn2 htb hns hspan)

/-- Active common-span blockers plus the zero-profile common-span blocker give
the richer-gauge unprojected P-window finite-span cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_rankBound
    M n hn2 htb hns
    (routeBSATUnprojectedPSideRankBound_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
      M n hn2 htb hns hn4 hzero hblock)

/-- Active-template blockers give the richer-gauge unprojected P-window
finite-span cover through the existing bounded-profile template-collapse
route. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTemplateBlockers
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hblock : CookLevinActiveProfileTemplateCollapseBlockers M n hn2 htb hns) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_rankBound
    M n hn2 htb hns
    (routeBSATUnprojectedPSideRankBound_of_activeTemplateBlockers
      M n hn2 htb hns hn4 hblock)

/-! ## Axiom audit anchors -/

#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_submodule
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_rankBound
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_exactWithinProfileLemma
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_boundedProfileCommonSpan
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpan
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_activeTemplateBlockers

end PallLean.Paper93.Paper283
