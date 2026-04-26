import PallLean.Paper93.Paper283.RouteBRicherGaugePWindowCover
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingsClosure

/-!
# Concrete wrappers for the Route B richer-gauge P-window cover

This file keeps the richer-gauge P-window finite-span cover reduced to the
smallest active fixed-profile common-span surfaces currently exposed by the
profile-compression layer.  The main wrapper below consumes the pointwise
`CookLevinAllBoundedProfileCommonSpanAtProfile` family directly; stronger
active/template/concreteW packages are provided only as convenience routes into
that same cover object.

No `spdp_profile_generators` route is used.
-/

namespace PallLean.Paper93.Paper283

open TuringMachine
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.DeepMath.PathB

/-- Pointwise fixed-profile all-span common spans are enough to build the
richer-gauge unprojected P-window finite-span cover.

This is the smallest exposed profile-common-span wrapper: the assumption is
exactly one `CookLevinAllBoundedProfileCommonSpanAtProfile` certificate for
each derivative-count profile. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpanAtProfiles
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hat :
      forall h : ProfileHistogram,
        CookLevinAllBoundedProfileCommonSpanAtProfile M n hn2 htb hns h) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpan
    M n hn2 htb hns
    (by
      intro h
      exact hat h)

/-- Pointwise active per-`S`/shift common spans are enough to build the
richer-gauge unprojected P-window finite-span cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_boundedProfileCommonSpanAtProfiles
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hat :
      forall h : ProfileHistogram,
        CookLevinBoundedProfileCommonSpanAtProfile M n hn2 htb hns h) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_boundedProfileCommonSpan
    M n hn2 htb hns
    (by
      intro h
      exact hat h)

/-- Live-profile common-span cases plus the non-scalar zero-profile
common-span package give the richer-gauge unprojected P-window finite-span
cover.

This is the useful non-template route: it deliberately avoids the false
zero-profile singleton/template-collapse target. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_liveProfileCases
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hlive :
      CookLevinAllBoundedProfileCommonSpanLiveProfileCases
        M n hn2 htb hns) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpan
    M n hn2 htb hns
    (cookLevinAllBoundedProfileCommonSpanLemma_of_liveProfileCases
      M n hn2 htb hns hn4 hzero hlive)

/-- Pointwise template-collapse certificates imply the all-span common-span
family and hence the richer-gauge unprojected P-window finite-span cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_templateCollapseAtProfiles
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hat :
      forall h : ProfileHistogram,
        CookLevinProfileTemplateCollapseAtProfile M n hn2 htb hns h) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpanAtProfiles
    M n hn2 htb hns
    (by
      intro h
      exact
        cookLevinAllBoundedProfileCommonSpanAtProfile_of_templateCollapseAtProfile
          M n hn2 htb hns h (hat h))

/-- The all-profile template-collapse lemma is enough for the richer-gauge
unprojected P-window finite-span cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_templateCollapse
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcollapse : CookLevinProfileTemplateCollapseLemma M n hn2 htb hns) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpan
    M n hn2 htb hns
    (cookLevinAllBoundedProfileCommonSpan_of_templateCollapse
      M n hn2 htb hns hcollapse)

/-- The bounded-profile template-collapse finite case split is enough for the
richer-gauge unprojected P-window finite-span cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_boundedProfileTemplateCollapse
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcollapse :
      CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn2 htb hns) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_templateCollapse
    M n hn2 htb hns
    (cookLevinProfileTemplateCollapseLemma_of_boundedProfile
      M n hn2 htb hns hcollapse)

/-- Universal fixed-profile raw-touched common-span certificates imply the
all-span common-span family and hence the richer-gauge P-window cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_rawTouchedDerivCommonSpanAtProfiles
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hraw :
      forall h : ProfileHistogram,
        CookLevinRawTouchedDerivCommonSpanAtProfile M n hn2 htb hns h) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpan
    M n hn2 htb hns
    (cookLevinAllBoundedProfileCommonSpan_of_rawTouchedDerivCommonSpanAtProfiles
      M n hn2 htb hns hraw)

/-- ConcreteW row embeddings close the all-bounded common-span route and hence
build the richer-gauge unprojected P-window finite-span cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_rowEmbeddings
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpan
    M n hn2 htb hns
    (cookLevinAllBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings
      M n hn2 htb hns hn4 hRowEmbeddings)

/-! ## Axiom audit anchors -/

#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_allBoundedProfileCommonSpanAtProfiles
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_boundedProfileCommonSpanAtProfiles
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_liveProfileCases
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_templateCollapseAtProfiles
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_templateCollapse
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_boundedProfileTemplateCollapse
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_rawTouchedDerivCommonSpanAtProfiles
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_rowEmbeddings

end PallLean.Paper93.Paper283
