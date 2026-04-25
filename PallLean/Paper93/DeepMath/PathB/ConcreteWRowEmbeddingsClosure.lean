import PallLean.Paper93.DeepMath.PathB.ActiveProfileSpanProgress
import PallLean.Paper93.Direct.TemplateCollapseDirect

/-!
# ConcreteW row-embedding closure for PathB

This file records that the landed concreteW per-type row-embedding package is
already strong enough to close the active live-profile frontier, the bounded
template-collapse frontier, and the all-bounded common-span frontier.

The route is:

* `Direct.CookLevinPerTypeRowEmbeddings_concreteW`
* `Direct.cookLevinProfileTemplateCollapse_direct`
* `CookLevinProfileTemplateCollapseLemma_of_boundedProfile`
* `cookLevinAllBoundedProfileCommonSpan_of_templateCollapse`

The active live-profile closure is re-exported from
`ActiveProfileSpanProgress`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open SymmetricPowerBound
open TuringMachine (DTM)
open WithinProfileBound

attribute [local instance] Classical.dec

/-- The concreteW row-embedding package closes the active live-profile
common-span frontier. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCases_closed_by_concreteW
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCases M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_concreteW_rowEmbeddings
    M n hn htb hns hn4 hRowEmbeddings

/-- The concreteW row-embedding package supplies the active type-case
blockers. -/
theorem cookLevinActiveProfileTypeCaseBlockers_closed_by_concreteW
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns :=
  cookLevinActiveProfileTypeCaseBlockers_of_concreteW_rowEmbeddings
    M n hn htb hns hn4 hRowEmbeddings

/-- The concreteW row-embedding package closes the bounded-profile
template-collapse frontier. -/
theorem cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn htb hns :=
  PallLean.Paper93.Direct.cookLevinProfileTemplateCollapse_direct
    M n hn hn4 htb hns hRowEmbeddings

/-- The concreteW row-embedding package closes the all-profile
template-collapse frontier. -/
theorem cookLevinProfileTemplateCollapseLemma_of_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinProfileTemplateCollapseLemma M n hn htb hns :=
  cookLevinProfileTemplateCollapseLemma_of_boundedProfile
    M n hn htb hns
    (cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)

/-- The concreteW row-embedding package closes the all-bounded fixed-profile
common-span frontier. -/
theorem cookLevinAllBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinAllBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpan_of_templateCollapse
    M n hn htb hns
    (cookLevinProfileTemplateCollapseLemma_of_concreteW_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)

/-- The concreteW row-embedding package also closes the active per-`S`/shift
common-span frontier. -/
theorem cookLevinBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinBoundedProfileCommonSpan_of_templateCollapse
    M n hn htb hns
    (cookLevinProfileTemplateCollapseLemma_of_concreteW_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)

/-- Universal closure form: a universal concreteW row-embedding package closes
the all-bounded common-span frontier for every Cook-Levin instance satisfying
the current side conditions. -/
theorem cookLevinAllBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings_universal
    (hRowEmbeddings_universal :
      ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
        (hn4 : n ≥ 4) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn htb hns hn4) :
    ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
      (_hn4 : n ≥ 4) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      CookLevinAllBoundedProfileCommonSpanLemma M n hn htb hns := by
  intro M n hn hn4 htb hns
  exact cookLevinAllBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings
    M n hn htb hns hn4
    (hRowEmbeddings_universal M n hn hn4 htb hns)

/-- Universal closure form for the active per-`S`/shift common-span frontier. -/
theorem cookLevinBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings_universal
    (hRowEmbeddings_universal :
      ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
        (hn4 : n ≥ 4) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn htb hns hn4) :
    ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2)
      (_hn4 : n ≥ 4) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      CookLevinBoundedProfileCommonSpanLemma M n hn htb hns := by
  intro M n hn hn4 htb hns
  exact cookLevinBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings
    M n hn htb hns hn4
    (hRowEmbeddings_universal M n hn hn4 htb hns)

/-! ## Axiom audit anchors -/

#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_closed_by_concreteW
#print axioms cookLevinActiveProfileTypeCaseBlockers_closed_by_concreteW
#print axioms cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_rowEmbeddings
#print axioms cookLevinProfileTemplateCollapseLemma_of_concreteW_rowEmbeddings
#print axioms cookLevinAllBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings
#print axioms cookLevinBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings
#print axioms cookLevinAllBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings_universal
#print axioms cookLevinBoundedProfileCommonSpanLemma_of_concreteW_rowEmbeddings_universal

end PallLean.Paper93.DeepMath.PathB
