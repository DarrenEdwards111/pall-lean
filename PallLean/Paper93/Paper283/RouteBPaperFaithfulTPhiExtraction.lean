import PallLean.Step4Compiler
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingBridge
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingsClosure

/-!
# Route B paper-faithful `TΦ` extraction

The paper's Route B extraction is not the broad multilinear-tail complement.
It is the explicit coupled-sheet map

`TΦ = basis ◦ affine relabel ◦ restriction ◦ projection`.

In the current formal development, the concrete checked instance of that
pipeline is the strict first-of-block coupled-sheet extraction from
`Step4Compiler`: restrict the ambient `embedded_Q` sheet along the strict
first-of-block map, identify it with the flat Cook-Levin restriction, and use
the canonical projection/relabel rank comparison.  This file gives that object
the Route B `TΦ` names and packages the two facts Route B actually needs:

* extraction/rank transfer to the coupled target;
* same-target identity-minor data on that target.

It deliberately does not route through the old broad head-span complement.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler.Step252
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The concrete paper-faithful `TΦ` coordinate map used by the strict
coupled-sheet extraction. -/
noncomputable abbrev routeBPaperFaithfulTPhiMap
    (M : DTM) (n : ℕ) :
    Fin (n / 3) → Fin (PaperFaithfulCompilation.cookLevinUVSplit M n).total :=
  cookLevinStrictFOBMap M n

/-- The `TΦ` coordinate map is injective, so it defines an honest restriction
and pullback partition. -/
theorem routeBPaperFaithfulTPhiMap_injective
    (M : DTM) (n : ℕ) :
    Function.Injective (routeBPaperFaithfulTPhiMap M n) :=
  cookLevinStrictFOBMap_injective M n

/-- The paper-faithful coupled-sheet target extracted by `TΦ`. -/
noncomputable def routeBPaperFaithfulTPhiTarget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total) :
    GodMoveExtractionTarget M n hn2 htb hns :=
  cookLevinStrictFOBTarget M n hn2 htb hns B_total

/-- The strict `TΦ` target polynomial is exactly the strict restriction of the
ambient embedded coupled sheet. -/
theorem routeBPaperFaithfulTPhiTarget_coupledPoly_eq
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total) :
    (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total).coupledPoly =
      MultilinearSPDP.restrictPoly ℚ (routeBPaperFaithfulTPhiMap M n)
        (routeBPaperFaithfulTPhiMap_injective M n)
        (Step4Compiler.Step247.partitioned_output_cookLevin
          M n hn2 htb hns).embedded_Q := by
  rfl

/-- The strict embedded-sheet restriction agrees with the flat Cook-Levin
first-of-block restriction.  This is the pointwise polynomial identity behind
the projected P-window row identity for this concrete `TΦ` target. -/
theorem routeBPaperFaithfulTPhi_restrict_embedded_Q_eq_restrict_compiledPoly
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    MultilinearSPDP.restrictPoly ℚ (routeBPaperFaithfulTPhiMap M n)
        (routeBPaperFaithfulTPhiMap_injective M n)
        (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).embedded_Q =
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n)
        (PaperFaithfulSeparation.compiledPoly
          (PaperFaithfulSeparation.cook_levin_compilation
            M n hn2 htb hns)) := by
  simpa [routeBPaperFaithfulTPhiMap] using
    cookLevinStrictFOB_restrict_embedded_Q_eq_restrict_compiledPoly
      M n hn2 htb hns

/-- Canonical projection/relabel rank monotonicity for the paper-faithful
`TΦ` target. -/
theorem routeBPaperFaithfulTPhi_canonical_projection_stage
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    CookLevinStrictFOBCanonicalProjectionStage
      M n hn2 htb hns B_total hB_total :=
  cookLevinStrictFOBCanonicalProjectionStage
    M n hn2 htb hns B_total hB_total

/-- The concrete `TΦ` extraction gives the Route B extraction/rank transfer
for the strict coupled-sheet target. -/
theorem routeBPaperFaithfulTPhi_extraction_transfer
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    PaperFaithfulSeparation.GodMoveRouteB_ExtractionObligation
      M n hn2 htb hns hdec
      (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total) := by
  change
    PaperFaithfulSeparation.GodMoveRouteB_ExtractionObligation
      M n hn2 htb hns hdec
      (cookLevinStrictFOBTarget M n hn2 htb hns B_total)
  exact
    cookLevinStrictFOB_routeB_extraction_transfer
      M n hn2 htb hns hdec B_total hB_total

/-- The same strict `TΦ` target carries the Route B identity-minor lower-bound
data. -/
def routeBPaperFaithfulTPhi_identity_minor_data
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    PaperFaithfulSeparation.RouteBIdentityMinorSameTargetData
      (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total) :=
  cookLevinStrictFOBTarget_identity_minor_data
    M n hn hn2 htb hns B_total hB_total

/-- The strict `TΦ` target provides both corrected Route B target facts on the
same coupled sheet: extraction transfer and identity-minor data. -/
theorem routeBPaperFaithfulTPhi_extraction_and_identity_minor
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    PaperFaithfulSeparation.GodMoveRouteB_ExtractionObligation
        M n hn2 htb hns hdec
        (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total) ∧
      Nonempty
        (PaperFaithfulSeparation.RouteBIdentityMinorSameTargetData
          (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total)) :=
  ⟨routeBPaperFaithfulTPhi_extraction_transfer
      M n hn2 htb hns hdec B_total hB_total,
    ⟨routeBPaperFaithfulTPhi_identity_minor_data
      M n hn hn2 htb hns B_total hB_total⟩⟩

/-! ## Final strict-`TΦ` source-transport consumers -/

/-- The strict paper-faithful `TΦ` target feeds the final source-transport
contradiction once the selected Cook-Levin P-side upper bound is supplied. -/
theorem false_of_routeBPaperFaithfulTPhi_qRankUpper
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    (hQ_upper : MultilinearSPDP.mlBlockedSpdpRank
      (MultilinearSPDP.pullbackPartition B_total
        (PaperFaithfulCompilation.cookLevinUVSplit M n).inlU)
      (Nat.log 2 n) (Nat.log 2 n)
      (show MvPolynomial (Fin n) ℚ from
        PaperFaithfulCompilation.cookLevinQ M n hn2 htb hns) ≤ n ^ 200) :
    False :=
  DirectRankPackage_cookLevin_strictFOB_source_transport_false
    M n hn htb hns hn2 B_total hB_total hQ_upper hdec

/-- The landed P-side theorem supplies the strict `TΦ` source-transport
consumer's exact `Q`-rank upper-bound input. -/
theorem false_of_routeBPaperFaithfulTPhi_from_p_side
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    False :=
  DirectRankPackage_cookLevin_strictFOB_source_transport_false_from_p_side
    M n hn htb hns hn2 B_total hB_total hdec

/-- The paper-faithful template-collapse P-side frontier also feeds the strict
`TΦ` final source-transport consumer directly. -/
theorem false_of_routeBPaperFaithfulTPhi_from_templateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    False :=
  DirectRankPackage_cookLevin_strictFOB_source_transport_false_from_templateCollapse
    M n hn htb hns hn2 B_total hB_total hdec hcollapse

/-- Canonical strict-`TΦ` contradiction from the template-collapse frontier.
This specializes the previous theorem to the actual Cook-Levin extended
partition, so callers do not have to carry an arbitrary `B_total` witness. -/
theorem false_of_routeBPaperFaithfulTPhi_canonical_from_templateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_from_templateCollapse
    M n hn hn2 htb hns hdec
    (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    rfl hcollapse

/-- Canonical strict-`TΦ` contradiction from the bounded-profile
template-collapse frontier.  This is the smaller paper §9 profile-compression
input; it is converted to the all-profile template-collapse statement by the
existing bounded-profile reduction. -/
theorem false_of_routeBPaperFaithfulTPhi_canonical_from_boundedProfileTemplateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_canonical_from_templateCollapse
    M n hn hn2 htb hns hdec
    (WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile
      M n hn2 htb hns hcollapse)

/-- At the paper scale, `n ≥ 2^804` supplies the side condition `n ≥ 4`
needed by the concreteW local chart/row-embedding route. -/
theorem routeB_paperScale_ge_four
    {n : ℕ} (hn : n ≥ 2 ^ 804) : n ≥ 4 := by
  have hpow : (4 : ℕ) ≤ 2 ^ 804 := by
    calc
      (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 804 := by
        exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  exact le_trans hpow hn

/-- The strict paper-faithful `TΦ` target consumes the concreteW row-embedding
package through the checked bounded-profile template-collapse theorem. -/
theorem false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4) :
    False :=
  false_of_routeBPaperFaithfulTPhi_canonical_from_boundedProfileTemplateCollapse
    M n hn hn2 htb hns hdec
    (cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_concreteW_rowEmbeddings
      M n hn2 htb hns hn4 hRowEmbeddings)

/-- The strict `TΦ` target consumes the concrete H3/H4/I5 local closure
frontier by first assembling the concreteW row-embedding package. -/
theorem false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_closureFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hn4 : n ≥ 4)
    (hFrontier :
      CookLevinConcreteWRowEmbeddingClosureFrontier
        M n hn2 htb hns hn4) :
    False :=
  false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_rowEmbeddings
    M n hn hn2 htb hns hdec hn4
    (CookLevinPerTypeRowEmbeddings_concreteW_of_closureFrontier
      M n hn2 htb hns hn4 hFrontier)

/-- A uniform concreteW row-embedding theorem closes the strict `TΦ`
contradiction-strength consumer.  This is the direct final hook for the local
chart/profile-compression route; it does not pass through the failed broad
multilinear-tail projection. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteW_rowEmbeddings
    (hRowEmbeddings :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn2 htb hns hn4) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  have hn4 : n ≥ 4 := routeB_paperScale_ge_four hn
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_rowEmbeddings
      M n hn hn2 htb hns hdec hn4
      (hRowEmbeddings M n hn2 hn4 htb hns)

/-- Legacy rich-projection discharge from the strict `TΦ` concreteW
row-embedding route, mediated only by the established no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteW_rowEmbeddings
    (hRowEmbeddings :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn2 htb hns hn4) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteW_rowEmbeddings
      hRowEmbeddings)

/-- A uniform concrete H3/H4/I5 local closure theorem closes the strict `TΦ`
contradiction-strength consumer through the concreteW row-embedding assembly. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteW_closureFrontier
    (hFrontier :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinConcreteWRowEmbeddingClosureFrontier
          M n hn2 htb hns hn4) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  have hn4 : n ≥ 4 := routeB_paperScale_ge_four hn
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_closureFrontier
      M n hn hn2 htb hns hdec hn4
      (hFrontier M n hn2 hn4 htb hns)

/-- Legacy rich-projection discharge from the strict `TΦ` concrete local
closure route, mediated only by the established no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteW_closureFrontier
    (hFrontier :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinConcreteWRowEmbeddingClosureFrontier
          M n hn2 htb hns hn4) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteW_closureFrontier
      hFrontier)

/-- The strict paper `TΦ` extraction closes the contradiction-strength Route B
consumer from the landed Cook-Levin P-side rank theorem.  This is the direct
paper-faithful final path: it uses the coupled-sheet `basis ◦ affine relabel ◦
restriction ◦ projection` target and never passes through the failed broad
head-span complement or global admissible-query promotion. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_p_side :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_from_p_side
      M n hn hn2 htb hns hdec
      (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
      rfl

/-- Legacy rich-projection discharge from the strict `TΦ` landed-P-side route,
mediated only by the established no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_p_side :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_p_side

/-- A uniform template-collapse theorem on the strict paper `TΦ` extraction
rules out bounded SAT deciders at the paper scale.  This is the direct final
consumer for the strict extraction path; it does not use the older broad
head-span complement. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_templateCollapse
    (hcollapse :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemma
          M n hn2 htb hns) :
    PallLean.Paper93.DeepMath.PathB.NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_templateCollapse
      M n hn hn2 htb hns hdec
      (hcollapse M n hn hn2 htb hns)

/-- A uniform bounded-profile template-collapse theorem on the strict paper
`TΦ` extraction rules out bounded SAT deciders at the paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_boundedProfileTemplateCollapse
    (hcollapse :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
          M n hn2 htb hns) :
    PallLean.Paper93.DeepMath.PathB.NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_boundedProfileTemplateCollapse
      M n hn hn2 htb hns hdec
      (hcollapse M n hn hn2 htb hns)

/-- The legacy rich-projection discharge follows from the strict-`TΦ`
template-collapse route only through the established no-decider equivalence.
This keeps the strict extraction path separate from the failed broad
multilinear-tail projection target. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_templateCollapse
    (hcollapse :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemma
          M n hn2 htb hns) :
    PallLean.Paper93.DeepMath.PathB.CookLevinRichProjectionDischarge :=
  PallLean.Paper93.DeepMath.PathB.cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_templateCollapse
      hcollapse)

/-- The legacy rich-projection discharge follows from the strict-`TΦ`
bounded-profile route only through the established no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_boundedProfileTemplateCollapse
    (hcollapse :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
          M n hn2 htb hns) :
    PallLean.Paper93.DeepMath.PathB.CookLevinRichProjectionDischarge :=
  PallLean.Paper93.DeepMath.PathB.cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_boundedProfileTemplateCollapse
      hcollapse)

/-! ## Axiom audit anchors -/

#print axioms routeBPaperFaithfulTPhiMap_injective
#print axioms routeBPaperFaithfulTPhi_restrict_embedded_Q_eq_restrict_compiledPoly
#print axioms routeBPaperFaithfulTPhi_canonical_projection_stage
#print axioms routeBPaperFaithfulTPhi_extraction_transfer
#print axioms routeBPaperFaithfulTPhi_identity_minor_data
#print axioms routeBPaperFaithfulTPhi_extraction_and_identity_minor
#print axioms false_of_routeBPaperFaithfulTPhi_qRankUpper
#print axioms false_of_routeBPaperFaithfulTPhi_from_p_side
#print axioms false_of_routeBPaperFaithfulTPhi_from_templateCollapse
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_templateCollapse
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_boundedProfileTemplateCollapse
#print axioms routeB_paperScale_ge_four
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_rowEmbeddings
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_closureFrontier
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_templateCollapse
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_templateCollapse
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_boundedProfileTemplateCollapse
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_boundedProfileTemplateCollapse
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteW_rowEmbeddings
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteW_rowEmbeddings
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteW_closureFrontier
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteW_closureFrontier
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_p_side
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_p_side

end PallLean.Paper93.Paper283
