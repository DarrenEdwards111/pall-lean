import PallLean.Step4Compiler
import PallLean.GlobalGodMoveGauge
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpanningBridge
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingBridge
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingsClosure
import PallLean.Paper93.DeepMath.PathB.PerTypeSpanningTemplateCollapseBridge
import PallLean.Paper93.DeepMath.PathB.ActiveProfileEndpointAugmentedProgress
import PallLean.Paper93.DeepMath.PathB.ActiveProfileEndpointAugmentedProofProgress
import PallLean.Paper93.CanonicalizationMap
import PallLean.Paper93.InterfaceProfile
import PallLean.Paper93.TemplateCollapseDischarge
import PallLean.Paper93.Paper283.RouteBTransportPSideBound
import PallLean.Paper93.Paper283.RouteBZeroProfileProjectedPWindowProgress
import PallLean.Paper93.Paper283.RouteBChargedShiftClosureProgress

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
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.Spanning
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

/-- Canonical projection stage for the strict paper-faithful `TΦ` target.

This is the narrow semantic stage matching the paper: the projection rank
comparison is only stated for the transported flat first-of-block restriction
partition and the transported strict coupled-sheet partition. -/
noncomputable def routeBPaperFaithfulTPhiCanonicalProjectionStage
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    CanonicalExtractionProjectionStage
      (target := routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total)
      (cookLevinStrictFOBRealRestrictionStage M n hn2 htb hns hdec) where
  inputPoly :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n)
      (PaperFaithfulSeparation.compiledPoly
        (PaperFaithfulSeparation.cook_levin_compilation
          M n hn2 htb hns))
  projectedPoly :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBMap M n)
      (cookLevinStrictFOBMap_injective M n)
      (Step4Compiler.Step247.partitioned_output_cookLevin
        M n hn2 htb hns).embedded_Q
  is_coordinate_selection := True
  projection_rank_mono := by
    intro κ ℓ
    change
      MultilinearSPDP.mlBlockedSpdpRank
          (MultilinearSPDP.pullbackPartition B_total
            (cookLevinStrictFOBMap M n)) κ ℓ
          (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBMap M n)
            (cookLevinStrictFOBMap_injective M n)
            (Step4Compiler.Step247.partitioned_output_cookLevin
              M n hn2 htb hns).embedded_Q) ≤
        MultilinearSPDP.mlBlockedSpdpRank
          (MultilinearSPDP.pullbackPartition
            (PaperFaithfulSeparation.cook_levin_compilation
              M n hn2 htb hns).partition
            (cookLevinStrictFOBFlatMap n)) κ ℓ
          (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
            (cookLevinStrictFOBFlatMap_injective n)
            (PaperFaithfulSeparation.compiledPoly
              (PaperFaithfulSeparation.cook_levin_compilation
                M n hn2 htb hns)))
    exact
      cookLevinStrictFOBRealProjectionStage_canonical_projection_rank_mono
        M n hn2 htb hns B_total hB_total κ ℓ

/-- Canonical staged semantic witness for the strict paper-faithful `TΦ`
target. -/
noncomputable def routeBPaperFaithfulTPhiCanonicalSemantics
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    CanonicalExtractionMapSemantics M n hn2 htb hns hdec
      (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total) where
  restriction := cookLevinStrictFOBRealRestrictionStage M n hn2 htb hns hdec
  projection :=
    routeBPaperFaithfulTPhiCanonicalProjectionStage
      M n hn2 htb hns hdec B_total hB_total
  projection_input_matches := rfl
  output_identification := rfl

/-- The strict paper-faithful `TΦ` target satisfies the narrow canonical
semantic obligation. -/
theorem routeBPaperFaithfulTPhi_canonicalSemanticObligation
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    GodMoveCanonicalExtractionSemanticObligation M n hn2 htb hns hdec
      (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total) :=
  ⟨routeBPaperFaithfulTPhiCanonicalSemantics
    M n hn2 htb hns hdec B_total hB_total⟩

/-- The canonical strict `TΦ` semantic witness gives the extraction transfer
without the legacy arbitrary-partition projection interface. -/
theorem routeBPaperFaithfulTPhi_extraction_transfer_from_canonicalSemantics
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    PaperFaithfulSeparation.GodMoveRouteB_ExtractionObligation
      M n hn2 htb hns hdec
      (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total) :=
  extraction_from_canonical_semantics
    (routeBPaperFaithfulTPhiCanonicalSemantics
      M n hn2 htb hns hdec B_total hB_total)

/-- The selected total partition for the canonical strict `TΦ` target. -/
noncomputable abbrev routeBPaperFaithfulTPhiCanonicalTotalPartition
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total :=
  PaperFaithfulCompilation.extendedCookLevinPartition M n hn2

/-- The selected canonical strict `TΦ` target. -/
noncomputable abbrev routeBPaperFaithfulTPhiCanonicalTarget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    GodMoveExtractionTarget M n hn2 htb hns :=
  routeBPaperFaithfulTPhiTarget M n hn2 htb hns
    (routeBPaperFaithfulTPhiCanonicalTotalPartition M n hn2)

/-- The selected canonical strict `TΦ` target satisfies the narrow canonical
semantic obligation. -/
theorem routeBPaperFaithfulTPhi_canonicalTargetSemanticObligation
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M) :
    GodMoveCanonicalExtractionSemanticObligation M n hn2 htb hns hdec
      (routeBPaperFaithfulTPhiCanonicalTarget M n hn2 htb hns) :=
  routeBPaperFaithfulTPhi_canonicalSemanticObligation
    M n hn2 htb hns hdec
    (routeBPaperFaithfulTPhiCanonicalTotalPartition M n hn2) rfl

/-- Extraction transfer for the selected canonical strict `TΦ` target through
the narrow canonical semantic interface. -/
theorem routeBPaperFaithfulTPhi_canonicalTargetExtractionTransfer
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M) :
    PaperFaithfulSeparation.GodMoveRouteB_ExtractionObligation
      M n hn2 htb hns hdec
      (routeBPaperFaithfulTPhiCanonicalTarget M n hn2 htb hns) :=
  routeBPaperFaithfulTPhi_extraction_transfer_from_canonicalSemantics
    M n hn2 htb hns hdec
    (routeBPaperFaithfulTPhiCanonicalTotalPartition M n hn2) rfl

/-- Same-target identity-minor data for the selected canonical strict `TΦ`
target. -/
noncomputable def routeBPaperFaithfulTPhi_canonicalTargetIdentityMinorData
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    PaperFaithfulSeparation.RouteBIdentityMinorSameTargetData
      (routeBPaperFaithfulTPhiCanonicalTarget M n hn2 htb hns) :=
  cookLevinStrictFOBTarget_identity_minor_data
    M n hn hn2 htb hns
    (routeBPaperFaithfulTPhiCanonicalTotalPartition M n hn2) rfl

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

/-! ## Normalized extracted coupled-sheet representative -/

/-- The paper-faithful Route B representative is the normalized coupled sheet
`Q×_{Φ,S}` produced by the `TΦ`/`ΠΦ` extraction, not the raw derivative row of
the local product-form Cook-Levin polynomial.

The global Route B component interface already stores that representative as
`E.coupledSheet`: the paper's `(N ◦ TΦ)(P_{M',n}) = Q×_{Φ,S}` output after
basis/relabel/restriction/projection and normalization. -/
noncomputable abbrev routeBPaperFaithfulTPhiNormalizedCoupledSheetRepresentative
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (E : GlobalGodMoveGauge.Theorem207Extraction M n hn hn2 htb hns) :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ :=
  E.coupledSheet

/-- Route B row identity for the normalized coupled-sheet representative.

This is the formal replacement for the refuted raw derivative target. Rows are
compared after the paper extraction/normalization has already selected
`Q×_{Φ,S}` as the representative. The remaining row operation is the standard
SPDP window row on that representative; no raw `restrictedCompiledPoly`
derivative row appears in the statement. -/
def RouteBPaperFaithfulTPhiNormalizedCoupledSheetRowIdentity
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (E : GlobalGodMoveGauge.Theorem207Extraction M n hn hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (shift :
      MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj
        (shift * SPDP.iterDerivList S
          (routeBPaperFaithfulTPhiNormalizedCoupledSheetRepresentative
            M n hn hn2 htb hns E)) =
      mlProj (shift * SPDP.iterDerivList S E.coupledSheet)

/-- The normalized coupled-sheet representative has the intended Route B row
identity by construction: after `(N ◦ TΦ)` has selected `Q×_{Φ,S}`, the row
representative is exactly `E.coupledSheet`. -/
theorem routeBPaperFaithfulTPhi_normalizedCoupledSheetRowIdentity
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (E : GlobalGodMoveGauge.Theorem207Extraction M n hn hn2 htb hns) :
    RouteBPaperFaithfulTPhiNormalizedCoupledSheetRowIdentity
      M n hn hn2 htb hns E := by
  intro S shift hSlen hshiftDegree hshiftVars hadm
  rfl

/-- Component-level Route B contradiction on the normalized extracted coupled
sheet.

This is the proof-facing consumer for the corrected representative: extraction
rank monotonicity compares the normalized sheet to the paper compiled source,
the P-side bound controls that source, and the NP-side identity minor lives on
the same normalized sheet. -/
theorem false_of_routeBPaperFaithfulTPhi_normalizedCoupledSheet_components
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (E : GlobalGodMoveGauge.Theorem207Extraction M n hn hn2 htb hns)
    (hExtract :
      GlobalGodMoveGauge.Theorem207ExtractionRankMonotone
        M n hn hn2 htb hns E)
    (hP :
      GlobalGodMoveGauge.Theorem207PSideUpperBound
        M n hn hn2 htb hns E)
    (hNP :
      GlobalGodMoveGauge.Theorem207NPSideLowerBound
        M n hn hn2 htb hns E) :
    False := by
  have hchoose_le : Nat.choose (n / 3) (Nat.log 2 n) ≤ n ^ 200 :=
    hNP.sheet_np_side_lower_bound.trans
      (hExtract.extraction_rank_monotone.trans hP.compiled_p_side_bound)
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans
      (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804))
      hn
  have hbin :
      n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono :
      Nat.choose (n / 30) (Nat.log 2 n) ≤
        Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans (le_trans hbin hmono) hchoose_le
  have hlog : 804 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hn_ge_1 : 1 ≤ n := by omega
  have hn_gt_1 : 1 < n := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right hn_ge_1 hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right hn_gt_1 (by omega : 200 < 201)))

/-- Source-transport version of the normalized coupled-sheet Route B
contradiction.

This is the paper-faithful variant when the instrumented source is not forced
into the local product-form `compiledPoly` variable space. The source is the
paper's `P_{M',n}` object with its own partition, the target is the normalized
`Q×_{Φ,S}` semantic extraction target, and the bridge is the rank-monotone
`TΦ/ΠΦ` transport between them. -/
theorem false_of_routeBPaperFaithfulTPhi_normalizedCoupledSheet_sourceTransport
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (source :
      GlobalGodMoveGauge.Theorem207PaperSource M n hn hn2 htb hns)
    (hP :
      GlobalGodMoveGauge.Theorem207PaperSourcePSideUpperBound
        M n hn hn2 htb hns source)
    (bridge :
      GlobalGodMoveGauge.Theorem207PaperSourceToTargetRankBridge
        M n hn hn2 htb hns source targetData.extractionTarget)
    (hNP :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank targetData.extractionTarget.coupledPartition
          (Nat.log 2 n) (Nat.log 2 n)
          targetData.extractionTarget.coupledPoly) :
    False :=
  GlobalGodMoveGauge.theorem207PaperSource_transport_false
    M n hn hn2 htb hns targetData.extractionTarget source hP bridge hNP

/-- Same source-transport Route B contradiction, with the NP lower bound
supplied by same-target identity-minor data on the normalized coupled-sheet
target. -/
theorem false_of_routeBPaperFaithfulTPhi_normalizedCoupledSheet_sourceTransport_sameTargetMinor
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (source :
      GlobalGodMoveGauge.Theorem207PaperSource M n hn hn2 htb hns)
    (hP :
      GlobalGodMoveGauge.Theorem207PaperSourcePSideUpperBound
        M n hn hn2 htb hns source)
    (bridge :
      GlobalGodMoveGauge.Theorem207PaperSourceToTargetRankBridge
        M n hn hn2 htb hns source targetData.extractionTarget)
    (minor : RouteBIdentityMinorSameTargetData targetData.extractionTarget) :
    False :=
  GlobalGodMoveGauge.theorem207PaperSource_transport_false
    M n hn hn2 htb hns targetData.extractionTarget source hP bridge
    (routeB_strong_np_from_same_target_identity_minor minor)

/-- Existing global source-transport data is enough to close the normalized
coupled-sheet Route B contradiction. This is the final consumer for the
corrected representative: prove the explicit semantic target, same-target
identity minor, paper source P-side bound, and source-to-target rank bridge,
then this theorem supplies `False`. -/
theorem false_of_routeBPaperFaithfulTPhi_normalizedCoupledSheet_from_sourceTransportData
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M) :
    False :=
  GlobalGodMoveGauge.theorem207SemanticTransportWitness_false
    M n hn hn2 htb hns hdec
    (GlobalGodMoveGauge.theorem207SemanticTransportWitness_from_source_transport_data
      M n hn hn2 htb hns hdec)

/-! ## Final strict-`TΦ` source-transport consumers -/

/-! ### Explicit strict-`TΦ` source-transport data

The following four declarations expose the real source-transport data for the
strict `TΦ` target directly. They replace the global semantic-transport seam
above with the concrete Cook-Levin source `P_{M',n} = full_output`, the strict
coupled-sheet target, the same-target identity minor, and the rank bridge
`target ≤ embedded_Q ≤ full_output`.
-/

/-- Exact target-data package for the strict paper-faithful `TΦ` target. -/
noncomputable def routeBPaperFaithfulTPhiTargetData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total) :
    GodMoveExtractionTargetData M n hn2 htb hns hdec :=
  GodMoveExtractionTargetData.ofHardInstanceData hard
    (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total)

/-- The explicit strict-`TΦ` target-data package carries exactly the strict
coupled-sheet extraction target. -/
theorem routeBPaperFaithfulTPhiTargetData_extractionTarget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total) :
    (routeBPaperFaithfulTPhiTargetData
      M n hn2 htb hns hdec hard B_total).extractionTarget =
      routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total := by
  rfl

/-- The concrete Cook-Levin paper source used by strict `TΦ` source transport. -/
noncomputable abbrev routeBPaperFaithfulTPhiPaperSource
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
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
    GlobalGodMoveGauge.Theorem207PaperSource M n hn hn2 htb hns :=
  (DirectRankPackage_cookLevin M n hn htb hns hn2
    B_total hB_total hQ_upper).toTheorem207PaperSource M hn2 htb hns

/-- The direct Cook-Levin P-side bound supplies the paper-source upper bound
for the strict `TΦ` source. -/
theorem routeBPaperFaithfulTPhiPaperSource_p_side_upper
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
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
    GlobalGodMoveGauge.Theorem207PaperSourcePSideUpperBound
      M n hn hn2 htb hns
      (routeBPaperFaithfulTPhiPaperSource
        M n hn hn2 htb hns B_total hB_total hQ_upper) := by
  exact
    (DirectRankPackage_cookLevin M n hn htb hns hn2
      B_total hB_total hQ_upper).toTheorem207PaperSource_p_side
        M hn2 htb hns rfl rfl

/-- The strict `TΦ` target is rank-below the concrete Cook-Levin paper source:
`target ≤ embedded_Q ≤ full_output`. -/
theorem routeBPaperFaithfulTPhi_source_to_target_rank_bridge
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
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
    GlobalGodMoveGauge.Theorem207PaperSourceToTargetRankBridge
      M n hn hn2 htb hns
      (routeBPaperFaithfulTPhiPaperSource
        M n hn hn2 htb hns B_total hB_total hQ_upper)
      (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total) := by
  change
    GlobalGodMoveGauge.Theorem207PaperSourceToTargetRankBridge
      M n hn hn2 htb hns
      ((DirectRankPackage_cookLevin M n hn htb hns hn2
        B_total hB_total hQ_upper).toTheorem207PaperSource M hn2 htb hns)
      (cookLevinStrictFOBTarget M n hn2 htb hns B_total)
  exact
    DirectRankPackage_cookLevin_strictFOB_source_to_target_rank_bridge
      M n hn htb hns hn2 B_total hB_total hQ_upper

/-- Strict `TΦ` source-transport contradiction from the explicit source,
target, same-target minor, P-side bound, and rank bridge.

This is the no-global-seam consumer: every source-transport datum is supplied
by the concrete Cook-Levin direct-rank package and the strict coupled-sheet
target. -/
theorem false_of_routeBPaperFaithfulTPhi_explicit_source_transport
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
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
    False := by
  exact
    false_of_routeBPaperFaithfulTPhi_normalizedCoupledSheet_sourceTransport_sameTargetMinor
      M n hn hn2 htb hns hdec
      (routeBPaperFaithfulTPhiTargetData
        M n hn2 htb hns hdec hard B_total)
      (routeBPaperFaithfulTPhiPaperSource
        M n hn hn2 htb hns B_total hB_total hQ_upper)
      (routeBPaperFaithfulTPhiPaperSource_p_side_upper
        M n hn hn2 htb hns B_total hB_total hQ_upper)
      (by
        simpa [routeBPaperFaithfulTPhiTargetData]
          using
            routeBPaperFaithfulTPhi_source_to_target_rank_bridge
              M n hn hn2 htb hns B_total hB_total hQ_upper)
      (by
        simpa [routeBPaperFaithfulTPhiTargetData]
          using
            routeBPaperFaithfulTPhi_identity_minor_data
              M n hn hn2 htb hns B_total hB_total)

/-- Strict `TΦ` source-transport contradiction from the explicit source and
target data, without packaging the target through hard-instance data.

This is the leanest source-transport consumer: the arithmetic contradiction
only needs the concrete paper source, its P-side bound, the strict target
bridge, and the same-target identity minor. The separate hard-instance
semantic package is only needed by callers that want the older semantic-gap
object. -/
theorem false_of_routeBPaperFaithfulTPhi_explicit_source_transport_target
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
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
  GlobalGodMoveGauge.theorem207PaperSource_transport_false
    M n hn hn2 htb hns
    (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total)
    (routeBPaperFaithfulTPhiPaperSource
      M n hn hn2 htb hns B_total hB_total hQ_upper)
    (routeBPaperFaithfulTPhiPaperSource_p_side_upper
      M n hn hn2 htb hns B_total hB_total hQ_upper)
    (routeBPaperFaithfulTPhi_source_to_target_rank_bridge
      M n hn hn2 htb hns B_total hB_total hQ_upper)
    (routeB_strong_np_from_same_target_identity_minor
      (routeBPaperFaithfulTPhi_identity_minor_data
        M n hn hn2 htb hns B_total hB_total))

/-- Explicit strict-`TΦ` source transport with the landed P-side theorem
supplying the exact `hQ_upper` input.

This keeps the new no-global-seam source-transport route visible while using
the existing Cook-Levin P-side rank theorem to construct the direct-rank
package. -/
theorem false_of_routeBPaperFaithfulTPhi_explicit_source_transport_from_p_side
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    False :=
  false_of_routeBPaperFaithfulTPhi_explicit_source_transport
    M n hn hn2 htb hns hdec hard B_total hB_total
    (cookLevinQ_rank_le_from_p_side_at_B_total
      M n hn htb hns hn2 B_total hB_total)

/-- Hard-instance-free version of
`false_of_routeBPaperFaithfulTPhi_explicit_source_transport_from_p_side`.
This is the exact source-transport contradiction closed by the landed P-side
rank theorem. -/
theorem false_of_routeBPaperFaithfulTPhi_explicit_target_from_p_side
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    False :=
  false_of_routeBPaperFaithfulTPhi_explicit_source_transport_target
    M n hn hn2 htb hns B_total hB_total
    (cookLevinQ_rank_le_from_p_side_at_B_total
      M n hn htb hns hn2 B_total hB_total)

/-- Explicit strict-`TΦ` source transport from the paper-faithful
template-collapse P-side frontier.

This is the honest reduced mathematical input for the no-global-seam route:
prove the concrete Cook-Levin profile template collapse, then the strict
source-transport contradiction follows through the explicit target/source
data above. -/
theorem false_of_routeBPaperFaithfulTPhi_explicit_source_transport_from_templateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_explicit_source_transport
    M n hn hn2 htb hns hdec hard B_total hB_total
    (cookLevinQ_rank_le_from_templateCollapse_at_B_total
      M n hn htb hns hn2 B_total hB_total hcollapse)

/-- Hard-instance-free explicit strict-`TΦ` source transport from
template-collapse. -/
theorem false_of_routeBPaperFaithfulTPhi_explicit_target_from_templateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_explicit_source_transport_target
    M n hn hn2 htb hns B_total hB_total
    (cookLevinQ_rank_le_from_templateCollapse_at_B_total
      M n hn htb hns hn2 B_total hB_total hcollapse)

/-- Canonical explicit strict-`TΦ` source transport from template collapse,
with the extended Cook-Levin partition selected definitionally. -/
theorem false_of_routeBPaperFaithfulTPhi_explicit_canonical_from_templateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_explicit_source_transport_from_templateCollapse
    M n hn hn2 htb hns hdec hard
    (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    rfl hcollapse

/-- Canonical hard-instance-free explicit strict-`TΦ` contradiction from
template collapse. -/
theorem false_of_routeBPaperFaithfulTPhi_explicit_target_canonical_from_templateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_explicit_target_from_templateCollapse
    M n hn hn2 htb hns
    (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    rfl hcollapse

/-- Canonical hard-instance-free explicit strict-`TΦ` contradiction from the
bounded-profile template-collapse frontier. -/
theorem false_of_routeBPaperFaithfulTPhi_explicit_target_canonical_from_boundedProfileTemplateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemmaBoundedProfile
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_explicit_target_canonical_from_templateCollapse
    M n hn hn2 htb hns
    (WithinProfileBound.cookLevinProfileTemplateCollapseLemma_of_boundedProfile
      M n hn2 htb hns hcollapse)

/-- Canonical hard-instance-free explicit strict-`TΦ` contradiction from the
post-span symmetric-product frontier. -/
theorem false_of_routeBPaperFaithfulTPhi_explicit_target_canonical_from_postSpanBoundedBySymProduct
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hpostSpan :
      WithinProfileBound.CookLevinPostSpanBoundedBySymProduct
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_explicit_target_canonical_from_boundedProfileTemplateCollapse
    M n hn hn2 htb hns
    (WithinProfileBound.cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_postSpanBoundedBySymProduct
      M n hn2 htb hns hpostSpan)

/-- Semantic-transport witness for the strict `TΦ` target from explicit
source-transport data and the staged semantic extraction theorem.

This is the older semantic-gap interface with the global existence seam
removed: the target is the strict `TΦ` target, the identity minor is the
same-target strict minor, and the source/P-side/bridge data are all supplied
by `DirectRankPackage_cookLevin`. The only semantic input left is the actual
`GodMoveExtractionTargetTheorem` for this strict target. -/
noncomputable def routeBPaperFaithfulTPhi_semanticTransportWitness
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    (hQ_upper : MultilinearSPDP.mlBlockedSpdpRank
      (MultilinearSPDP.pullbackPartition B_total
        (PaperFaithfulCompilation.cookLevinUVSplit M n).inlU)
      (Nat.log 2 n) (Nat.log 2 n)
      (show MvPolynomial (Fin n) ℚ from
        PaperFaithfulCompilation.cookLevinQ M n hn2 htb hns) ≤ n ^ 200)
    (hsem :
      GodMoveExtractionTargetTheorem M n hn2 htb hns hdec
        (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total)) :
    GlobalGodMoveGauge.Theorem207SemanticTransportWitness
      M n hn hn2 htb hns hdec :=
  GlobalGodMoveGauge.theorem207SemanticTransportWitness_of_target_data
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhiTargetData
      M n hn2 htb hns hdec hard B_total)
    (by
      simpa [routeBPaperFaithfulTPhiTargetData] using hsem)
    (by
      simpa [routeBPaperFaithfulTPhiTargetData]
        using
          routeBPaperFaithfulTPhi_identity_minor_data
            M n hn hn2 htb hns B_total hB_total)
    (routeBPaperFaithfulTPhiPaperSource
      M n hn hn2 htb hns B_total hB_total hQ_upper)
    (routeBPaperFaithfulTPhiPaperSource_p_side_upper
      M n hn hn2 htb hns B_total hB_total hQ_upper)
    (by
      simpa [routeBPaperFaithfulTPhiTargetData]
        using
          routeBPaperFaithfulTPhi_source_to_target_rank_bridge
            M n hn hn2 htb hns B_total hB_total hQ_upper)

/-- The explicit strict-`TΦ` semantic witness closes `False` once the staged
semantic extraction theorem and exact P-side input are supplied. -/
theorem false_of_routeBPaperFaithfulTPhi_semanticTransportWitness
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    (hQ_upper : MultilinearSPDP.mlBlockedSpdpRank
      (MultilinearSPDP.pullbackPartition B_total
        (PaperFaithfulCompilation.cookLevinUVSplit M n).inlU)
      (Nat.log 2 n) (Nat.log 2 n)
      (show MvPolynomial (Fin n) ℚ from
        PaperFaithfulCompilation.cookLevinQ M n hn2 htb hns) ≤ n ^ 200)
    (hsem :
      GodMoveExtractionTargetTheorem M n hn2 htb hns hdec
        (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total)) :
    False :=
  GlobalGodMoveGauge.theorem207SemanticTransportWitness_false
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_semanticTransportWitness
      M n hn hn2 htb hns hdec hard B_total hB_total hQ_upper hsem)

/-- Semantic-witness strict `TΦ` contradiction from template collapse. -/
theorem false_of_routeBPaperFaithfulTPhi_semanticTransportWitness_from_templateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns)
    (hsem :
      GodMoveExtractionTargetTheorem M n hn2 htb hns hdec
        (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total)) :
    False :=
  false_of_routeBPaperFaithfulTPhi_semanticTransportWitness
    M n hn hn2 htb hns hdec hard B_total hB_total
    (cookLevinQ_rank_le_from_templateCollapse_at_B_total
      M n hn htb hns hn2 B_total hB_total hcollapse)
    hsem

/-- Canonical semantic-transport witness for the strict `TΦ` target.

This is the paper-faithful semantic witness: the extraction stage is supplied
by the transported strict `TΦ` partitions, so callers no longer need the
legacy arbitrary-partition `GodMoveExtractionTargetTheorem`. -/
noncomputable def routeBPaperFaithfulTPhi_canonicalSemanticTransportWitness
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
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
    GlobalGodMoveGauge.Theorem207CanonicalSemanticTransportWitness
      M n hn hn2 htb hns hdec :=
  GlobalGodMoveGauge.theorem207CanonicalSemanticTransportWitness_of_target_data
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhiTargetData
      M n hn2 htb hns hdec hard B_total)
    (by
      simpa [routeBPaperFaithfulTPhiTargetData]
        using
          routeBPaperFaithfulTPhi_canonicalSemanticObligation
            M n hn2 htb hns hdec B_total hB_total)
    (by
      simpa [routeBPaperFaithfulTPhiTargetData]
        using
          routeBPaperFaithfulTPhi_identity_minor_data
            M n hn hn2 htb hns B_total hB_total)
    (routeBPaperFaithfulTPhiPaperSource
      M n hn hn2 htb hns B_total hB_total hQ_upper)
    (routeBPaperFaithfulTPhiPaperSource_p_side_upper
      M n hn hn2 htb hns B_total hB_total hQ_upper)
    (by
      simpa [routeBPaperFaithfulTPhiTargetData]
        using
          routeBPaperFaithfulTPhi_source_to_target_rank_bridge
            M n hn hn2 htb hns B_total hB_total hQ_upper)

/-- The canonical strict `TΦ` semantic witness closes `False` once the exact
P-side input is supplied.  Unlike the legacy semantic-witness theorem, this
does not assume the broad arbitrary-partition semantic interface. -/
theorem false_of_routeBPaperFaithfulTPhi_canonicalSemanticTransportWitness
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
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
  GlobalGodMoveGauge.theorem207CanonicalSemanticTransportWitness_false
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_canonicalSemanticTransportWitness
      M n hn hn2 htb hns hdec hard B_total hB_total hQ_upper)

/-- Canonical semantic-witness strict `TΦ` contradiction from template
collapse, using only the transported-partition semantic interface. -/
theorem false_of_routeBPaperFaithfulTPhi_canonicalSemanticTransportWitness_from_templateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_canonicalSemanticTransportWitness
    M n hn hn2 htb hns hdec hard B_total hB_total
    (cookLevinQ_rank_le_from_templateCollapse_at_B_total
      M n hn htb hns hn2 B_total hB_total hcollapse)

/-- Selected canonical semantic-witness strict `TΦ` contradiction from
template collapse. -/
theorem false_of_routeBPaperFaithfulTPhi_canonicalSemanticTransportWitness_canonical_from_templateCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hard : GodMoveHardInstanceData M n hn2 htb hns hdec)
    (hcollapse :
      WithinProfileBound.CookLevinProfileTemplateCollapseLemma
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_canonicalSemanticTransportWitness_from_templateCollapse
    M n hn hn2 htb hns hdec hard
    (routeBPaperFaithfulTPhiCanonicalTotalPartition M n hn2)
    rfl hcollapse

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

/-- Canonical strict-`TΦ` contradiction from the honest per-type spanning
frontier.  This is the narrow Route B P-side proof input exposed by the
profile-normal-form route: a universal per-type spanning theorem supplies the
bounded-profile template collapse, which then feeds the canonical strict
extraction. -/
theorem false_of_routeBPaperFaithfulTPhi_canonical_from_perTypeSpanning_universal
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hSpan_univ : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning_universal) :
    False :=
  false_of_routeBPaperFaithfulTPhi_canonical_from_boundedProfileTemplateCollapse
    M n hn hn2 htb hns hdec
    (cookLevinBoundedProfileTemplateCollapse_of_perTypeSpanning_universal
      hSpan_univ M n hn hn2 htb hns)

/-- Canonical strict-`TΦ` contradiction from the narrow post-span symmetric
product generator obligation.  This is the proof-facing replacement surface for
the legacy `spdp_profile_generators` P-side route: for each bounded derivative
profile, supply one template-bounded finite generating family for the concrete
Cook-Levin post-span. -/
theorem false_of_routeBPaperFaithfulTPhi_canonical_from_postSpanBoundedBySymProduct
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hpostSpan :
      WithinProfileBound.CookLevinPostSpanBoundedBySymProduct
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_canonical_from_boundedProfileTemplateCollapse
    M n hn hn2 htb hns hdec
    (WithinProfileBound.cookLevinProfileTemplateCollapseLemmaBoundedProfile_of_postSpanBoundedBySymProduct
      M n hn2 htb hns hpostSpan)

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

/-! ## Strict-`TΦ` projected/log-window zero-profile hook -/

/-- The strict paper-faithful `TΦ` ambient SAT-gauge map: restrict to the
strict first-of-block coordinates and re-expand by the same coordinate map.

This is intentionally only a `SATDeciderGaugeMap`, not an `NFrame`
`CandidateGauge`: the existing projected final certificate requires a
finite-rank candidate projection, while strict `TΦ` is a coordinate
restriction/relabel map whose range is not packaged as such a finite-row
candidate. -/
noncomputable def routeBPaperFaithfulTPhiAmbientGauge
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeMap M n hn2 htb hns := by
  dsimp [SATDeciderGaugeMap, SATDeciderGaugeSpace]
  rw [PaperFaithfulSeparation.cook_levin_numVars M n hn2 htb hns]
  exact
    ((MvPolynomial.rename (cookLevinStrictFOBFlatMap n) :
        MvPolynomial (Fin (n / 3)) ℚ →ₐ[ℚ]
          MvPolynomial (Fin n) ℚ).toLinearMap).comp
      ((MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) :
          MvPolynomial (Fin n) ℚ →ₐ[ℚ]
            MvPolynomial (Fin (n / 3)) ℚ).toLinearMap)

/-- Minimal strict-`TΦ` projected P-window containment in a selected
zero-profile projected span.

This is the replacement proposition for the head-span-specific row identity:
it speaks directly about the strict `TΦ` ambient gauge map, and does not
mention the broad head-span complement. -/
def RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
    zeroProfileProjectedShiftSpan (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      project

/-- Applying the strict `TΦ` ambient gauge to the Cook-Levin polynomial is
definitionally the flat strict first-of-block restriction followed by
re-expansion along the same coordinate map. -/
theorem routeBPaperFaithfulTPhiAmbientGauge_compiledPoly_eq_reexpandedStrictFOB
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  dsimp [routeBPaperFaithfulTPhiAmbientGauge, SATDeciderGaugeMap,
    SATDeciderGaugeSpace]
  change
    ((MvPolynomial.rename (cookLevinStrictFOBFlatMap n)).toLinearMap)
        (((MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n)).toLinearMap)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) =
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
  rfl

/-- Minimal row identity for the strict `TΦ` projected P-window.

Every strict `TΦ` P-window generator must be the selected quotient projection
of the matching zero-profile shifted base-product row. -/
def RouteBPaperFaithfulTPhiProjectedPWindowZeroProfileRowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
      project
        (mlProj
          (shift *
            Finset.univ.prod
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)))

/-- Compiled/re-expanded form of the strict `TΦ` row identity.

This isolates the remaining algebra after the strict first-of-block
restriction/re-expansion identity and the Cook-Levin factor-list product have
been unfolded. -/
def RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj
        (shift * SPDP.iterDerivList S
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))) =
      project
        (mlProj
          (shift * cookLevinZeroProfileBaseProduct M n hn2 htb hns))

/-- If a differentiated row touches a coordinate outside the strict
first-of-block image, the re-expanded strict-FOB polynomial contributes no
row. -/
theorem routeBPaperFaithfulTPhi_strictFOB_offRangeDerivativeRow_zero
    (n : ℕ)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (p : MvPolynomial (Fin n) ℚ)
    (hoff :
      ∃ v ∈ S, v ∉ Set.range (cookLevinStrictFOBFlatMap n)) :
    mlProj
        (shift * SPDP.iterDerivList S
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n) p))) = 0 := by
  rw [MultilinearSPDP.iterDerivList_rename_zero
    (cookLevinStrictFOBFlatMap n) (cookLevinStrictFOBFlatMap_injective n)
    S hoff]
  simp

/-- Restricting to strict first-of-block coordinates and re-expanding is the
identity on polynomials whose variables are already in the strict-FOB range. -/
theorem routeBPaperFaithfulTPhi_rename_restrictStrictFOB_of_vars_range
    (n : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (hvars : ↑p.vars ⊆ Set.range (cookLevinStrictFOBFlatMap n)) :
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n) p) = p := by
  let f := cookLevinStrictFOBFlatMap n
  let hf := cookLevinStrictFOBFlatMap_injective n
  have heq :
      ((MvPolynomial.rename f).comp
          (MultilinearSPDP.restrictPoly ℚ f hf)) =
        MvPolynomial.aeval
          (fun j : Fin n =>
            if j ∈ Set.range f then
              MvPolynomial.X j
            else
              (0 : MvPolynomial (Fin n) ℚ)) := by
    ext j
    simp only [AlgHom.comp_apply, MultilinearSPDP.restrictPoly_X,
      MvPolynomial.aeval_X]
    by_cases hj : ∃ i, f i = j
    · rw [dif_pos hj, MvPolynomial.rename_X,
        if_pos ⟨hj.choose, hj.choose_spec⟩]
      simp [hj.choose_spec]
    · rw [dif_neg hj, map_zero, if_neg]
      intro h
      exact hj h
  rw [show MvPolynomial.rename f
        (MultilinearSPDP.restrictPoly ℚ f hf p) =
      ((MvPolynomial.rename f).comp
        (MultilinearSPDP.restrictPoly ℚ f hf)) p from rfl, heq]
  exact MvPolynomial.aeval_ite_mem_eq_self p hvars

/-- On rows already written in strict first-of-block coordinates, the
re-expanded strict-FOB derivative row is just the renamed restricted
derivative row. -/
theorem routeBPaperFaithfulTPhi_strictFOB_renamedDerivativeRow
    (n : ℕ)
    (S : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (p : MvPolynomial (Fin n) ℚ) :
    mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          SPDP.iterDerivList (S.map (cookLevinStrictFOBFlatMap n))
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
              (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
                (cookLevinStrictFOBFlatMap_injective n) p))) =
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          (shift *
            MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n)
              (SPDP.iterDerivList
                (S.map (cookLevinStrictFOBFlatMap n)) p))) := by
  rw [MultilinearSPDP.iterDerivList_rename
    (cookLevinStrictFOBFlatMap n) (cookLevinStrictFOBFlatMap_injective n)]
  rw [MultilinearSPDP.iterDerivList_restrictPoly
    ℚ (cookLevinStrictFOBFlatMap n) (cookLevinStrictFOBFlatMap_injective n)]
  rw [← map_mul (MvPolynomial.rename (cookLevinStrictFOBFlatMap n))]
  rw [MultilinearSPDP.mlProj_rename
    (cookLevinStrictFOBFlatMap n) (cookLevinStrictFOBFlatMap_injective n)]

/-- Source-coordinate form of the strict first-of-block derivative row
reduction.  This is the all-range row identity before rewriting the source
derivative through `restrictPoly`. -/
theorem routeBPaperFaithfulTPhi_strictFOB_renamedDerivativeRow_restrict
    (n : ℕ)
    (S : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (p : MvPolynomial (Fin n) ℚ) :
    mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          SPDP.iterDerivList (S.map (cookLevinStrictFOBFlatMap n))
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
              (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
                (cookLevinStrictFOBFlatMap_injective n) p))) =
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          (shift *
            SPDP.iterDerivList S
              (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
                (cookLevinStrictFOBFlatMap_injective n) p))) := by
  rw [MultilinearSPDP.iterDerivList_rename
    (cookLevinStrictFOBFlatMap n) (cookLevinStrictFOBFlatMap_injective n)]
  rw [← map_mul (MvPolynomial.rename (cookLevinStrictFOBFlatMap n))]
  rw [MultilinearSPDP.mlProj_rename
    (cookLevinStrictFOBFlatMap n) (cookLevinStrictFOBFlatMap_injective n)]

/-- The concrete strict-`TΦ` ambient row for an all-range derivative list is
the renamed source-coordinate derivative row of the restricted Cook-Levin
polynomial. -/
theorem routeBPaperFaithfulTPhi_rangePWindowRow_eq_renamedRestrictedRow
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ) :
    mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          SPDP.iterDerivList (S.map (cookLevinStrictFOBFlatMap n))
            ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          (shift *
            SPDP.iterDerivList S
              (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
                (cookLevinStrictFOBFlatMap_injective n)
                (compiledPoly
                  (cook_levin_compilation M n hn2 htb hns))))) := by
  rw [routeBPaperFaithfulTPhiAmbientGauge_compiledPoly_eq_reexpandedStrictFOB
    M n hn2 htb hns]
  exact
    routeBPaperFaithfulTPhi_strictFOB_renamedDerivativeRow_restrict
      n S shift
      (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- If the derivative list is the strict-FOB image of a source list and the
ambient shift uses only strict-FOB variables, the strict row reduces to a
renamed restricted derivative row. -/
theorem routeBPaperFaithfulTPhi_strictFOB_allRangeDerivativeRow
    (n : ℕ)
    (S : List (Fin n)) (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin n) ℚ)
    (p : MvPolynomial (Fin n) ℚ)
    (hS : S'.map (cookLevinStrictFOBFlatMap n) = S)
    (hshiftRange :
      ↑shift.vars ⊆ Set.range (cookLevinStrictFOBFlatMap n)) :
    mlProj
        (shift * SPDP.iterDerivList S
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n) p))) =
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n) shift *
            MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n)
              (SPDP.iterDerivList S p))) := by
  subst S
  let shift' :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) shift
  have hshift :
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift' = shift := by
    simpa [shift'] using
      routeBPaperFaithfulTPhi_rename_restrictStrictFOB_of_vars_range
        n shift hshiftRange
  calc
    mlProj
        (shift * SPDP.iterDerivList
          (S'.map (cookLevinStrictFOBFlatMap n))
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n) p))) =
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift' *
          SPDP.iterDerivList
            (S'.map (cookLevinStrictFOBFlatMap n))
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
              (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
                (cookLevinStrictFOBFlatMap_injective n) p))) := by
        rw [hshift]
    _ =
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj
        (shift' *
          MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
            (cookLevinStrictFOBFlatMap_injective n)
            (SPDP.iterDerivList
              (S'.map (cookLevinStrictFOBFlatMap n)) p))) :=
        routeBPaperFaithfulTPhi_strictFOB_renamedDerivativeRow
          n S' shift' p

/-- Singleton-shift zero-profile rows are exactly the part killed by the
concrete singleton quotient.  Thus the off-range strict-FOB zero row matches
the concrete RHS when the shift is the offending singleton variable itself. -/
theorem routeBPaperFaithfulTPhi_strictFOB_offRangeSingletonShiftRow_singletonQuotient
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (v : Fin n)
    (hvS : v ∈ S)
    (hoffv : v ∉ Set.range (cookLevinStrictFOBFlatMap n)) :
    mlProj
        (MvPolynomial.X v * SPDP.iterDerivList S
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))) =
      zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (mlProj
          (MvPolynomial.X v * cookLevinZeroProfileBaseProduct M n hn2 htb hns)) := by
  have hlhs :
      mlProj
          (MvPolynomial.X v * SPDP.iterDerivList S
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
              (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
                (cookLevinStrictFOBFlatMap_injective n)
                (compiledPoly (cook_levin_compilation M n hn2 htb hns))))) =
        0 := by
    exact
      routeBPaperFaithfulTPhi_strictFOB_offRangeDerivativeRow_zero
        n S (MvPolynomial.X v)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))
        ⟨v, hvS, hoffv⟩
  have hrhs :
      zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (mlProj
          (MvPolynomial.X v * cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
        0 := by
    simpa [cookLevinZeroProfileBaseProduct] using
      zeroProfileQuotientBySingletonShiftProjection_killsSingletonShifts
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) v
  rw [hlhs, hrhs]

/-- In the all-range case, strict-FOB derivative erasure for the concrete
singleton quotient is exactly the projected zero-profile equality displayed
on the right.  This is the remaining RHS algebra after the strict-FOB reducer
has rewritten the LHS. -/
theorem routeBPaperFaithfulTPhi_strictFOB_allRangeDerivativeRow_singletonQuotient_iff_projected
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin n) ℚ)
    (hS : S'.map (cookLevinStrictFOBFlatMap n) = S)
    (hshiftRange :
      ↑shift.vars ⊆ Set.range (cookLevinStrictFOBFlatMap n)) :
    (mlProj
        (shift * SPDP.iterDerivList S
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))) =
      zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (mlProj
          (shift * cookLevinZeroProfileBaseProduct M n hn2 htb hns))) ↔
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n) shift *
            MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n)
              (SPDP.iterDerivList S
                (compiledPoly (cook_levin_compilation M n hn2 htb hns))))) =
      zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (mlProj
          (shift * cookLevinZeroProfileBaseProduct M n hn2 htb hns)) := by
  rw [routeBPaperFaithfulTPhi_strictFOB_allRangeDerivativeRow
    n S S' shift
    (compiledPoly (cook_levin_compilation M n hn2 htb hns))
    hS hshiftRange]

/-- Elements of the singleton-shift subspace have zero constant coefficient. -/
theorem routeBPaperFaithfulTPhi_zeroProfileSingletonShiftSubspace_coeff_zero
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    {q : MvPolynomial (Fin n) ℚ}
    (hq : q ∈ zeroProfileSingletonShiftSubspace factors) :
    MvPolynomial.coeff (0 : Fin n →₀ ℕ) q = 0 := by
  classical
  unfold zeroProfileSingletonShiftSubspace at hq
  refine Submodule.span_induction
    (p := fun q : MvPolynomial (Fin n) ℚ => fun _ =>
      MvPolynomial.coeff (0 : Fin n →₀ ℕ) q = 0) ?_ ?_ ?_ ?_ hq
  · intro row hrow
    rcases hrow with ⟨i, rfl⟩
    rw [MultilinearSPDP.coeff_mlProj_of_isMultilinear_mono _ _
      (by intro j; simp)]
    rw [MvPolynomial.coeff_X_mul']
    simp
  · simp
  · intro p q hp hq hp0 hq0
    rw [MvPolynomial.coeff_add, hp0, hq0]
    simp
  · intro a p hp hp0
    rw [MvPolynomial.coeff_smul, hp0]
    simp

/-- The concrete singleton quotient projection is zero exactly on the chosen
singleton-shift subspace. -/
theorem routeBPaperFaithfulTPhi_zeroProfileQuotientBySingletonShiftProjection_apply_eq_zero_iff
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (q : MvPolynomial (Fin n) ℚ) :
    zeroProfileQuotientBySingletonShiftProjection factors q = 0 ↔
      q ∈ zeroProfileSingletonShiftSubspace factors := by
  rw [zeroProfileQuotientBySingletonShiftProjection]
  exact
    Submodule.IsCompl.projection_apply_eq_zero_iff
      (zeroProfileSingletonShiftSubspace_isCompl_complement factors).symm

/-- The concrete singleton quotient does not kill the zero-profile base row:
the base row has constant coefficient `1`, while the projection kernel is the
singleton-shift subspace, whose elements have zero constant coefficient. -/
theorem routeBPaperFaithfulTPhi_singletonQuotientProjection_baseRow_ne_zero
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      (mlProj (cookLevinZeroProfileBaseProduct M n hn2 htb hns)) ≠ 0 := by
  intro hzero
  have hmem :
      mlProj (cookLevinZeroProfileBaseProduct M n hn2 htb hns) ∈
        zeroProfileSingletonShiftSubspace
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) :=
    (routeBPaperFaithfulTPhi_zeroProfileQuotientBySingletonShiftProjection_apply_eq_zero_iff
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      (mlProj (cookLevinZeroProfileBaseProduct M n hn2 htb hns))).mp hzero
  have hcoeff_zero :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (mlProj (cookLevinZeroProfileBaseProduct M n hn2 htb hns)) = 0 :=
    routeBPaperFaithfulTPhi_zeroProfileSingletonShiftSubspace_coeff_zero
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i) hmem
  have hcoeff_one :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (mlProj (cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
        (1 : ℚ) := by
    rw [MultilinearSPDP.coeff_mlProj_of_isMultilinear_mono _ _
      (by intro j; simp)]
    exact cookLevinZeroProfileBaseProduct_coeff_zero M n hn2 htb hns
  norm_num [hcoeff_one] at hcoeff_zero

/-- If strict-FOB derivative erasure held for the concrete singleton quotient,
then every off-range row would force the projected zero-profile RHS row to be
zero.  This is the exact extra projection property demanded by the off-range
split. -/
theorem routeBPaperFaithfulTPhi_strictFOB_offRangeRow_forces_singletonQuotient_zero
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (herase :
      RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)))
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (hSlen : S.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars : shift.vars ⊆ S.toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S)
    (hoff :
      ∃ v ∈ S, v ∉ Set.range (cookLevinStrictFOBFlatMap n)) :
    zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      (mlProj
        (shift * cookLevinZeroProfileBaseProduct M n hn2 htb hns)) = 0 := by
  have hrow :=
    herase S shift hSlen hshiftDegree hshiftVars hadm
  have hlhs :
      mlProj
          (shift * SPDP.iterDerivList S
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
              (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
                (cookLevinStrictFOBFlatMap_injective n)
                (compiledPoly (cook_levin_compilation M n hn2 htb hns))))) =
        0 :=
    routeBPaperFaithfulTPhi_strictFOB_offRangeDerivativeRow_zero
      n S shift
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) hoff
  rw [hlhs] at hrow
  exact hrow.symm

/-- Consequently, any off-range admissible derivative list rules out the full
strict-FOB derivative-erasure statement for the concrete singleton quotient:
using `shift = 1` would force the concrete quotient to kill the zero-profile
base row, but the base-row lemma above proves it does not. -/
theorem routeBPaperFaithfulTPhi_strictFOB_singletonQuotient_offRangeConstantRow_noGo
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n))
    (hSlen : S.length = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S)
    (hoff :
      ∃ v ∈ S, v ∉ Set.range (cookLevinStrictFOBFlatMap n)) :
    ¬ RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) := by
  intro herase
  have hzero :
      zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (mlProj
          ((1 : MvPolynomial (Fin n) ℚ) *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns)) = 0 :=
    routeBPaperFaithfulTPhi_strictFOB_offRangeRow_forces_singletonQuotient_zero
      M n hn2 htb hns herase S (1 : MvPolynomial (Fin n) ℚ)
      hSlen (by simp) (by simp) hadm hoff
  have hbase_zero :
      zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (mlProj (cookLevinZeroProfileBaseProduct M n hn2 htb hns)) = 0 := by
    simpa using hzero
  exact
    routeBPaperFaithfulTPhi_singletonQuotientProjection_baseRow_ne_zero
      M n hn2 htb hns hbase_zero

/-! ## Range-only strict-FOB projected target -/

/-- Corrected strict-`TΦ` range-only projected P-window subspace.

The failed full target quantified over every ambient derivative list.  This
range-only target keeps only rows whose derivative list is explicitly the
strict first-of-block image of a source list, so the off-range zero-row
obstruction is not present in the query surface. -/
noncomputable def routeBPaperFaithfulTPhiRangePWindowSubspace
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    { q : MvPolynomial (Fin n) ℚ |
      ∃ (S' : List (Fin (n / 3)))
        (shift : MvPolynomial (Fin (n / 3)) ℚ),
        S'.length = Nat.log 2 n ∧
        shift.totalDegree ≤ Nat.log 2 n ∧
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)) ∧
        q =
          mlProj
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
              SPDP.iterDerivList (S'.map (cookLevinStrictFOBFlatMap n))
                ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
                  (compiledPoly
                    (cook_levin_compilation M n hn2 htb hns)))) }

/-- Budgeted common-span target for the corrected range-only strict `TΦ`
P-window subspace.

This is the paper-faithful granularity: after canonical/profile compression we
only need the whole row family to lie in a bounded subspace, not a pointwise
coefficient identity for every multi-tag probe. -/
def RouteBPaperFaithfulTPhiRangePWindowCommonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (budget : ℕ) : Prop :=
  ∃ G : Finset (MvPolynomial (Fin n) ℚ),
    G.card ≤ budget ∧
    routeBPaperFaithfulTPhiRangePWindowSubspace M n hn2 htb hns ≤
      Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))

/-- Profile/local-normal-form containment for the corrected range-only strict
`TΦ` P-window subspace.

The alphabet `A` is the finite interface/profile normal-form alphabet from the
paper.  Proving this containment is the replacement for the refuted pointwise
coefficient-balance route: every canonicalized strict `TΦ` row is classified by
bounded profile/interface data and lands in the corresponding compressed
profile span. -/
def RouteBPaperFaithfulTPhiRangePWindowControlledByProfileSubspace
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n)) : Prop :=
  routeBPaperFaithfulTPhiRangePWindowSubspace M n hn2 htb hns ≤
    zeroProfileLocalTypeCompressedProfileSpan A

/-- Generator-by-generator form of the strict `TΦ` profile-subspace
containment.  This is the proof shape suggested by the paper: canonicalize the
window, read off its bounded profile/interface type, and show the resulting
row lies in the corresponding compressed profile span. -/
def RouteBPaperFaithfulTPhiRangePWindowProfileGeneratorReduction
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n)) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          SPDP.iterDerivList (S'.map (cookLevinStrictFOBFlatMap n))
            ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      zeroProfileLocalTypeCompressedProfileSpan A

/-- The profile-subspace containment is exactly its generator-membership form
for the range-only strict `TΦ` subspace. -/
theorem routeBPaperFaithfulTPhi_rangePWindowControlledByProfileSubspace_iff_generatorReduction
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n)) :
    RouteBPaperFaithfulTPhiRangePWindowControlledByProfileSubspace
        M n hn2 htb hns A ↔
      RouteBPaperFaithfulTPhiRangePWindowProfileGeneratorReduction
        M n hn2 htb hns A := by
  classical
  constructor
  · intro hcontrol S' shift hSlen hshiftDegree hshiftVars hadm
    apply hcontrol
    unfold routeBPaperFaithfulTPhiRangePWindowSubspace
    exact Submodule.subset_span
      ⟨S', shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  · intro hgen
    unfold RouteBPaperFaithfulTPhiRangePWindowControlledByProfileSubspace
    unfold routeBPaperFaithfulTPhiRangePWindowSubspace
    refine Submodule.span_le.mpr ?_
    intro q hq
    rcases hq with
      ⟨S', shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
    exact hgen S' shift hSlen hshiftDegree hshiftVars hadm

/-- A profile-subspace containment immediately gives the paper-scale bounded
common-span form, using the finite local normal-form basis supplied by the
alphabet. -/
theorem routeBPaperFaithfulTPhi_rangePWindowCommonSpanWithBudget_of_profileSubspace
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n))
    (hprofile :
      RouteBPaperFaithfulTPhiRangePWindowControlledByProfileSubspace
        M n hn2 htb hns A) :
    RouteBPaperFaithfulTPhiRangePWindowCommonSpanWithBudget
      M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) := by
  classical
  refine ⟨zeroProfileLocalTypeGlobalBasis A,
    zeroProfileLocalTypeGlobalBasis_card_le_withinProfileBound A, ?_⟩
  simpa [RouteBPaperFaithfulTPhiRangePWindowControlledByProfileSubspace,
    zeroProfileLocalTypeCompressedProfileSpan] using hprofile

/-- Paper-faithful strict `TΦ` profile/subspace frontier.

This is the corrected target after the pointwise coefficient-balance no-go
lemmas: provide a finite local normal-form alphabet and prove the range-only
strict `TΦ` P-window rows land in its compressed profile subspace. -/
def RouteBPaperFaithfulTPhiStrictProfileSubspaceContainment
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ A : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n),
    RouteBPaperFaithfulTPhiRangePWindowControlledByProfileSubspace
      M n hn2 htb hns A

/-- Concrete finite local alphabet/classifier for strict `TΦ` range-window
rows.

This is the proof object the paper asks for after canonical/profile
compression: assign every admissible strict `TΦ` row to a bounded local type and
prove the row lies in that type's finite-dimensional span.  Supplying an
inhabitant of this structure proves the abstract
`RouteBPaperFaithfulTPhiStrictProfileSubspaceContainment` frontier. -/
structure RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  alphabet : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n)
  rowType :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ),
      S'.length = Nat.log 2 n →
      shift.totalDegree ≤ Nat.log 2 n →
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)) →
      alphabet.type
  row_mem_typeSpace :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n))),
      mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            SPDP.iterDerivList (S'.map (cookLevinStrictFOBFlatMap n))
              ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
        zeroProfileLocalTypeSpace alphabet
          (rowType S' shift hSlen hshiftDegree hshiftVars hadm)

/-- A strict finite local classifier proves the profile-subspace containment
for its alphabet. -/
theorem routeBPaperFaithfulTPhi_rangePWindowControlledByProfileSubspace_of_classifier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C :
      RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifier
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowControlledByProfileSubspace
      M n hn2 htb hns C.alphabet := by
  classical
  exact
    (routeBPaperFaithfulTPhi_rangePWindowControlledByProfileSubspace_iff_generatorReduction
      M n hn2 htb hns C.alphabet).mpr
      (fun S' shift hSlen hshiftDegree hshiftVars hadm =>
        (zeroProfileLocalTypeSpace_le_compressedProfileSpan C.alphabet
          (C.rowType S' shift hSlen hshiftDegree hshiftVars hadm))
          (C.row_mem_typeSpace S' shift hSlen hshiftDegree hshiftVars hadm))

/-- The concrete finite local classifier is exactly enough to inhabit the
strict profile/subspace frontier. -/
theorem routeBPaperFaithfulTPhi_strictProfileSubspaceContainment_of_classifier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C :
      RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifier
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictProfileSubspaceContainment
      M n hn2 htb hns :=
  ⟨C.alphabet,
    routeBPaperFaithfulTPhi_rangePWindowControlledByProfileSubspace_of_classifier
      M n hn2 htb hns C⟩

/-- Classifier-obligation form of the remaining paper-faithful strict `TΦ`
frontier. -/
def RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  Nonempty
    (RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifier
      M n hn2 htb hns)

/-- Classifier-obligation bridge to the abstract profile/subspace frontier. -/
theorem routeBPaperFaithfulTPhi_strictProfileSubspaceContainment_of_classifierObligation
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hclassifier :
      RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictProfileSubspaceContainment
      M n hn2 htb hns := by
  rcases hclassifier with ⟨C⟩
  exact
    routeBPaperFaithfulTPhi_strictProfileSubspaceContainment_of_classifier
      M n hn2 htb hns C

/-- A bounded common span can be packaged as a one-type strict `TΦ` local
classifier.  This is the reverse packaging direction: once the row family has
been compressed into a finite span of size `withinProfileBound`, it supplies a
finite local alphabet/classifier automatically. -/
noncomputable def routeBPaperFaithfulTPhi_strictProfileSubspaceClassifier_of_commonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcommon :
      RouteBPaperFaithfulTPhiRangePWindowCommonSpanWithBudget
        M n hn2 htb hns (withinProfileBound (Nat.log 2 n))) :
    RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifier
      M n hn2 htb hns := by
  classical
  let G : Finset (MvPolynomial (Fin n) ℚ) := Classical.choose hcommon
  have hspec := Classical.choose_spec hcommon
  let hG_card : G.card ≤ withinProfileBound (Nat.log 2 n) := hspec.1
  let hG_span : routeBPaperFaithfulTPhiRangePWindowSubspace M n hn2 htb hns ≤
      Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) := hspec.2
  refine
    { alphabet :=
        { type := PUnit
          typeFintype := inferInstance
          localDim := withinProfileBound (Nat.log 2 n)
          localBasis := fun _ => G
          localBasis_card_le := fun _ => hG_card
          profileSymmetricPowerBudget_le := by simp }
      rowType := ?_
      row_mem_typeSpace := ?_ }
  · intro S' shift hSlen hshiftDegree hshiftVars hadm
    exact PUnit.unit
  · intro S' shift hSlen hshiftDegree hshiftVars hadm
    apply hG_span
    unfold routeBPaperFaithfulTPhiRangePWindowSubspace
    exact Submodule.subset_span
      ⟨S', shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩

/-- Bounded common-span form gives the classifier-obligation form. -/
theorem routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_commonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcommon :
      RouteBPaperFaithfulTPhiRangePWindowCommonSpanWithBudget
        M n hn2 htb hns (withinProfileBound (Nat.log 2 n))) :
    RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
      M n hn2 htb hns :=
  ⟨routeBPaperFaithfulTPhi_strictProfileSubspaceClassifier_of_commonSpanWithBudget
      M n hn2 htb hns hcommon⟩

/-- The strict profile/subspace frontier is enough to produce the bounded
common-span package consumed by the dimension/rank assembly. -/
theorem routeBPaperFaithfulTPhi_rangePWindowCommonSpanWithBudget_of_strictProfileSubspaceContainment
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcontain :
      RouteBPaperFaithfulTPhiStrictProfileSubspaceContainment
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowCommonSpanWithBudget
      M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) := by
  rcases hcontain with ⟨A, hprofile⟩
  exact
    routeBPaperFaithfulTPhi_rangePWindowCommonSpanWithBudget_of_profileSubspace
      M n hn2 htb hns A hprofile

/-- The strict classifier obligation and the bounded common-span package are
equivalent frontiers.  The forward direction uses the classifier's finite
alphabet basis; the reverse direction packages any bounded span as a one-type
classifier. -/
theorem routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_iff_commonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
        M n hn2 htb hns ↔
      RouteBPaperFaithfulTPhiRangePWindowCommonSpanWithBudget
        M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) := by
  constructor
  · intro hclassifier
    exact
      routeBPaperFaithfulTPhi_rangePWindowCommonSpanWithBudget_of_strictProfileSubspaceContainment
        M n hn2 htb hns
        (routeBPaperFaithfulTPhi_strictProfileSubspaceContainment_of_classifierObligation
          M n hn2 htb hns hclassifier)
  · intro hcommon
    exact
      routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_commonSpanWithBudget
        M n hn2 htb hns hcommon

/-- Range-only strict-`TΦ` containment in a selected projected zero-profile
span. -/
def RouteBPaperFaithfulTPhiRangePWindowControlledByZeroProfileProjection
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  routeBPaperFaithfulTPhiRangePWindowSubspace M n hn2 htb hns ≤
    zeroProfileProjectedShiftSpan (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      project

/-- Pointwise row identity for the corrected range-only strict-`TΦ` target. -/
def RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          SPDP.iterDerivList (S'.map (cookLevinStrictFOBFlatMap n))
            ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
      project
        (mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns))

/-- Generator-membership form for the corrected range-only strict-`TΦ`
target. -/
def RouteBPaperFaithfulTPhiRangePWindowZeroProfileGeneratorReduction
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          SPDP.iterDerivList (S'.map (cookLevinStrictFOBFlatMap n))
            ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      zeroProfileProjectedShiftSpan (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project

/-- The range-only pointwise row identity gives generator membership in the
selected projected zero-profile span. -/
theorem routeBPaperFaithfulTPhi_rangePWindowGenerator_mem_zeroProfileProjection
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
        M n hn2 htb hns project)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (hSlen : S'.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n))) :
    mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          SPDP.iterDerivList (S'.map (cookLevinStrictFOBFlatMap n))
            ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      zeroProfileProjectedShiftSpan (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project := by
  classical
  have hzero :
      mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            Finset.univ.prod
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) ∈
        zeroProfileShiftImageSet (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) := by
    simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
      Set.mem_singleton_iff]
    exact
      ⟨S'.map (cookLevinStrictFOBFlatMap n),
        by simpa [List.length_map] using le_of_eq hSlen,
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift,
        hshiftVars, rfl⟩
  have hproject :
      project
          (mlProj
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
              Finset.univ.prod
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) ∈
        zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          project := by
    exact Submodule.mem_map_of_mem (Submodule.subset_span hzero)
  rw [hrow S' shift hSlen hshiftDegree hshiftVars hadm]
  simpa [cookLevinZeroProfileBaseProduct] using hproject

/-- The range-only strict `TΦ` containment is exactly the corresponding
generator-by-generator zero-profile membership check. -/
theorem routeBPaperFaithfulTPhi_rangePWindowControlledByZeroProfileProjection_iff_generatorReduction
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) :
    RouteBPaperFaithfulTPhiRangePWindowControlledByZeroProfileProjection
        M n hn2 htb hns project ↔
      RouteBPaperFaithfulTPhiRangePWindowZeroProfileGeneratorReduction
        M n hn2 htb hns project := by
  classical
  constructor
  · intro hcontrol S' shift hSlen hshiftDegree hshiftVars hadm
    apply hcontrol
    unfold routeBPaperFaithfulTPhiRangePWindowSubspace
    exact Submodule.subset_span
      ⟨S', shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  · intro hgen
    unfold RouteBPaperFaithfulTPhiRangePWindowControlledByZeroProfileProjection
    unfold routeBPaperFaithfulTPhiRangePWindowSubspace
    refine Submodule.span_le.mpr ?_
    intro q hq
    rcases hq with
      ⟨S', shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
    exact hgen S' shift hSlen hshiftDegree hshiftVars hadm

/-- The pointwise range-only strict `TΦ` row identity proves the corrected
range-only projected P-window containment. -/
theorem routeBPaperFaithfulTPhi_rangePWindowControlledByZeroProfileProjection_of_rowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
        M n hn2 htb hns project) :
    RouteBPaperFaithfulTPhiRangePWindowControlledByZeroProfileProjection
      M n hn2 htb hns project :=
  (routeBPaperFaithfulTPhi_rangePWindowControlledByZeroProfileProjection_iff_generatorReduction
    M n hn2 htb hns project).mpr
    (fun S' shift hSlen hshiftDegree hshiftVars hadm =>
      routeBPaperFaithfulTPhi_rangePWindowGenerator_mem_zeroProfileProjection
        M n hn2 htb hns project hrow S' shift
        hSlen hshiftDegree hshiftVars hadm)

/-- A Cook-Levin finite local type normal-form map, together with the strict
range row identity at the identity projection, constructs the actual strict
`TΦ` profile-subspace classifier.

This is the row-level local-monoid/profile instantiation: the classifier's type
for a strict source-coordinate row is the local type assigned by the
zero-profile generator type map to the corresponding embedded row.  The row
identity transports the strict derivative row into exactly that selected local
type space. -/
noncomputable def routeBPaperFaithfulTPhi_strictProfileSubspaceClassifier_of_localTypeNormalForm_rowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hlocal :
      CookLevinZeroProfileLocalTypeNormalFormObligation M n hn2 htb hns)
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
        M n hn2 htb hns
        (LinearMap.id :
          MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)) :
      RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifier
      M n hn2 htb hns := by
  classical
  let A : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n) :=
    Classical.choose hlocal
  let hmap : ZeroProfileGeneratorTypeMap (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i) A :=
    Classical.choice (Classical.choose_spec hlocal)
  refine
    { alphabet := A
      rowType := ?_
      row_mem_typeSpace := ?_ }
  · intro S' shift hSlen hshiftDegree hshiftVars hadm
    exact hmap.rowType
      (S'.map (cookLevinStrictFOBFlatMap n))
      (by simpa [List.length_map] using le_of_eq hSlen)
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift)
      hshiftVars
  · intro S' shift hSlen hshiftDegree hshiftVars hadm
    have hbase :
        mlProj
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
              Finset.univ.prod
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) ∈
          zeroProfileLocalTypeSpace A
            (hmap.rowType
              (S'.map (cookLevinStrictFOBFlatMap n))
              (by simpa [List.length_map] using le_of_eq hSlen)
              (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift)
              hshiftVars) :=
      hmap.row_mem_typeSpace
        (S'.map (cookLevinStrictFOBFlatMap n))
        (by simpa [List.length_map] using le_of_eq hSlen)
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift)
        hshiftVars
    rw [hrow S' shift hSlen hshiftDegree hshiftVars hadm]
    simpa [cookLevinZeroProfileBaseProduct] using hbase

/-- Obligation form of the local-monoid/profile classifier constructor. -/
theorem routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_localTypeNormalForm_rowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hlocal :
      CookLevinZeroProfileLocalTypeNormalFormObligation M n hn2 htb hns)
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
        M n hn2 htb hns
        (LinearMap.id :
          MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)) :
    RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
      M n hn2 htb hns :=
  ⟨routeBPaperFaithfulTPhi_strictProfileSubspaceClassifier_of_localTypeNormalForm_rowIdentity
    M n hn2 htb hns hlocal hrow⟩

/-- A projected zero-profile common span gives the corrected range-only strict
`TΦ` bounded common span as soon as the range P-window rows have been shown to
land in that projected span.

This is the non-pointwise close-out for the strict range surface: the finite
generators are the projected zero-profile generators, and the only algebraic
input is the containment of strict `TΦ` rows in that projected zero-profile
subspace. -/
theorem routeBPaperFaithfulTPhi_rangePWindowCommonSpanWithBudget_of_zeroProfileProjectedCommonSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project (withinProfileBound (Nat.log 2 n)))
    (hcontrol :
      RouteBPaperFaithfulTPhiRangePWindowControlledByZeroProfileProjection
        M n hn2 htb hns project) :
    RouteBPaperFaithfulTPhiRangePWindowCommonSpanWithBudget
      M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) := by
  classical
  rcases hspan with ⟨G, hG_card, hG_span⟩
  refine ⟨G, hG_card, ?_⟩
  intro q hq
  have hzero :
      q ∈ zeroProfileProjectedShiftSpan (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project :=
    hcontrol hq
  have hzero_le :
      zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          project ≤
        Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) := by
    rw [zeroProfileProjectedShiftSpan_eq_span_projectedShiftImageSet]
    exact Submodule.span_le.mpr hG_span
  exact hzero_le hzero

/-- Pointwise strict range-row identity plus a projected zero-profile common
span closes the corrected range-only bounded common-span target.

The theorem deliberately separates the two ingredients: the finite projected
profile basis is supplied by `hspan`; the row algebra is exactly the selected
strict `TΦ` row identity, not a refuted broad coefficient-balance claim. -/
theorem routeBPaperFaithfulTPhi_rangePWindowCommonSpanWithBudget_of_rowIdentity_projectedCommonSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project (withinProfileBound (Nat.log 2 n)))
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
        M n hn2 htb hns project) :
    RouteBPaperFaithfulTPhiRangePWindowCommonSpanWithBudget
      M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) :=
  routeBPaperFaithfulTPhi_rangePWindowCommonSpanWithBudget_of_zeroProfileProjectedCommonSpan
    M n hn2 htb hns project hspan
    (routeBPaperFaithfulTPhi_rangePWindowControlledByZeroProfileProjection_of_rowIdentity
      M n hn2 htb hns project hrow)

/-- Smaller source-coordinate equality left after the all-range strict-FOB
row reduction.  The derivative list is over `Fin (n / 3)`; no off-range
ambient derivative rows are queried. -/
def RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          (shift *
            SPDP.iterDerivList S'
              (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
                (cookLevinStrictFOBFlatMap_injective n)
                (compiledPoly
                  (cook_levin_compilation M n hn2 htb hns))))) =
      project
        (mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns))

/-- Exact residual-balance form of the range-only restricted row gate.

After subtracting the undifferentiated strict-restricted row, the remaining
equality is precisely: the strict source-coordinate derivative residual equals
the gap between the selected projected zero-profile base row and the
re-expanded strict-restricted base row. -/
def RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          (shift * (SPDP.iterDerivList S' r - r))) =
      project
          (mlProj
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns)) -
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * r))

private theorem routeBPaperFaithfulTPhi_restrictedResidual_split
    (n : ℕ)
    (S' : List (Fin (n / 3)))
    (shift r : MvPolynomial (Fin (n / 3)) ℚ) :
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          (shift * (SPDP.iterDerivList S' r - r))) =
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * SPDP.iterDerivList S' r)) -
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * r)) := by
  have hsrc :
      mlProj (shift * (SPDP.iterDerivList S' r - r)) =
        mlProj (shift * SPDP.iterDerivList S' r) -
          mlProj (shift * r) := by
    rw [mul_sub]
    change (MultilinearSPDP.mlProjHom ℚ)
        (shift * SPDP.iterDerivList S' r - shift * r) =
      (MultilinearSPDP.mlProjHom ℚ)
          (shift * SPDP.iterDerivList S' r) -
        (MultilinearSPDP.mlProjHom ℚ) (shift * r)
    rw [map_sub]
  rw [hsrc, map_sub]

/-- The restricted row identity is equivalent to the residual-balance equality
above.  This is the exact remaining algebra for the range-only strict-`TΦ`
projected/log-window target. -/
theorem routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_iff_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns project ↔
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns project := by
  constructor
  · intro hrow S' shift hSlen hshiftDegree hshiftVars hadm
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    have hsplit :=
      routeBPaperFaithfulTPhi_restrictedResidual_split n S' shift r
    have hrow' :
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (mlProj (shift * SPDP.iterDerivList S' r)) =
          project
            (mlProj
              (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
                cookLevinZeroProfileBaseProduct M n hn2 htb hns)) := by
      simpa [p, r] using
        hrow S' shift hSlen hshiftDegree hshiftVars hadm
    calc
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * (SPDP.iterDerivList S' r - r))) =
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (mlProj (shift * SPDP.iterDerivList S' r)) -
          MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (mlProj (shift * r)) := hsplit
      _ =
        project
            (mlProj
              (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
                cookLevinZeroProfileBaseProduct M n hn2 htb hns)) -
          MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (mlProj (shift * r)) := by
          rw [hrow']
  · intro hres S' shift hSlen hshiftDegree hshiftVars hadm
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    have hsplit :=
      routeBPaperFaithfulTPhi_restrictedResidual_split n S' shift r
    have hbal := hres S' shift hSlen hshiftDegree hshiftVars hadm
    change
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * SPDP.iterDerivList S' r)) =
        project
          (mlProj
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns))
    dsimp only [p, r] at hbal
    rw [hsplit] at hbal
    have hcancel := congrArg
      (fun q : MvPolynomial (Fin n) ℚ =>
        q + MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * r))) hbal
    simpa [p, r, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      hcancel

/-- Forward-use form of the residual-balance reduction. -/
theorem routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_of_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns project) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
      M n hn2 htb hns project :=
  (routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_iff_restrictedResidualBalance
    M n hn2 htb hns project).mpr hres

/-- No-go form: a failed residual-balance equality refutes the restricted row
identity for the selected projection. -/
theorem routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_noGo_of_not_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hbad :
      ¬ RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
          M n hn2 htb hns project) :
    ¬ RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns project := by
  intro hrow
  exact hbad
    ((routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_iff_restrictedResidualBalance
      M n hn2 htb hns project).mp hrow)

/-- Specialization of the exact residual-balance reduction to the concrete
singleton-quotient projection used by the quotiented zero-profile target. -/
theorem routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientRowIdentity_iff_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) ↔
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) :=
  routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_iff_restrictedResidualBalance
    M n hn2 htb hns
    (zeroProfileQuotientBySingletonShiftProjection
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i))

/-! ## Explicit singleton normal-form representative -/

/-- The coefficient functional at a monomial, as a linear map. -/
noncomputable def mvPolynomialCoeffLinear (n : ℕ) (m : Fin n →₀ ℕ) :
    MvPolynomial (Fin n) ℚ →ₗ[ℚ] ℚ where
  toFun := fun q => MvPolynomial.coeff m q
  map_add' := by
    intro p q
    rw [MvPolynomial.coeff_add]
  map_smul' := by
    intro c q
    rw [MvPolynomial.coeff_smul]
    rfl

/-- The rank-one linear map extracting one singleton coefficient and placing it
on the matching zero-profile singleton-shift row. -/
noncomputable def zeroProfileSingletonCoeffProjector {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) (i : Fin n) :
    MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ where
  toFun := fun q =>
    MvPolynomial.coeff (Finsupp.single i 1) q •
      mlProj (MvPolynomial.X i * Finset.univ.prod factors)
  map_add' := by
    intro p q
    simp [MvPolynomial.coeff_add, add_smul]
  map_smul' := by
    intro c q
    simp [MvPolynomial.coeff_smul, mul_smul]

/-- Explicit singleton-shift normal-form projection.

It removes the degree-one singleton coordinates by subtracting the corresponding
singleton-shift rows.  Unlike `zeroProfileSingletonShiftComplement`, this is a
semantic representative map, not an arbitrary `Classical.choose` complement. -/
noncomputable def zeroProfileSingletonNormalFormProjection {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ :=
  LinearMap.id -
    ∑ i : Fin n, zeroProfileSingletonCoeffProjector factors i

theorem zeroProfileSingletonNormalFormProjection_apply {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (q : MvPolynomial (Fin n) ℚ) :
    zeroProfileSingletonNormalFormProjection factors q =
      q -
        ∑ i : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1) q •
            mlProj (MvPolynomial.X i * Finset.univ.prod factors) := by
  classical
  simp [zeroProfileSingletonNormalFormProjection,
    zeroProfileSingletonCoeffProjector]

/-- Coefficient form of the explicit singleton normalizer.  This is the
algebraic shape of the remaining strict `TΦ` calculation: for every
non-singleton monomial, the normalized coefficient is the raw coefficient minus
the singleton correction contributed by the erased singleton coordinates. -/
theorem zeroProfileSingletonNormalFormProjection_coeff
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (q : MvPolynomial (Fin n) ℚ) (α : Fin n →₀ ℕ) :
    MvPolynomial.coeff α (zeroProfileSingletonNormalFormProjection factors q) =
      MvPolynomial.coeff α q -
        ∑ i : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1) q *
            MvPolynomial.coeff α
              (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) := by
  classical
  rw [zeroProfileSingletonNormalFormProjection_apply]
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_smul]

/-- Coefficient probe for singleton-shift rows at a multilinear monomial:
multiplication by `X i` either removes the `i` coordinate from the target
monomial or contributes zero when `i` is absent. -/
theorem coeff_mlProj_X_mul_of_isMultilinear
    {n : ℕ} (p : MvPolynomial (Fin n) ℚ) (i : Fin n)
    (α : Fin n →₀ ℕ)
    (hα : Finsupp.IsMultilinear α) :
    MvPolynomial.coeff α (mlProj (MvPolynomial.X i * p)) =
      if i ∈ α.support then
        MvPolynomial.coeff (α - Finsupp.single i 1) p
      else 0 := by
  rw [MultilinearSPDP.coeff_mlProj_of_isMultilinear_mono _ _ hα]
  rw [MvPolynomial.coeff_X_mul']

theorem coeff_zero_mlProj_X_mul
    {n : ℕ} (p : MvPolynomial (Fin n) ℚ) (i : Fin n) :
    MvPolynomial.coeff (0 : Fin n →₀ ℕ)
      (mlProj (MvPolynomial.X i * p)) = 0 := by
  have hzero : Finsupp.IsMultilinear (0 : Fin n →₀ ℕ) := by
    intro v
    simp
  rw [coeff_mlProj_X_mul_of_isMultilinear p i (0 : Fin n →₀ ℕ) hzero]
  simp

/-- Support of a strict tag monomial is exactly the tagged finset. -/
theorem tagMonomial_mem_support_iff {N : ℕ}
    (S : Finset (Fin N)) (v : Fin N) :
    v ∈ (SymmetricPower.tagMonomial S).support ↔ v ∈ S := by
  classical
  rw [Finsupp.mem_support_iff, SymmetricPower.tagMonomial_apply]
  by_cases hv : v ∈ S <;> simp [hv]

/-- Removing a tagged coordinate from a strict tag monomial is `erase` on the
underlying source finset. -/
theorem tagMonomial_map_sub_single
    {m n : ℕ} (e : Fin m ↪ Fin n)
    (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S) :
    SymmetricPower.tagMonomial (S.map e) - Finsupp.single (e j) 1 =
      SymmetricPower.tagMonomial ((S.erase j).map e) := by
  classical
  ext x
  by_cases hx : x = e j
  · subst x
    simp [SymmetricPower.tagMonomial_apply, hj]
  · have hnotj : j ∉ S.erase j := by simp
    have hiff :
        x ∈ Finset.map e (S.erase j) ↔ x ∈ Finset.map e S := by
      constructor
      · intro hxmem
        rcases Finset.mem_map.mp hxmem with ⟨y, hy, rfl⟩
        exact Finset.mem_map.mpr ⟨y, Finset.mem_of_mem_erase hy, rfl⟩
      · intro hxmem
        rcases Finset.mem_map.mp hxmem with ⟨y, hy, hyx⟩
        have hyj : y ≠ j := by
          intro h
          apply hx
          rw [← hyx, h]
        exact Finset.mem_map.mpr ⟨y, Finset.mem_erase.mpr ⟨hyj, hy⟩, hyx⟩
    simp [SymmetricPower.tagMonomial_apply, hx, hiff]

/-- The explicit normalizer discards only singleton-shift rows. -/
theorem zeroProfileSingletonNormalFormProjection_residual_mem_singletonShiftSubspace
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (q : MvPolynomial (Fin n) ℚ) :
    q - zeroProfileSingletonNormalFormProjection factors q ∈
      zeroProfileSingletonShiftSubspace factors := by
  classical
  rw [zeroProfileSingletonNormalFormProjection_apply]
  have hsum :
      (∑ i : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1) q •
            mlProj (MvPolynomial.X i * Finset.univ.prod factors)) ∈
        zeroProfileSingletonShiftSubspace factors := by
    refine Submodule.sum_mem _ ?_
    intro i _hi
    exact Submodule.smul_mem _
      (MvPolynomial.coeff (Finsupp.single i 1) q)
      (Submodule.subset_span (Set.mem_range_self i))
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum

/-- With constant coefficient `1`, the singleton normalizer erases every
degree-one singleton coefficient. -/
theorem zeroProfileSingletonNormalFormProjection_coeff_single_eq_zero
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (Finset.univ.prod factors) = (1 : ℚ))
    (q : MvPolynomial (Fin n) ℚ) (i : Fin n) :
    MvPolynomial.coeff (Finsupp.single i 1)
        (zeroProfileSingletonNormalFormProjection factors q) = 0 := by
  classical
  rw [zeroProfileSingletonNormalFormProjection_apply]
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sum]
  have hsum :
      (∑ x : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1)
            (MvPolynomial.coeff (Finsupp.single x 1) q •
              mlProj (MvPolynomial.X x * Finset.univ.prod factors))) =
        MvPolynomial.coeff (Finsupp.single i 1) q := by
    calc
      (∑ x : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1)
            (MvPolynomial.coeff (Finsupp.single x 1) q •
              mlProj (MvPolynomial.X x * Finset.univ.prod factors)))
          =
        ∑ x : Fin n,
          MvPolynomial.coeff (Finsupp.single x 1) q *
            MvPolynomial.coeff (Finsupp.single i 1)
              (mlProj (MvPolynomial.X x * Finset.univ.prod factors)) := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            rw [MvPolynomial.coeff_smul]
            rfl
      _ =
        ∑ x : Fin n,
          MvPolynomial.coeff (Finsupp.single x 1) q *
            (if x = i then
              MvPolynomial.coeff (0 : Fin n →₀ ℕ)
                (Finset.univ.prod factors)
            else 0) := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            rw [coeff_singleton_mlProj_X_mul]
      _ =
        ∑ x : Fin n,
          MvPolynomial.coeff (Finsupp.single x 1) q *
            (if x = i then (1 : ℚ) else 0) := by
            simp [hconst]
      _ = MvPolynomial.coeff (Finsupp.single i 1) q := by
            rw [Finset.sum_eq_single i]
            · simp
            · intro x _hx hxi
              rw [if_neg hxi, mul_zero]
            · intro hi
              exact False.elim (hi (Finset.mem_univ i))
  rw [hsum, sub_self]

/-- A polynomial with no singleton coefficients is fixed by the explicit
singleton normalizer. -/
theorem zeroProfileSingletonNormalFormProjection_apply_eq_self_of_coeff_single_zero
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    {q : MvPolynomial (Fin n) ℚ}
    (hcoeff :
      ∀ i : Fin n, MvPolynomial.coeff (Finsupp.single i 1) q = 0) :
    zeroProfileSingletonNormalFormProjection factors q = q := by
  classical
  rw [zeroProfileSingletonNormalFormProjection_apply]
  have hsum :
      (∑ i : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1) q •
            mlProj (MvPolynomial.X i * Finset.univ.prod factors)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _hi
    rw [hcoeff i]
    simp
  rw [hsum, sub_zero]

/-- The explicit singleton normalizer is idempotent when the base product has
constant coefficient `1`. -/
theorem zeroProfileSingletonNormalFormProjection_idempotent_of_constCoeff_one
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (Finset.univ.prod factors) = (1 : ℚ)) :
    (zeroProfileSingletonNormalFormProjection factors).comp
        (zeroProfileSingletonNormalFormProjection factors) =
      zeroProfileSingletonNormalFormProjection factors := by
  classical
  apply LinearMap.ext
  intro q
  exact
    zeroProfileSingletonNormalFormProjection_apply_eq_self_of_coeff_single_zero
      factors
      (fun i =>
        zeroProfileSingletonNormalFormProjection_coeff_single_eq_zero
          factors hconst q i)

/-- With constant coefficient `1`, the explicit singleton normalizer kills each
singleton-shift generator. -/
theorem zeroProfileSingletonNormalFormProjection_killsSingletonShifts
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (Finset.univ.prod factors) = (1 : ℚ)) :
    ZeroProfileProjectionKillsSingletonShifts factors
      (zeroProfileSingletonNormalFormProjection factors) := by
  classical
  intro i
  rw [zeroProfileSingletonNormalFormProjection_apply]
  have hsum :
      (∑ x : Fin n,
          MvPolynomial.coeff (Finsupp.single x 1)
              (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) •
            mlProj (MvPolynomial.X x * Finset.univ.prod factors)) =
        mlProj (MvPolynomial.X i * Finset.univ.prod factors) := by
    calc
      (∑ x : Fin n,
          MvPolynomial.coeff (Finsupp.single x 1)
              (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) •
            mlProj (MvPolynomial.X x * Finset.univ.prod factors))
          =
        ∑ x : Fin n,
          (if i = x then (1 : ℚ) else 0) •
            mlProj (MvPolynomial.X x * Finset.univ.prod factors) := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            rw [coeff_singleton_mlProj_X_mul]
            simp [hconst]
      _ = mlProj (MvPolynomial.X i * Finset.univ.prod factors) := by
            rw [Finset.sum_eq_single i]
            · simp
            · intro x _hx hxi
              have hix : i ≠ x := fun h => hxi h.symm
              rw [if_neg hix, zero_smul]
            · intro hi
              exact False.elim (hi (Finset.mem_univ i))
  rw [hsum, sub_self]

/-- Kernel form: the explicit singleton normalizer kills the whole
singleton-shift subspace. -/
theorem zeroProfileSingletonNormalFormProjection_singletonShiftSubspace_le_ker
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (Finset.univ.prod factors) = (1 : ℚ)) :
    zeroProfileSingletonShiftSubspace factors ≤
      LinearMap.ker (zeroProfileSingletonNormalFormProjection factors) :=
  (zeroProfileProjectionKillsSingletonShifts_iff_singletonShiftSubspace_le_ker
    factors (zeroProfileSingletonNormalFormProjection factors)).mp
    (zeroProfileSingletonNormalFormProjection_killsSingletonShifts
      factors hconst)

/-- Equality modulo singleton-shift residuals gives equality after the explicit
singleton normalizer. -/
theorem zeroProfileSingletonNormalFormProjection_eq_of_sub_mem_singletonShiftSubspace
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (Finset.univ.prod factors) = (1 : ℚ))
    {q d : MvPolynomial (Fin n) ℚ}
    (hres : q - d ∈ zeroProfileSingletonShiftSubspace factors) :
    zeroProfileSingletonNormalFormProjection factors q =
      zeroProfileSingletonNormalFormProjection factors d := by
  classical
  have hker :=
    zeroProfileSingletonNormalFormProjection_singletonShiftSubspace_le_ker
      factors hconst hres
  have hzero :
      zeroProfileSingletonNormalFormProjection factors (q - d) = 0 :=
    LinearMap.mem_ker.mp hker
  have hsub :
      zeroProfileSingletonNormalFormProjection factors q -
        zeroProfileSingletonNormalFormProjection factors d = 0 := by
    simpa [map_sub] using hzero
  exact sub_eq_zero.mp hsub

/-- Equality modulo singleton-shift residuals is exactly equality after the
canonical singleton quotient projection.  No complement membership of the raw
derivative representative is required. -/
theorem zeroProfileQuotientBySingletonShiftProjection_eq_of_sub_mem_singletonShiftSubspace
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    {q d : MvPolynomial (Fin n) ℚ}
    (hres : q - d ∈ zeroProfileSingletonShiftSubspace factors) :
    zeroProfileQuotientBySingletonShiftProjection factors q =
      zeroProfileQuotientBySingletonShiftProjection factors d := by
  classical
  have hker :=
    zeroProfileQuotientBySingletonShiftProjection_singletonShiftSubspace_le_ker
      factors hres
  have hzero :
      zeroProfileQuotientBySingletonShiftProjection factors (q - d) = 0 :=
    LinearMap.mem_ker.mp hker
  have hsub :
      zeroProfileQuotientBySingletonShiftProjection factors q -
        zeroProfileQuotientBySingletonShiftProjection factors d = 0 := by
    simpa [map_sub] using hzero
  exact sub_eq_zero.mp hsub

/-- Equality after the explicit singleton normalizer implies the raw rows differ
only by singleton-shift residual noise. -/
theorem sub_mem_singletonShiftSubspace_of_zeroProfileSingletonNormalFormProjection_eq
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    {q d : MvPolynomial (Fin n) ℚ}
    (h :
      zeroProfileSingletonNormalFormProjection factors q =
        zeroProfileSingletonNormalFormProjection factors d) :
    q - d ∈ zeroProfileSingletonShiftSubspace factors := by
  classical
  have hq :
      q - zeroProfileSingletonNormalFormProjection factors q ∈
        zeroProfileSingletonShiftSubspace factors :=
    zeroProfileSingletonNormalFormProjection_residual_mem_singletonShiftSubspace
      factors q
  have hd :
      d - zeroProfileSingletonNormalFormProjection factors d ∈
        zeroProfileSingletonShiftSubspace factors :=
    zeroProfileSingletonNormalFormProjection_residual_mem_singletonShiftSubspace
      factors d
  have hneg :
      -(d - zeroProfileSingletonNormalFormProjection factors d) ∈
        zeroProfileSingletonShiftSubspace factors :=
    Submodule.neg_mem _ hd
  have hadd :
      (q - zeroProfileSingletonNormalFormProjection factors q) -
          (d - zeroProfileSingletonNormalFormProjection factors d) ∈
        zeroProfileSingletonShiftSubspace factors := by
    simpa [sub_eq_add_neg] using Submodule.add_mem _ hq hneg
  simpa [h, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd

/-- Semantic strict-`TΦ` residual target for the explicit singleton normalizer:
the strict derivative row must be the canonical normal form of the matching
zero-profile row. -/
def RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj (shift * SPDP.iterDerivList S' r))
    zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q = d

/-- Paper-faithful semantic strict-`TΦ` target for the explicit singleton
normalizer: both the zero-profile row and the strict derivative row are compared
after passing to the same canonical singleton-normal-form representative. -/
def RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj (shift * SPDP.iterDerivList S' r))
    zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q =
      zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) d

/-- Residual-only version of the strict singleton-normal-form target: the raw
zero-profile row and the raw derivative row may differ, but only by
singleton-shift noise.  This avoids the non-paper-faithful arbitrary complement
condition from the earlier singleton quotient decomposition. -/
def RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj (shift * SPDP.iterDerivList S' r))
    q - d ∈
      zeroProfileSingletonShiftSubspace
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)

/-- Quotient-level strict-`TΦ` row identity: compare the zero-profile row and
the derivative row only after quotienting singleton-shift noise. -/
def RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientRowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj (shift * SPDP.iterDerivList S' r))
    zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q =
      zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) d

/-- Fixed-representative condition for the singleton quotient route: every
strict derivative row is already the quotient representative selected by the
singleton-shift projection. -/
def RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj (shift * SPDP.iterDerivList S' r))
    zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) d = d

/-- The actual normalized coefficient computation left by the paper-faithful
singleton residual route.  Singleton coefficients are deliberately absent:
the semantic normalizer kills them on both sides. -/
def RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    ∀ α : Fin n →₀ ℕ,
      (∀ i : Fin n, α ≠ Finsupp.single i 1) →
      let p : MvPolynomial (Fin n) ℚ :=
        compiledPoly (cook_levin_compilation M n hn2 htb hns)
      let r : MvPolynomial (Fin (n / 3)) ℚ :=
        MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n) p
      let q : MvPolynomial (Fin n) ℚ :=
        mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns)
      let d : MvPolynomial (Fin n) ℚ :=
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * SPDP.iterDerivList S' r))
      MvPolynomial.coeff α
          (zeroProfileSingletonNormalFormProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q) =
        MvPolynomial.coeff α
          (zeroProfileSingletonNormalFormProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) d)

/-- Expanded coefficient-balance form of the normalized non-singleton target.
This is the concrete Cook-Levin computation after the singleton normalizer is
unfolded: the raw non-singleton coefficient mismatch must be exactly balanced
by the singleton-erasure correction terms. -/
def RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    ∀ α : Fin n →₀ ℕ,
      (∀ i : Fin n, α ≠ Finsupp.single i 1) →
      let factors : Fin (cookLevinFactorList M n hn2 htb hns).length →
          MvPolynomial (Fin n) ℚ :=
        fun i => (cookLevinFactorList M n hn2 htb hns).get i
      let p : MvPolynomial (Fin n) ℚ :=
        compiledPoly (cook_levin_compilation M n hn2 htb hns)
      let r : MvPolynomial (Fin (n / 3)) ℚ :=
        MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n) p
      let q : MvPolynomial (Fin n) ℚ :=
        mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns)
      let d : MvPolynomial (Fin n) ℚ :=
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * SPDP.iterDerivList S' r))
      MvPolynomial.coeff α q -
          ∑ i : Fin n,
            MvPolynomial.coeff (Finsupp.single i 1) q *
              MvPolynomial.coeff α
                (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) =
        MvPolynomial.coeff α d -
          ∑ i : Fin n,
            MvPolynomial.coeff (Finsupp.single i 1) d *
              MvPolynomial.coeff α
                (mlProj (MvPolynomial.X i * Finset.univ.prod factors))

/-- Type of paper-faithful canonical/profile row-family selectors for the
strict `TΦ` coefficient audit.

The broad balance above quantifies over arbitrary strict differentiated rows
`S'` and arbitrary non-singleton coefficient probes `α`.  The manuscript's
Route B path is narrower: derivative windows are first canonicalized by
`can(w)`, local update words are reduced to finite monoid normal forms, and
the extracted target is compared after the block-local `N ◦ TΦ`
normalization.  This is deliberately only a type alias, not a default
predicate: the concrete selector must be supplied from the canonical-window /
finite-local-normal-form construction. -/
abbrev RouteBPaperFaithfulTPhiCanonicalProfileRowFamily
    (M : DTM) (n : ℕ) (_hn2 : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n) :=
  ∀ (_S' : List (Fin (n / 3)))
    (_shift : MvPolynomial (Fin (n / 3)) ℚ)
    (_α : Fin n →₀ ℕ), Prop

/-- Canonical/profile-local replacement for the refuted broad normalized
coefficient balance.

This is the row-algebra target suggested by the paper: only coefficient probes
belonging to the canonical window/profile row family are consumed.  The
selector is explicit so the next proof must connect it to `can(w)` and finite
local normal forms, instead of silently ranging over arbitrary multi-tag
strict rows. -/
def RouteBPaperFaithfulTPhiCanonicalProfileNormalizedCoeffBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (canonicalRow :
      RouteBPaperFaithfulTPhiCanonicalProfileRowFamily
        M n hn2 htb hns) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    ∀ α : Fin n →₀ ℕ,
      (∀ i : Fin n, α ≠ Finsupp.single i 1) →
      canonicalRow S' shift α →
      let factors : Fin (cookLevinFactorList M n hn2 htb hns).length →
          MvPolynomial (Fin n) ℚ :=
        fun i => (cookLevinFactorList M n hn2 htb hns).get i
      let p : MvPolynomial (Fin n) ℚ :=
        compiledPoly (cook_levin_compilation M n hn2 htb hns)
      let r : MvPolynomial (Fin (n / 3)) ℚ :=
        MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n) p
      let q : MvPolynomial (Fin n) ℚ :=
        mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns)
      let d : MvPolynomial (Fin n) ℚ :=
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * SPDP.iterDerivList S' r))
      MvPolynomial.coeff α q -
          ∑ i : Fin n,
            MvPolynomial.coeff (Finsupp.single i 1) q *
              MvPolynomial.coeff α
                (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) =
        MvPolynomial.coeff α d -
          ∑ i : Fin n,
            MvPolynomial.coeff (Finsupp.single i 1) d *
              MvPolynomial.coeff α
                (mlProj (MvPolynomial.X i * Finset.univ.prod factors))

/-- The old broad balance implies the canonical/profile-local balance for any
chosen canonical row family.  The converse is intentionally absent: Route B
should not re-expand the canonical target back to arbitrary strict rows. -/
theorem routeBPaperFaithfulTPhi_canonicalProfileNormalizedCoeffBalance_of_broad
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (canonicalRow :
      ∀ (_S' : List (Fin (n / 3)))
        (_shift : MvPolynomial (Fin (n / 3)) ℚ)
        (_α : Fin n →₀ ℕ), Prop)
    (hbalance :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiCanonicalProfileNormalizedCoeffBalance
      M n hn2 htb hns canonicalRow := by
  intro S' shift hlen hdeg hvars hadm α hα _hcanonical
  exact hbalance S' shift hlen hdeg hvars hadm α hα

/-- Safety condition for the canonical/profile row family: it must exclude the
two-differentiated-strict-tag unit-shift witness that refutes the broad
normalized balance.

This is the Lean-facing form of the paper correction: `can(w)`/finite local
normal forms must select a row family whose `S,T` relationship is not the
arbitrary two-tag configuration exposed by the no-go theorem below. -/
def RouteBPaperFaithfulTPhiCanonicalProfileExcludesTwoTagUnitShift
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (canonicalRow :
      RouteBPaperFaithfulTPhiCanonicalProfileRowFamily
        M n hn2 htb hns) : Prop :=
  ∀ (T : Finset (Fin (n / 3))) (j k : Fin (n / 3)),
    j ∈ T →
    k ∈ T →
    j ≠ k →
    Even T.card →
    T.card = Nat.log 2 n →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (T.toList.map (cookLevinStrictFOBFlatMap n)) →
    ¬ canonicalRow T.toList (1 : MvPolynomial (Fin (n / 3)) ℚ)
      (SymmetricPower.tagMonomial
        (({j, k} : Finset (Fin (n / 3))).map
          ⟨cookLevinStrictFOBFlatMap n,
            cookLevinStrictFOBFlatMap_injective n⟩))

/-- Corrected canonical/profile residual-balance package for the strict `TΦ`
route.  It combines the narrowed coefficient computation with the explicit
two-tag exclusion that Lean proved necessary for any paper-faithful
canonical-window/profile target. -/
structure RouteBPaperFaithfulTPhiCanonicalProfileResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  canonicalRow :
    RouteBPaperFaithfulTPhiCanonicalProfileRowFamily
      M n hn2 htb hns
  coeff_balance :
    RouteBPaperFaithfulTPhiCanonicalProfileNormalizedCoeffBalance
      M n hn2 htb hns canonicalRow
  excludes_two_tag :
    RouteBPaperFaithfulTPhiCanonicalProfileExcludesTwoTagUnitShift
      M n hn2 htb hns canonicalRow

/-- Narrowed normalized row-identity target for the paper-faithful
canonical/profile route.

This is intentionally coefficient-level and gated by `canonicalRow`: unlike the
refuted broad `RouteBPaperFaithfulTPhiRangePWindowRestricted...` identities, it
only asks for normalized coefficient equality on the canonical/profile probes
selected by `can(w)`/the finite local normal-form classifier. -/
def RouteBPaperFaithfulTPhiCanonicalProfileRestrictedNormalizedCoeffIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (canonicalRow :
      RouteBPaperFaithfulTPhiCanonicalProfileRowFamily
        M n hn2 htb hns) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    ∀ α : Fin n →₀ ℕ,
      (∀ i : Fin n, α ≠ Finsupp.single i 1) →
      canonicalRow S' shift α →
      let p : MvPolynomial (Fin n) ℚ :=
        compiledPoly (cook_levin_compilation M n hn2 htb hns)
      let r : MvPolynomial (Fin (n / 3)) ℚ :=
        MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n) p
      let q : MvPolynomial (Fin n) ℚ :=
        mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns)
      let d : MvPolynomial (Fin n) ℚ :=
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * SPDP.iterDerivList S' r))
      MvPolynomial.coeff α
          (zeroProfileSingletonNormalFormProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q) =
        MvPolynomial.coeff α
          (zeroProfileSingletonNormalFormProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) d)

/-- The narrowed canonical/profile coefficient balance is exactly the
non-singleton coefficient form of the semantic singleton-normalizer identity,
but only on canonical/profile-selected probes. -/
theorem routeBPaperFaithfulTPhi_canonicalProfileRestrictedNormalizedCoeffIdentity_of_balance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (canonicalRow :
      RouteBPaperFaithfulTPhiCanonicalProfileRowFamily
        M n hn2 htb hns)
    (hbalance :
      RouteBPaperFaithfulTPhiCanonicalProfileNormalizedCoeffBalance
        M n hn2 htb hns canonicalRow) :
    RouteBPaperFaithfulTPhiCanonicalProfileRestrictedNormalizedCoeffIdentity
      M n hn2 htb hns canonicalRow := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm α hα hcanon
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  have hq :=
    zeroProfileSingletonNormalFormProjection_coeff
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q α
  have hd :=
    zeroProfileSingletonNormalFormProjection_coeff
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i) d α
  dsimp only
  rw [hq, hd]
  simpa [p, r, q, d] using
    hbalance S' shift hSlen hshiftDegree hshiftVars hadm α hα hcanon

/-- A canonical/profile residual-balance package supplies the narrowed
normalized coefficient identity on its selected row family. -/
theorem routeBPaperFaithfulTPhi_canonicalProfileRestrictedNormalizedCoeffIdentity_of_residualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (H :
      RouteBPaperFaithfulTPhiCanonicalProfileResidualBalance
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiCanonicalProfileRestrictedNormalizedCoeffIdentity
      M n hn2 htb hns H.canonicalRow :=
  routeBPaperFaithfulTPhi_canonicalProfileRestrictedNormalizedCoeffIdentity_of_balance
    M n hn2 htb hns H.canonicalRow H.coeff_balance

/-- Concrete data that instantiates the strict `TΦ` canonical/profile row
selector from the paper's canonical-window map.

The fields deliberately separate the syntactic decoding of a strict
coefficient query into a window from the two mathematical facts still needed:
the canonical family excludes the refuted two-tag raw witness, and the
normalized coefficient identity holds on the selected canonical rows. -/
structure RouteBPaperFaithfulTPhiCanonicalWindowProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  BlockIdx : Type
  LocalOp : Type
  blockFintype : Fintype BlockIdx
  blockDecEq : DecidableEq BlockIdx
  localFintype : Fintype LocalOp
  localDecEq : DecidableEq LocalOp
  prodLinearOrder : LinearOrder (BlockIdx × LocalOp)
  scheme :
    PallLean.Paper93.CanonScheme
      (BlockIdx := BlockIdx) (LocalOp := LocalOp) (Nat.log 2 n)
  rawWindowOf :
    List (Fin (n / 3)) →
      MvPolynomial (Fin (n / 3)) ℚ →
        (Fin n →₀ ℕ) →
          PallLean.Paper93.Window BlockIdx LocalOp (Nat.log 2 n)
  coeff_balance :
    RouteBPaperFaithfulTPhiCanonicalProfileNormalizedCoeffBalance
      M n hn2 htb hns
      (fun S' shift α => by
        letI := blockFintype
        letI := blockDecEq
        letI := localFintype
        letI := localDecEq
        letI := prodLinearOrder
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n) scheme (rawWindowOf S' shift α))
  excludes_two_tag :
    RouteBPaperFaithfulTPhiCanonicalProfileExcludesTwoTagUnitShift
      M n hn2 htb hns
      (fun S' shift α => by
        letI := blockFintype
        letI := blockDecEq
        letI := localFintype
        letI := localDecEq
        letI := prodLinearOrder
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n) scheme (rawWindowOf S' shift α))

/-- The canonical representative selected by `can(w)` for a decoded strict
`TΦ` coefficient query. -/
noncomputable def routeBPaperFaithfulTPhiCanonicalWindowOf
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D :
      RouteBPaperFaithfulTPhiCanonicalWindowProfileData
        M n hn2 htb hns)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (α : Fin n →₀ ℕ) :
    PallLean.Paper93.Window D.BlockIdx D.LocalOp (Nat.log 2 n) := by
  letI := D.blockFintype
  letI := D.blockDecEq
  letI := D.localFintype
  letI := D.localDecEq
  letI := D.prodLinearOrder
  exact
    PallLean.Paper93.canWindow
      (κ := Nat.log 2 n) D.scheme (D.rawWindowOf S' shift α)

/-- The decoded query is in the selected canonical/profile row family exactly
when its raw decoded window is already fixed by `can(w)`. -/
def routeBPaperFaithfulTPhiCanonicalWindowRowFamily
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D :
      RouteBPaperFaithfulTPhiCanonicalWindowProfileData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiCanonicalProfileRowFamily
      M n hn2 htb hns :=
  fun S' shift α => by
    letI := D.blockFintype
    letI := D.blockDecEq
    letI := D.localFintype
    letI := D.localDecEq
    letI := D.prodLinearOrder
    exact
      PallLean.Paper93.IsCanonical
        (κ := Nat.log 2 n) D.scheme (D.rawWindowOf S' shift α)

/-- The `can(w)` representative of any decoded strict query is canonical. -/
theorem routeBPaperFaithfulTPhiCanonicalWindowOf_isCanonical
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D :
      RouteBPaperFaithfulTPhiCanonicalWindowProfileData
        M n hn2 htb hns)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (α : Fin n →₀ ℕ) :
    by
      letI := D.blockFintype
      letI := D.blockDecEq
      letI := D.localFintype
      letI := D.localDecEq
      letI := D.prodLinearOrder
      exact
        PallLean.Paper93.IsCanonical
          (κ := Nat.log 2 n) D.scheme
          (routeBPaperFaithfulTPhiCanonicalWindowOf D S' shift α) := by
  classical
  letI := D.blockFintype
  letI := D.blockDecEq
  letI := D.localFintype
  letI := D.localDecEq
  letI := D.prodLinearOrder
  dsimp [routeBPaperFaithfulTPhiCanonicalWindowOf]
  exact
    PallLean.Paper93.isCanonical_canWindow
      (κ := Nat.log 2 n) D.scheme (D.rawWindowOf S' shift α)

/-- The canonical-window decoding data instantiates the corrected
canonical/profile residual-balance package. -/
def routeBPaperFaithfulTPhi_canonicalProfileResidualBalance_of_canonicalWindowData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiCanonicalWindowProfileData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiCanonicalProfileResidualBalance
      M n hn2 htb hns where
  canonicalRow :=
    routeBPaperFaithfulTPhiCanonicalWindowRowFamily D
  coeff_balance := by
    simpa [routeBPaperFaithfulTPhiCanonicalWindowRowFamily] using
      D.coeff_balance
  excludes_two_tag := by
    simpa [routeBPaperFaithfulTPhiCanonicalWindowRowFamily] using
      D.excludes_two_tag

/-! ### Concrete strict-`TΦ` window decoder -/

/-- Block alphabet for strict `TΦ` derivative windows.

Index `0` is the out-of-range/default block used only when a total decoder is
applied to a malformed list position.  A genuine strict source coordinate
`j : Fin (n / 3)` is encoded as block `j.val + 1`. -/
abbrev RouteBPaperFaithfulTPhiStrictBlockIdx (n : ℕ) : Type :=
  Fin (n / 3 + 1)

/-- The local operation alphabet for the strict first pass.

The boolean records whether the coefficient probe is one of the refuted
two-strict-tag witnesses.  This keeps the `can(w)` selector honest: the
normal-form machinery sees the coefficient-profile obstruction instead of only
the derivative-coordinate list. -/
abbrev RouteBPaperFaithfulTPhiStrictLocalOp : Type :=
  Bool

/-- Linear order on strict window symbols. -/
def routeBPaperFaithfulTPhiStrictProdLinearOrder (n : ℕ) :
    LinearOrder
      (RouteBPaperFaithfulTPhiStrictBlockIdx n ×
        RouteBPaperFaithfulTPhiStrictLocalOp) :=
  LinearOrder.lift'
    (fun p =>
      p.1.val * 2 + if p.2 then 1 else 0)
    (fun a b h => by
      apply Prod.ext
      · apply Fin.ext
        cases a with
        | mk a₁ a₂ =>
          cases b with
          | mk b₁ b₂ =>
            cases a₂ <;> cases b₂ <;> simp at h ⊢ <;> omega
      · cases a with
        | mk a₁ a₂ =>
          cases b with
          | mk b₁ b₂ =>
            cases a₂ <;> cases b₂ <;> simp at h ⊢ <;> omega)

/-- Encode one strict source coordinate as a non-default block. -/
def routeBPaperFaithfulTPhiStrictBlockOfCoord {n : ℕ}
    (j : Fin (n / 3)) :
    RouteBPaperFaithfulTPhiStrictBlockIdx n :=
  ⟨j.val + 1, by
    have hj : j.val < n / 3 := j.isLt
    omega⟩

/-- Total list-position decoder for strict source coordinates.  Genuine
positions encode `S'[i]`; missing positions encode the default block `0`.

The totality is useful because `rawWindowOf` must produce a length
`Nat.log 2 n` vector before the admissibility/length hypotheses are available. -/
def routeBPaperFaithfulTPhiStrictBlockOfList
    {n : ℕ} (S' : List (Fin (n / 3))) (i : ℕ) :
    RouteBPaperFaithfulTPhiStrictBlockIdx n :=
  if h : i < S'.length then
    routeBPaperFaithfulTPhiStrictBlockOfCoord (S'.get ⟨i, h⟩)
  else
    0

/-- Coefficient-profile marker for the strict `TΦ` no-go witness.  It detects
exactly the degree-two strict-tag probes that Lean proved cannot be part of
the broad normalized row family. -/
noncomputable def routeBPaperFaithfulTPhiStrictCoeffMarker
    (n : ℕ) (α : Fin n →₀ ℕ) : Bool :=
  decide
    (∃ j k : Fin (n / 3),
      j ≠ k ∧
        α =
          SymmetricPower.tagMonomial
            (({j, k} : Finset (Fin (n / 3))).map
              ⟨cookLevinStrictFOBFlatMap n,
                cookLevinStrictFOBFlatMap_injective n⟩))

/-- Concrete raw strict `TΦ` derivative window: the block component records the
strict source coordinate at each derivative position, and the local-op
component records the finite coefficient profile relevant to the strict
normal-form exclusion. -/
noncomputable def routeBPaperFaithfulTPhiStrictRawWindowOf
    (n : ℕ)
    (S' : List (Fin (n / 3)))
    (_shift : MvPolynomial (Fin (n / 3)) ℚ)
    (α : Fin n →₀ ℕ) :
    PallLean.Paper93.Window
      (RouteBPaperFaithfulTPhiStrictBlockIdx n)
      RouteBPaperFaithfulTPhiStrictLocalOp
      (Nat.log 2 n) :=
  List.Vector.ofFn
    (fun i =>
      (routeBPaperFaithfulTPhiStrictBlockOfList S' i.val,
        routeBPaperFaithfulTPhiStrictCoeffMarker n α))

@[simp] theorem routeBPaperFaithfulTPhiStrictBlockOfList_of_get
    {n : ℕ} (S' : List (Fin (n / 3))) (i : ℕ) (h : i < S'.length) :
    routeBPaperFaithfulTPhiStrictBlockOfList S' i =
      routeBPaperFaithfulTPhiStrictBlockOfCoord (S'.get ⟨i, h⟩) := by
  simp [routeBPaperFaithfulTPhiStrictBlockOfList, h]

@[simp] theorem routeBPaperFaithfulTPhiStrictBlockOfList_of_not_lt
    {n : ℕ} (S' : List (Fin (n / 3))) (i : ℕ) (h : ¬ i < S'.length) :
    routeBPaperFaithfulTPhiStrictBlockOfList S' i = 0 := by
  simp [routeBPaperFaithfulTPhiStrictBlockOfList, h]

@[simp] theorem routeBPaperFaithfulTPhiStrictCoeffMarker_twoTag
    {n : ℕ} (j k : Fin (n / 3)) (hjk : j ≠ k) :
    routeBPaperFaithfulTPhiStrictCoeffMarker n
        (SymmetricPower.tagMonomial
          (({j, k} : Finset (Fin (n / 3))).map
            ⟨cookLevinStrictFOBFlatMap n,
              cookLevinStrictFOBFlatMap_injective n⟩)) =
      true := by
  classical
  unfold routeBPaperFaithfulTPhiStrictCoeffMarker
  rw [decide_eq_true]
  exact ⟨j, k, hjk, rfl⟩

/-- Default strict window used as the normal form for excluded coefficient
profiles. -/
def routeBPaperFaithfulTPhiStrictDefaultWindow (n κ : ℕ) :
    PallLean.Paper93.Window
      (RouteBPaperFaithfulTPhiStrictBlockIdx n)
      RouteBPaperFaithfulTPhiStrictLocalOp
      κ :=
  List.Vector.ofFn (fun _ => (0, false))

/-- A strict window contains the excluded two-tag coefficient marker. -/
def routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff
    {n κ : ℕ}
    (w :
      PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        κ) : Prop :=
  ∃ i : Fin κ, (w.get i).2 = true

/-- Normal-form key for strict windows: marked coefficient profiles collapse to
the default representative; unmarked windows keep their full raw window. -/
noncomputable def routeBPaperFaithfulTPhiStrictWindowNF (n κ : ℕ)
    (w :
      PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        κ) :
    PallLean.Paper93.Window
      (RouteBPaperFaithfulTPhiStrictBlockIdx n)
      RouteBPaperFaithfulTPhiStrictLocalOp
      κ :=
  if routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff w then
    routeBPaperFaithfulTPhiStrictDefaultWindow n κ
  else
    w

/-- Canonicalization scheme induced by the strict finite normal-form key. -/
noncomputable def routeBPaperFaithfulTPhiStrictCanonScheme (n κ : ℕ) :
    PallLean.Paper93.CanonScheme
      (BlockIdx := RouteBPaperFaithfulTPhiStrictBlockIdx n)
      (LocalOp := RouteBPaperFaithfulTPhiStrictLocalOp)
      κ where
  eqv := fun w =>
    { cls :=
        (Finset.univ :
          Finset
            (PallLean.Paper93.Window
              (RouteBPaperFaithfulTPhiStrictBlockIdx n)
              RouteBPaperFaithfulTPhiStrictLocalOp
              κ)).filter
          (fun w' =>
            routeBPaperFaithfulTPhiStrictWindowNF n κ w' =
              routeBPaperFaithfulTPhiStrictWindowNF n κ w)
      self_mem := by simp }
  sym := by
    intro w w' hw'
    apply Finset.ext
    intro u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw' ⊢
    rw [hw']

theorem routeBPaperFaithfulTPhiStrictRawWindow_marked_of_twoTag
    {n : ℕ} (T : Finset (Fin (n / 3))) (j k : Fin (n / 3))
    (hTcard : T.card = Nat.log 2 n)
    (hj : j ∈ T) (hk : k ∈ T) (hjk : j ≠ k) :
    routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff
      (routeBPaperFaithfulTPhiStrictRawWindowOf n T.toList
        (1 : MvPolynomial (Fin (n / 3)) ℚ)
        (SymmetricPower.tagMonomial
          (({j, k} : Finset (Fin (n / 3))).map
            ⟨cookLevinStrictFOBFlatMap n,
              cookLevinStrictFOBFlatMap_injective n⟩))) := by
  classical
  have hcard_ge : 0 < Nat.log 2 n := by
    have htwo : 2 ≤ T.card := by
      have hsub : ({j, k} : Finset (Fin (n / 3))) ⊆ T := by
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · exact hj
        · exact hk
      have hpair : ({j, k} : Finset (Fin (n / 3))).card = 2 := by
        simpa using Finset.card_pair hjk
      have := Finset.card_le_card hsub
      simpa [hpair] using this
    omega
  refine ⟨⟨0, hcard_ge⟩, ?_⟩
  simpa [routeBPaperFaithfulTPhiStrictRawWindowOf] using
    routeBPaperFaithfulTPhiStrictCoeffMarker_twoTag j k hjk

theorem routeBPaperFaithfulTPhiStrictDefaultWindow_not_marked
    (n κ : ℕ) :
    ¬ routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff
      (routeBPaperFaithfulTPhiStrictDefaultWindow n κ) := by
  intro h
  rcases h with ⟨i, hi⟩
  simp [routeBPaperFaithfulTPhiStrictDefaultWindow] at hi

@[simp] theorem routeBPaperFaithfulTPhiStrictWindowNF_eq_self_of_unmarked
    {n κ : ℕ}
    {w :
      PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        κ}
    (hw : ¬ routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff w) :
    routeBPaperFaithfulTPhiStrictWindowNF n κ w = w := by
  simp [routeBPaperFaithfulTPhiStrictWindowNF, hw]

@[simp] theorem routeBPaperFaithfulTPhiStrictCoeffMarker_zero
    (n : ℕ) :
    routeBPaperFaithfulTPhiStrictCoeffMarker n
        (0 : Fin n →₀ ℕ) =
      false := by
  classical
  unfold routeBPaperFaithfulTPhiStrictCoeffMarker
  rw [decide_eq_false_iff_not]
  intro h
  rcases h with ⟨j, k, _hjk, hα⟩
  have hval :=
    congrArg (fun β : Fin n →₀ ℕ => β (cookLevinStrictFOBFlatMap n j)) hα
  simp [SymmetricPower.tagMonomial_apply] at hval

theorem routeBPaperFaithfulTPhiStrictRawWindow_zero_unmarked
    (n : ℕ) (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ) :
    ¬ routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff
      (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift
        (0 : Fin n →₀ ℕ)) := by
  intro h
  rcases h with ⟨i, hi⟩
  simp [routeBPaperFaithfulTPhiStrictRawWindowOf] at hi

theorem routeBPaperFaithfulTPhiStrictCoeffMarker_singleton
    (n : ℕ) (i : Fin n) :
    routeBPaperFaithfulTPhiStrictCoeffMarker n
        (Finsupp.single i 1 : Fin n →₀ ℕ) =
      false := by
  classical
  unfold routeBPaperFaithfulTPhiStrictCoeffMarker
  rw [decide_eq_false_iff_not]
  intro h
  rcases h with ⟨j, k, hjk, hα⟩
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  by_cases hij : i = e j
  · have hval :=
      congrArg (fun β : Fin n →₀ ℕ =>
        β (cookLevinStrictFOBFlatMap n k)) hα
    have hik : cookLevinStrictFOBFlatMap n k ≠ i := by
      intro hik
      apply hjk
      exact (cookLevinStrictFOBFlatMap_injective n (hik.trans hij)).symm
    have hbad : (0 : ℕ) = 1 := by
      simp [Finsupp.single_eq_of_ne hik,
        SymmetricPower.tagMonomial_apply] at hval
    norm_num at hbad
  · have hval :=
      congrArg (fun β : Fin n →₀ ℕ =>
        β (cookLevinStrictFOBFlatMap n j)) hα
    have hij' : cookLevinStrictFOBFlatMap n j ≠ i := by
      intro h
      exact hij h.symm
    have hbad : (0 : ℕ) = 1 := by
      simp [Finsupp.single_eq_of_ne hij',
        SymmetricPower.tagMonomial_apply] at hval
    norm_num at hbad

theorem routeBPaperFaithfulTPhiStrictRawWindow_singleton_unmarked
    (n : ℕ) (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ) (i : Fin n) :
    ¬ routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff
      (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift
        (Finsupp.single i 1 : Fin n →₀ ℕ)) := by
  intro h
  rcases h with ⟨idx, hidx⟩
  simp [routeBPaperFaithfulTPhiStrictRawWindowOf,
    routeBPaperFaithfulTPhiStrictCoeffMarker_singleton] at hidx

theorem routeBPaperFaithfulTPhiStrictDefaultWindow_mem_marked_class
    {n κ : ℕ}
    {w :
      PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        κ}
    (hw : routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff w) :
    routeBPaperFaithfulTPhiStrictDefaultWindow n κ ∈
      ((routeBPaperFaithfulTPhiStrictCanonScheme n κ).eqv w).cls := by
  classical
  simp [routeBPaperFaithfulTPhiStrictCanonScheme,
    routeBPaperFaithfulTPhiStrictWindowNF, hw,
    routeBPaperFaithfulTPhiStrictDefaultWindow_not_marked]

private theorem routeBPaperFaithfulTPhi_list_replicate_min_le
    {α : Type} [LinearOrder α] (a : α)
    (ha : ∀ x : α, a ≤ x) :
    ∀ l : List α, List.replicate l.length a ≤ l
  | [] => by simp
  | x :: xs => by
      have hx : a ≤ x := ha x
      have ht : List.replicate xs.length a ≤ xs :=
        routeBPaperFaithfulTPhi_list_replicate_min_le a ha xs
      rw [le_iff_lt_or_eq] at hx
      rcases hx with hx | rfl
      · rw [le_iff_lt_or_eq]
        left
        exact List.Lex.rel hx
      · simpa [List.length_cons, List.replicate] using
          List.cons_le_cons a ht

theorem routeBPaperFaithfulTPhiStrictDefaultWindow_le
    (n κ : ℕ)
    (w :
      PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        κ) :
    letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
    routeBPaperFaithfulTPhiStrictDefaultWindow n κ ≤ w := by
  classical
  letI lin := routeBPaperFaithfulTPhiStrictProdLinearOrder n
  change (routeBPaperFaithfulTPhiStrictDefaultWindow n κ).toList ≤
    w.toList
  rw [show (routeBPaperFaithfulTPhiStrictDefaultWindow n κ).toList =
      List.replicate κ
        ((0, false) :
          RouteBPaperFaithfulTPhiStrictBlockIdx n ×
            RouteBPaperFaithfulTPhiStrictLocalOp) by
    simp [routeBPaperFaithfulTPhiStrictDefaultWindow]]
  have ha :
      ∀ x :
        RouteBPaperFaithfulTPhiStrictBlockIdx n ×
          RouteBPaperFaithfulTPhiStrictLocalOp,
        @LE.le _ lin.toLE
          ((0, false) :
            RouteBPaperFaithfulTPhiStrictBlockIdx n ×
              RouteBPaperFaithfulTPhiStrictLocalOp) x := by
    intro p
    cases p with
    | mk b op =>
        cases b with
        | mk bv bh =>
            cases op <;>
              change 0 ≤ bv * 2 + (if _ then 1 else 0) <;> omega
  simpa [w.toList_length] using
    (routeBPaperFaithfulTPhi_list_replicate_min_le _ ha w.toList)

theorem routeBPaperFaithfulTPhiStrictCanWindow_eq_default_of_marked
    {n κ : ℕ}
    {w :
      PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        κ}
    (hw : routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff w) :
    letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
    PallLean.Paper93.canWindow
      (κ := κ) (routeBPaperFaithfulTPhiStrictCanonScheme n κ) w =
      routeBPaperFaithfulTPhiStrictDefaultWindow n κ := by
  classical
  letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
  apply le_antisymm
  · exact
      PallLean.Paper93.canWindow_le
        (κ := κ) (routeBPaperFaithfulTPhiStrictCanonScheme n κ) w
        (routeBPaperFaithfulTPhiStrictDefaultWindow n κ)
        (routeBPaperFaithfulTPhiStrictDefaultWindow_mem_marked_class hw)
  · exact routeBPaperFaithfulTPhiStrictDefaultWindow_le n κ _

theorem routeBPaperFaithfulTPhiStrictCanWindow_eq_self_of_unmarked
    {n κ : ℕ}
    {w :
      PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        κ}
    (hw : ¬ routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff w) :
    letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
    PallLean.Paper93.canWindow
      (κ := κ) (routeBPaperFaithfulTPhiStrictCanonScheme n κ) w = w := by
  classical
  letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
  apply le_antisymm
  · exact
      PallLean.Paper93.canWindow_le
        (κ := κ) (routeBPaperFaithfulTPhiStrictCanonScheme n κ) w
        w
        ((routeBPaperFaithfulTPhiStrictCanonScheme n κ).eqv w).self_mem
  · have hmem :
        PallLean.Paper93.canWindow
            (κ := κ) (routeBPaperFaithfulTPhiStrictCanonScheme n κ) w ∈
          ((routeBPaperFaithfulTPhiStrictCanonScheme n κ).eqv w).cls :=
        PallLean.Paper93.canWindow_mem_class
          (κ := κ) (routeBPaperFaithfulTPhiStrictCanonScheme n κ) w
    simp only [routeBPaperFaithfulTPhiStrictCanonScheme, Finset.mem_filter,
      Finset.mem_univ, true_and] at hmem
    rw [routeBPaperFaithfulTPhiStrictWindowNF_eq_self_of_unmarked hw] at hmem
    change
      routeBPaperFaithfulTPhiStrictWindowNF n κ
          (PallLean.Paper93.canWindow
            (κ := κ) (routeBPaperFaithfulTPhiStrictCanonScheme n κ) w) =
        w at hmem
    by_cases hc :
        routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff
          (PallLean.Paper93.canWindow
            (κ := κ) (routeBPaperFaithfulTPhiStrictCanonScheme n κ) w)
    · have hdef :
          routeBPaperFaithfulTPhiStrictDefaultWindow n κ = w := by
        rw [routeBPaperFaithfulTPhiStrictWindowNF, if_pos hc] at hmem
        exact hmem
      rw [← hdef]
      exact routeBPaperFaithfulTPhiStrictDefaultWindow_le n κ _
    · have hcw :
          PallLean.Paper93.canWindow
              (κ := κ) (routeBPaperFaithfulTPhiStrictCanonScheme n κ) w = w := by
        rw [routeBPaperFaithfulTPhiStrictWindowNF, if_neg hc] at hmem
        exact hmem
      rw [hcw]

theorem routeBPaperFaithfulTPhiStrict_not_isCanonical_of_marked
    {n κ : ℕ}
    {w :
      PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        κ}
    (hw : routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff w) :
    letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
    ¬ PallLean.Paper93.IsCanonical
      (κ := κ) (routeBPaperFaithfulTPhiStrictCanonScheme n κ) w := by
  classical
  letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
  intro hcan
  have hdef : routeBPaperFaithfulTPhiStrictDefaultWindow n κ = w := by
    simpa [PallLean.Paper93.IsCanonical] using
      (routeBPaperFaithfulTPhiStrictCanWindow_eq_default_of_marked hw).symm.trans
        hcan
  have hnot := routeBPaperFaithfulTPhiStrictDefaultWindow_not_marked n κ
  exact hnot (hdef.symm ▸ hw)

theorem routeBPaperFaithfulTPhiStrictRawWindow_twoTag_not_isCanonical
    {n : ℕ} (T : Finset (Fin (n / 3))) (j k : Fin (n / 3))
    (hTcard : T.card = Nat.log 2 n)
    (hj : j ∈ T) (hk : k ∈ T) (hjk : j ≠ k) :
    letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
    ¬ PallLean.Paper93.IsCanonical
      (κ := Nat.log 2 n)
      (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n))
      (routeBPaperFaithfulTPhiStrictRawWindowOf n T.toList
        (1 : MvPolynomial (Fin (n / 3)) ℚ)
        (SymmetricPower.tagMonomial
          (({j, k} : Finset (Fin (n / 3))).map
            ⟨cookLevinStrictFOBFlatMap n,
              cookLevinStrictFOBFlatMap_injective n⟩))) := by
  classical
  letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
  exact
    routeBPaperFaithfulTPhiStrict_not_isCanonical_of_marked
      (routeBPaperFaithfulTPhiStrictRawWindow_marked_of_twoTag
        T j k hTcard hj hk hjk)

theorem routeBPaperFaithfulTPhiStrictCanonScheme_excludes_two_tag
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiCanonicalProfileExcludesTwoTagUnitShift
      M n hn2 htb hns
      (fun S' shift α => by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n))
            (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)) := by
  classical
  intro T j k hj hk hjk _hEven hTcard _hadm
  exact
    routeBPaperFaithfulTPhiStrictRawWindow_twoTag_not_isCanonical
      T j k hTcard hj hk hjk

/-- Broad strict finite-local-normal-form row family: the decoded row must
already be canonical for the strict scheme and must not carry the marked
two-tag coefficient profile.

This family is useful as a diagnostic boundary, but it is not the final
paper-faithful coefficient target: it still admits the zero-profile odd
unit-shift rows refuted below. -/
def routeBPaperFaithfulTPhiStrictUnmarkedCanonicalRowFamily
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiCanonicalProfileRowFamily
      M n hn2 htb hns :=
  fun S' shift α => by
    letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
    exact
      PallLean.Paper93.IsCanonical
          (κ := Nat.log 2 n)
          (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n))
          (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α) ∧
        ¬ routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff
          (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)

/-- Diagnostic broad coefficient-balance target for strict rows that are both
canonical finite-local-normal-form rows and unmarked.

This is intentionally not the final Route B target: Lean proves below that
its fully expanded algebraic form is too wide when odd unit-shift zero-profile
rows are available. -/
abbrev RouteBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  RouteBPaperFaithfulTPhiCanonicalProfileNormalizedCoeffBalance
    M n hn2 htb hns
    (routeBPaperFaithfulTPhiStrictUnmarkedCanonicalRowFamily
      M n hn2 htb hns)

/-- Fully expanded Cook-Levin coefficient computation for the broad strict
unmarked finite-local-normal-form rows.

This is intentionally kept as a named diagnostic target, not as a paper claim:
the theorem
`routeBPaperFaithfulTPhi_not_strictUnmarkedCanonicalCoeffAlgebra_of_unitShift_odd_length`
shows that this all-unmarked/all-admissible pointwise algebra is too broad. -/
def RouteBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffAlgebra
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    ∀ α : Fin n →₀ ℕ,
      (∀ i : Fin n, α ≠ Finsupp.single i 1) →
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n))
            (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)) →
      ¬ routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff
        (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α) →
      let factors : Fin (cookLevinFactorList M n hn2 htb hns).length →
          MvPolynomial (Fin n) ℚ :=
        fun i => (cookLevinFactorList M n hn2 htb hns).get i
      let p : MvPolynomial (Fin n) ℚ :=
        compiledPoly (cook_levin_compilation M n hn2 htb hns)
      let r : MvPolynomial (Fin (n / 3)) ℚ :=
        MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n) p
      let q : MvPolynomial (Fin n) ℚ :=
        mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns)
      let d : MvPolynomial (Fin n) ℚ :=
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * SPDP.iterDerivList S' r))
      MvPolynomial.coeff α q -
          ∑ i : Fin n,
            MvPolynomial.coeff (Finsupp.single i 1) q *
              MvPolynomial.coeff α
                (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) =
        MvPolynomial.coeff α d -
          ∑ i : Fin n,
            MvPolynomial.coeff (Finsupp.single i 1) d *
              MvPolynomial.coeff α
                (mlProj (MvPolynomial.X i * Finset.univ.prod factors))

theorem routeBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffAlgebra_forces_unitShift_constantCoeff_balance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (halgebra :
      RouteBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffAlgebra
        M n hn2 htb hns)
    (S' : List (Fin (n / 3)))
    (hSlen : S'.length = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n))) :
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (1 : MvPolynomial (Fin (n / 3)) ℚ) *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
            SPDP.iterDerivList S' r))
    MvPolynomial.coeff (0 : Fin n →₀ ℕ) q =
      MvPolynomial.coeff (0 : Fin n →₀ ℕ) d := by
  classical
  let factors : Fin (cookLevinFactorList M n hn2 htb hns).length →
      MvPolynomial (Fin n) ℚ :=
    fun i => (cookLevinFactorList M n hn2 htb hns).get i
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (1 : MvPolynomial (Fin (n / 3)) ℚ) *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj
        ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
          SPDP.iterDerivList S' r))
  have hα : ∀ i : Fin n, (0 : Fin n →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro i hi
    have hval := congrArg (fun β : Fin n →₀ ℕ => β i) hi
    simp at hval
  have hunmarked :
      ¬ routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff
        (routeBPaperFaithfulTPhiStrictRawWindowOf n S'
          (1 : MvPolynomial (Fin (n / 3)) ℚ)
          (0 : Fin n →₀ ℕ)) :=
    routeBPaperFaithfulTPhiStrictRawWindow_zero_unmarked n S'
      (1 : MvPolynomial (Fin (n / 3)) ℚ)
  have hcan :
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n))
            (routeBPaperFaithfulTPhiStrictRawWindowOf n S'
              (1 : MvPolynomial (Fin (n / 3)) ℚ)
              (0 : Fin n →₀ ℕ))) := by
    letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
    exact
      routeBPaperFaithfulTPhiStrictCanWindow_eq_self_of_unmarked
        (n := n) (κ := Nat.log 2 n) hunmarked
  have hbalance :=
    halgebra S' (1 : MvPolynomial (Fin (n / 3)) ℚ)
      hSlen (by simp) (by simp) hadm
      (0 : Fin n →₀ ℕ) hα hcan hunmarked
  have hsumq :
      (∑ i : Fin n,
        MvPolynomial.coeff (Finsupp.single i 1) q *
          MvPolynomial.coeff (0 : Fin n →₀ ℕ)
            (mlProj (MvPolynomial.X i * Finset.univ.prod factors))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _hi
    rw [coeff_zero_mlProj_X_mul, mul_zero]
  have hsumd :
      (∑ i : Fin n,
        MvPolynomial.coeff (Finsupp.single i 1) d *
          MvPolynomial.coeff (0 : Fin n →₀ ℕ)
            (mlProj (MvPolynomial.X i * Finset.univ.prod factors))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _hi
    rw [coeff_zero_mlProj_X_mul, mul_zero]
  dsimp only at hbalance
  rw [hsumq, hsumd, sub_zero, sub_zero] at hbalance
  simpa [p, r, q, d] using hbalance

theorem routeBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffBalance_of_algebra
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (halgebra :
      RouteBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffAlgebra
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffBalance
      M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm α hα hrow
  exact
    halgebra S' shift hSlen hshiftDegree hshiftVars hadm α hα
      hrow.1 hrow.2

theorem routeBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffAlgebra_of_balance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbalance :
      RouteBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffBalance
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffAlgebra
      M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm α hα hcan hunmarked
  exact
    hbalance S' shift hSlen hshiftDegree hshiftVars hadm α hα
      ⟨hcan, hunmarked⟩

theorem routeBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffBalance_iff_algebra
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffBalance
        M n hn2 htb hns ↔
      RouteBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffAlgebra
        M n hn2 htb hns :=
  ⟨routeBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffAlgebra_of_balance
      M n hn2 htb hns,
    routeBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffBalance_of_algebra
      M n hn2 htb hns⟩

theorem routeBPaperFaithfulTPhiStrictUnmarkedCanonicalRowFamily_excludes_two_tag
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiCanonicalProfileExcludesTwoTagUnitShift
      M n hn2 htb hns
      (routeBPaperFaithfulTPhiStrictUnmarkedCanonicalRowFamily
        M n hn2 htb hns) := by
  classical
  intro T j k hj hk hjk _hEven hTcard _hadm hrow
  exact hrow.2
    (routeBPaperFaithfulTPhiStrictRawWindow_marked_of_twoTag
      T j k hTcard hj hk hjk)

/-- Paper-faithful strict canonical row family after the discovered
normal-form gates.

This is deliberately narrow.  It keeps only the zero-profile unit-shift rows
whose strict derivative list is nodup and even-length, in addition to the
canonical/unmarked strict normal-form gates.  This row family belongs to the
coefficient-identity diagnostic route, not to the later profile-cover route. -/
def routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiCanonicalProfileRowFamily
      M n hn2 htb hns :=
  fun S' shift α =>
    routeBPaperFaithfulTPhiStrictUnmarkedCanonicalRowFamily
        M n hn2 htb hns S' shift α ∧
      shift = (1 : MvPolynomial (Fin (n / 3)) ℚ) ∧
      α = (0 : Fin n →₀ ℕ) ∧
      S'.Nodup ∧
      Even S'.length

/-- Profile-cover row family for strict `TΦ` range rows.

Unlike the coefficient-identity row family above, this classifier surface may
use any unmarked canonical coefficient probe to attach a profile to a strict
range row.  The derivative row being covered does not depend on that probe. -/
def routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiCanonicalProfileRowFamily
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhiStrictUnmarkedCanonicalRowFamily
    M n hn2 htb hns

/-- The replacement strict coefficient target: the normalized coefficient
identity is only requested on canonical, unmarked rows that also satisfy the
unit-shift zero-profile parity/normalization gate. -/
abbrev RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  RouteBPaperFaithfulTPhiCanonicalProfileNormalizedCoeffBalance
    M n hn2 htb hns
    (routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
      M n hn2 htb hns)

/-- Fully expanded paper-faithful strict coefficient target.

This is the narrowed replacement for the broad diagnostic algebra above.  The
mathematical coefficient identity is unchanged, but its hypotheses now expose
all three row gates separately: strict canonical normal form, absence of the
marked two-tag coefficient profile, and the unit-shift zero-profile
unit-shift zero-profile side condition. -/
def RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffAlgebra
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    ∀ α : Fin n →₀ ℕ,
      (∀ i : Fin n, α ≠ Finsupp.single i 1) →
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n))
            (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)) →
      ¬ routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff
        (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α) →
      shift = (1 : MvPolynomial (Fin (n / 3)) ℚ) →
      α = (0 : Fin n →₀ ℕ) →
      S'.Nodup →
      Even S'.length →
      let factors : Fin (cookLevinFactorList M n hn2 htb hns).length →
          MvPolynomial (Fin n) ℚ :=
        fun i => (cookLevinFactorList M n hn2 htb hns).get i
      let p : MvPolynomial (Fin n) ℚ :=
        compiledPoly (cook_levin_compilation M n hn2 htb hns)
      let r : MvPolynomial (Fin (n / 3)) ℚ :=
        MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n) p
      let q : MvPolynomial (Fin n) ℚ :=
        mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns)
      let d : MvPolynomial (Fin n) ℚ :=
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * SPDP.iterDerivList S' r))
      MvPolynomial.coeff α q -
          ∑ i : Fin n,
            MvPolynomial.coeff (Finsupp.single i 1) q *
              MvPolynomial.coeff α
                (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) =
        MvPolynomial.coeff α d -
          ∑ i : Fin n,
            MvPolynomial.coeff (Finsupp.single i 1) d *
              MvPolynomial.coeff α
                (mlProj (MvPolynomial.X i * Finset.univ.prod factors))

theorem routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance_of_algebra
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (halgebra :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffAlgebra
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance
      M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm α hα hrow
  rcases hrow with ⟨hrowUnmarked, hshiftUnit, hαzero, hSnd, hEven⟩
  exact
    halgebra S' shift hSlen hshiftDegree hshiftVars hadm α hα
      hrowUnmarked.1 hrowUnmarked.2 hshiftUnit hαzero hSnd hEven

theorem routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffAlgebra_of_balance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbalance :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffAlgebra
      M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm α hα hcan hunmarked
    hshiftUnit hαzero hSnd hEven
  exact
    hbalance S' shift hSlen hshiftDegree hshiftVars hadm α hα
      ⟨⟨hcan, hunmarked⟩, hshiftUnit, hαzero, hSnd, hEven⟩

theorem routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance_iff_algebra
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance
        M n hn2 htb hns ↔
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffAlgebra
        M n hn2 htb hns :=
  ⟨routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffAlgebra_of_balance
      M n hn2 htb hns,
    routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance_of_algebra
      M n hn2 htb hns⟩

/-- Strict specialization of the narrowed normalized coefficient identity.
This is the target to use instead of the broad restricted row identity: it is
already gated by canonicality, the two-tag normal-form exclusion, and the
unit-shift parity/normalization condition. -/
abbrev RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRestrictedNormalizedCoeffIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  RouteBPaperFaithfulTPhiCanonicalProfileRestrictedNormalizedCoeffIdentity
    M n hn2 htb hns
    (routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
      M n hn2 htb hns)

/-- The narrowed strict coefficient balance gives the narrowed normalized
identity directly.  This is the paper-faithful replacement for the broad
restricted identity route. -/
theorem routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRestrictedNormalizedCoeffIdentity_of_balance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbalance :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRestrictedNormalizedCoeffIdentity
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_canonicalProfileRestrictedNormalizedCoeffIdentity_of_balance
    M n hn2 htb hns
    (routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
      M n hn2 htb hns)
    hbalance

theorem routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily_excludes_two_tag
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiCanonicalProfileExcludesTwoTagUnitShift
      M n hn2 htb hns
      (routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
        M n hn2 htb hns) := by
  classical
  intro T j k hj hk hjk _hEven hTcard _hadm hrow
  exact hrow.1.2
    (routeBPaperFaithfulTPhiStrictRawWindow_marked_of_twoTag
      T j k hTcard hj hk hjk)

theorem routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily_excludes_odd_zero_unitShift
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S' : List (Fin (n / 3)))
    (hSnd : S'.Nodup)
    (hOdd : Odd S'.length) :
    ¬ routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
        M n hn2 htb hns S'
        (1 : MvPolynomial (Fin (n / 3)) ℚ)
        (0 : Fin n →₀ ℕ) := by
  intro hrow
  have hEven : Even S'.length := hrow.2.2.2.2
  rcases hEven with ⟨a, ha⟩
  rcases hOdd with ⟨b, hb⟩
  omega


/-! ### Narrow strict paper-faithful profile/subspace consumer -/

/-- The strict paper-faithful canonical P-window subspace.

Unlike `routeBPaperFaithfulTPhiRangePWindowSubspace`, this subspace is gated by
`routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily`; it therefore
only contains the narrowed canonical/profile rows for which the coefficient
algebra above is valid.  This is the subspace consumer to use for the
paper-faithful route, not the broad restricted residual/row-identity targets. -/
noncomputable def routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    { q : MvPolynomial (Fin n) ℚ |
      ∃ (S' : List (Fin (n / 3)))
        (shift : MvPolynomial (Fin (n / 3)) ℚ)
        (α : Fin n →₀ ℕ),
        S'.length = Nat.log 2 n ∧
        shift.totalDegree ≤ Nat.log 2 n ∧
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)) ∧
        routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
          M n hn2 htb hns S' shift α ∧
        q =
          mlProj
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
              SPDP.iterDerivList (S'.map (cookLevinStrictFOBFlatMap n))
                ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
                  (compiledPoly
                    (cook_levin_compilation M n hn2 htb hns)))) }


/-- The narrowed strict canonical P-window row subspace is contained in the
ordinary SPDP subspace of the strict ambient `TΦ` polynomial.

This is the formal bridge from the row-family presentation to the matrix/SPDP
rank object: every generator in the narrowed canonical family is still an SPDP
generator with derivative list `S'.map cookLevinStrictFOBFlatMap` and multiplier
`rename cookLevinStrictFOBFlatMap shift`. -/
theorem routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalPWindowSubspace_le_mlBlockedSpdpSubspace
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
        M n hn2 htb hns ≤
      MultilinearSPDP.mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  classical
  unfold routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
  refine Submodule.span_le.mpr ?_
  intro q hq
  rcases hq with
    ⟨S', shift, α, hSlen, hshiftDegree, hshiftVars, hadm, _hrow, rfl⟩
  apply Submodule.subset_span
  refine ⟨S'.map (cookLevinStrictFOBFlatMap n),
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift, ?_, ?_, ?_, hadm, rfl⟩
  · simpa [List.length_map] using hSlen
  · exact le_trans
      (MvPolynomial.totalDegree_rename_le (cookLevinStrictFOBFlatMap n) shift)
      hshiftDegree
  · exact hshiftVars

/-- Bounded common-span target for the narrowed strict paper-faithful canonical
P-window subspace. -/
def RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCommonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (budget : ℕ) : Prop :=
  ∃ G : Finset (MvPolynomial (Fin n) ℚ),
    G.card ≤ budget ∧
    routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
        M n hn2 htb hns ≤
      Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))

/-- Narrow canonical/profile-subspace containment: only the
paper-faithful canonical row family is consumed. -/
def RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalControlledByProfileSubspace
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n)) : Prop :=
  routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
      M n hn2 htb hns ≤
    zeroProfileLocalTypeCompressedProfileSpan A

/-- Generator form of the narrow profile/subspace consumer.  The `hrow` input
is the important gate: downstream proofs may only consume rows in
`routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily`. -/
def RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileGeneratorReduction
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n)) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (α : Fin n →₀ ℕ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
      M n hn2 htb hns S' shift α →
    mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          SPDP.iterDerivList (S'.map (cookLevinStrictFOBFlatMap n))
            ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      zeroProfileLocalTypeCompressedProfileSpan A

/-- The narrow profile-subspace containment is exactly its generator-membership
form. -/
theorem routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalControlledByProfileSubspace_iff_generatorReduction
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n)) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalControlledByProfileSubspace
        M n hn2 htb hns A ↔
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileGeneratorReduction
        M n hn2 htb hns A := by
  classical
  constructor
  · intro hcontrol S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    apply hcontrol
    unfold routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
    exact Submodule.subset_span
      ⟨S', shift, α, hSlen, hshiftDegree, hshiftVars, hadm, hrow, rfl⟩
  · intro hgen
    unfold RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalControlledByProfileSubspace
    unfold routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
    refine Submodule.span_le.mpr ?_
    intro q hq
    rcases hq with
      ⟨S', shift, α, hSlen, hshiftDegree, hshiftVars, hadm, hrow, rfl⟩
    exact hgen S' shift α hSlen hshiftDegree hshiftVars hadm hrow

/-- A narrow profile-subspace containment gives the bounded common-span form for
exactly the narrowed canonical row subspace. -/
theorem routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalCommonSpanWithBudget_of_profileSubspace
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n))
    (hprofile :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalControlledByProfileSubspace
        M n hn2 htb hns A) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCommonSpanWithBudget
      M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) := by
  classical
  refine ⟨zeroProfileLocalTypeGlobalBasis A,
    zeroProfileLocalTypeGlobalBasis_card_le_withinProfileBound A, ?_⟩
  simpa [RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalControlledByProfileSubspace,
    zeroProfileLocalTypeCompressedProfileSpan] using hprofile

/-- The narrow strict paper-faithful profile/subspace frontier.  This is the
final local-normal-form obligation after the coefficient algebra has been
closed: classify only the narrowed canonical row family into a bounded profile
alphabet. -/
def RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileSubspaceContainment
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ A : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n),
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalControlledByProfileSubspace
      M n hn2 htb hns A

/-- Direct classifier for the narrowed strict paper-faithful row family.  This
bypasses `RouteBPaperFaithfulTPhiStrictCanonicalWindowData`: no raw
`CanonScheme` predicate is needed unless a later proof wants to connect back to
`can(w)`. -/
structure RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileClassifier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  alphabet : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n)
  rowType :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ),
      S'.length = Nat.log 2 n →
      shift.totalDegree ≤ Nat.log 2 n →
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)) →
      routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
        M n hn2 htb hns S' shift α →
      alphabet.type
  row_mem_typeSpace :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            SPDP.iterDerivList (S'.map (cookLevinStrictFOBFlatMap n))
              ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
        zeroProfileLocalTypeSpace alphabet
          (rowType S' shift α hSlen hshiftDegree hshiftVars hadm hrow)


/-! ### Paper §9.3–§9.4 local profile compression surface -/

/-- Paper-faithful local-profile compression data for narrowed strict `TΦ`
canonical derivative rows.

This is the Lean surface corresponding to the paper's §9.3–§9.4 route:
canonicalize derivative windows, compress each live interface to a finite local
monoid normal form, then place rows with the same interface-anonymous profile in
a bounded symmetric-power/profile space.  Notice what is *not* present here:
there is no equality with zero-profile shifted base-product rows and no broad
residual/row-identity hypothesis. -/
structure RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalLocalProfileCompression
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  alphabet : ZeroProfileLocalTypeAlphabet n (Nat.log 2 n)
  profileOfCanonicalRow :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ),
      S'.length = Nat.log 2 n →
      shift.totalDegree ≤ Nat.log 2 n →
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)) →
      routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
        M n hn2 htb hns S' shift α →
      alphabet.type
  canonicalRow_mem_profileSpace :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            SPDP.iterDerivList (S'.map (cookLevinStrictFOBFlatMap n))
              ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
        zeroProfileLocalTypeSpace alphabet
          (profileOfCanonicalRow S' shift α hSlen hshiftDegree hshiftVars hadm hrow)


/-- Concrete canonical-window/profile-compression data for the strict `TΦ`
row family.

This is the paper §9.3 object in Lean form.  The profile type is attached to
canonical windows produced by `routeBPaperFaithfulTPhiStrictCanonScheme` on
`routeBPaperFaithfulTPhiStrictRawWindowOf`; each profile carries a bounded
local basis, and each narrowed canonical derivative row is proved to lie in the
basis span of the profile selected by its canonical window.

This is deliberately a direct row-in-profile-space surface.  It does not route
through zero-profile shifted rows, residual balance, or a broad row identity. -/
structure RouteBPaperFaithfulTPhiStrictCanonicalWindowProfileCompressionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  profileType : Type
  [profileTypeFintype : Fintype profileType]
  localDim : ℕ
  localBasis : profileType → Finset (MvPolynomial (Fin n) ℚ)
  localBasis_card_le : ∀ ρ, (localBasis ρ).card ≤ localDim
  profileBudget_le : Fintype.card profileType * localDim ≤
    withinProfileBound (Nat.log 2 n)
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      profileType
  canonicalRow_mem_profileSpan :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            SPDP.iterDerivList (S'.map (cookLevinStrictFOBFlatMap n))
              ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
        Submodule.span ℚ
          (↑(localBasis
            (profileOfCanonicalWindow
              (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
              hrow.1.1)) : Set (MvPolynomial (Fin n) ℚ))

attribute [instance] RouteBPaperFaithfulTPhiStrictCanonicalWindowProfileCompressionData.profileTypeFintype


/-! ### Paper-faithful orbit-rank profile target

The paper's Lemma 27 does not assert that all interface-renamings of a profile
live in one literal ambient common span.  It asserts rank invariance under
within-block interface permutations: rows of the same interface-anonymous
profile are compared after invertible row/column reindexings.  The following
surface records that route directly. -/

/-- One canonical strict `TΦ` derivative row, as a polynomial row vector in the
ambient coefficient space. -/
noncomputable def routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ) :
    MvPolynomial (Fin n) ℚ :=
  mlProj
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
      SPDP.iterDerivList (S'.map (cookLevinStrictFOBFlatMap n))
        ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))))

/-- Strict canonical derivative rows are literal generators of the strict
ambient `TΦ` SPDP subspace.

This is the row-level fact used by the paper's profile decomposition: the row
is first a strict ambient SPDP row, and only then must the canonical
local-monoid/profile analysis place it into the profile subspace selected by
its canonical window. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalDerivativeRow_mem_ambientSpdpSubspace
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (hSlen : S'.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n))) :
    routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
        M n hn2 htb hns S' shift ∈
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  exact
    Submodule.subset_span
      ⟨S'.map (cookLevinStrictFOBFlatMap n),
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift,
        by simpa using hSlen,
        by
          exact le_trans
            (MvPolynomial.totalDegree_rename_le
              (cookLevinStrictFOBFlatMap n) shift)
            hshiftDegree,
        hshiftVars,
        hadm,
        rfl⟩

/-- Paper-faithful orbit/profile rank data for narrowed strict `TΦ` canonical
rows.

For a canonical row, `profileOfCanonicalWindow` picks its interface-anonymous
profile.  The row is not required to lie literally in one global common span.
Instead, it lies in an invertible image of the bounded local profile space for
that profile.  This matches paper Lemma 27: within-block interface permutations
act by invertible reindexings, so they preserve rank contribution without
forcing a literal ambient-span equality. -/
structure RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  profileType : Type
  [profileTypeFintype : Fintype profileType]
  localDim : ℕ
  localBasis : profileType → Finset (MvPolynomial (Fin n) ℚ)
  localBasis_card_le : ∀ ρ, (localBasis ρ).card ≤ localDim
  profileBudget_le : Fintype.card profileType * localDim ≤
    withinProfileBound (Nat.log 2 n)
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      profileType
  orbitEquiv :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      MvPolynomial (Fin n) ℚ ≃ₗ[ℚ] MvPolynomial (Fin n) ℚ
  canonicalRow_mem_orbitProfileSpan :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        Submodule.map
          (orbitEquiv S' shift α hSlen hshiftDegree hshiftVars hadm hrow).toLinearMap
          (Submodule.span ℚ
            (↑(localBasis
              (profileOfCanonicalWindow
                (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
                hrow.1.1)) : Set (MvPolynomial (Fin n) ℚ)))

attribute [instance] RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData.profileTypeFintype


/-- The orbit image of the bounded local profile space selected by a canonical
strict `TΦ` row. -/
noncomputable def routeBPaperFaithfulTPhiStrictCanonicalOrbitProfileSubspace
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (α : Fin n →₀ ℕ)
    (hSlen : S'.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)))
    (hrow :
      routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
        M n hn2 htb hns S' shift α) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.map
    (D.orbitEquiv S' shift α hSlen hshiftDegree hshiftVars hadm hrow).toLinearMap
    (Submodule.span ℚ
      (↑(D.localBasis
        (D.profileOfCanonicalWindow
          (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
          hrow.1.1)) : Set (MvPolynomial (Fin n) ℚ)))

/-- Paper Lemma 27 in the form needed downstream: the invertible orbit/rename
image of a profile space has the same finite-rank budget as the local profile
space.  This is where the formal route uses permutation/rename finrank
preservation rather than a literal common ambient span. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalOrbitProfileSubspace_finrank_le
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (α : Fin n →₀ ℕ)
    (hSlen : S'.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)))
    (hrow :
      routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
        M n hn2 htb hns S' shift α) :
    Module.finrank ℚ
      (routeBPaperFaithfulTPhiStrictCanonicalOrbitProfileSubspace
        D S' shift α hSlen hshiftDegree hshiftVars hadm hrow) ≤ D.localDim := by
  let ρ :=
    D.profileOfCanonicalWindow
      (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α) hrow.1.1
  let V : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    Submodule.span ℚ (↑(D.localBasis ρ) : Set (MvPolynomial (Fin n) ℚ))
  have hmap :
      Module.finrank ℚ
        (Submodule.map
          (D.orbitEquiv S' shift α hSlen hshiftDegree hshiftVars hadm hrow).toLinearMap V)
        = Module.finrank ℚ V := by
    exact
      ((D.orbitEquiv S' shift α hSlen hshiftDegree hshiftVars hadm hrow).finrank_map_eq V)
  have hspan : Module.finrank ℚ V ≤ (D.localBasis ρ).card := by
    simpa [V] using
      (finrank_span_finset_le_card (D.localBasis ρ) :
        Module.finrank ℚ
          (Submodule.span ℚ
            (↑(D.localBasis ρ) : Set (MvPolynomial (Fin n) ℚ))) ≤
          (D.localBasis ρ).card)
  have hcard : (D.localBasis ρ).card ≤ D.localDim := D.localBasis_card_le ρ
  simpa [routeBPaperFaithfulTPhiStrictCanonicalOrbitProfileSubspace, V, ρ] using
    (hmap.le.trans (hspan.trans hcard))

/-- Each narrowed canonical row lies in its selected orbit profile subspace. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalRow_mem_orbitProfileSubspace
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (α : Fin n →₀ ℕ)
    (hSlen : S'.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)))
    (hrow :
      routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
        M n hn2 htb hns S' shift α) :
    routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
        M n hn2 htb hns S' shift ∈
      routeBPaperFaithfulTPhiStrictCanonicalOrbitProfileSubspace
        D S' shift α hSlen hshiftDegree hshiftVars hadm hrow := by
  simpa [routeBPaperFaithfulTPhiStrictCanonicalOrbitProfileSubspace] using
    D.canonicalRow_mem_orbitProfileSpan
      S' shift α hSlen hshiftDegree hshiftVars hadm hrow


/-- Downstream rank-budget form of the paper-faithful orbit route.

This is intentionally an orbit/rank statement, not a literal common-span
statement.  It records exactly the data needed by the paper's Lemma 27 + Lemma
31 route: finitely many interface-anonymous profiles, a bounded local space for
each profile, and every canonical row contained in an invertible permutation /
rename image of the appropriate local space. -/
def RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankBoundWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (budget : ℕ) : Prop :=
  ∃ D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns,
    Fintype.card D.profileType * D.localDim ≤ budget

/-- Orbit-rank data immediately supplies the downstream orbit-rank budget.
This is the bridge that replaces the previous attempt to force all rows into a
literal global common span. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitRankBoundWithBudget_of_data
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankBoundWithBudget
      M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) :=
  ⟨D, D.profileBudget_le⟩

/-- The orbit-rank budget exposes the per-row local-rank bound for every
narrowed canonical strict row.  The row may live in a row-dependent invertible
rename/permutation image, but that image has the same finrank as the bounded
profile space. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitRankBound_row_finrank_le
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (hbudget :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankBoundWithBudget
        M n hn2 htb hns (withinProfileBound (Nat.log 2 n)))
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (α : Fin n →₀ ℕ)
    (hSlen : S'.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)))
    (hrow :
      routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
        M n hn2 htb hns S' shift α) :
    ∃ D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
        M n hn2 htb hns,
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        routeBPaperFaithfulTPhiStrictCanonicalOrbitProfileSubspace
          D S' shift α hSlen hshiftDegree hshiftVars hadm hrow ∧
      Module.finrank ℚ
        (routeBPaperFaithfulTPhiStrictCanonicalOrbitProfileSubspace
          D S' shift α hSlen hshiftDegree hshiftVars hadm hrow) ≤
        D.localDim ∧
      Fintype.card D.profileType * D.localDim ≤
        withinProfileBound (Nat.log 2 n) := by
  rcases hbudget with ⟨D, hD⟩
  exact ⟨D,
    routeBPaperFaithfulTPhi_strictCanonicalRow_mem_orbitProfileSubspace
      D S' shift α hSlen hshiftDegree hshiftVars hadm hrow,
    routeBPaperFaithfulTPhi_strictCanonicalOrbitProfileSubspace_finrank_le
      D S' shift α hSlen hshiftDegree hshiftVars hadm hrow,
    hD⟩

/-- The paper-faithful orbit-rank frontier: finite profiles, bounded local
spaces, and canonical rows landing in invertible orbit images of those spaces. -/
def RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankFrontier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  Nonempty
    (RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns)

/-- Package orbit-rank data as the orbit-rank frontier. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitRankFrontier_of_data
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankFrontier
      M n hn2 htb hns :=
  ⟨D⟩

/-- An orbit-rank frontier supplies the canonical within-profile budget. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitRankBoundWithBudget_of_frontier
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (h :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankFrontier
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankBoundWithBudget
      M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) := by
  rcases h with ⟨D⟩
  exact routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitRankBoundWithBudget_of_data D

/-- Matrix/global rank frontier for the paper-faithful orbit route.

Per-row orbit images alone do not imply a global span/rank bound, because the
invertible image may vary with the row.  This is the honest downstream load-
bearing target: the whole narrowed canonical row subspace must have finite rank
bounded by the total profile budget after the block-permutation/profile matrix
assembly of paper Lemma 27. -/
def RouteBPaperFaithfulTPhiStrictCanonicalWindowMatrixRankFrontier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns,
    Module.finrank ℚ
      (routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
        M n hn2 htb hns) ≤ Fintype.card D.profileType * D.localDim

/-- The matrix/global frontier gives the direct finite-rank budget for the
narrowed canonical strict `TΦ` row subspace. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalPWindowSubspace_finrank_le_of_matrixRankFrontier
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (hfrontier :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowMatrixRankFrontier
        M n hn2 htb hns) :
    Module.finrank ℚ
      (routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
        M n hn2 htb hns) ≤ withinProfileBound (Nat.log 2 n) := by
  rcases hfrontier with ⟨D, hrank⟩
  exact hrank.trans D.profileBudget_le



/-- Exact strict ambient `TΦ` SPDP-rank upper-bound target for a chosen orbit
profile package.

This is deliberately stronger than the narrowed canonical matrix frontier: it
bounds the whole ambient SPDP subspace, including all admissible shifts and
rows, by the same finite profile budget carried by `D`.  Proving this is the
full global finite-local-monoid / canonical-window orbit assembly theorem. -/
def RouteBPaperFaithfulTPhiStrictAmbientMlRankUpper
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns) : Prop :=
  MultilinearSPDP.mlBlockedSpdpRank
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
    Fintype.card D.profileType * D.localDim



/-- The finite global basis obtained by assembling all profile-local bases in
one ambient coefficient space.  This is the matrix-assembly object in the
paper route: after canonical/profile/orbit normalization, every ambient strict
`TΦ` row must be shown to land in the span of this finite union. -/
noncomputable def routeBPaperFaithfulTPhiStrictGlobalProfileBasis
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  Finset.univ.biUnion D.localBasis

/-- Cardinality of the assembled profile basis is bounded by
`#profiles * localDim`. -/
theorem routeBPaperFaithfulTPhi_strictGlobalProfileBasis_card_le
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns) :
    (routeBPaperFaithfulTPhiStrictGlobalProfileBasis D).card ≤
      Fintype.card D.profileType * D.localDim := by
  classical
  unfold routeBPaperFaithfulTPhiStrictGlobalProfileBasis
  calc
    (Finset.univ.biUnion D.localBasis).card ≤
        ∑ ρ : D.profileType, (D.localBasis ρ).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ρ : D.profileType, D.localDim := by
      exact Finset.sum_le_sum (fun ρ _ => D.localBasis_card_le ρ)
    _ = Fintype.card D.profileType * D.localDim := by
      simp [Finset.sum_const, Finset.card_univ, mul_comm]

/-- Exact global matrix-assembly cover for a chosen strict `TΦ` profile/orbit
package.  This is the concrete remaining row-span statement: the whole ambient
strict `TΦ` SPDP subspace, not merely the narrowed canonical rows, is contained
in the span of the finite assembled profile basis. -/
def RouteBPaperFaithfulTPhiStrictAmbientGlobalProfileSpanCover
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns) : Prop :=
  MultilinearSPDP.mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
    Submodule.span ℚ
      (↑(routeBPaperFaithfulTPhiStrictGlobalProfileBasis D) :
        Set (MvPolynomial (Fin n) ℚ))


/-- Generator-by-generator form of the ambient assembled-profile cover. -/
def RouteBPaperFaithfulTPhiStrictAmbientGlobalProfileGeneratorCover
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      Submodule.span ℚ
        (↑(routeBPaperFaithfulTPhiStrictGlobalProfileBasis D) :
          Set (MvPolynomial (Fin n) ℚ))

/-- The ambient cover is exactly the generator-by-generator cover. -/
theorem routeBPaperFaithfulTPhi_strictAmbientGlobalProfileSpanCover_iff_generatorCover
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictAmbientGlobalProfileSpanCover D ↔
      RouteBPaperFaithfulTPhiStrictAmbientGlobalProfileGeneratorCover D := by
  constructor
  · intro hcover S shift hSlen hshiftDegree hshiftVars hadm
    apply hcover
    unfold MultilinearSPDP.mlBlockedSpdpSubspace
    exact Submodule.subset_span
      ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  · intro hgen
    unfold RouteBPaperFaithfulTPhiStrictAmbientGlobalProfileSpanCover
    unfold MultilinearSPDP.mlBlockedSpdpSubspace
    refine Submodule.span_le.mpr ?_
    intro q hq
    rcases hq with ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
    exact hgen S shift hSlen hshiftDegree hshiftVars hadm

/-- Range-row form of the assembled-profile cover.  This is the exact
canonicalization frontier left by the paper route: after off-range strict-FOB
rows vanish, every all-range source-coordinate row must land in the assembled
finite profile basis. -/
def RouteBPaperFaithfulTPhiStrictRangeRowsGlobalProfileSpanCover
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
        M n hn2 htb hns S' shift ∈
      Submodule.span ℚ
        (↑(routeBPaperFaithfulTPhiStrictGlobalProfileBasis D) :
          Set (MvPolynomial (Fin n) ℚ))


/-- A global assembled-profile span cover proves the exact strict ambient
`TΦ` rank upper bound.  This is the formal matrix-rank assembly step: once the
rows are covered by the finite union of profile-local bases, finrank is bounded
by the size of that union and hence by `#profiles * localDim`. -/
theorem routeBPaperFaithfulTPhi_strictAmbientMlRankUpper_of_globalProfileSpanCover
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns)
    (hcover : RouteBPaperFaithfulTPhiStrictAmbientGlobalProfileSpanCover D) :
    RouteBPaperFaithfulTPhiStrictAmbientMlRankUpper M n hn2 htb hns D := by
  unfold RouteBPaperFaithfulTPhiStrictAmbientMlRankUpper
  have hmono :
      Module.finrank ℚ
          (MultilinearSPDP.mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ≤
        Module.finrank ℚ
          (Submodule.span ℚ
            (↑(routeBPaperFaithfulTPhiStrictGlobalProfileBasis D) :
              Set (MvPolynomial (Fin n) ℚ))) :=
    Submodule.finrank_mono hcover
  exact hmono.trans
    ((finrank_span_finset_le_card
        (routeBPaperFaithfulTPhiStrictGlobalProfileBasis D)).trans
      (routeBPaperFaithfulTPhi_strictGlobalProfileBasis_card_le D))

/-- Paper-faithful global assembly target for strict `TΦ`.

This is the theorem shape matching the paper route: finite interface-anonymous
profiles, bounded local profile spaces, orbit/permutation rank preservation,
and one global matrix assembly bounding the *ambient* strict `TΦ` SPDP matrix.
It deliberately does not mention arbitrary projected zero-profile containment. -/
def RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns,
    RouteBPaperFaithfulTPhiStrictAmbientMlRankUpper M n hn2 htb hns D

/-- Constructor form of the paper-faithful global assembly: provide the finite
profile/orbit package and the ambient global assembled-basis cover. -/
theorem routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_globalProfileSpanCover
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns)
    (hcover : RouteBPaperFaithfulTPhiStrictAmbientGlobalProfileSpanCover D) :
    RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
      M n hn2 htb hns :=
  ⟨D, routeBPaperFaithfulTPhi_strictAmbientMlRankUpper_of_globalProfileSpanCover
    D hcover⟩

/-- Projected zero-profile containment plus a projected common-span budget gives
exactly the strict ambient `TΦ` SPDP-rank upper bound requested.

This is a safe bridge: the real content remains the full projected containment
of the ambient SPDP subspace and the finite projected common-span budget. -/
theorem routeBPaperFaithfulTPhi_strictAmbientMlRankUpper_of_projectedCommonSpanWithBudget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project (Fintype.card D.profileType * D.localDim))
    (hcontrol :
      RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project) :
    RouteBPaperFaithfulTPhiStrictAmbientMlRankUpper
      M n hn2 htb hns D := by
  unfold RouteBPaperFaithfulTPhiStrictAmbientMlRankUpper
  unfold MultilinearSPDP.mlBlockedSpdpRank
  let T : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    zeroProfileProjectedShiftSpan (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      project
  let S : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    MultilinearSPDP.mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
  have hTfinite : Module.Finite ℚ ↥T := by
    simpa [T] using
      (zeroProfileProjectedShiftSpan_finite (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project)
  have hST : S ≤ T := by
    simpa [S, T] using hcontrol
  have hmono : Module.finrank ℚ ↥S ≤ Module.finrank ℚ ↥T := by
    exact @Submodule.finrank_mono ℚ (MvPolynomial (Fin n) ℚ)
      _ _ _ _ S T hTfinite hST
  have hTbound : Module.finrank ℚ ↥T ≤ Fintype.card D.profileType * D.localDim := by
    simpa [T] using
      (zeroProfileProjectedShiftSpan_finrank_le_of_commonSpanWithBudget
        (κ := Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project hspan)
  simpa [S, T] using hmono.trans hTbound

/-- An exact SPDP-rank upper bound for the strict ambient `TΦ` polynomial closes
the matrix/global frontier.  This is the direct bridge from a genuine
matrix-level Lemma 27/31 assembly to the narrowed canonical row subspace. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalWindowMatrixRankFrontier_of_mlRankUpper
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns)
    (hrank :
      MultilinearSPDP.mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
        Fintype.card D.profileType * D.localDim) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowMatrixRankFrontier
      M n hn2 htb hns := by
  refine ⟨D, ?_⟩
  have hle :=
    Submodule.finrank_mono
      (routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalPWindowSubspace_le_mlBlockedSpdpSubspace
        M n hn2 htb hns)
  exact hle.trans hrank

/-- The same global assembly also closes the narrowed canonical matrix-rank
frontier.  This records the paper's direction of travel: ambient matrix
assembly is the load-bearing result; the narrowed canonical frontier is a
consumer, not the source of the full ambient theorem. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalWindowMatrixRankFrontier_of_strictPaperProfileOrbitGlobalAssembly
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (hassembly :
      RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowMatrixRankFrontier
      M n hn2 htb hns := by
  rcases hassembly with ⟨D, hrank⟩
  exact
    routeBPaperFaithfulTPhi_strictCanonicalWindowMatrixRankFrontier_of_mlRankUpper
      D hrank

/-- Literal bounded common-span data is a sufficient, stronger way to obtain
the matrix/global rank frontier.  This keeps the old common-span route as a
special case without claiming that arbitrary row-dependent orbit images assemble
into one common span. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalWindowMatrixRankFrontier_of_commonSpanWithBudget
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns)
    (hcommon :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCommonSpanWithBudget
        M n hn2 htb hns (Fintype.card D.profileType * D.localDim)) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowMatrixRankFrontier
      M n hn2 htb hns := by
  rcases hcommon with ⟨G, hGcard, hle⟩
  refine ⟨D, ?_⟩
  have hmono :
      Module.finrank ℚ
        (routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
          M n hn2 htb hns) ≤
        Module.finrank ℚ
          (Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))) :=
    Submodule.finrank_mono hle
  have hspan :
      Module.finrank ℚ
        (Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))) ≤ G.card :=
    finrank_span_finset_le_card G
  exact hmono.trans (hspan.trans hGcard)

/-- Literal profile-compression data is a special case of the paper-faithful
orbit-rank data, using the identity orbit equivalence. -/
noncomputable def routeBPaperFaithfulTPhi_strictOrbitRankData_of_literalProfileCompressionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowProfileCompressionData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns where
  profileType := D.profileType
  profileTypeFintype := inferInstance
  localDim := D.localDim
  localBasis := D.localBasis
  localBasis_card_le := D.localBasis_card_le
  profileBudget_le := D.profileBudget_le
  profileOfCanonicalWindow := D.profileOfCanonicalWindow
  orbitEquiv := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    exact LinearEquiv.refl ℚ (MvPolynomial (Fin n) ℚ)
  canonicalRow_mem_orbitProfileSpan := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    simpa [routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow] using
      D.canonicalRow_mem_profileSpan
        S' shift α hSlen hshiftDegree hshiftVars hadm hrow

/-- Local-monoid/profile row-cover data for strict `TΦ` range rows.

This is the load-bearing profile membership theorem surface for the global
matrix assembly: each range-source row admits an unmarked canonical coefficient
probe, and the resulting canonical window selects a bounded local profile basis
that literally spans the derivative row. -/
structure RouteBPaperFaithfulTPhiStrictRangeRowProfileCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  profileType : Type
  [profileTypeFintype : Fintype profileType]
  localDim : ℕ
  localBasis : profileType → Finset (MvPolynomial (Fin n) ℚ)
  localBasis_card_le : ∀ ρ, (localBasis ρ).card ≤ localDim
  profileBudget_le : Fintype.card profileType * localDim ≤
    withinProfileBound (Nat.log 2 n)
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      profileType
  canonicalRangeRow_mem_profileSpan :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        Submodule.span ℚ
          (↑(localBasis
            (profileOfCanonicalWindow
              (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
              hrow.1)) : Set (MvPolynomial (Fin n) ℚ))

attribute [instance] RouteBPaperFaithfulTPhiStrictRangeRowProfileCoverData.profileTypeFintype

/-! ### Corrected paper-shaped bounded-profile row-cover surface

The legacy `RouteBPaperFaithfulTPhiStrictRangeRowProfileCoverData` surface uses
`withinProfileBound` as the total `#profiles * localDim` budget.  That is too
tight for the paper's §9.3-§9.4 decomposition, where bounded profile count and
within-profile dimension multiply to `combinedProfileBound`.  The following
objects keep the actual bounded-profile shape explicit instead of collapsing
the profile index to one synthetic bucket. -/

/-- Local-monoid/profile analysis needed for strict `TΦ` range rows.

This is the missing mathematical content in paper form:
each canonical strict range row selects a bounded derivative-count profile, and
the row belongs to the actual Cook-Levin all-bounded-profile post-span for that
profile.  The exact within-profile finrank lemma then supplies finite bases for
those profile post-spans. -/
structure RouteBPaperFaithfulTPhiStrictLocalMonoidProfileAnalysis
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      BoundedProfile (Nat.log 2 n)
  canonicalRangeRow_mem_profilePostSpan :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        allBoundedProfilePostSpan
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          (cookLevinConstraintType M n hn2 htb hns)
          ((profileOfCanonicalWindow
            (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
            hrow.1).toHistogram)
  exactWithinProfile :
    CookLevinExactWithinProfileFinrankLemma M n hn2 htb hns

/-- Constructor for the actual paper-shaped local-monoid/profile analysis.

The hypothesis `hmem` is deliberately the single selected-profile row-membership
fact.  The generic Cook-Levin all-profile cover is not accepted here: the paper
step still has to explain which canonical-window profile owns the strict
ambient-gauge row. -/
noncomputable def routeBPaperFaithfulTPhi_strictLocalMonoidProfileAnalysis_of_postSpanSelection
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (profileOfCanonicalWindow :
      ∀ w : PallLean.Paper93.Window
          (RouteBPaperFaithfulTPhiStrictBlockIdx n)
          RouteBPaperFaithfulTPhiStrictLocalOp
          (Nat.log 2 n),
        (by
          letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
          exact
            PallLean.Paper93.IsCanonical
              (κ := Nat.log 2 n)
              (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
        BoundedProfile (Nat.log 2 n))
    (hmem :
      ∀ (S' : List (Fin (n / 3)))
        (shift : MvPolynomial (Fin (n / 3)) ℚ)
        (α : Fin n →₀ ℕ)
        (hSlen : S'.length = Nat.log 2 n)
        (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
        (hshiftVars :
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
            (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
        (hadm :
          SPDP.isBlockAdmissible
            (cook_levin_compilation M n hn2 htb hns).partition
            (S'.map (cookLevinStrictFOBFlatMap n)))
        (hrow :
          routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
            M n hn2 htb hns S' shift α),
        routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
            M n hn2 htb hns S' shift ∈
          allBoundedProfilePostSpan
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            (cookLevinConstraintType M n hn2 htb hns)
            ((profileOfCanonicalWindow
              (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
              hrow.1).toHistogram))
    (hexact : CookLevinExactWithinProfileFinrankLemma M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictLocalMonoidProfileAnalysis
      M n hn2 htb hns where
  profileOfCanonicalWindow := profileOfCanonicalWindow
  canonicalRangeRow_mem_profilePostSpan := hmem
  exactWithinProfile := hexact

/-- Paper-shaped range-row profile-cover data with the correct combined
profile budget. -/
structure RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  profileType : Type
  [profileTypeFintype : Fintype profileType]
  localDim : ℕ
  localBasis : profileType → Finset (MvPolynomial (Fin n) ℚ)
  localBasis_card_le : ∀ ρ, (localBasis ρ).card ≤ localDim
  profileBudget_le : Fintype.card profileType * localDim ≤
    combinedProfileBound (Nat.log 2 n)
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      profileType
  canonicalRangeRow_mem_profileSpan :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        Submodule.span ℚ
          (↑(localBasis
            (profileOfCanonicalWindow
              (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
              hrow.1)) : Set (MvPolynomial (Fin n) ℚ))

attribute [instance] RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData.profileTypeFintype

/-- Paper §9.3 local-monoid/profile analysis for strict `TΦ` range rows.

This is the direct interface-anonymous normal-form version of the row-cover
fact.  Its profiles are the finite local-monoid normal forms from canonical
windows, not the derivative-count `ProfileHistogram` used internally by the
generic Cook-Levin Leibniz expansion.  The total budget is therefore the
paper's sum-over-profiles budget `combinedProfileBound`: number of profiles
times the within-profile local dimension.
-/
structure RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileAnalysis
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  profileType : Type
  [profileTypeFintype : Fintype profileType]
  localDim : ℕ
  localBasis : profileType → Finset (MvPolynomial (Fin n) ℚ)
  localBasis_card_le : ∀ ρ, (localBasis ρ).card ≤ localDim
  profileBudget_le : Fintype.card profileType * localDim ≤
    combinedProfileBound (Nat.log 2 n)
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      profileType
  canonicalRangeRow_mem_localProfileSpan :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        Submodule.span ℚ
          (↑(localBasis
            (profileOfCanonicalWindow
              (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
              hrow.1)) : Set (MvPolynomial (Fin n) ℚ))

attribute [instance]
  RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileAnalysis.profileTypeFintype

/-- Paper §9.3--§9.4 local-monoid profile data with the two real bounds kept
separate.

This is the non-shortcut surface for the remaining strict `TΦ` row-cover
content.  The profile count bound is Lemma 29's interface-anonymous profile
compression, while the local dimension bound is Lemma 31's within-profile
span bound.  The combined budget is deliberately not an input field; it is
derived below as `profileCount * withinProfileBound = combinedProfileBound`.
-/
structure RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  profileType : Type
  [profileTypeFintype : Fintype profileType]
  profileCount_le :
    Fintype.card profileType ≤ profileCount (Nat.log 2 n)
  localDim : ℕ
  localDim_le :
    localDim ≤ withinProfileBound (Nat.log 2 n)
  localBasis : profileType → Finset (MvPolynomial (Fin n) ℚ)
  localBasis_card_le : ∀ ρ, (localBasis ρ).card ≤ localDim
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      profileType
  canonicalRangeRow_mem_localProfileSpan :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        Submodule.span ℚ
          (↑(localBasis
            (profileOfCanonicalWindow
              (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
              hrow.1)) : Set (MvPolynomial (Fin n) ℚ))

attribute [instance]
  RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileData.profileTypeFintype

/-- Realizable interface-anonymous profile subtype from paper §9.3,
Definition 21 and Lemma 29, specialized to the strict `TΦ` profile budget. -/
abbrev RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
    (LocalNormalForm : Type) [Fintype LocalNormalForm]
    [DecidableEq LocalNormalForm] (κ : ℕ) : Type :=
  { h : PallLean.Paper93.InterfaceAnonymousProfile LocalNormalForm //
      h ∈ PallLean.Paper93.RealizableProfiles LocalNormalForm κ }

/-- Paper §9.3 local-monoid profile data in its literal interface-anonymous
histogram form.

This is deliberately narrower than the generic `BoundedProfile`/post-span
bridge: profiles are realizable histograms over a finite normal-form alphabet
`Σ^{≤q}`, the profile-count field is Lemma 29, the local-dimension field is
Lemma 31, and the row-membership field is exactly the selected canonical-window
profile span. -/
structure RouteBPaperFaithfulTPhiStrictInterfaceAnonymousLocalMonoidProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  localNormalForm : Type
  [localNormalFormFintype : Fintype localNormalForm]
  [localNormalFormDecidableEq : DecidableEq localNormalForm]
  profileCount_le :
    Fintype.card
        (RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
          localNormalForm (Nat.log 2 n)) ≤
      profileCount (Nat.log 2 n)
  localDim : ℕ
  localDim_le :
    localDim ≤ withinProfileBound (Nat.log 2 n)
  localBasis :
    RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
      localNormalForm (Nat.log 2 n) →
      Finset (MvPolynomial (Fin n) ℚ)
  localBasis_card_le : ∀ ρ, (localBasis ρ).card ≤ localDim
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
        localNormalForm (Nat.log 2 n)
  canonicalRangeRow_mem_interfaceProfileSpan :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        Submodule.span ℚ
          (↑(localBasis
            (profileOfCanonicalWindow
              (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
              hrow.1)) : Set (MvPolynomial (Fin n) ℚ))

attribute [instance]
  RouteBPaperFaithfulTPhiStrictInterfaceAnonymousLocalMonoidProfileData.localNormalFormFintype
attribute [instance]
  RouteBPaperFaithfulTPhiStrictInterfaceAnonymousLocalMonoidProfileData.localNormalFormDecidableEq

/-- Lemma 29 profile count for strict interface-anonymous profiles, derived
from the actual realizable-histogram finset and a four-bin local normal-form
alphabet. -/
theorem routeBPaperFaithfulTPhi_strictInterfaceAnonymousProfiles_card_le_profileCount
    (LocalNormalForm : Type) [Fintype LocalNormalForm]
    [DecidableEq LocalNormalForm]
    (hcard : Fintype.card LocalNormalForm ≤ 4) (κ : ℕ) :
    Fintype.card
        (RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
          LocalNormalForm κ) ≤
      profileCount κ := by
  classical
  calc
    Fintype.card
        (RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
          LocalNormalForm κ)
        = (PallLean.Paper93.RealizableProfiles LocalNormalForm κ).card := by
          simp [RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles]
    _ ≤ (κ + 1) ^ Fintype.card LocalNormalForm :=
          PallLean.Paper93.profileCompression_card_bound LocalNormalForm κ
    _ ≤ (κ + 1) ^ 4 :=
          Nat.pow_le_pow_right (by omega) hcard
    _ = profileCount κ := rfl

/-- Literal interface-anonymous local-monoid profile data with the Lemma 29
profile-count bound derived from a bounded finite normal-form alphabet.

Compared with
`RouteBPaperFaithfulTPhiStrictInterfaceAnonymousLocalMonoidProfileData`, this
is the sharper paper-shaped construction surface: the profile count is no
longer supplied directly.  The remaining mathematical fields are exactly the
finite `Σ^{≤q}` alphabet bound, Lemma 31 local bases, and selected canonical
row membership. -/
structure RouteBPaperFaithfulTPhiStrictBoundedInterfaceAnonymousLocalMonoidProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  localNormalForm : Type
  [localNormalFormFintype : Fintype localNormalForm]
  [localNormalFormDecidableEq : DecidableEq localNormalForm]
  localNormalForm_card_le : Fintype.card localNormalForm ≤ 4
  localDim : ℕ
  localDim_le :
    localDim ≤ withinProfileBound (Nat.log 2 n)
  localBasis :
    RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
      localNormalForm (Nat.log 2 n) →
      Finset (MvPolynomial (Fin n) ℚ)
  localBasis_card_le : ∀ ρ, (localBasis ρ).card ≤ localDim
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
        localNormalForm (Nat.log 2 n)
  canonicalRangeRow_mem_interfaceProfileSpan :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        Submodule.span ℚ
          (↑(localBasis
            (profileOfCanonicalWindow
              (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
              hrow.1)) : Set (MvPolynomial (Fin n) ℚ))

attribute [instance]
  RouteBPaperFaithfulTPhiStrictBoundedInterfaceAnonymousLocalMonoidProfileData.localNormalFormFintype
attribute [instance]
  RouteBPaperFaithfulTPhiStrictBoundedInterfaceAnonymousLocalMonoidProfileData.localNormalFormDecidableEq

/-- Strict `TΦ` interface-anonymous local-monoid profile data with the
paper's actual Cook-Levin four-valued interface alphabet.

This is narrower than the bounded-alphabet surface: the local normal forms are
not an arbitrary finite type with a cardinality proof.  They are exactly the
`ConstraintType` alphabet used by the compiled coefficient-basis interface
spaces.  The remaining live facts are therefore the profile selector, Lemma 31
local bases for these profiles, and selected canonical row membership. -/
structure RouteBPaperFaithfulTPhiStrictConstraintTypeInterfaceProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  localDim : ℕ
  localDim_le :
    localDim ≤ withinProfileBound (Nat.log 2 n)
  localBasis :
    RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
      ConstraintType (Nat.log 2 n) →
      Finset (MvPolynomial (Fin n) ℚ)
  localBasis_card_le : ∀ ρ, (localBasis ρ).card ≤ localDim
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
        ConstraintType (Nat.log 2 n)
  canonicalRangeRow_mem_constraintTypeProfileSpan :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        Submodule.span ℚ
          (↑(localBasis
            (profileOfCanonicalWindow
              (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
              hrow.1)) : Set (MvPolynomial (Fin n) ℚ))

/-- A realizable strict interface-anonymous `ConstraintType` profile has each
coordinate bounded by its total live-interface budget. -/
theorem routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfile_component_le
    {κ : ℕ}
    (ρ : RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles ConstraintType κ)
    (τ : ConstraintType) :
    ρ.val τ ≤ κ := by
  classical
  rcases Finset.mem_image.mp ρ.property with ⟨f, hf, hρ⟩
  have hsum : (∑ σ : ConstraintType, (f σ : ℕ)) = κ := by
    exact (Finset.mem_filter.mp hf).2
  have hcoord : ρ.val τ = (f τ : ℕ) := by
    exact (congrFun hρ τ).symm
  have hle_sum : (f τ : ℕ) ≤ ∑ σ : ConstraintType, (f σ : ℕ) :=
    Finset.single_le_sum
      (fun σ _ => Nat.zero_le (f σ : ℕ)) (Finset.mem_univ τ)
  omega

/-- The bounded-profile view of a realizable `ConstraintType` interface
profile. -/
noncomputable def routeBPaperFaithfulTPhi_strictBoundedProfileOfConstraintTypeInterfaceProfile
    {κ : ℕ}
    (ρ : RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles ConstraintType κ) :
    BoundedProfile κ :=
  ⟨ρ.val,
    routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfile_component_le ρ⟩

/-- Strict `TΦ` `ConstraintType` profile-subspace data.

This is narrower than supplying finite local bases directly.  For each
realizable interface-anonymous profile, it supplies the actual profile
subspace and its within-profile dimension bound; the finite basis used
downstream is then chosen mechanically from a basis of that subspace.  The
remaining mathematical content is the canonical-window profile selector and
selected row membership in the selected profile subspace `V_h`.

This is the paper-faithful final local-monoid/profile surface.  It does not
assert that a whole Leibniz-expanded derivative row belongs to one exact
derivative-count post-span; it only asks for the selected profile subspace
containment supplied by the paper's Lemma-31 analysis. -/
structure RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  profileSubspace :
    RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
      ConstraintType (Nat.log 2 n) →
      Submodule ℚ (MvPolynomial (Fin n) ℚ)
  profileSubspace_finite :
    ∀ ρ, Module.Finite ℚ ↥(profileSubspace ρ)
  profileSubspace_finrank_le :
    ∀ ρ,
      Module.finrank ℚ ↥(profileSubspace ρ) ≤
        withinProfileBound (Nat.log 2 n)
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
        ConstraintType (Nat.log 2 n)
  canonicalRangeRow_mem_constraintTypeProfileSubspace :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        profileSubspace
          (profileOfCanonicalWindow
            (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
            hrow.1)

/-- The literal selected `V_h` row span for strict `TΦ` canonical windows.

For a fixed canonical-window profile selector, this is the subspace spanned by
all strict canonical derivative rows whose selected interface-anonymous
`ConstraintType` profile is `ρ`.  This matches the paper's `V_h` surface:
membership is by profile selection, while the nontrivial Lemma-31 content is
the separate finite-dimensional bound for each such selected span. -/
noncomputable def routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (profileOfCanonicalWindow :
      ∀ w : PallLean.Paper93.Window
          (RouteBPaperFaithfulTPhiStrictBlockIdx n)
          RouteBPaperFaithfulTPhiStrictLocalOp
          (Nat.log 2 n),
        (by
          letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
          exact
            PallLean.Paper93.IsCanonical
              (κ := Nat.log 2 n)
              (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
        RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
          ConstraintType (Nat.log 2 n))
    (ρ :
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
        ConstraintType (Nat.log 2 n)) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    { row : MvPolynomial (Fin n) ℚ |
      ∃ (S' : List (Fin (n / 3)))
        (shift : MvPolynomial (Fin (n / 3)) ℚ)
        (α : Fin n →₀ ℕ)
        (_hSlen : S'.length = Nat.log 2 n)
        (_hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
        (_hshiftVars :
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
            (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
        (_hadm :
          SPDP.isBlockAdmissible
            (cook_levin_compilation M n hn2 htb hns).partition
            (S'.map (cookLevinStrictFOBFlatMap n)))
        (hrow :
          routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
            M n hn2 htb hns S' shift α),
        profileOfCanonicalWindow
            (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
            hrow.1 = ρ ∧
          row =
            routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
              M n hn2 htb hns S' shift }

/-- A selected strict canonical derivative row belongs to its literal selected
`V_h` row span by construction. -/
theorem routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow_mem_constraintTypeCanonicalProfileRowSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (profileOfCanonicalWindow :
      ∀ w : PallLean.Paper93.Window
          (RouteBPaperFaithfulTPhiStrictBlockIdx n)
          RouteBPaperFaithfulTPhiStrictLocalOp
          (Nat.log 2 n),
        (by
          letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
          exact
            PallLean.Paper93.IsCanonical
              (κ := Nat.log 2 n)
              (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
        RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
          ConstraintType (Nat.log 2 n))
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (α : Fin n →₀ ℕ)
    (hSlen : S'.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)))
    (hrow :
      routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
        M n hn2 htb hns S' shift α) :
    routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
        M n hn2 htb hns S' shift ∈
      routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
        M n hn2 htb hns profileOfCanonicalWindow
        (profileOfCanonicalWindow
          (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
          hrow.1) := by
  classical
  refine Submodule.subset_span ?_
  refine ⟨S', shift, α, hSlen, hshiftDegree, hshiftVars, hadm, hrow, ?_, rfl⟩
  rfl

/-- Paper-shaped Lemma-31 row-span data for strict `TΦ`.

This is the exact final mathematical obligation after removing the selected
post-span over-specification: choose the canonical-window interface profile,
take `V_h` to be the row span of all rows with that selected profile, and prove
the Lemma-31 finite-dimensional bound for each selected row span.  The row
membership field of `RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData`
then follows definitionally from the span, not from any one-bucket Leibniz
collapse. -/
structure RouteBPaperFaithfulTPhiStrictCanonicalProfileRowSpanData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
        ConstraintType (Nat.log 2 n)
  canonicalProfileRowSpan_finite :
    ∀ ρ,
      Module.Finite ℚ
        ↥(routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
          M n hn2 htb hns profileOfCanonicalWindow ρ)
  canonicalProfileRowSpan_finrank_le :
    ∀ ρ,
      Module.finrank ℚ
          ↥(routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
            M n hn2 htb hns profileOfCanonicalWindow ρ) ≤
        withinProfileBound (Nat.log 2 n)

/-- The literal canonical-profile row span is contained in any selected
interface-profile basis span that contains every selected canonical row.

This is the precise Lemma-31 reduction for the row-span `V_h`: once the local
monoid/interface analysis supplies the bounded basis span for each selected
profile, the literal row span is a subspace of that finite bounded span. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalProfileRowSpan_le_interfaceProfileSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictConstraintTypeInterfaceProfileData
        M n hn2 htb hns)
    (ρ :
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
        ConstraintType (Nat.log 2 n)) :
    routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
        M n hn2 htb hns D.profileOfCanonicalWindow ρ ≤
      Submodule.span ℚ
        (↑(D.localBasis ρ) : Set (MvPolynomial (Fin n) ℚ)) := by
  classical
  unfold routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
  refine Submodule.span_le.mpr ?_
  intro row hrow
  rcases hrow with
    ⟨S', shift, α, hSlen, hshiftDegree, hshiftVars, hadm, hcanon, hρ, rfl⟩
  have hmem :=
    D.canonicalRangeRow_mem_constraintTypeProfileSpan
      S' shift α hSlen hshiftDegree hshiftVars hadm hcanon
  simpa [hρ] using hmem

/-- Interface-profile Lemma-31 data bounds the literal selected row-span
`V_h`.

This closes the row-span dimension question relative to the real paper input:
the selected local basis/span field.  No selected exact post-span collapse is
used; the proof is just `rowSpan ≤ span(localBasis h)` plus the finite basis
cardinality bound. -/
noncomputable def routeBPaperFaithfulTPhi_strictCanonicalProfileRowSpanData_of_interfaceProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictConstraintTypeInterfaceProfileData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictCanonicalProfileRowSpanData
      M n hn2 htb hns where
  profileOfCanonicalWindow := D.profileOfCanonicalWindow
  canonicalProfileRowSpan_finite := by
    intro ρ
    let U :=
      routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
        M n hn2 htb hns D.profileOfCanonicalWindow ρ
    let V := Submodule.span ℚ
      (↑(D.localBasis ρ) : Set (MvPolynomial (Fin n) ℚ))
    have hle : U ≤ V := by
      simpa [U, V] using
        routeBPaperFaithfulTPhi_strictCanonicalProfileRowSpan_le_interfaceProfileSpan
          M n hn2 htb hns D ρ
    haveI hVfin : Module.Finite ℚ ↥V := by
      exact Module.Finite.span_of_finite ℚ (Finset.finite_toSet (D.localBasis ρ))
    exact Module.Finite.of_injective
      ((Submodule.inclusion hle) : U →ₗ[ℚ] V)
      (Submodule.inclusion_injective hle)
  canonicalProfileRowSpan_finrank_le := by
    intro ρ
    let U :=
      routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
        M n hn2 htb hns D.profileOfCanonicalWindow ρ
    let V := Submodule.span ℚ
      (↑(D.localBasis ρ) : Set (MvPolynomial (Fin n) ℚ))
    have hle : U ≤ V := by
      simpa [U, V] using
        routeBPaperFaithfulTPhi_strictCanonicalProfileRowSpan_le_interfaceProfileSpan
          M n hn2 htb hns D ρ
    haveI hVfin : Module.Finite ℚ ↥V := by
      exact Module.Finite.span_of_finite ℚ (Finset.finite_toSet (D.localBasis ρ))
    haveI hUfin : Module.Finite ℚ ↥U :=
      Module.Finite.of_injective
        ((Submodule.inclusion hle) : U →ₗ[ℚ] V)
        (Submodule.inclusion_injective hle)
    calc
      Module.finrank ℚ ↥U ≤ Module.finrank ℚ ↥V :=
        Submodule.finrank_mono hle
      _ ≤ (D.localBasis ρ).card := by
        simpa [V] using finrank_span_finset_le_card (D.localBasis ρ)
      _ ≤ D.localDim := D.localBasis_card_le ρ
      _ ≤ withinProfileBound (Nat.log 2 n) := D.localDim_le


/-- Literal selected row-span data supplies explicit interface-profile local
bases by choosing a finite basis of each row-span `V_h`.

Together with
`routeBPaperFaithfulTPhi_strictCanonicalProfileRowSpanData_of_interfaceProfileData`,
this records that the interface-basis formulation and the literal row-span
formulation are equivalent packaging of the same Lemma-31 obligation.  No
post-span collapse or ambient common-span argument is used. -/
noncomputable def routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData_of_canonicalProfileRowSpanData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalProfileRowSpanData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictConstraintTypeInterfaceProfileData
      M n hn2 htb hns where
  localDim := withinProfileBound (Nat.log 2 n)
  localDim_le := le_rfl
  localBasis := fun ρ =>
    letI := D.canonicalProfileRowSpan_finite ρ
    basisImageFinset
      (routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
        M n hn2 htb hns D.profileOfCanonicalWindow ρ)
  localBasis_card_le := by
    intro ρ
    letI := D.canonicalProfileRowSpan_finite ρ
    exact
      (basisImageFinset_card_le
        (routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
          M n hn2 htb hns D.profileOfCanonicalWindow ρ)).trans
        (D.canonicalProfileRowSpan_finrank_le ρ)
  profileOfCanonicalWindow := D.profileOfCanonicalWindow
  canonicalRangeRow_mem_constraintTypeProfileSpan := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    let ρ :=
      D.profileOfCanonicalWindow
        (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α) hrow.1
    have hmem :
        routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
            M n hn2 htb hns S' shift ∈
          routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
            M n hn2 htb hns D.profileOfCanonicalWindow ρ := by
      simpa [ρ] using
        routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow_mem_constraintTypeCanonicalProfileRowSpan
          M n hn2 htb hns D.profileOfCanonicalWindow
          S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    letI := D.canonicalProfileRowSpan_finite ρ
    have hspan :
        Submodule.span ℚ
            (↑(basisImageFinset
              (routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
                M n hn2 htb hns D.profileOfCanonicalWindow ρ)) :
              Set (MvPolynomial (Fin n) ℚ)) =
          routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
            M n hn2 htb hns D.profileOfCanonicalWindow ρ := by
      letI := D.canonicalProfileRowSpan_finite ρ
      exact span_basisImageFinset_eq
        (routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
          M n hn2 htb hns D.profileOfCanonicalWindow ρ)
    change
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        Submodule.span ℚ
          (↑(basisImageFinset
            (routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
              M n hn2 htb hns D.profileOfCanonicalWindow ρ)) :
            Set (MvPolynomial (Fin n) ℚ))
    rw [hspan]
    exact hmem


/-- Paper-faithful packaging equivalence between the selected interface-profile
basis formulation and the literal selected row-span `V_h` formulation.

This is intentionally only an equivalence of final surfaces: it does not turn
ambient `iSup` membership into selected-profile membership, does not assert a
single exact post-span collapse, and does not prove the raw local-monoid
Lemma-31 compression.  It records that once the real selected `V_h` finite
bound is proved, the interface-profile basis surface and row-span surface are
interchangeable without changing the mathematical target. -/
theorem routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData_nonempty_iff_canonicalProfileRowSpanData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Nonempty
        (RouteBPaperFaithfulTPhiStrictConstraintTypeInterfaceProfileData
          M n hn2 htb hns) ↔
      Nonempty
        (RouteBPaperFaithfulTPhiStrictCanonicalProfileRowSpanData
          M n hn2 htb hns) := by
  constructor
  · intro hD
    rcases hD with ⟨D⟩
    exact
      ⟨routeBPaperFaithfulTPhi_strictCanonicalProfileRowSpanData_of_interfaceProfileData
        M n hn2 htb hns D⟩
  · intro hD
    rcases hD with ⟨D⟩
    exact
      ⟨routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData_of_canonicalProfileRowSpanData
        M n hn2 htb hns D⟩

/-- The literal selected row-span `V_h` data instantiates the final
profile-subspace surface. -/
noncomputable def routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData_of_canonicalProfileRowSpanData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalProfileRowSpanData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
      M n hn2 htb hns where
  profileSubspace :=
    routeBPaperFaithfulTPhiStrictConstraintTypeCanonicalProfileRowSpan
      M n hn2 htb hns D.profileOfCanonicalWindow
  profileSubspace_finite :=
    D.canonicalProfileRowSpan_finite
  profileSubspace_finrank_le :=
    D.canonicalProfileRowSpan_finrank_le
  profileOfCanonicalWindow :=
    D.profileOfCanonicalWindow
  canonicalRangeRow_mem_constraintTypeProfileSubspace := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    exact
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow_mem_constraintTypeCanonicalProfileRowSpan
        M n hn2 htb hns D.profileOfCanonicalWindow
        S' shift α hSlen hshiftDegree hshiftVars hadm hrow

/-- Strict `TΦ` `ConstraintType` post-span selection data.

This is a strictly stronger Cook-Levin specialization, not the final
paper-shaped obligation: it says a canonical window selects a realizable
`ConstraintType` profile, and the corresponding strict derivative row lies in
the single all-bounded derivative-count post-span for that selected profile.
The generic Leibniz decomposition only gives the supremum over exact
derivative-count post-spans, so this surface requires an additional
single-selected-profile collapse theorem.  The paper's direct logical shape is
the weaker
`RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData`, where Lemma
31 supplies a profile subspace `V_h`; this post-span surface is only accepted
when the selected profile subspace is independently known to be this concrete
post-span. -/
structure RouteBPaperFaithfulTPhiStrictConstraintTypePostSpanSelectionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  profileOfCanonicalWindow :
    ∀ w : PallLean.Paper93.Window
        (RouteBPaperFaithfulTPhiStrictBlockIdx n)
        RouteBPaperFaithfulTPhiStrictLocalOp
        (Nat.log 2 n),
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n)) w) →
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
        ConstraintType (Nat.log 2 n)
  canonicalRangeRow_mem_constraintTypePostSpan :
    ∀ (S' : List (Fin (n / 3)))
      (shift : MvPolynomial (Fin (n / 3)) ℚ)
      (α : Fin n →₀ ℕ)
      (hSlen : S'.length = Nat.log 2 n)
      (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
      (hshiftVars :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
      (hadm :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)))
      (hrow :
        routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
          M n hn2 htb hns S' shift α),
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        allBoundedProfilePostSpan
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          (cookLevinConstraintType M n hn2 htb hns)
          ((profileOfCanonicalWindow
            (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
            hrow.1).val)
  exactWithinProfile :
    CookLevinExactWithinProfileFinrankLemma M n hn2 htb hns

/-- The actual selected Cook-Levin profile post-span for a realizable strict
`ConstraintType` interface profile. -/
noncomputable def routeBPaperFaithfulTPhi_strictConstraintTypeSelectedPostSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (ρ :
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
        ConstraintType (Nat.log 2 n)) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  allBoundedProfilePostSpan
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
    (cookLevinConstraintType M n hn2 htb hns)
    ρ.val

/-- Product-form Cook-Levin rows land in the supremum over all
derivative-count profile post-spans.

This is the strongest profile-membership fact supplied directly by the
generic Leibniz decomposition: `iterDerivList` of the product expands into a
span of distributed factor derivatives, and those distributed terms are then
classified by their derivative-count profiles.  It deliberately does not pick
one selected profile; that selection is the remaining strict `TΦ`
local-monoid/profile content. -/
theorem routeBPaperFaithfulTPhi_compiledPoly_row_mem_allConstraintTypePostSpan_iSup
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ)
    (hSlen : S.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars : shift.vars ⊆ S.toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S) :
    mlProj
        (shift * SPDP.iterDerivList S
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ∈
      ⨆ h : ProfileHistogram,
        allBoundedProfilePostSpan
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          (cookLevinConstraintType M n hn2 htb hns)
          h := by
  classical
  let factors : Fin (cookLevinFactorList M n hn2 htb hns).length →
      MvPolynomial (Fin n) ℚ :=
    fun i => (cookLevinFactorList M n hn2 htb hns).get i
  have hp :
      compiledPoly (cook_levin_compilation M n hn2 htb hns) =
        Finset.univ.prod factors := by
    let factorList : List (MvPolynomial (Fin n) ℚ) :=
      cookLevinFactorList M n hn2 htb hns
    have hcompiled :
        compiledPoly (cook_levin_compilation M n hn2 htb hns) =
          factorList.prod := by
      simpa [factorList, cookLevinFactorList] using
        compiledPoly_eq_constraints_prod M n hn2 htb hns
    have hprod :
        factorList.prod =
          Finset.univ.prod (fun i : Fin factorList.length => factorList.get i) := by
      rw [← Fin.prod_univ_getElem]
      simp [List.get_eq_getElem]
    calc
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
          = factorList.prod := hcompiled
      _ = Finset.univ.prod (fun i : Fin factorList.length => factorList.get i) :=
          hprod
      _ = Finset.univ.prod factors := by
          simp [factors, factorList]
  have hrow :
      mlProj
          (shift * SPDP.iterDerivList S
            (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
    exact
      Submodule.subset_span
        ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  exact
    (mlBlockedSpdpSubspace_le_allBoundedProfilePostSpan_iSup
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      factors
      (cookLevinConstraintType M n hn2 htb hns)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) hp) hrow

/-- Logical obstruction behind the selected-profile mismatch: membership in a
supremum of subspaces does not imply membership in an arbitrary selected
summand.

The strict `TΦ` generic Leibniz theorem above therefore cannot by itself prove
the stronger `PostSpanSelectionData` field.  The paper-shaped final target is
selected `V_h` containment, where `V_h` may contain the whole normalized
canonical row, not a single exact derivative-count bucket. -/
theorem routeBPaperFaithfulTPhi_iSup_membership_does_not_imply_selected_subspace :
    ¬ (∀ (V : Bool → Submodule ℚ ℚ) (selected : Bool) (x : ℚ),
        x ∈ (⨆ b : Bool, V b) → x ∈ V selected) := by
  intro h
  let V : Bool → Submodule ℚ ℚ := fun b => if b then ⊥ else ⊤
  have hx : (1 : ℚ) ∈ (⨆ b : Bool, V b) := by
    exact (le_iSup V false) (by simp [V])
  have hselected : (1 : ℚ) ∈ V true := h V true 1 hx
  simp [V] at hselected

/-- Exact within-profile finrank supplies the dimension bound for the selected
strict `ConstraintType` profile post-span, in the optional stronger post-span
specialization. -/
theorem routeBPaperFaithfulTPhi_strictConstraintTypeSelectedPostSpan_finrank_le
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D :
      RouteBPaperFaithfulTPhiStrictConstraintTypePostSpanSelectionData
        M n hn2 htb hns)
    (ρ :
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
        ConstraintType (Nat.log 2 n)) :
    Module.finrank ℚ
        ↥(routeBPaperFaithfulTPhi_strictConstraintTypeSelectedPostSpan
          M n hn2 htb hns ρ) ≤
      withinProfileBound (Nat.log 2 n) := by
  simpa [routeBPaperFaithfulTPhi_strictConstraintTypeSelectedPostSpan] using
    D.exactWithinProfile ρ.val

/-- Optional stronger post-span selection data instantiates the paper-faithful
profile-subspace data by taking `V_h` to be the selected Cook-Levin post-span.

This is only an adapter from a stronger theorem into the real final surface;
the final proof target is `RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData`
itself. -/
noncomputable def routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData_of_postSpanSelectionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictConstraintTypePostSpanSelectionData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
      M n hn2 htb hns where
  profileSubspace :=
    routeBPaperFaithfulTPhi_strictConstraintTypeSelectedPostSpan
      M n hn2 htb hns
  profileSubspace_finite := by
    intro ρ
    dsimp [routeBPaperFaithfulTPhi_strictConstraintTypeSelectedPostSpan]
    infer_instance
  profileSubspace_finrank_le := by
    intro ρ
    exact
      routeBPaperFaithfulTPhi_strictConstraintTypeSelectedPostSpan_finrank_le D ρ
  profileOfCanonicalWindow := D.profileOfCanonicalWindow
  canonicalRangeRow_mem_constraintTypeProfileSubspace := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    simpa [routeBPaperFaithfulTPhi_strictConstraintTypeSelectedPostSpan] using
      D.canonicalRangeRow_mem_constraintTypePostSpan
        S' shift α hSlen hshiftDegree hshiftVars hadm hrow

/-- The basis selected from a strict `ConstraintType` profile subspace. -/
noncomputable def routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceBasis
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D :
      RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
        M n hn2 htb hns)
    (ρ :
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
        ConstraintType (Nat.log 2 n)) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  letI := D.profileSubspace_finite ρ
  basisImageFinset (D.profileSubspace ρ)

/-- Literal `ConstraintType` interface-profile data instantiates the
profile-subspace surface by taking `V_h` to be the span of the local Lemma-31
basis for profile `h`.

This is the paper-shaped direction: profiles remain the realizable
interface-anonymous `ConstraintType` histograms, and row membership is exactly
the selected local profile-span membership supplied by the local-monoid/profile
analysis. -/
noncomputable def routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData_of_interfaceProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictConstraintTypeInterfaceProfileData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
      M n hn2 htb hns where
  profileSubspace := fun ρ =>
    Submodule.span ℚ
      (↑(D.localBasis ρ) : Set (MvPolynomial (Fin n) ℚ))
  profileSubspace_finite := by
    intro ρ
    exact Module.Finite.span_of_finite ℚ (Finset.finite_toSet (D.localBasis ρ))
  profileSubspace_finrank_le := by
    intro ρ
    exact
      (finrank_span_finset_le_card (D.localBasis ρ)).trans
        ((D.localBasis_card_le ρ).trans D.localDim_le)
  profileOfCanonicalWindow := D.profileOfCanonicalWindow
  canonicalRangeRow_mem_constraintTypeProfileSubspace := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    simpa using
      D.canonicalRangeRow_mem_constraintTypeProfileSpan
        S' shift α hSlen hshiftDegree hshiftVars hadm hrow

/-- Profile-subspace data instantiates the stricter `ConstraintType`
interface-profile data; local bases are no longer an assumption. -/
noncomputable def routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData_of_profileSubspaceData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictConstraintTypeInterfaceProfileData
      M n hn2 htb hns where
  localDim := withinProfileBound (Nat.log 2 n)
  localDim_le := le_rfl
  localBasis :=
    routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceBasis D
  localBasis_card_le := by
    intro ρ
    letI := D.profileSubspace_finite ρ
    exact
      (basisImageFinset_card_le (D.profileSubspace ρ)).trans
        (D.profileSubspace_finrank_le ρ)
  profileOfCanonicalWindow := D.profileOfCanonicalWindow
  canonicalRangeRow_mem_constraintTypeProfileSpan := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    let ρ :=
      D.profileOfCanonicalWindow
        (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α) hrow.1
    have hmem :
        routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
            M n hn2 htb hns S' shift ∈
          D.profileSubspace ρ := by
      simpa [ρ] using
        D.canonicalRangeRow_mem_constraintTypeProfileSubspace
          S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    have hspan :
        Submodule.span ℚ
            (↑(routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceBasis
              D ρ) : Set (MvPolynomial (Fin n) ℚ)) =
          D.profileSubspace ρ := by
      letI := D.profileSubspace_finite ρ
      exact span_basisImageFinset_eq (D.profileSubspace ρ)
    change
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        Submodule.span ℚ
          (↑(routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceBasis
            D ρ) : Set (MvPolynomial (Fin n) ℚ))
    rw [hspan]
    exact hmem

/-- Optional stronger selected realizable `ConstraintType` post-span data
supplies the literal interface-profile data.

This is an adapter from the stronger exact-post-span statement into the
paper-shaped interface-profile data.  It should not be read as the final proof
surface; the paper-faithful target is the selected `V_h` containment encoded by
`RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData` or the
equivalent interface-basis form. -/
noncomputable def routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData_of_postSpanSelectionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictConstraintTypePostSpanSelectionData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictConstraintTypeInterfaceProfileData
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData_of_profileSubspaceData
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData_of_postSpanSelectionData
      M n hn2 htb hns D)

/-- The same optional stronger selected realizable `ConstraintType` post-span
data instantiates the bounded-profile local-monoid analysis by forgetting only
the realizability certificate to a bounded histogram.

This is a compatibility adapter for older bounded-profile APIs; it remains
stronger than the paper's `V_h` profile-subspace target. -/
noncomputable def routeBPaperFaithfulTPhi_strictLocalMonoidProfileAnalysis_of_constraintTypePostSpanSelectionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictConstraintTypePostSpanSelectionData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictLocalMonoidProfileAnalysis
      M n hn2 htb hns where
  profileOfCanonicalWindow := fun w hw =>
    routeBPaperFaithfulTPhi_strictBoundedProfileOfConstraintTypeInterfaceProfile
      (D.profileOfCanonicalWindow w hw)
  canonicalRangeRow_mem_profilePostSpan := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    simpa [routeBPaperFaithfulTPhi_strictBoundedProfileOfConstraintTypeInterfaceProfile,
      BoundedProfile.toHistogram] using
      D.canonicalRangeRow_mem_constraintTypePostSpan
        S' shift α hSlen hshiftDegree hshiftVars hadm hrow
  exactWithinProfile := D.exactWithinProfile

/-- The actual Cook-Levin interface alphabet has the four profile bins used by
paper §9 Lemma 29. -/
theorem routeBPaperFaithfulTPhi_strictConstraintType_card_le_four :
    Fintype.card ConstraintType ≤ 4 := by
  simpa [SymmetricPowerBound.constraintType_card]

/-- The concrete `ConstraintType` profile surface instantiates the bounded
interface-anonymous surface without any arbitrary alphabet choice. -/
noncomputable def routeBPaperFaithfulTPhi_strictBoundedInterfaceAnonymousLocalMonoidProfileData_of_constraintTypeInterfaceProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictConstraintTypeInterfaceProfileData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictBoundedInterfaceAnonymousLocalMonoidProfileData
      M n hn2 htb hns where
  localNormalForm := ConstraintType
  localNormalFormFintype := inferInstance
  localNormalFormDecidableEq := inferInstance
  localNormalForm_card_le :=
    routeBPaperFaithfulTPhi_strictConstraintType_card_le_four
  localDim := D.localDim
  localDim_le := D.localDim_le
  localBasis := D.localBasis
  localBasis_card_le := D.localBasis_card_le
  profileOfCanonicalWindow := D.profileOfCanonicalWindow
  canonicalRangeRow_mem_interfaceProfileSpan :=
    D.canonicalRangeRow_mem_constraintTypeProfileSpan

/-- Bounded finite-normal-form alphabet data instantiates the literal
interface-anonymous profile data, with Lemma 29 deriving `profileCount_le`. -/
noncomputable def routeBPaperFaithfulTPhi_strictInterfaceAnonymousLocalMonoidProfileData_of_boundedInterfaceAnonymousLocalMonoidProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictBoundedInterfaceAnonymousLocalMonoidProfileData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictInterfaceAnonymousLocalMonoidProfileData
      M n hn2 htb hns where
  localNormalForm := D.localNormalForm
  localNormalFormFintype := inferInstance
  localNormalFormDecidableEq := inferInstance
  profileCount_le :=
    routeBPaperFaithfulTPhi_strictInterfaceAnonymousProfiles_card_le_profileCount
      D.localNormalForm D.localNormalForm_card_le (Nat.log 2 n)
  localDim := D.localDim
  localDim_le := D.localDim_le
  localBasis := D.localBasis
  localBasis_card_le := D.localBasis_card_le
  profileOfCanonicalWindow := D.profileOfCanonicalWindow
  canonicalRangeRow_mem_interfaceProfileSpan :=
    D.canonicalRangeRow_mem_interfaceProfileSpan

/-- Literal interface-anonymous local-monoid data instantiates the existing
separated paper §9.3--§9.4 profile data. -/
noncomputable def routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData_of_interfaceAnonymousLocalMonoidProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousLocalMonoidProfileData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileData
      M n hn2 htb hns where
  profileType :=
    RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
      D.localNormalForm (Nat.log 2 n)
  profileTypeFintype := inferInstance
  profileCount_le := D.profileCount_le
  localDim := D.localDim
  localDim_le := D.localDim_le
  localBasis := D.localBasis
  localBasis_card_le := D.localBasis_card_le
  profileOfCanonicalWindow := D.profileOfCanonicalWindow
  canonicalRangeRow_mem_localProfileSpan :=
    D.canonicalRangeRow_mem_interfaceProfileSpan

/-- The separated paper bounds compose to the corrected combined budget. -/
theorem routeBPaperFaithfulTPhi_strictLocalMonoidProfileData_budget_le
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileData
        M n hn2 htb hns) :
    Fintype.card D.profileType * D.localDim ≤
      combinedProfileBound (Nat.log 2 n) := by
  calc
    Fintype.card D.profileType * D.localDim
        ≤ profileCount (Nat.log 2 n) * withinProfileBound (Nat.log 2 n) :=
      Nat.mul_le_mul D.profileCount_le D.localDim_le
    _ = combinedProfileBound (Nat.log 2 n) := rfl

/-- Constructor from the paper's separated Lemma 29/Lemma 31 data to the
existing final analysis object. -/
noncomputable def routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileAnalysis_of_data
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileAnalysis
      M n hn2 htb hns where
  profileType := D.profileType
  profileTypeFintype := inferInstance
  localDim := D.localDim
  localBasis := D.localBasis
  localBasis_card_le := D.localBasis_card_le
  profileBudget_le :=
    routeBPaperFaithfulTPhi_strictLocalMonoidProfileData_budget_le D
  profileOfCanonicalWindow := D.profileOfCanonicalWindow
  canonicalRangeRow_mem_localProfileSpan :=
    D.canonicalRangeRow_mem_localProfileSpan

/-- The actual local-monoid/profile analysis instantiates the corrected
paper-shaped range-row cover data without passing through a one-profile
classifier or a broad projected row identity. -/
noncomputable def routeBPaperFaithfulTPhi_strictPaperRangeRowProfileCoverData_of_localMonoidProfileCover
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileAnalysis
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
      M n hn2 htb hns where
  profileType := A.profileType
  profileTypeFintype := inferInstance
  localDim := A.localDim
  localBasis := A.localBasis
  localBasis_card_le := A.localBasis_card_le
  profileBudget_le := A.profileBudget_le
  profileOfCanonicalWindow := A.profileOfCanonicalWindow
  canonicalRangeRow_mem_profileSpan := A.canonicalRangeRow_mem_localProfileSpan

/-- The finite basis chosen for one bounded profile from the exact
within-profile Cook-Levin lemma. -/
noncomputable def routeBPaperFaithfulTPhi_strictProfileBasisOfLocalMonoidAnalysis
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (A : RouteBPaperFaithfulTPhiStrictLocalMonoidProfileAnalysis
      M n hn2 htb hns)
    (bp : BoundedProfile (Nat.log 2 n)) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  Classical.choose
    (cookLevinAllBoundedProfileCommonSpanAtProfile_of_exactWithinProfileFinrankLemma
      M n hn2 htb hns A.exactWithinProfile bp.toHistogram)

/-- Local-monoid/profile analysis instantiates the corrected bounded-profile
range-row cover data. -/
noncomputable def routeBPaperFaithfulTPhi_strictPaperRangeRowProfileCoverData_of_localMonoidProfileAnalysis
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : RouteBPaperFaithfulTPhiStrictLocalMonoidProfileAnalysis
      M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
      M n hn2 htb hns where
  profileType := BoundedProfile (Nat.log 2 n)
  profileTypeFintype := inferInstance
  localDim := withinProfileBound (Nat.log 2 n)
  localBasis := routeBPaperFaithfulTPhi_strictProfileBasisOfLocalMonoidAnalysis A
  localBasis_card_le := by
    intro bp
    unfold routeBPaperFaithfulTPhi_strictProfileBasisOfLocalMonoidAnalysis
    exact
      (Classical.choose_spec
        (cookLevinAllBoundedProfileCommonSpanAtProfile_of_exactWithinProfileFinrankLemma
          M n hn2 htb hns A.exactWithinProfile bp.toHistogram)).1
  profileBudget_le := by
    calc
      Fintype.card (BoundedProfile (Nat.log 2 n)) *
          withinProfileBound (Nat.log 2 n)
          ≤ profileCount (Nat.log 2 n) * withinProfileBound (Nat.log 2 n) :=
            Nat.mul_le_mul_right _ (boundedProfile_card_le_profileCount (Nat.log 2 n))
      _ = combinedProfileBound (Nat.log 2 n) := rfl
  profileOfCanonicalWindow := A.profileOfCanonicalWindow
  canonicalRangeRow_mem_profileSpan := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    let bp : BoundedProfile (Nat.log 2 n) :=
      A.profileOfCanonicalWindow
        (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α) hrow.1
    have hmemPost :
        routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
            M n hn2 htb hns S' shift ∈
          allBoundedProfilePostSpan
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            (cookLevinConstraintType M n hn2 htb hns)
            bp.toHistogram := by
      simpa [bp] using
        A.canonicalRangeRow_mem_profilePostSpan
          S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    have hspan :
        allBoundedProfilePostSpan
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            (cookLevinConstraintType M n hn2 htb hns)
            bp.toHistogram ≤
          Submodule.span ℚ
            (↑(routeBPaperFaithfulTPhi_strictProfileBasisOfLocalMonoidAnalysis A bp) :
              Set (MvPolynomial (Fin n) ℚ)) :=
      (Classical.choose_spec
        (cookLevinAllBoundedProfileCommonSpanAtProfile_of_exactWithinProfileFinrankLemma
          M n hn2 htb hns A.exactWithinProfile bp.toHistogram)).2
    simpa [bp, routeBPaperFaithfulTPhi_strictProfileBasisOfLocalMonoidAnalysis] using
      hspan hmemPost

/-- The local-monoid/profile analysis instantiates the separated paper
Lemma 29/Lemma 31 data.

This is the paper-shaped close of the row-cover frontier: profiles are the
bounded derivative-count profiles selected by canonical windows, the profile
count bound is kept as its own Lemma 29 field, the within-profile dimension is
kept as its own Lemma 31 field, and row membership is obtained by first landing
in the matching Cook-Levin profile post-span and then using the exact
within-profile finite-basis lemma. -/
noncomputable def routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData_of_localMonoidProfileAnalysis
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : RouteBPaperFaithfulTPhiStrictLocalMonoidProfileAnalysis
      M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileData
      M n hn2 htb hns where
  profileType := BoundedProfile (Nat.log 2 n)
  profileTypeFintype := inferInstance
  profileCount_le := boundedProfile_card_le_profileCount (Nat.log 2 n)
  localDim := withinProfileBound (Nat.log 2 n)
  localDim_le := le_rfl
  localBasis := routeBPaperFaithfulTPhi_strictProfileBasisOfLocalMonoidAnalysis A
  localBasis_card_le := by
    intro bp
    unfold routeBPaperFaithfulTPhi_strictProfileBasisOfLocalMonoidAnalysis
    exact
      (Classical.choose_spec
        (cookLevinAllBoundedProfileCommonSpanAtProfile_of_exactWithinProfileFinrankLemma
          M n hn2 htb hns A.exactWithinProfile bp.toHistogram)).1
  profileOfCanonicalWindow := A.profileOfCanonicalWindow
  canonicalRangeRow_mem_localProfileSpan := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    let bp : BoundedProfile (Nat.log 2 n) :=
      A.profileOfCanonicalWindow
        (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α) hrow.1
    have hmemPost :
        routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
            M n hn2 htb hns S' shift ∈
          allBoundedProfilePostSpan
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            (cookLevinConstraintType M n hn2 htb hns)
            bp.toHistogram := by
      simpa [bp] using
        A.canonicalRangeRow_mem_profilePostSpan
          S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    have hspan :
        allBoundedProfilePostSpan
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            (cookLevinConstraintType M n hn2 htb hns)
            bp.toHistogram ≤
          Submodule.span ℚ
            (↑(routeBPaperFaithfulTPhi_strictProfileBasisOfLocalMonoidAnalysis A bp) :
              Set (MvPolynomial (Fin n) ℚ)) :=
      (Classical.choose_spec
        (cookLevinAllBoundedProfileCommonSpanAtProfile_of_exactWithinProfileFinrankLemma
          M n hn2 htb hns A.exactWithinProfile bp.toHistogram)).2
    simpa [bp, routeBPaperFaithfulTPhi_strictProfileBasisOfLocalMonoidAnalysis] using
      hspan hmemPost

/-- Global basis for the corrected paper-shaped range-row cover. -/
noncomputable def routeBPaperFaithfulTPhiStrictPaperGlobalProfileBasis
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
      M n hn2 htb hns) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  Finset.univ.biUnion D.localBasis

/-- Corrected paper-shaped strict range-row global profile-span cover. -/
def RouteBPaperFaithfulTPhiStrictPaperRangeRowsGlobalProfileSpanCover
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
      M n hn2 htb hns) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
        M n hn2 htb hns S' shift ∈
      Submodule.span ℚ
        (↑(routeBPaperFaithfulTPhiStrictPaperGlobalProfileBasis D) :
          Set (MvPolynomial (Fin n) ℚ))

/-- Corrected local-monoid/profile row-cover theorem with bounded profiles and
the combined profile budget. -/
theorem routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover_of_paperRangeRowProfileCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperRangeRowsGlobalProfileSpanCover D := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  let i0 : Fin n := ⟨0, by omega⟩
  let α : Fin n →₀ ℕ := Finsupp.single i0 1
  have hunmarked :
      ¬ routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff
        (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α) := by
    simpa [α] using
      routeBPaperFaithfulTPhiStrictRawWindow_singleton_unmarked
        n S' shift i0
  have hcan :
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n))
            (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)) := by
    letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
    exact
      routeBPaperFaithfulTPhiStrictCanWindow_eq_self_of_unmarked
        (n := n) (κ := Nat.log 2 n) hunmarked
  have hrow :
      routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
        M n hn2 htb hns S' shift α := by
    exact ⟨hcan, hunmarked⟩
  let ρ :=
    D.profileOfCanonicalWindow
      (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α) hrow.1
  have hmem :
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        Submodule.span ℚ
          (↑(D.localBasis ρ) : Set (MvPolynomial (Fin n) ℚ)) := by
    simpa [ρ] using
      D.canonicalRangeRow_mem_profileSpan
        S' shift α hSlen hshiftDegree hshiftVars hadm hrow
  have hsubset :
      (↑(D.localBasis ρ) : Set (MvPolynomial (Fin n) ℚ)) ⊆
        (↑(routeBPaperFaithfulTPhiStrictPaperGlobalProfileBasis D) :
          Set (MvPolynomial (Fin n) ℚ)) := by
    intro q hq
    change q ∈ routeBPaperFaithfulTPhiStrictPaperGlobalProfileBasis D
    unfold routeBPaperFaithfulTPhiStrictPaperGlobalProfileBasis
    exact Finset.mem_biUnion.mpr ⟨ρ, Finset.mem_univ ρ, hq⟩
  exact (Submodule.span_mono hsubset) hmem

/-- Local-monoid/profile analysis gives the corrected paper-shaped data and
range-row cover in one step. -/
theorem routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover_of_localMonoidProfileAnalysis
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : RouteBPaperFaithfulTPhiStrictLocalMonoidProfileAnalysis
      M n hn2 htb hns) :
    ∃ D : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
        M n hn2 htb hns,
      RouteBPaperFaithfulTPhiStrictPaperRangeRowsGlobalProfileSpanCover D := by
  let D :=
    routeBPaperFaithfulTPhi_strictPaperRangeRowProfileCoverData_of_localMonoidProfileAnalysis
      M n hn2 htb hns A
  exact
    ⟨D,
      routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover_of_paperRangeRowProfileCoverData
        M n hn2 htb hns D⟩

/-- Local-monoid/profile analysis gives the corrected strict range-row global
profile-span cover.  This is the paper-shaped close-out for the row-cover
step: canonical windows select finite normal-form profiles, each row lands in
the selected profile span, then the global basis is the finite union over
profiles. -/
theorem routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover_of_localMonoidProfileCover
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileAnalysis
        M n hn2 htb hns) :
    ∃ D : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
        M n hn2 htb hns,
      RouteBPaperFaithfulTPhiStrictPaperRangeRowsGlobalProfileSpanCover D := by
  let D :=
    routeBPaperFaithfulTPhi_strictPaperRangeRowProfileCoverData_of_localMonoidProfileCover
      M n hn2 htb hns A
  exact
    ⟨D,
      routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover_of_paperRangeRowProfileCoverData
        M n hn2 htb hns D⟩

/-- Paper-shaped range-row cover from separated local-monoid profile data. -/
theorem routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover_of_localMonoidProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileData
        M n hn2 htb hns) :
    ∃ C : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
        M n hn2 htb hns,
      RouteBPaperFaithfulTPhiStrictPaperRangeRowsGlobalProfileSpanCover C :=
  routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover_of_localMonoidProfileCover
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileAnalysis_of_data
      M n hn2 htb hns D)

/-- Literal interface-anonymous local-monoid data gives the actual
paper-shaped strict range-row cover by the existing global assembly. -/
theorem routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover_of_interfaceAnonymousLocalMonoidProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictInterfaceAnonymousLocalMonoidProfileData
        M n hn2 htb hns) :
    ∃ C : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
        M n hn2 htb hns,
      RouteBPaperFaithfulTPhiStrictPaperRangeRowsGlobalProfileSpanCover C :=
  routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover_of_localMonoidProfileData
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData_of_interfaceAnonymousLocalMonoidProfileData
      M n hn2 htb hns D)

/-- Cardinality bound for the corrected paper-shaped assembled profile basis. -/
theorem routeBPaperFaithfulTPhi_strictPaperGlobalProfileBasis_card_le
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
      M n hn2 htb hns) :
    (routeBPaperFaithfulTPhiStrictPaperGlobalProfileBasis D).card ≤
      Fintype.card D.profileType * D.localDim := by
  classical
  unfold routeBPaperFaithfulTPhiStrictPaperGlobalProfileBasis
  calc
    (Finset.univ.biUnion D.localBasis).card ≤
        ∑ ρ : D.profileType, (D.localBasis ρ).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ρ : D.profileType, D.localDim := by
      exact Finset.sum_le_sum (fun ρ _ => D.localBasis_card_le ρ)
    _ = Fintype.card D.profileType * D.localDim := by
      simp [Finset.sum_const, Finset.card_univ, mul_comm]

/-- The existing strict local-monoid/profile classifier instantiates the
range-row profile-cover data needed by global assembly.

The classifier supplies the genuine local type for each row and membership in
that type's local span.  This constructor packages those local spans into one
assembled profile basis for the row-cover data: the window profile type is the
single assembled profile, and its basis is the union of the classifier's local
profile bases. -/
noncomputable def routeBPaperFaithfulTPhi_strictRangeRowProfileCoverData_of_classifier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C :
      RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifier
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictRangeRowProfileCoverData
      M n hn2 htb hns where
  profileType := PUnit
  profileTypeFintype := inferInstance
  localDim := withinProfileBound (Nat.log 2 n)
  localBasis := fun _ => zeroProfileLocalTypeGlobalBasis C.alphabet
  localBasis_card_le := fun _ =>
    zeroProfileLocalTypeGlobalBasis_card_le_withinProfileBound C.alphabet
  profileBudget_le := by simp
  profileOfCanonicalWindow := by
    intro _w _hw
    exact PUnit.unit
  canonicalRangeRow_mem_profileSpan := by
    classical
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    have hlocal :
        routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
            M n hn2 htb hns S' shift ∈
          zeroProfileLocalTypeSpace C.alphabet
            (C.rowType S' shift hSlen hshiftDegree hshiftVars hadm) := by
      simpa [routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow] using
        C.row_mem_typeSpace S' shift hSlen hshiftDegree hshiftVars hadm
    simpa [zeroProfileLocalTypeGlobalBasis] using
      (zeroProfileLocalTypeSpace_le_globalBasis_span C.alphabet
        (C.rowType S' shift hSlen hshiftDegree hshiftVars hadm)) hlocal

/-- Classifier-obligation form: the local-monoid/profile row classifier
constructs the range-row profile-cover data. -/
theorem routeBPaperFaithfulTPhi_strictRangeRowProfileCoverData_of_classifierObligation
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hclassifier :
      RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
        M n hn2 htb hns) :
    Nonempty
      (RouteBPaperFaithfulTPhiStrictRangeRowProfileCoverData
        M n hn2 htb hns) := by
  rcases hclassifier with ⟨C⟩
  exact
    ⟨routeBPaperFaithfulTPhi_strictRangeRowProfileCoverData_of_classifier
      M n hn2 htb hns C⟩

/-- Range-row profile-cover data is a special case of the existing orbit-rank
package, by using the identity orbit equivalence and restricting its membership
field to the narrower paper-faithful canonical rows. -/
noncomputable def routeBPaperFaithfulTPhi_strictOrbitRankData_of_rangeRowProfileCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictRangeRowProfileCoverData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns where
  profileType := D.profileType
  profileTypeFintype := inferInstance
  localDim := D.localDim
  localBasis := D.localBasis
  localBasis_card_le := D.localBasis_card_le
  profileBudget_le := D.profileBudget_le
  profileOfCanonicalWindow := D.profileOfCanonicalWindow
  orbitEquiv := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    exact LinearEquiv.refl ℚ (MvPolynomial (Fin n) ℚ)
  canonicalRow_mem_orbitProfileSpan := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    simpa [routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow] using
      D.canonicalRangeRow_mem_profileSpan
        S' shift α hSlen hshiftDegree hshiftVars hadm hrow.1

/-- The local-monoid/profile row-cover theorem for strict `TΦ` range rows.

The input data is the paper-shaped row fact: canonical-window profiles, bounded
local profile bases, and local span membership for every canonical profile-cover
row.  The proof only chooses a fixed unmarked coefficient representative in
order to select the canonical profile for the source-coordinate row; the actual
row membership comes from `canonicalRangeRow_mem_profileSpan`, and the final
step is the paper's sum-over-profiles assembly into the finite global basis. -/
theorem routeBPaperFaithfulTPhi_strictRangeRowsGlobalProfileSpanCover_of_rangeRowProfileCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictRangeRowProfileCoverData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictRangeRowsGlobalProfileSpanCover
      (routeBPaperFaithfulTPhi_strictOrbitRankData_of_rangeRowProfileCoverData
        M n hn2 htb hns D) := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  let i0 : Fin n := ⟨0, by omega⟩
  let α : Fin n →₀ ℕ := Finsupp.single i0 1
  have hunmarked :
      ¬ routeBPaperFaithfulTPhiStrictWindowHasMarkedCoeff
        (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α) := by
    simpa [α] using
      routeBPaperFaithfulTPhiStrictRawWindow_singleton_unmarked
        n S' shift i0
  have hcan :
      (by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n)
            (routeBPaperFaithfulTPhiStrictCanonScheme n (Nat.log 2 n))
            (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)) := by
    letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
    exact
      routeBPaperFaithfulTPhiStrictCanWindow_eq_self_of_unmarked
        (n := n) (κ := Nat.log 2 n) hunmarked
  have hrow :
      routeBPaperFaithfulTPhiStrictProfileCoverCanonicalRowFamily
        M n hn2 htb hns S' shift α := by
    exact ⟨hcan, hunmarked⟩
  have hmem :
      routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow
          M n hn2 htb hns S' shift ∈
        Submodule.span ℚ
          (↑(D.localBasis
            (D.profileOfCanonicalWindow
              (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
              hrow.1)) : Set (MvPolynomial (Fin n) ℚ)) :=
    D.canonicalRangeRow_mem_profileSpan
      S' shift α hSlen hshiftDegree hshiftVars hadm hrow
  let D' :=
    routeBPaperFaithfulTPhi_strictOrbitRankData_of_rangeRowProfileCoverData
      M n hn2 htb hns D
  let ρ :=
    D.profileOfCanonicalWindow
      (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α) hrow.1
  have hsubset :
      (↑(D.localBasis ρ) : Set (MvPolynomial (Fin n) ℚ)) ⊆
        (↑(routeBPaperFaithfulTPhiStrictGlobalProfileBasis D') :
          Set (MvPolynomial (Fin n) ℚ)) := by
    intro q hq
    change q ∈ routeBPaperFaithfulTPhiStrictGlobalProfileBasis D'
    unfold routeBPaperFaithfulTPhiStrictGlobalProfileBasis
    exact Finset.mem_biUnion.mpr ⟨ρ, Finset.mem_univ ρ, hq⟩
  exact (Submodule.span_mono hsubset) hmem

/-- Exact paper-shaped construction requested by the global assembly step.

Given the local-monoid/profile range-row membership theorem, construct the
canonical-window orbit/rank data `D` and prove the actual strict range-row
global profile-span cover for that same `D`.  This is intentionally the live
row-cover surface, not a projected identity or broad common-span shortcut. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitRankData_exists_rangeRowsGlobalProfileSpanCover_of_rangeRowProfileCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictRangeRowProfileCoverData
        M n hn2 htb hns) :
    ∃ D' : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
        M n hn2 htb hns,
      RouteBPaperFaithfulTPhiStrictRangeRowsGlobalProfileSpanCover D' := by
  refine
    ⟨routeBPaperFaithfulTPhi_strictOrbitRankData_of_rangeRowProfileCoverData
        M n hn2 htb hns D, ?_⟩
  exact
    routeBPaperFaithfulTPhi_strictRangeRowsGlobalProfileSpanCover_of_rangeRowProfileCoverData
      M n hn2 htb hns D

/-- Literal profile-compression data gives an orbit-rank frontier by taking the
identity orbit equivalence. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitRankFrontier_of_literalProfileCompression
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowProfileCompressionData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankFrontier
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitRankFrontier_of_data
    (routeBPaperFaithfulTPhi_strictOrbitRankData_of_literalProfileCompressionData
      M n hn2 htb hns D)

/-- Literal profile-compression data gives the canonical orbit-rank budget. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitRankBoundWithBudget_of_literalProfileCompression
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowProfileCompressionData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankBoundWithBudget
      M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) :=
  routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitRankBoundWithBudget_of_data
    (routeBPaperFaithfulTPhi_strictOrbitRankData_of_literalProfileCompressionData
      M n hn2 htb hns D)

/-- The concrete canonical-window/profile data gives the `ZeroProfileLocalTypeAlphabet`
needed by the downstream common-span API. -/
noncomputable def RouteBPaperFaithfulTPhiStrictCanonicalWindowProfileCompressionData.toLocalTypeAlphabet
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowProfileCompressionData
        M n hn2 htb hns) :
    ZeroProfileLocalTypeAlphabet n (Nat.log 2 n) where
  type := D.profileType
  typeFintype := inferInstance
  localDim := D.localDim
  localBasis := D.localBasis
  localBasis_card_le := D.localBasis_card_le
  profileSymmetricPowerBudget_le := D.profileBudget_le

/-- The concrete canonical-window/profile data instantiates the paper-faithful
local-profile compression surface. -/
noncomputable def routeBPaperFaithfulTPhi_strictCanonicalWindowProfileCompression_to_localProfileCompression
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowProfileCompressionData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalLocalProfileCompression
      M n hn2 htb hns where
  alphabet := D.toLocalTypeAlphabet
  profileOfCanonicalRow := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    exact
      D.profileOfCanonicalWindow
        (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
        hrow.1.1
  canonicalRow_mem_profileSpace := by
    intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    exact
      D.canonicalRow_mem_profileSpan
        S' shift α hSlen hshiftDegree hshiftVars hadm hrow

/-- The paper-local-profile-compression surface is exactly a direct narrowed
classifier.  This bridge is intentionally definition-level: the mathematical
content is the canonical row membership in the local profile space, not any
residual identity with zero-profile base-product rows. -/
noncomputable def routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifier_of_localProfileCompression
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalLocalProfileCompression
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileClassifier
      M n hn2 htb hns where
  alphabet := C.alphabet
  rowType := C.profileOfCanonicalRow
  row_mem_typeSpace := C.canonicalRow_mem_profileSpace

/-- A direct narrow classifier proves the narrowed profile/subspace frontier. -/
theorem routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileSubspaceContainment_of_classifier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileClassifier
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileSubspaceContainment
      M n hn2 htb hns := by
  classical
  refine ⟨C.alphabet, ?_⟩
  exact
    (routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalControlledByProfileSubspace_iff_generatorReduction
      M n hn2 htb hns C.alphabet).mpr
      (fun S' shift α hSlen hshiftDegree hshiftVars hadm hrow =>
        (zeroProfileLocalTypeSpace_le_compressedProfileSpan C.alphabet
          (C.rowType S' shift α hSlen hshiftDegree hshiftVars hadm hrow))
          (C.row_mem_typeSpace S' shift α hSlen hshiftDegree hshiftVars hadm hrow))


/-- A bounded common span for the narrowed row subspace can be repackaged as a
one-type narrow classifier.  This is the reverse direction for the clean
frontier: once the narrowed canonical rows are compressed into a bounded span,
they automatically form a local-profile classifier without mentioning the broad
residual/row-identity surfaces. -/
noncomputable def routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifier_of_commonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcommon :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCommonSpanWithBudget
        M n hn2 htb hns (withinProfileBound (Nat.log 2 n))) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileClassifier
      M n hn2 htb hns := by
  classical
  let G : Finset (MvPolynomial (Fin n) ℚ) := Classical.choose hcommon
  have hspec := Classical.choose_spec hcommon
  let hG_card : G.card ≤ withinProfileBound (Nat.log 2 n) := hspec.1
  let hG_span :
      routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
          M n hn2 htb hns ≤
        Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) := hspec.2
  refine
    { alphabet :=
        { type := PUnit
          typeFintype := inferInstance
          localDim := withinProfileBound (Nat.log 2 n)
          localBasis := fun _ => G
          localBasis_card_le := fun _ => hG_card
          profileSymmetricPowerBudget_le := by simp }
      rowType := ?_
      row_mem_typeSpace := ?_ }
  · intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    exact PUnit.unit
  · intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    apply hG_span
    unfold routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
    exact Submodule.subset_span
      ⟨S', shift, α, hSlen, hshiftDegree, hshiftVars, hadm, hrow, rfl⟩

/-- Classifier-obligation form of the remaining narrowed profile frontier. -/
def RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileClassifierObligation
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  Nonempty
    (RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileClassifier
      M n hn2 htb hns)


/-- Bounded common-span form gives the narrowed classifier-obligation form. -/
theorem routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifierObligation_of_commonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcommon :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCommonSpanWithBudget
        M n hn2 htb hns (withinProfileBound (Nat.log 2 n))) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileClassifierObligation
      M n hn2 htb hns :=
  ⟨routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifier_of_commonSpanWithBudget
      M n hn2 htb hns hcommon⟩

/-- The remaining classifier obligation closes the narrowed profile/subspace
frontier and hence the narrowed bounded common-span consumer. -/
theorem routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalCommonSpanWithBudget_of_classifierObligation
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hclassifier :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileClassifierObligation
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCommonSpanWithBudget
      M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) := by
  rcases hclassifier with ⟨C⟩
  rcases routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileSubspaceContainment_of_classifier
      M n hn2 htb hns C with ⟨A, hA⟩
  exact
    routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalCommonSpanWithBudget_of_profileSubspace
      M n hn2 htb hns A hA

/-- Paper-faithful local profile compression proves the narrowed classifier
obligation. -/
theorem routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifierObligation_of_localProfileCompression
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalLocalProfileCompression
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileClassifierObligation
      M n hn2 htb hns :=
  ⟨routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifier_of_localProfileCompression
      M n hn2 htb hns C⟩

/-- Paper-faithful local profile compression closes the narrowed bounded
common-span consumer. -/
theorem routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalCommonSpanWithBudget_of_localProfileCompression
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalLocalProfileCompression
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCommonSpanWithBudget
      M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) :=
  routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalCommonSpanWithBudget_of_classifierObligation
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifierObligation_of_localProfileCompression
      M n hn2 htb hns C)


/-- A narrowed bounded common span instantiates the concrete canonical-window
profile-compression data with a one-profile alphabet.

This is the explicit data-level constructor: the profile alphabet has one
profile, its local basis is the bounded spanning family `G`, the budget is
`G.card ≤ withinProfileBound`, and row membership is obtained by the narrowed
canonical P-window subspace inclusion.  It is useful as a sanity check and as a
bridge from any independently proved paper Lemma-31/common-span theorem into
the canonical-window profile data surface. -/
noncomputable def routeBPaperFaithfulTPhi_strictCanonicalWindowProfileCompressionData_of_commonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcommon :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCommonSpanWithBudget
        M n hn2 htb hns (withinProfileBound (Nat.log 2 n))) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowProfileCompressionData
      M n hn2 htb hns := by
  classical
  let G : Finset (MvPolynomial (Fin n) ℚ) := Classical.choose hcommon
  have hspec := Classical.choose_spec hcommon
  let hG_card : G.card ≤ withinProfileBound (Nat.log 2 n) := hspec.1
  let hG_span :
      routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
          M n hn2 htb hns ≤
        Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) := hspec.2
  refine
    { profileType := PUnit
      profileTypeFintype := inferInstance
      localDim := withinProfileBound (Nat.log 2 n)
      localBasis := fun _ => G
      localBasis_card_le := fun _ => hG_card
      profileBudget_le := by simp
      profileOfCanonicalWindow := ?_
      canonicalRow_mem_profileSpan := ?_ }
  · intro w hw
    exact PUnit.unit
  · intro S' shift α hSlen hshiftDegree hshiftVars hadm hrow
    apply hG_span
    unfold routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
    exact Submodule.subset_span
      ⟨S', shift, α, hSlen, hshiftDegree, hshiftVars, hadm, hrow, rfl⟩

/-- The concrete canonical-window profile data and the narrowed bounded common
span package are equivalent frontiers.  The reverse direction is the one-profile
instantiation above; the forward direction uses the already established local
profile-compression bridge. -/
theorem routeBPaperFaithfulTPhi_strictCanonicalWindowProfileCompressionData_iff_commonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Nonempty
        (RouteBPaperFaithfulTPhiStrictCanonicalWindowProfileCompressionData
          M n hn2 htb hns) ↔
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCommonSpanWithBudget
        M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) := by
  constructor
  · intro hD
    rcases hD with ⟨D⟩
    exact
      routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalCommonSpanWithBudget_of_localProfileCompression
        M n hn2 htb hns
        (routeBPaperFaithfulTPhi_strictCanonicalWindowProfileCompression_to_localProfileCompression
          M n hn2 htb hns D)
  · intro hcommon
    exact
      ⟨routeBPaperFaithfulTPhi_strictCanonicalWindowProfileCompressionData_of_commonSpanWithBudget
        M n hn2 htb hns hcommon⟩

/-- Concrete canonical-window/profile compression closes the narrowed classifier
obligation. -/
theorem routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifierObligation_of_strictCanonicalWindowProfileCompression
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowProfileCompressionData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileClassifierObligation
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifierObligation_of_localProfileCompression
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_strictCanonicalWindowProfileCompression_to_localProfileCompression
      M n hn2 htb hns D)


/-- The narrowed classifier obligation is equivalent to the narrowed bounded
common-span package.  This names the exact remaining finite local-profile
frontier, avoiding both broad residual balance and broad row identity. -/
theorem routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifierObligation_iff_commonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileClassifierObligation
        M n hn2 htb hns ↔
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCommonSpanWithBudget
        M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) := by
  constructor
  · intro hclassifier
    exact
      routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalCommonSpanWithBudget_of_classifierObligation
        M n hn2 htb hns hclassifier
  · intro hcommon
    exact
      routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifierObligation_of_commonSpanWithBudget
        M n hn2 htb hns hcommon

/-- The old range-wide common-span frontier implies the narrowed one by
subspace restriction.  This is only a compatibility bridge: it does not revive
the range-wide residual or row-identity targets. -/
theorem routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalCommonSpanWithBudget_of_rangeCommonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcommon :
      RouteBPaperFaithfulTPhiRangePWindowCommonSpanWithBudget
        M n hn2 htb hns (withinProfileBound (Nat.log 2 n))) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCommonSpanWithBudget
      M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) := by
  classical
  rcases hcommon with ⟨G, hG_card, hG_span⟩
  refine ⟨G, hG_card, ?_⟩
  unfold routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalPWindowSubspace
  refine Submodule.span_le.mpr ?_
  intro q hq
  rcases hq with
    ⟨S', shift, α, hSlen, hshiftDegree, hshiftVars, hadm, _hrow, rfl⟩
  apply hG_span
  unfold routeBPaperFaithfulTPhiRangePWindowSubspace
  exact Submodule.subset_span
    ⟨S', shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩

/-- The old range-wide common span also instantiates the concrete narrowed
canonical-window profile data by first restricting to the narrowed row surface.
This is a compatibility bridge only; it does not use residual or row identity. -/
noncomputable def routeBPaperFaithfulTPhi_strictCanonicalWindowProfileCompressionData_of_rangeCommonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcommon :
      RouteBPaperFaithfulTPhiRangePWindowCommonSpanWithBudget
        M n hn2 htb hns (withinProfileBound (Nat.log 2 n))) :
    RouteBPaperFaithfulTPhiStrictCanonicalWindowProfileCompressionData
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_strictCanonicalWindowProfileCompressionData_of_commonSpanWithBudget
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalCommonSpanWithBudget_of_rangeCommonSpanWithBudget
      M n hn2 htb hns hcommon)

/-- The old range-wide classifier obligation also implies the narrowed
classifier obligation, simply by restricting the row surface. -/
theorem routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifierObligation_of_rangeClassifierObligation
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hclassifier :
      RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalProfileClassifierObligation
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalProfileClassifierObligation_of_commonSpanWithBudget
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_strictPaperFaithfulCanonicalCommonSpanWithBudget_of_rangeCommonSpanWithBudget
      M n hn2 htb hns
      ((routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_iff_commonSpanWithBudget
        M n hn2 htb hns).mp hclassifier))

def routeBPaperFaithfulTPhi_canonicalProfileResidualBalance_of_strictPaperFaithfulCoeffBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbalance :
      RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiCanonicalProfileResidualBalance
      M n hn2 htb hns where
  canonicalRow :=
    routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily
      M n hn2 htb hns
  coeff_balance := hbalance
  excludes_two_tag :=
    routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily_excludes_two_tag
      M n hn2 htb hns

/-- Backward-compatible diagnostic packager for the broad unmarked target.
Prefer
`routeBPaperFaithfulTPhi_canonicalProfileResidualBalance_of_strictPaperFaithfulCoeffBalance`
for new Route B work. -/
def routeBPaperFaithfulTPhi_canonicalProfileResidualBalance_of_strictUnmarkedCoeffBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbalance :
      RouteBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffBalance
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiCanonicalProfileResidualBalance
      M n hn2 htb hns where
  canonicalRow :=
    routeBPaperFaithfulTPhiStrictUnmarkedCanonicalRowFamily
      M n hn2 htb hns
  coeff_balance := hbalance
  excludes_two_tag :=
    routeBPaperFaithfulTPhiStrictUnmarkedCanonicalRowFamily_excludes_two_tag
      M n hn2 htb hns

/-- Specialized canonical-window data for the concrete strict `TΦ` decoder.
The remaining fields are exactly the finite-local-normal-form obligations:
choose the canonical scheme for these strict windows, prove the narrowed
coefficient balance on canonical decoded rows, and prove the two-tag raw
witness is not canonical for that scheme. -/
structure RouteBPaperFaithfulTPhiStrictCanonicalWindowData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  scheme :
    PallLean.Paper93.CanonScheme
      (BlockIdx := RouteBPaperFaithfulTPhiStrictBlockIdx n)
      (LocalOp := RouteBPaperFaithfulTPhiStrictLocalOp)
      (Nat.log 2 n)
  coeff_balance :
    RouteBPaperFaithfulTPhiCanonicalProfileNormalizedCoeffBalance
      M n hn2 htb hns
      (fun S' shift α => by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n) scheme
            (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α))
  excludes_two_tag :
    RouteBPaperFaithfulTPhiCanonicalProfileExcludesTwoTagUnitShift
      M n hn2 htb hns
      (fun S' shift α => by
        letI := routeBPaperFaithfulTPhiStrictProdLinearOrder n
        exact
          PallLean.Paper93.IsCanonical
            (κ := Nat.log 2 n) scheme
            (routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α))

/-- The concrete strict decoder instantiates the general canonical-window
profile data. -/
noncomputable def routeBPaperFaithfulTPhi_canonicalWindowData_of_strictData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiCanonicalWindowProfileData
      M n hn2 htb hns where
  BlockIdx := RouteBPaperFaithfulTPhiStrictBlockIdx n
  LocalOp := RouteBPaperFaithfulTPhiStrictLocalOp
  blockFintype := inferInstance
  blockDecEq := inferInstance
  localFintype := inferInstance
  localDecEq := inferInstance
  prodLinearOrder := routeBPaperFaithfulTPhiStrictProdLinearOrder n
  scheme := D.scheme
  rawWindowOf := routeBPaperFaithfulTPhiStrictRawWindowOf n
  coeff_balance := by
    simpa using D.coeff_balance
  excludes_two_tag := by
    simpa using D.excludes_two_tag

/-- The concrete strict decoder feeds the corrected canonical/profile
residual-balance package. -/
noncomputable def routeBPaperFaithfulTPhi_canonicalProfileResidualBalance_of_strictData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiCanonicalProfileResidualBalance
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_canonicalProfileResidualBalance_of_canonicalWindowData
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_canonicalWindowData_of_strictData
      M n hn2 htb hns D)

/-- The expanded corrected coefficient balance is exactly enough to discharge
the named normalized non-singleton coefficient identity. -/
theorem routeBPaperFaithfulTPhi_normalizedNonSingletonCoeffIdentity_of_coeffBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbalance :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
        M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm α hα
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  dsimp only
  have hq :=
    zeroProfileSingletonNormalFormProjection_coeff
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q α
  have hd :=
    zeroProfileSingletonNormalFormProjection_coeff
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i) d α
  rw [hq, hd]
  simpa [p, r, q, d] using
    hbalance S' shift hSlen hshiftDegree hshiftVars hadm α hα

/-- The compact normalized non-singleton coefficient identity is equivalent to
the expanded balance form after unfolding the singleton normalizer. -/
theorem routeBPaperFaithfulTPhi_coeffBalance_of_normalizedNonSingletonCoeffIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcoeff :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm α hα
  let factors : Fin (cookLevinFactorList M n hn2 htb hns).length →
      MvPolynomial (Fin n) ℚ :=
    fun i => (cookLevinFactorList M n hn2 htb hns).get i
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  have hrow :
      MvPolynomial.coeff α (zeroProfileSingletonNormalFormProjection factors q) =
        MvPolynomial.coeff α (zeroProfileSingletonNormalFormProjection factors d) := by
    simpa [factors, p, r, q, d] using
      hcoeff S' shift hSlen hshiftDegree hshiftVars hadm α hα
  have hq :=
    zeroProfileSingletonNormalFormProjection_coeff factors q α
  have hd :=
    zeroProfileSingletonNormalFormProjection_coeff factors d α
  rw [hq, hd] at hrow
  simpa [factors, p, r, q, d] using hrow

/-- The compact normalized non-singleton coefficient identity is equivalent to
the expanded balance form. -/
theorem routeBPaperFaithfulTPhi_normalizedNonSingletonCoeffIdentity_iff_coeffBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
        M n hn2 htb hns ↔
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns :=
  ⟨routeBPaperFaithfulTPhi_coeffBalance_of_normalizedNonSingletonCoeffIdentity
      M n hn2 htb hns,
    routeBPaperFaithfulTPhi_normalizedNonSingletonCoeffIdentity_of_coeffBalance
      M n hn2 htb hns⟩

/-- Normalized row equality is equivalent to the expanded coefficient-balance
form used by the proof-facing strict `TΦ` gate. -/
theorem routeBPaperFaithfulTPhi_coeffBalance_of_singletonNormalizedRowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm α hα
  let factors : Fin (cookLevinFactorList M n hn2 htb hns).length →
      MvPolynomial (Fin n) ℚ :=
    fun i => (cookLevinFactorList M n hn2 htb hns).get i
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  have hrow :
      zeroProfileSingletonNormalFormProjection factors q =
        zeroProfileSingletonNormalFormProjection factors d := by
    simpa [factors, p, r, q, d] using
      hnorm S' shift hSlen hshiftDegree hshiftVars hadm
  have hcoeff :
      MvPolynomial.coeff α (zeroProfileSingletonNormalFormProjection factors q) =
        MvPolynomial.coeff α (zeroProfileSingletonNormalFormProjection factors d) :=
    congrArg (fun z : MvPolynomial (Fin n) ℚ => MvPolynomial.coeff α z) hrow
  have hq :=
    zeroProfileSingletonNormalFormProjection_coeff factors q α
  have hd :=
    zeroProfileSingletonNormalFormProjection_coeff factors d α
  rw [hq, hd] at hcoeff
  simpa [factors, p, r, q, d] using hcoeff

/-- Singleton-residual row algebra discharges the expanded normalized
coefficient-balance gate. -/
theorem routeBPaperFaithfulTPhi_coeffBalance_of_singletonResidual
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns := by
  classical
  refine
    routeBPaperFaithfulTPhi_coeffBalance_of_singletonNormalizedRowIdentity
      M n hn2 htb hns ?_
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  have hres' :
      q - d ∈
        zeroProfileSingletonShiftSubspace
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) := by
    simpa [p, r, q, d] using
      hres S' shift hSlen hshiftDegree hshiftVars hadm
  have hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
          (Finset.univ.prod
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) =
        (1 : ℚ) := by
    simpa [cookLevinZeroProfileBaseProduct] using
      cookLevinZeroProfileBaseProduct_coeff_zero M n hn2 htb hns
  exact
    zeroProfileSingletonNormalFormProjection_eq_of_sub_mem_singletonShiftSubspace
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      hconst hres'

/-- The strict singleton-quotient residual-balance row identity implies the
raw rows differ only by singleton-shift noise.  This collapses the normalized
coefficient gate to the single residual-balance row algebra. -/
theorem routeBPaperFaithfulTPhi_singletonResidual_of_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  let project :=
    zeroProfileQuotientBySingletonShiftProjection
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
  have hrow :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns project :=
    routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_of_restrictedResidualBalance
      M n hn2 htb hns project hres
  have hqd : d = project q := by
    have hrow' := hrow S' shift hSlen hshiftDegree hshiftVars hadm
    simpa [project, p, r, q, d] using hrow'
  have hprojResidual :
      q - project q ∈
        zeroProfileSingletonShiftSubspace
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) :=
    zeroProfileQuotientBySingletonShiftProjection_residual_mem_singletonShiftSubspace
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q
  change q - d ∈
    zeroProfileSingletonShiftSubspace
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
  rw [hqd]
  exact hprojResidual

/-- The strict singleton-quotient residual-balance row identity also proves
that every derivative row is fixed by the chosen quotient projection.  The
fixed-representative condition is therefore not a separate mathematical gate
once the residual-balance row algebra is available. -/
theorem routeBPaperFaithfulTPhi_derivativeFixed_of_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
        M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  let project :=
    zeroProfileQuotientBySingletonShiftProjection
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
  have hrow :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns project :=
    routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_of_restrictedResidualBalance
      M n hn2 htb hns project hres
  have hqd : d = project q := by
    have hrow' := hrow S' shift hSlen hshiftDegree hshiftVars hadm
    simpa [project, p, r, q, d] using hrow'
  have hidem :
      project (project q) = project q := by
    have hmap :=
      congrArg
        (fun L : MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ =>
          L q)
        (zeroProfileQuotientBySingletonShiftProjection_idempotent
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
    simpa [project, LinearMap.comp_apply] using hmap
  calc
    project d = project (project q) := by rw [hqd]
    _ = project q := hidem
    _ = d := hqd.symm

/-- The strict singleton-quotient residual-balance row identity discharges the
expanded normalized coefficient-balance gate. -/
theorem routeBPaperFaithfulTPhi_coeffBalance_of_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_coeffBalance_of_singletonResidual
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_singletonResidual_of_restrictedResidualBalance
      M n hn2 htb hns hres)

/-- Residual-only singleton noise gives equality after the canonical singleton
quotient projection. -/
theorem routeBPaperFaithfulTPhi_singletonQuotientRowIdentity_of_singletonResidual
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientRowIdentity
      M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  have hres' :
      q - d ∈
        zeroProfileSingletonShiftSubspace
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) := by
    simpa [p, r, q, d] using
      hres S' shift hSlen hshiftDegree hshiftVars hadm
  exact
    zeroProfileQuotientBySingletonShiftProjection_eq_of_sub_mem_singletonShiftSubspace
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i) hres'

/-- For the canonical singleton quotient, quotient row equality is equivalent
to saying the raw row difference is singleton-shift residual noise. -/
theorem routeBPaperFaithfulTPhi_singletonQuotientRowIdentity_iff_singletonResidual
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientRowIdentity
        M n hn2 htb hns ↔
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns := by
  classical
  constructor
  · intro hquot S' shift hSlen hshiftDegree hshiftVars hadm
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj (shift * SPDP.iterDerivList S' r))
    have hquot' :
        zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q =
          zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) d := by
      simpa [p, r, q, d] using
        hquot S' shift hSlen hshiftDegree hshiftVars hadm
    have hzero :
        zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            (q - d) = 0 := by
      rw [map_sub, hquot', sub_self]
    exact
      (routeBPaperFaithfulTPhi_zeroProfileQuotientBySingletonShiftProjection_apply_eq_zero_iff
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (q - d)).mp hzero
  · exact
      routeBPaperFaithfulTPhi_singletonQuotientRowIdentity_of_singletonResidual
        M n hn2 htb hns

/-- Quotient row equality recovers the old raw restricted row identity exactly
when each strict derivative row is already the chosen singleton-quotient
representative.  This makes the representative condition explicit instead of
hiding it inside a raw equality target. -/
theorem routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_of_singletonQuotientRowIdentity_fixedDerivative
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hquot :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientRowIdentity
        M n hn2 htb hns)
    (hfix :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
      M n hn2 htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  have hquot' :
      zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q =
        zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) d := by
    simpa [p, r, q, d] using
      hquot S' shift hSlen hshiftDegree hshiftVars hadm
  have hfix' :
      zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) d = d := by
    simpa [p, r, d] using
      hfix S' shift hSlen hshiftDegree hshiftVars hadm
  calc
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          (shift *
            SPDP.iterDerivList S'
              (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
                (cookLevinStrictFOBFlatMap_injective n)
                (compiledPoly
                  (cook_levin_compilation M n hn2 htb hns))))) = d := by
        rfl
    _ =
      zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q := by
        rw [← hfix', ← hquot']
    _ =
      zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          (mlProj
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns)) := by
        rfl

/-- The raw normal-form identity implies the normalized row identity. -/
theorem routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_singletonNormalFormIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormIdentity
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
      M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  have h := hnorm S' shift hSlen hshiftDegree hshiftVars hadm
  have hrow :
      zeroProfileSingletonNormalFormProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q = d := by
    simpa [p, r, q, d] using h
  have hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
          (Finset.univ.prod
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) =
        (1 : ℚ) := by
    simpa [cookLevinZeroProfileBaseProduct] using
      cookLevinZeroProfileBaseProduct_coeff_zero M n hn2 htb hns
  have hidem :
      zeroProfileSingletonNormalFormProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          (zeroProfileSingletonNormalFormProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q) =
        zeroProfileSingletonNormalFormProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q := by
    have hmap :=
      congrArg
        (fun L : MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ =>
          L q)
        (zeroProfileSingletonNormalFormProjection_idempotent_of_constCoeff_one
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) hconst)
    simpa [LinearMap.comp_apply] using hmap
  calc
    zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q =
      zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileSingletonNormalFormProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q) := by
        exact hidem.symm
    _ =
      zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) d := by
        rw [hrow]

/-- Residual-only singleton noise gives the normalized strict-`TΦ` row identity. -/
theorem routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_singletonResidual
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
      M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  have hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
          (Finset.univ.prod
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) =
        (1 : ℚ) := by
    simpa [cookLevinZeroProfileBaseProduct] using
      cookLevinZeroProfileBaseProduct_coeff_zero M n hn2 htb hns
  have hres' :
      q - d ∈
        zeroProfileSingletonShiftSubspace
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) := by
    simpa [p, r, q, d] using
      hres S' shift hSlen hshiftDegree hshiftVars hadm
  exact
    zeroProfileSingletonNormalFormProjection_eq_of_sub_mem_singletonShiftSubspace
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      hconst hres'

/-- The normalized strict-`TΦ` row identity is equivalent to the residual-only
singleton-noise statement. -/
theorem routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_iff_singletonResidual
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns ↔
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns := by
  classical
  constructor
  · intro hnorm S' shift hSlen hshiftDegree hshiftVars hadm
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj (shift * SPDP.iterDerivList S' r))
    have h := hnorm S' shift hSlen hshiftDegree hshiftVars hadm
    exact
      sub_mem_singletonShiftSubspace_of_zeroProfileSingletonNormalFormProjection_eq
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (by simpa [p, r, q, d] using h)
  · exact
      routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_singletonResidual
        M n hn2 htb hns

/-- The semantic normal-form identity gives the range-only row identity for the
explicit singleton normalizer. -/
theorem routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_of_singletonNormalFormIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormIdentity
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
      M n hn2 htb hns
      (zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) := by
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  have h := hnorm S' shift hSlen hshiftDegree hshiftVars hadm
  simpa using h.symm

/-- Coefficient-extensional proof rule for the explicit singleton normalizer:
to prove the normal-form row identity it is enough to prove that the target row
has no singleton coefficients, and that all remaining coefficients match the
normalizer image. -/
theorem zeroProfileSingletonNormalFormProjection_eq_of_coeff_split
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (Finset.univ.prod factors) = (1 : ℚ))
    (q d : MvPolynomial (Fin n) ℚ)
    (hsingleton :
      ∀ i : Fin n, MvPolynomial.coeff (Finsupp.single i 1) d = 0)
    (hnonsingle :
      ∀ α : Fin n →₀ ℕ,
        (∀ i : Fin n, α ≠ Finsupp.single i 1) →
          MvPolynomial.coeff α
              (zeroProfileSingletonNormalFormProjection factors q) =
            MvPolynomial.coeff α d) :
    zeroProfileSingletonNormalFormProjection factors q = d := by
  classical
  ext α
  by_cases hα : ∃ i : Fin n, α = Finsupp.single i 1
  · rcases hα with ⟨i, rfl⟩
    rw [zeroProfileSingletonNormalFormProjection_coeff_single_eq_zero
      factors hconst q i, hsingleton i]
  · exact hnonsingle α (fun i hi => hα ⟨i, hi⟩)

/-- Route-B strict `TΦ` normal-form identity from the two concrete coefficient
proof gates: singleton derivative coefficients vanish, and every non-singleton
coefficient agrees with the normalized zero-profile row. -/
theorem routeBPaperFaithfulTPhi_singletonNormalFormIdentity_of_coeff_split
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hsingleton :
      ∀ (S' : List (Fin (n / 3)))
        (shift : MvPolynomial (Fin (n / 3)) ℚ),
        S'.length = Nat.log 2 n →
        shift.totalDegree ≤ Nat.log 2 n →
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)) →
        ∀ i : Fin n,
          let p : MvPolynomial (Fin n) ℚ :=
            compiledPoly (cook_levin_compilation M n hn2 htb hns)
          let r : MvPolynomial (Fin (n / 3)) ℚ :=
            MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n) p
          MvPolynomial.coeff (Finsupp.single i 1)
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
              (mlProj (shift * SPDP.iterDerivList S' r))) = 0)
    (hnonsingle :
      ∀ (S' : List (Fin (n / 3)))
        (shift : MvPolynomial (Fin (n / 3)) ℚ),
        S'.length = Nat.log 2 n →
        shift.totalDegree ≤ Nat.log 2 n →
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)) →
        ∀ α : Fin n →₀ ℕ,
          (∀ i : Fin n, α ≠ Finsupp.single i 1) →
          let p : MvPolynomial (Fin n) ℚ :=
            compiledPoly (cook_levin_compilation M n hn2 htb hns)
          let r : MvPolynomial (Fin (n / 3)) ℚ :=
            MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n) p
          let q : MvPolynomial (Fin n) ℚ :=
            mlProj
              (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
                cookLevinZeroProfileBaseProduct M n hn2 htb hns)
          MvPolynomial.coeff α
              (zeroProfileSingletonNormalFormProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q) =
            MvPolynomial.coeff α
              (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
                (mlProj (shift * SPDP.iterDerivList S' r)))) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormIdentity
        M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  have hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
          (Finset.univ.prod
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) =
        (1 : ℚ) := by
    simpa [cookLevinZeroProfileBaseProduct] using
      cookLevinZeroProfileBaseProduct_coeff_zero M n hn2 htb hns
  exact
    zeroProfileSingletonNormalFormProjection_eq_of_coeff_split
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      hconst q d
      (fun i => by
        simpa [p, r, d] using
          hsingleton S' shift hSlen hshiftDegree hshiftVars hadm i)
      (fun α hα => by
        simpa [p, r, q, d] using
          hnonsingle S' shift hSlen hshiftDegree hshiftVars hadm α hα)

/-- The concrete coefficient split closes the residual-only singleton-noise
gate directly.  This is the proof-facing form of the remaining Cook-Levin
strict `TΦ` row algebra. -/
theorem routeBPaperFaithfulTPhi_singletonResidual_of_coeff_split
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hsingleton :
      ∀ (S' : List (Fin (n / 3)))
        (shift : MvPolynomial (Fin (n / 3)) ℚ),
        S'.length = Nat.log 2 n →
        shift.totalDegree ≤ Nat.log 2 n →
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)) →
        ∀ i : Fin n,
          let p : MvPolynomial (Fin n) ℚ :=
            compiledPoly (cook_levin_compilation M n hn2 htb hns)
          let r : MvPolynomial (Fin (n / 3)) ℚ :=
            MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n) p
          MvPolynomial.coeff (Finsupp.single i 1)
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
              (mlProj (shift * SPDP.iterDerivList S' r))) = 0)
    (hnonsingle :
      ∀ (S' : List (Fin (n / 3)))
        (shift : MvPolynomial (Fin (n / 3)) ℚ),
        S'.length = Nat.log 2 n →
        shift.totalDegree ≤ Nat.log 2 n →
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)) →
        ∀ α : Fin n →₀ ℕ,
          (∀ i : Fin n, α ≠ Finsupp.single i 1) →
          let p : MvPolynomial (Fin n) ℚ :=
            compiledPoly (cook_levin_compilation M n hn2 htb hns)
          let r : MvPolynomial (Fin (n / 3)) ℚ :=
            MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n) p
          let q : MvPolynomial (Fin n) ℚ :=
            mlProj
              (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
                cookLevinZeroProfileBaseProduct M n hn2 htb hns)
          MvPolynomial.coeff α
              (zeroProfileSingletonNormalFormProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q) =
            MvPolynomial.coeff α
              (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
                (mlProj (shift * SPDP.iterDerivList S' r)))) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns :=
  (routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_iff_singletonResidual
    M n hn2 htb hns).mp
    (routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_singletonNormalFormIdentity
      M n hn2 htb hns
      (routeBPaperFaithfulTPhi_singletonNormalFormIdentity_of_coeff_split
        M n hn2 htb hns hsingleton hnonsingle))

/-- Normalized coefficient proof rule for the residual-only gate.  Unlike the
raw normal-form identity, this does not require singleton coefficients of the
derivative row to vanish: the explicit normalizer kills singleton coordinates
on both sides.  The real remaining coefficient computation is therefore only
the non-singleton equality after normalizing both rows. -/
theorem routeBPaperFaithfulTPhi_singletonResidual_of_normalized_nonSingleton_coeff
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnonsingle :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns := by
  classical
  refine
    (routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_iff_singletonResidual
      M n hn2 htb hns).mp ?_
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  have hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
          (Finset.univ.prod
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) =
        (1 : ℚ) := by
    simpa [cookLevinZeroProfileBaseProduct] using
      cookLevinZeroProfileBaseProduct_coeff_zero M n hn2 htb hns
  ext α
  by_cases hα : ∃ i : Fin n, α = Finsupp.single i 1
  · rcases hα with ⟨i, rfl⟩
    rw [zeroProfileSingletonNormalFormProjection_coeff_single_eq_zero
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i) hconst q i]
    rw [zeroProfileSingletonNormalFormProjection_coeff_single_eq_zero
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i) hconst d i]
  · exact
      hnonsingle S' shift hSlen hshiftDegree hshiftVars hadm α
        (fun i hi => hα ⟨i, hi⟩)

/-- The normalized non-singleton coefficient computation is enough to prove
the strict singleton-normalizer row identity.  Singleton coordinates need no
separate proof: the semantic normalizer erases them on both sides. -/
theorem routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_normalizedNonSingletonCoeff
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcoeff :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns :=
  (routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_iff_singletonResidual
    M n hn2 htb hns).mpr
    (routeBPaperFaithfulTPhi_singletonResidual_of_normalized_nonSingleton_coeff
      M n hn2 htb hns hcoeff)

/-- Expanded normalized coefficient balance is the exact proof-facing
coefficient gate for the semantic singleton-normalizer row identity. -/
theorem routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_coeffBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbalance :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_normalizedNonSingletonCoeff
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_normalizedNonSingletonCoeffIdentity_of_coeffBalance
      M n hn2 htb hns hbalance)

/-- The expanded normalized coefficient balance is equivalent to equality
after the semantic singleton normalizer.  This packages coefficient
extensionality and the fact that singleton coordinates are erased on both
sides. -/
theorem routeBPaperFaithfulTPhi_normalizedCoeffBalance_iff_singletonNormalizedRowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns ↔
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns := by
  constructor
  · exact
      routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_coeffBalance
        M n hn2 htb hns
  · exact
      routeBPaperFaithfulTPhi_coeffBalance_of_singletonNormalizedRowIdentity
        M n hn2 htb hns

/-- Equivalently, the expanded coefficient computation is precisely the
residual statement that the strict zero-profile row and the extracted
derivative row differ by singleton-shift noise. -/
theorem routeBPaperFaithfulTPhi_normalizedCoeffBalance_iff_singletonResidual
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns ↔
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns := by
  constructor
  · intro hbalance
    exact
      (routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_iff_singletonResidual
        M n hn2 htb hns).mp
        (routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_coeffBalance
          M n hn2 htb hns hbalance)
  · exact
      routeBPaperFaithfulTPhi_coeffBalance_of_singletonResidual
        M n hn2 htb hns

/-- Singleton-residual membership forces constant coefficients to agree.  This
is the first concrete coefficient test for the remaining strict `TΦ` residual
gate, because singleton-shift noise has zero constant coefficient. -/
theorem routeBPaperFaithfulTPhi_singletonResidual_forces_constantCoeff_balance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (hSlen : S'.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n))) :
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj (shift * SPDP.iterDerivList S' r))
    MvPolynomial.coeff (0 : Fin n →₀ ℕ) q =
      MvPolynomial.coeff (0 : Fin n →₀ ℕ) d := by
  classical
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  have hmem :
      q - d ∈
        zeroProfileSingletonShiftSubspace
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) := by
    simpa [p, r, q, d] using
      hres S' shift hSlen hshiftDegree hshiftVars hadm
  have hzero :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ) (q - d) = 0 :=
    routeBPaperFaithfulTPhi_zeroProfileSingletonShiftSubspace_coeff_zero
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i) hmem
  rw [MvPolynomial.coeff_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- A single strict source row with mismatched constant coefficient rules out
the singleton-residual gate.  This is the proof-facing no-go criterion for the
remaining row algebra. -/
theorem routeBPaperFaithfulTPhi_not_singletonResidual_of_constantCoeff_ne
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (hSlen : S'.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)))
    (hcoeff_ne :
      let p : MvPolynomial (Fin n) ℚ :=
        compiledPoly (cook_levin_compilation M n hn2 htb hns)
      let r : MvPolynomial (Fin (n / 3)) ℚ :=
        MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n) p
      let q : MvPolynomial (Fin n) ℚ :=
        mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns)
      let d : MvPolynomial (Fin n) ℚ :=
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * SPDP.iterDerivList S' r))
      MvPolynomial.coeff (0 : Fin n →₀ ℕ) q ≠
        MvPolynomial.coeff (0 : Fin n →₀ ℕ) d) :
    ¬ RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns := by
  intro hres
  exact hcoeff_ne
    (routeBPaperFaithfulTPhi_singletonResidual_forces_constantCoeff_balance
      M n hn2 htb hns hres S' shift hSlen hshiftDegree hshiftVars hadm)

/-- The strict zero-profile row with unit shift has constant coefficient `1`.
This is the concrete left-hand side of the constant-coefficient residual test. -/
theorem routeBPaperFaithfulTPhi_unitShift_zeroProfileRow_constantCoeff
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    MvPolynomial.coeff (0 : Fin n →₀ ℕ)
      (mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (1 : MvPolynomial (Fin (n / 3)) ℚ) *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)) = (1 : ℚ) := by
  rw [map_one, one_mul]
  rw [MultilinearSPDP.coeff_mlProj_of_isMultilinear_mono _ _
    (by intro i; simp)]
  exact cookLevinZeroProfileBaseProduct_coeff_zero M n hn2 htb hns

/-- Full strict tag-monomial coefficient of the unit-shift zero-profile row.
The constant-coefficient lemma above is the `S = ∅` specialization; this
computes every strict first-of-block coefficient on the source side. -/
theorem routeBPaperFaithfulTPhi_unitShift_zeroProfileRow_tagCoeff
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (n / 3))) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
    MvPolynomial.coeff (SymmetricPower.tagMonomial (S.map e))
      (mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (1 : MvPolynomial (Fin (n / 3)) ℚ) *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
      (-1 : ℚ) ^ S.card := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  rw [map_one, one_mul]
  rw [cookLevinZeroProfileBaseProduct_eq_compiledPoly M n hn2 htb hns]
  exact
    _root_.Step4Compiler.Step252.coeff_mlProj_compiled_strictFOB_tag
      M n hn2 htb hns S

/-- The singleton-normalizer basis row has an explicit strict-tag coefficient:
for a tagged coordinate present in the target tag, multiplication by that
coordinate removes it and exposes the erased zero-profile coefficient. -/
theorem routeBPaperFaithfulTPhi_unitShift_singletonShiftRow_tagCoeff
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (n / 3))) (j : Fin (n / 3)) (hj : j ∈ S) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
    MvPolynomial.coeff (SymmetricPower.tagMonomial (S.map e))
      (mlProj
        (MvPolynomial.X (e j) *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
      (-1 : ℚ) ^ (S.erase j).card := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
  have hmem : e j ∈ α.support := by
    simpa [α] using
      (tagMonomial_mem_support_iff (S.map e) (e j)).mpr
        (Finset.mem_map.mpr ⟨j, hj, rfl⟩)
  have hprobe :
      MvPolynomial.coeff α
        (mlProj
          (MvPolynomial.X (e j) *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
        MvPolynomial.coeff
          (α - Finsupp.single (e j) 1)
          (cookLevinZeroProfileBaseProduct M n hn2 htb hns) := by
    rw [coeff_mlProj_X_mul_of_isMultilinear]
    · simp [hmem]
    · exact SymmetricPower.tagMonomial_isMultilinear (S.map e)
  have hsub :
      α - Finsupp.single (e j) 1 =
        SymmetricPower.tagMonomial ((S.erase j).map e) := by
    simpa [α] using tagMonomial_map_sub_single e S j hj
  have hbase :
      MvPolynomial.coeff
          (SymmetricPower.tagMonomial ((S.erase j).map e))
          (cookLevinZeroProfileBaseProduct M n hn2 htb hns) =
        (-1 : ℚ) ^ (S.erase j).card := by
    have hml :=
      routeBPaperFaithfulTPhi_unitShift_zeroProfileRow_tagCoeff
        M n hn2 htb hns (S.erase j)
    have hmono :
        Finsupp.IsMultilinear
          (SymmetricPower.tagMonomial ((S.erase j).map e)) :=
      SymmetricPower.tagMonomial_isMultilinear ((S.erase j).map e)
    rw [map_one, one_mul] at hml
    have hml' :
        MvPolynomial.coeff
            (SymmetricPower.tagMonomial ((S.erase j).map e))
            (mlProj (cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
          (-1 : ℚ) ^ (S.erase j).card := by
      simpa [e] using hml
    have hproj :
        MvPolynomial.coeff
            (SymmetricPower.tagMonomial ((S.erase j).map e))
            (mlProj (cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
          MvPolynomial.coeff
            (SymmetricPower.tagMonomial ((S.erase j).map e))
            (cookLevinZeroProfileBaseProduct M n hn2 htb hns) := by
      rw [MultilinearSPDP.coeff_mlProj_of_isMultilinear_mono _ _ hmono]
    exact hproj.symm.trans hml'
  rw [hsub] at hprobe
  simpa [α] using hprobe.trans hbase

/-- Strict singleton coefficient of the unit-shift zero-profile row. -/
theorem routeBPaperFaithfulTPhi_unitShift_zeroProfileRow_singletonCoeff
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (j : Fin (n / 3)) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
    MvPolynomial.coeff (Finsupp.single (e j) 1)
      (mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (1 : MvPolynomial (Fin (n / 3)) ℚ) *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
      (-1 : ℚ) := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  have htag :
      SymmetricPower.tagMonomial (({j} : Finset (Fin (n / 3))).map e) =
        Finsupp.single (e j) 1 := by
    ext x
    by_cases hx : x = e j
    · subst x
      simp [SymmetricPower.tagMonomial_apply]
    · simp [SymmetricPower.tagMonomial_apply, hx]
  have hcoeff :=
    routeBPaperFaithfulTPhi_unitShift_zeroProfileRow_tagCoeff
      M n hn2 htb hns ({j} : Finset (Fin (n / 3)))
  have hcoeff' :
      MvPolynomial.coeff
          (SymmetricPower.tagMonomial (({j} : Finset (Fin (n / 3))).map e))
          (mlProj
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
                (1 : MvPolynomial (Fin (n / 3)) ℚ) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
        (-1 : ℚ) := by
    simpa [e] using hcoeff
  rw [htag] at hcoeff'
  simpa [e] using hcoeff'

/-- The zero-profile side of each strict singleton-normalizer correction
summand is completely explicit. -/
theorem routeBPaperFaithfulTPhi_unitShift_zeroProfile_correctionSummand
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (n / 3))) (j : Fin (n / 3)) (hj : j ∈ S) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (1 : MvPolynomial (Fin (n / 3)) ℚ) *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
    MvPolynomial.coeff (Finsupp.single (e j) 1) q *
        MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X (e j) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
      -((-1 : ℚ) ^ (S.erase j).card) := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (1 : MvPolynomial (Fin (n / 3)) ℚ) *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
  have hsingle :
      MvPolynomial.coeff (Finsupp.single (e j) 1) q = (-1 : ℚ) := by
    simpa [e, q] using
      routeBPaperFaithfulTPhi_unitShift_zeroProfileRow_singletonCoeff
        M n hn2 htb hns j
  have hshift :
      MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X (e j) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
        (-1 : ℚ) ^ (S.erase j).card := by
    simpa [e, α] using
      routeBPaperFaithfulTPhi_unitShift_singletonShiftRow_tagCoeff
        M n hn2 htb hns S j hj
  have hmain :
      MvPolynomial.coeff (Finsupp.single (e j) 1) q *
          MvPolynomial.coeff α
            (mlProj
              (MvPolynomial.X (e j) *
                cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
        -((-1 : ℚ) ^ (S.erase j).card) := by
    rw [hsingle, hshift]
    ring
  simpa [e, q, α] using hmain

/-- For unit shift, the singleton-residual gate forces the extracted strict
derivative row to have constant coefficient `1`.  This is the first concrete
row-family test before any higher coefficient comparison is attempted. -/
theorem routeBPaperFaithfulTPhi_singletonResidual_forces_unitShift_derivative_constantCoeff_one
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns)
    (S' : List (Fin (n / 3)))
    (hSlen : S'.length = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n))) :
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    MvPolynomial.coeff (0 : Fin n →₀ ℕ)
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
            SPDP.iterDerivList S' r))) = (1 : ℚ) := by
  classical
  let shift : MvPolynomial (Fin (n / 3)) ℚ := 1
  have hvars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset := by
    simp [shift]
  have hbalance :=
    routeBPaperFaithfulTPhi_singletonResidual_forces_constantCoeff_balance
      M n hn2 htb hns hres S' shift hSlen (by simp [shift]) hvars hadm
  have hleft :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns)) = (1 : ℚ) := by
    simpa [shift] using
      routeBPaperFaithfulTPhi_unitShift_zeroProfileRow_constantCoeff
        M n hn2 htb hns
  exact hbalance.symm.trans hleft

/-- Actual constant coefficient of the intended strict `TΦ` derivative row,
indexed by a canonical finite derivative set.  This is the concrete
Cook-Levin coefficient computation behind the unit-shift residual test. -/
theorem routeBPaperFaithfulTPhi_unitShift_derivative_constantCoeff_finset
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (T : Finset (Fin (n / 3))) :
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    MvPolynomial.coeff (0 : Fin n →₀ ℕ)
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
            SPDP.iterDerivList T.toList r))) =
      (-1 : ℚ) ^ T.card := by
  classical
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin (n / 3)) ℚ :=
    mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) * SPDP.iterDerivList T.toList r)
  have hrename :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) q) =
      MvPolynomial.coeff (0 : Fin (n / 3) →₀ ℕ) q := by
    simpa using
      (MvPolynomial.coeff_rename_mapDomain (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) q
        (0 : Fin (n / 3) →₀ ℕ))
  have hcoeff :
      MvPolynomial.coeff (0 : Fin (n / 3) →₀ ℕ)
        (mlProj (SPDP.iterDerivList T.toList r)) =
      (-1 : ℚ) ^ T.card := by
    have hgeneral :=
      _root_.Step4Compiler.Step252.coeff_mlProj_strictFOB_restrict_compiled_general
        M n hn2 htb hns (∅ : Finset (Fin (n / 3))) T
    simpa [SymmetricPower.tagMonomial, Finset.card_empty, p, r] using hgeneral
  calc
    MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj
            ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
              SPDP.iterDerivList T.toList r)))
        = MvPolynomial.coeff (0 : Fin n →₀ ℕ)
            (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) q) := by
              simp [q]
    _ = MvPolynomial.coeff (0 : Fin (n / 3) →₀ ℕ) q := hrename
    _ = MvPolynomial.coeff (0 : Fin (n / 3) →₀ ℕ)
          (mlProj (SPDP.iterDerivList T.toList r)) := by
              simp [q]
    _ = (-1 : ℚ) ^ T.card := hcoeff

/-- Full strict tag-monomial coefficient of the intended strict `TΦ`
derivative row, indexed by source and derivative finite sets.  This is the
higher/nonconstant coefficient analogue of
`routeBPaperFaithfulTPhi_unitShift_derivative_constantCoeff_finset`. -/
theorem routeBPaperFaithfulTPhi_unitShift_derivative_tagCoeff_finset
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S T : Finset (Fin (n / 3))) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    MvPolynomial.coeff (SymmetricPower.tagMonomial (S.map e))
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
            SPDP.iterDerivList T.toList r))) =
      (2 : ℚ) ^ (S ∩ T).card * (-1) ^ (S \ T).card *
        (-1) ^ (T \ S).card := by
  classical
  let f := cookLevinStrictFOBFlatMap n
  let hf := cookLevinStrictFOBFlatMap_injective n
  let e : Fin (n / 3) ↪ Fin n := ⟨f, hf⟩
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ f hf p
  let q : MvPolynomial (Fin (n / 3)) ℚ :=
    mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
      SPDP.iterDerivList T.toList r)
  have hrename :
      MvPolynomial.coeff (SymmetricPower.tagMonomial (S.map e))
        (MvPolynomial.rename f q) =
      MvPolynomial.coeff (SymmetricPower.tagMonomial S) q := by
    have hcoeff :=
      MvPolynomial.coeff_rename_mapDomain f hf q
        (SymmetricPower.tagMonomial S)
    have hmap :=
      _root_.Step4Compiler.Step252.strictFOB_mapDomain_tagMonomial_eq
        f hf S
    simpa [e, hmap] using hcoeff
  have hcoeff :
      MvPolynomial.coeff (SymmetricPower.tagMonomial S)
        (mlProj (SPDP.iterDerivList T.toList r)) =
      (2 : ℚ) ^ (S ∩ T).card * (-1) ^ (S \ T).card *
        (-1) ^ (T \ S).card := by
    have hgeneral :=
      _root_.Step4Compiler.Step252.coeff_mlProj_strictFOB_restrict_compiled_general
        M n hn2 htb hns S T
    simpa [p, r, f, hf] using hgeneral
  calc
    MvPolynomial.coeff (SymmetricPower.tagMonomial (S.map e))
        (MvPolynomial.rename f
          (mlProj
            ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
              SPDP.iterDerivList T.toList r)))
        = MvPolynomial.coeff (SymmetricPower.tagMonomial (S.map e))
            (MvPolynomial.rename f q) := by simp [q]
    _ = MvPolynomial.coeff (SymmetricPower.tagMonomial S) q := hrename
    _ = MvPolynomial.coeff (SymmetricPower.tagMonomial S)
          (mlProj (SPDP.iterDerivList T.toList r)) := by simp [q]
    _ = (2 : ℚ) ^ (S ∩ T).card * (-1) ^ (S \ T).card *
          (-1) ^ (T \ S).card := hcoeff

/-- Strict singleton coefficient of the extracted derivative row. -/
theorem routeBPaperFaithfulTPhi_unitShift_derivative_singletonCoeff
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (j : Fin (n / 3)) (T : Finset (Fin (n / 3))) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    MvPolynomial.coeff (Finsupp.single (e j) 1)
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
            SPDP.iterDerivList T.toList r))) =
      (2 : ℚ) ^ (({j} : Finset (Fin (n / 3))) ∩ T).card *
        (-1) ^ (({j} : Finset (Fin (n / 3))) \ T).card *
        (-1) ^ (T \ ({j} : Finset (Fin (n / 3)))).card := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  have htag :
      SymmetricPower.tagMonomial (({j} : Finset (Fin (n / 3))).map e) =
        Finsupp.single (e j) 1 := by
    ext x
    by_cases hx : x = e j
    · subst x
      simp [SymmetricPower.tagMonomial_apply]
    · simp [SymmetricPower.tagMonomial_apply, hx]
  have hcoeff :=
    routeBPaperFaithfulTPhi_unitShift_derivative_tagCoeff_finset
      M n hn2 htb hns ({j} : Finset (Fin (n / 3))) T
  have hcoeff' :
      MvPolynomial.coeff
          (SymmetricPower.tagMonomial (({j} : Finset (Fin (n / 3))).map e))
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (mlProj
              ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
                SPDP.iterDerivList T.toList
                  (MultilinearSPDP.restrictPoly ℚ
                    (cookLevinStrictFOBFlatMap n)
                    (cookLevinStrictFOBFlatMap_injective n)
                    (compiledPoly
                      (cook_levin_compilation M n hn2 htb hns)))))) =
        (2 : ℚ) ^ (({j} : Finset (Fin (n / 3))) ∩ T).card *
          (-1) ^ (({j} : Finset (Fin (n / 3))) \ T).card *
          (-1) ^ (T \ ({j} : Finset (Fin (n / 3)))).card := by
    simpa [e] using hcoeff
  rw [htag] at hcoeff'
  simpa [e] using hcoeff'

/-- The derivative side of each strict singleton-normalizer correction
summand is completely explicit. -/
theorem routeBPaperFaithfulTPhi_unitShift_derivative_correctionSummand
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S T : Finset (Fin (n / 3))) (j : Fin (n / 3)) (hj : j ∈ S) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
          SPDP.iterDerivList T.toList r))
    let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
    MvPolynomial.coeff (Finsupp.single (e j) 1) d *
        MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X (e j) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
      ((2 : ℚ) ^ (({j} : Finset (Fin (n / 3))) ∩ T).card *
          (-1) ^ (({j} : Finset (Fin (n / 3))) \ T).card *
          (-1) ^ (T \ ({j} : Finset (Fin (n / 3)))).card) *
        ((-1 : ℚ) ^ (S.erase j).card) := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
        SPDP.iterDerivList T.toList r))
  let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
  have hsingle :
      MvPolynomial.coeff (Finsupp.single (e j) 1) d =
        (2 : ℚ) ^ (({j} : Finset (Fin (n / 3))) ∩ T).card *
          (-1) ^ (({j} : Finset (Fin (n / 3))) \ T).card *
          (-1) ^ (T \ ({j} : Finset (Fin (n / 3)))).card := by
    simpa [e, p, r, d] using
      routeBPaperFaithfulTPhi_unitShift_derivative_singletonCoeff
        M n hn2 htb hns j T
  have hshift :
      MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X (e j) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
        (-1 : ℚ) ^ (S.erase j).card := by
    simpa [e, α] using
      routeBPaperFaithfulTPhi_unitShift_singletonShiftRow_tagCoeff
        M n hn2 htb hns S j hj
  have hmain :
      MvPolynomial.coeff (Finsupp.single (e j) 1) d *
          MvPolynomial.coeff α
            (mlProj
              (MvPolynomial.X (e j) *
                cookLevinZeroProfileBaseProduct M n hn2 htb hns)) =
        ((2 : ℚ) ^ (({j} : Finset (Fin (n / 3))) ∩ T).card *
            (-1) ^ (({j} : Finset (Fin (n / 3))) \ T).card *
            (-1) ^ (T \ ({j} : Finset (Fin (n / 3)))).card) *
          ((-1 : ℚ) ^ (S.erase j).card) := by
    rw [hsingle, hshift]
  simpa [e, p, r, d, α] using hmain

/-- Collapse the zero-profile singleton-normalizer correction sum over the
strict tagged support.  This is the finite-sum form of the pointwise
zero-profile correction summand. -/
theorem routeBPaperFaithfulTPhi_unitShift_zeroProfile_correctionSumOnStrictSupport
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (n / 3))) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩;
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (1 : MvPolynomial (Fin (n / 3)) ℚ) *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns);
    let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e);
    (∑ j ∈ S,
      MvPolynomial.coeff (Finsupp.single (e j) 1) q *
        MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X (e j) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns))) =
      ∑ j ∈ S, -((-1 : ℚ) ^ (S.erase j).card) := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (1 : MvPolynomial (Fin (n / 3)) ℚ) *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
  refine Finset.sum_congr rfl ?_
  intro j hj
  simpa [e, q, α] using
    routeBPaperFaithfulTPhi_unitShift_zeroProfile_correctionSummand
      M n hn2 htb hns S j hj

/-- The zero-profile strict-support correction sum is a single cardinality
factor, because every erased strict tag has cardinality `|S|-1`. -/
theorem routeBPaperFaithfulTPhi_unitShift_zeroProfile_correctionSumOnStrictSupport_card
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (n / 3))) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩;
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (1 : MvPolynomial (Fin (n / 3)) ℚ) *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns);
    let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e);
    (∑ j ∈ S,
      MvPolynomial.coeff (Finsupp.single (e j) 1) q *
        MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X (e j) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns))) =
      -((S.card : ℚ) * ((-1 : ℚ) ^ (S.card - 1))) := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (1 : MvPolynomial (Fin (n / 3)) ℚ) *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
  have hsum :=
    routeBPaperFaithfulTPhi_unitShift_zeroProfile_correctionSumOnStrictSupport
      M n hn2 htb hns S
  have hconst :
      (∑ j ∈ S, -((-1 : ℚ) ^ (S.erase j).card)) =
        ∑ _j ∈ S, -((-1 : ℚ) ^ (S.card - 1)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.card_erase_of_mem hj]
  have hsumConst :
      (∑ _j ∈ S, -((-1 : ℚ) ^ (S.card - 1))) =
        -((S.card : ℚ) * ((-1 : ℚ) ^ (S.card - 1))) := by
    simp [Finset.sum_const]
  calc
    (∑ j ∈ S,
      MvPolynomial.coeff (Finsupp.single (e j) 1) q *
        MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X (e j) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns)))
        = ∑ j ∈ S, -((-1 : ℚ) ^ (S.erase j).card) := by
          simpa [e, q, α] using hsum
    _ = ∑ _j ∈ S, -((-1 : ℚ) ^ (S.card - 1)) := hconst
    _ = -((S.card : ℚ) * ((-1 : ℚ) ^ (S.card - 1))) := hsumConst

/-- Collapse the derivative singleton-normalizer correction sum over the
strict tagged support.  This leaves only the explicit membership-in-`T`
coefficient factor. -/
theorem routeBPaperFaithfulTPhi_unitShift_derivative_correctionSumOnStrictSupport
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S T : Finset (Fin (n / 3))) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩;
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns);
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p;
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
          SPDP.iterDerivList T.toList r));
    let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e);
    (∑ j ∈ S,
      MvPolynomial.coeff (Finsupp.single (e j) 1) d *
        MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X (e j) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns))) =
      ∑ j ∈ S,
        ((2 : ℚ) ^ (({j} : Finset (Fin (n / 3))) ∩ T).card *
            (-1) ^ (({j} : Finset (Fin (n / 3))) \ T).card *
            (-1) ^ (T \ ({j} : Finset (Fin (n / 3)))).card) *
          ((-1 : ℚ) ^ (S.erase j).card) := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
        SPDP.iterDerivList T.toList r))
  let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
  refine Finset.sum_congr rfl ?_
  intro j hj
  simpa [e, p, r, d, α] using
    routeBPaperFaithfulTPhi_unitShift_derivative_correctionSummand
      M n hn2 htb hns S T j hj

/-- The singleton derivative coefficient factor has only two cases: the
shifted coordinate is in the differentiated strict set `T`, or it is not. -/
theorem routeBPaperFaithfulTPhi_unitShift_derivative_singletonFactor_byMembership
    {N : ℕ} (T : Finset (Fin N)) (j : Fin N) :
    (2 : ℚ) ^ (({j} : Finset (Fin N)) ∩ T).card *
        (-1) ^ (({j} : Finset (Fin N)) \ T).card *
        (-1) ^ (T \ ({j} : Finset (Fin N))).card =
      if j ∈ T then
        (2 : ℚ) * (-1) ^ (T.card - 1)
      else
        -((-1 : ℚ) ^ T.card) := by
  classical
  by_cases hjT : j ∈ T
  · have hsdiff : T \ ({j} : Finset (Fin N)) = T.erase j := by
      ext x
      by_cases hxj : x = j <;> simp [Finset.mem_sdiff, hxj]
    have hsingletonDiff : ({j} : Finset (Fin N)) \ T = ∅ := by
      ext x
      by_cases hxj : x = j <;> simp [Finset.mem_sdiff, hxj, hjT]
    simp [hjT, hsdiff, hsingletonDiff, Finset.card_erase_of_mem hjT]
  · have hsdiff : T \ ({j} : Finset (Fin N)) = T := by
      ext x
      by_cases hxj : x = j <;> simp [Finset.mem_sdiff, hxj, hjT]
    have hsingletonDiff : ({j} : Finset (Fin N)) \ T = {j} := by
      ext x
      by_cases hxj : x = j <;> simp [Finset.mem_sdiff, hxj, hjT]
    simp [hjT, hsdiff, hsingletonDiff]

/-- Collapse the derivative strict-support correction sum to the explicit
`S ∩ T` / `S \ T` membership cases.  This is the arithmetic form needed by
the normalized residual balance: the remaining dependence is only whether
each strict source coordinate was differentiated. -/
theorem routeBPaperFaithfulTPhi_unitShift_derivative_correctionSumOnStrictSupport_byMembership
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S T : Finset (Fin (n / 3))) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩;
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns);
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p;
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
          SPDP.iterDerivList T.toList r));
    let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e);
    (∑ j ∈ S,
      MvPolynomial.coeff (Finsupp.single (e j) 1) d *
        MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X (e j) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns))) =
      ∑ j ∈ S,
        (if j ∈ T then
          (2 : ℚ) * (-1) ^ (T.card - 1)
        else
          -((-1 : ℚ) ^ T.card)) *
          ((-1 : ℚ) ^ (S.card - 1)) := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
        SPDP.iterDerivList T.toList r))
  let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
  have hsum :=
    routeBPaperFaithfulTPhi_unitShift_derivative_correctionSumOnStrictSupport
      M n hn2 htb hns S T
  have hcase :
      (∑ j ∈ S,
        ((2 : ℚ) ^ (({j} : Finset (Fin (n / 3))) ∩ T).card *
            (-1) ^ (({j} : Finset (Fin (n / 3))) \ T).card *
            (-1) ^ (T \ ({j} : Finset (Fin (n / 3)))).card) *
          ((-1 : ℚ) ^ (S.erase j).card)) =
        ∑ j ∈ S,
          (if j ∈ T then
            (2 : ℚ) * (-1) ^ (T.card - 1)
          else
            -((-1 : ℚ) ^ T.card)) *
            ((-1 : ℚ) ^ (S.card - 1)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [routeBPaperFaithfulTPhi_unitShift_derivative_singletonFactor_byMembership T j]
    rw [Finset.card_erase_of_mem hj]
  calc
    (∑ j ∈ S,
      MvPolynomial.coeff (Finsupp.single (e j) 1) d *
        MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X (e j) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns)))
        = ∑ j ∈ S,
            ((2 : ℚ) ^ (({j} : Finset (Fin (n / 3))) ∩ T).card *
                (-1) ^ (({j} : Finset (Fin (n / 3))) \ T).card *
                (-1) ^ (T \ ({j} : Finset (Fin (n / 3)))).card) *
              ((-1 : ℚ) ^ (S.erase j).card) := by
          simpa [e, p, r, d, α] using hsum
    _ = ∑ j ∈ S,
          (if j ∈ T then
            (2 : ℚ) * (-1) ^ (T.card - 1)
          else
            -((-1 : ℚ) ^ T.card)) *
            ((-1 : ℚ) ^ (S.card - 1)) := hcase

/-- Split the derivative correction sum into the two finite regions
`S ∩ T` and `S \ T`. -/
theorem routeBPaperFaithfulTPhi_unitShift_derivative_correctionSumOnStrictSupport_inter_sdiff
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S T : Finset (Fin (n / 3))) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩;
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns);
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p;
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
          SPDP.iterDerivList T.toList r));
    let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e);
    (∑ j ∈ S,
      MvPolynomial.coeff (Finsupp.single (e j) 1) d *
        MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X (e j) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns))) =
      ((S ∩ T).card : ℚ) *
        (((2 : ℚ) * (-1) ^ (T.card - 1)) *
          ((-1 : ℚ) ^ (S.card - 1))) +
      ((S \ T).card : ℚ) *
        ((-((-1 : ℚ) ^ T.card)) *
          ((-1 : ℚ) ^ (S.card - 1))) := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
        SPDP.iterDerivList T.toList r))
  let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
  have hmem :=
    routeBPaperFaithfulTPhi_unitShift_derivative_correctionSumOnStrictSupport_byMembership
      M n hn2 htb hns S T
  let a : ℚ := (2 : ℚ) * (-1) ^ (T.card - 1)
  let b : ℚ := -((-1 : ℚ) ^ T.card)
  let c : ℚ := (-1 : ℚ) ^ (S.card - 1)
  have hsplit :
      (∑ j ∈ S, (if j ∈ T then a else b) * c) =
        (∑ j ∈ S ∩ T, a * c) + ∑ j ∈ S \ T, b * c := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun j => j ∈ T)
      (fun j => (if j ∈ T then a else b) * c)]
    have hleft :
        (∑ x ∈ S ∩ T, (if x ∈ T then a else b) * c) =
          ∑ x ∈ S ∩ T, a * c := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      exact by simp [Finset.mem_inter.mp hx |>.2]
    have hright :
        (∑ x ∈ S \ T, (if x ∈ T then a else b) * c) =
          ∑ x ∈ S \ T, b * c := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      exact by simp [Finset.mem_sdiff.mp hx |>.2]
    rw [Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff, hleft, hright]
  calc
    (∑ j ∈ S,
      MvPolynomial.coeff (Finsupp.single (e j) 1) d *
        MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X (e j) *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns)))
        = ∑ j ∈ S,
            (if j ∈ T then
              (2 : ℚ) * (-1) ^ (T.card - 1)
            else
              -((-1 : ℚ) ^ T.card)) *
              ((-1 : ℚ) ^ (S.card - 1)) := by
          simpa [e, p, r, d, α] using hmem
    _ = (∑ j ∈ S ∩ T,
          ((2 : ℚ) * (-1) ^ (T.card - 1)) *
            ((-1 : ℚ) ^ (S.card - 1))) +
        ∑ j ∈ S \ T,
          (-((-1 : ℚ) ^ T.card)) *
            ((-1 : ℚ) ^ (S.card - 1)) := by
          simpa [a, b, c] using hsplit
    _ = ((S ∩ T).card : ℚ) *
          (((2 : ℚ) * (-1) ^ (T.card - 1)) *
            ((-1 : ℚ) ^ (S.card - 1))) +
        ((S \ T).card : ℚ) *
          ((-((-1 : ℚ) ^ T.card)) *
            ((-1 : ℚ) ^ (S.card - 1))) := by
          simp [Finset.sum_const]

/-- A singleton-shift row cannot contribute to a strict tag coefficient
outside that tag's support. -/
theorem routeBPaperFaithfulTPhi_unitShift_singletonShiftRow_tagCoeff_zero_of_notMem
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (n / 3))) (i : Fin n)
    (hi :
      i ∉ (SymmetricPower.tagMonomial
        (S.map ⟨cookLevinStrictFOBFlatMap n,
          cookLevinStrictFOBFlatMap_injective n⟩)).support) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩;
    let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e);
    MvPolynomial.coeff α
      (mlProj
        (MvPolynomial.X i *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)) = 0 := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
  have hml :
      Finsupp.IsMultilinear α := by
    simpa [α] using SymmetricPower.tagMonomial_isMultilinear (S.map e)
  have hcoeff :=
    coeff_mlProj_X_mul_of_isMultilinear
      (cookLevinZeroProfileBaseProduct M n hn2 htb hns) i α hml
  have hi' : i ∉ α.support := by
    simpa [e, α] using hi
  simpa [hi'] using hcoeff

/-- The full ambient singleton-normalizer correction sum restricts to the
strict tag support.  Off-support singleton-shift rows have zero coefficient at
the queried strict tag monomial. -/
theorem routeBPaperFaithfulTPhi_unitShift_correctionSum_restricts_to_strictSupport
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (n / 3))) (row : MvPolynomial (Fin n) ℚ) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩;
    let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e);
    (∑ i : Fin n,
      MvPolynomial.coeff (Finsupp.single i 1) row *
        MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X i *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns))) =
      ∑ j ∈ S,
        MvPolynomial.coeff (Finsupp.single (e j) 1) row *
          MvPolynomial.coeff α
            (mlProj
              (MvPolynomial.X (e j) *
                cookLevinZeroProfileBaseProduct M n hn2 htb hns)) := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
  let f : Fin n → ℚ := fun i =>
    MvPolynomial.coeff (Finsupp.single i 1) row *
      MvPolynomial.coeff α
        (mlProj
          (MvPolynomial.X i *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns))
  have hsupport : α.support = S.map e := by
    ext i
    simpa [α] using tagMonomial_mem_support_iff (S.map e) i
  have hrestrict :
      (∑ i : Fin n, f i) = ∑ i ∈ α.support, f i := by
    rw [← Finset.sum_subset (Finset.subset_univ α.support)]
    intro i _ hi
    have hzero :
        MvPolynomial.coeff α
          (mlProj
            (MvPolynomial.X i *
              cookLevinZeroProfileBaseProduct M n hn2 htb hns)) = 0 := by
      simpa [e, α] using
        routeBPaperFaithfulTPhi_unitShift_singletonShiftRow_tagCoeff_zero_of_notMem
          M n hn2 htb hns S i (by simpa [e, α, hsupport] using hi)
    simp [f, hzero]
  calc
    (∑ i : Fin n, f i) = ∑ i ∈ α.support, f i := hrestrict
    _ = ∑ i ∈ S.map e, f i := by simp [hsupport]
    _ = ∑ j ∈ S, f (e j) := by
      simp [Finset.sum_map]

/-- Plugging the explicit strict tag coefficient formulas into the expanded
normalized coefficient-balance gate leaves exactly the singleton-normalizer
correction identity.  This is the coefficient audit for the normalized
`TΦ` route: the raw zero-profile and extracted derivative coefficients are
computed, so the remaining work is precisely the correction-sum conversion. -/
theorem routeBPaperFaithfulTPhi_normalizedCoeffBalance_forces_unitShift_strictTagCorrection
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbalance :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns)
    (S T : Finset (Fin (n / 3)))
    (hTcard : T.card = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (T.toList.map (cookLevinStrictFOBFlatMap n)))
    (hα :
      ∀ i : Fin n,
        SymmetricPower.tagMonomial
          (S.map ⟨cookLevinStrictFOBFlatMap n,
            cookLevinStrictFOBFlatMap_injective n⟩) ≠
          Finsupp.single i 1) :
    let e : Fin (n / 3) ↪ Fin n :=
      ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
    let factors : Fin (cookLevinFactorList M n hn2 htb hns).length →
        MvPolynomial (Fin n) ℚ :=
      fun i => (cookLevinFactorList M n hn2 htb hns).get i
    let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (1 : MvPolynomial (Fin (n / 3)) ℚ) *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
          SPDP.iterDerivList T.toList r))
    (-1 : ℚ) ^ S.card -
        ∑ i : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1) q *
            MvPolynomial.coeff α
              (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) =
      (2 : ℚ) ^ (S ∩ T).card * (-1) ^ (S \ T).card *
          (-1) ^ (T \ S).card -
        ∑ i : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1) d *
            MvPolynomial.coeff α
              (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  let factors : Fin (cookLevinFactorList M n hn2 htb hns).length →
      MvPolynomial (Fin n) ℚ :=
    fun i => (cookLevinFactorList M n hn2 htb hns).get i
  let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (1 : MvPolynomial (Fin (n / 3)) ℚ) *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
        SPDP.iterDerivList T.toList r))
  have hlen : T.toList.length = Nat.log 2 n := by
    simpa [hTcard] using T.length_toList
  have hdeg :
      (1 : MvPolynomial (Fin (n / 3)) ℚ).totalDegree ≤ Nat.log 2 n := by
    simp
  have hvars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (1 : MvPolynomial (Fin (n / 3)) ℚ)).vars ⊆
        (T.toList.map (cookLevinStrictFOBFlatMap n)).toFinset := by
    simp
  have hα' : ∀ i : Fin n, α ≠ Finsupp.single i 1 := by
    simpa [α, e] using hα
  have hbal :=
    hbalance T.toList (1 : MvPolynomial (Fin (n / 3)) ℚ)
      hlen hdeg hvars hadm α hα'
  have hq :
      MvPolynomial.coeff α q = (-1 : ℚ) ^ S.card := by
    simpa [α, q, e] using
      routeBPaperFaithfulTPhi_unitShift_zeroProfileRow_tagCoeff
        M n hn2 htb hns S
  have hd :
      MvPolynomial.coeff α d =
        (2 : ℚ) ^ (S ∩ T).card * (-1) ^ (S \ T).card *
          (-1) ^ (T \ S).card := by
    simpa [α, d, p, r, e] using
      routeBPaperFaithfulTPhi_unitShift_derivative_tagCoeff_finset
        M n hn2 htb hns S T
  have hbal' :
      MvPolynomial.coeff α q -
          ∑ i : Fin n,
            MvPolynomial.coeff (Finsupp.single i 1) q *
              MvPolynomial.coeff α
                (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) =
        MvPolynomial.coeff α d -
          ∑ i : Fin n,
            MvPolynomial.coeff (Finsupp.single i 1) d *
              MvPolynomial.coeff α
                (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) := by
    simpa [factors, p, r, q, d, α] using hbal
  rw [hq, hd] at hbal'
  simpa [factors, p, r, q, d, α] using hbal'

/-- The expanded normalized balance, after the support restriction and
membership-case sum collapse, is a pure cardinal arithmetic identity.  This is
the fully exposed unit-shift coefficient test for the strict `TΦ` residual
gate. -/
theorem routeBPaperFaithfulTPhi_normalizedCoeffBalance_forces_unitShift_collapsedArithmetic
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbalance :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns)
    (S T : Finset (Fin (n / 3)))
    (hTcard : T.card = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (T.toList.map (cookLevinStrictFOBFlatMap n)))
    (hα :
      ∀ i : Fin n,
        SymmetricPower.tagMonomial
          (S.map ⟨cookLevinStrictFOBFlatMap n,
            cookLevinStrictFOBFlatMap_injective n⟩) ≠
          Finsupp.single i 1) :
    (-1 : ℚ) ^ S.card -
        (-((S.card : ℚ) * ((-1 : ℚ) ^ (S.card - 1)))) =
      (2 : ℚ) ^ (S ∩ T).card * (-1) ^ (S \ T).card *
          (-1) ^ (T \ S).card -
        (((S ∩ T).card : ℚ) *
          (((2 : ℚ) * (-1) ^ (T.card - 1)) *
            ((-1 : ℚ) ^ (S.card - 1))) +
        ((S \ T).card : ℚ) *
          ((-((-1 : ℚ) ^ T.card)) *
            ((-1 : ℚ) ^ (S.card - 1)))) := by
  classical
  let e : Fin (n / 3) ↪ Fin n :=
    ⟨cookLevinStrictFOBFlatMap n, cookLevinStrictFOBFlatMap_injective n⟩
  let factors : Fin (cookLevinFactorList M n hn2 htb hns).length →
      MvPolynomial (Fin n) ℚ :=
    fun i => (cookLevinFactorList M n hn2 htb hns).get i
  let α : Fin n →₀ ℕ := SymmetricPower.tagMonomial (S.map e)
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (1 : MvPolynomial (Fin (n / 3)) ℚ) *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
        SPDP.iterDerivList T.toList r))
  have hforce :=
    routeBPaperFaithfulTPhi_normalizedCoeffBalance_forces_unitShift_strictTagCorrection
      M n hn2 htb hns hbalance S T hTcard hadm hα
  have hforce' :
      (-1 : ℚ) ^ S.card -
          ∑ i : Fin n,
            MvPolynomial.coeff (Finsupp.single i 1) q *
              MvPolynomial.coeff α
                (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) =
        (2 : ℚ) ^ (S ∩ T).card * (-1) ^ (S \ T).card *
            (-1) ^ (T \ S).card -
          ∑ i : Fin n,
            MvPolynomial.coeff (Finsupp.single i 1) d *
              MvPolynomial.coeff α
                (mlProj (MvPolynomial.X i * Finset.univ.prod factors)) := by
    simpa [e, factors, α, p, r, q, d] using hforce
  have hqRestrict :
      (∑ i : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1) q *
            MvPolynomial.coeff α
              (mlProj (MvPolynomial.X i * Finset.univ.prod factors))) =
        ∑ j ∈ S,
          MvPolynomial.coeff (Finsupp.single (e j) 1) q *
            MvPolynomial.coeff α
              (mlProj
                (MvPolynomial.X (e j) *
                  cookLevinZeroProfileBaseProduct M n hn2 htb hns)) := by
    simpa [e, factors, α, q, cookLevinZeroProfileBaseProduct] using
      routeBPaperFaithfulTPhi_unitShift_correctionSum_restricts_to_strictSupport
        M n hn2 htb hns S q
  have hqCard :
      (∑ j ∈ S,
          MvPolynomial.coeff (Finsupp.single (e j) 1) q *
            MvPolynomial.coeff α
              (mlProj
                (MvPolynomial.X (e j) *
                  cookLevinZeroProfileBaseProduct M n hn2 htb hns))) =
        -((S.card : ℚ) * ((-1 : ℚ) ^ (S.card - 1))) := by
    simpa [e, q, α] using
      routeBPaperFaithfulTPhi_unitShift_zeroProfile_correctionSumOnStrictSupport_card
        M n hn2 htb hns S
  have hdRestrict :
      (∑ i : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1) d *
            MvPolynomial.coeff α
              (mlProj (MvPolynomial.X i * Finset.univ.prod factors))) =
        ∑ j ∈ S,
          MvPolynomial.coeff (Finsupp.single (e j) 1) d *
            MvPolynomial.coeff α
              (mlProj
                (MvPolynomial.X (e j) *
                  cookLevinZeroProfileBaseProduct M n hn2 htb hns)) := by
    simpa [e, factors, α, d, cookLevinZeroProfileBaseProduct] using
      routeBPaperFaithfulTPhi_unitShift_correctionSum_restricts_to_strictSupport
        M n hn2 htb hns S d
  have hdCard :
      (∑ j ∈ S,
          MvPolynomial.coeff (Finsupp.single (e j) 1) d *
            MvPolynomial.coeff α
              (mlProj
                (MvPolynomial.X (e j) *
                  cookLevinZeroProfileBaseProduct M n hn2 htb hns))) =
        ((S ∩ T).card : ℚ) *
          (((2 : ℚ) * (-1) ^ (T.card - 1)) *
            ((-1 : ℚ) ^ (S.card - 1))) +
        ((S \ T).card : ℚ) *
          ((-((-1 : ℚ) ^ T.card)) *
            ((-1 : ℚ) ^ (S.card - 1))) := by
    simpa [e, p, r, d, α] using
      routeBPaperFaithfulTPhi_unitShift_derivative_correctionSumOnStrictSupport_inter_sdiff
        M n hn2 htb hns S T
  have hqAmbient :
      (∑ i : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1) q *
            MvPolynomial.coeff α
              (mlProj (MvPolynomial.X i * Finset.univ.prod factors))) =
        -((S.card : ℚ) * ((-1 : ℚ) ^ (S.card - 1))) :=
    hqRestrict.trans hqCard
  have hdAmbient :
      (∑ i : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1) d *
            MvPolynomial.coeff α
              (mlProj (MvPolynomial.X i * Finset.univ.prod factors))) =
        ((S ∩ T).card : ℚ) *
          (((2 : ℚ) * (-1) ^ (T.card - 1)) *
            ((-1 : ℚ) ^ (S.card - 1))) +
        ((S \ T).card : ℚ) *
          ((-((-1 : ℚ) ^ T.card)) *
            ((-1 : ℚ) ^ (S.card - 1))) :=
    hdRestrict.trans hdCard
  rw [hqAmbient, hdAmbient] at hforce'
  simpa [e, factors, α, p, r, q, d] using hforce'

/-- The collapsed cardinal identity fails on the first genuinely
non-singleton strict row when both strict coordinates were differentiated and
the derivative set has even cardinality.  This is the pass/fail test for the
broad normalized unit-shift target: the target cannot include every
two-coordinate strict tag inside an even `T`. -/
theorem routeBPaperFaithfulTPhi_unitShift_collapsedArithmetic_twoTag_noGo
    {N : ℕ} (T : Finset (Fin N)) (j k : Fin N)
    (hj : j ∈ T) (hk : k ∈ T) (hjk : j ≠ k)
    (hEvenT : Even T.card) :
    ¬
      (let S : Finset (Fin N) := {j, k}
       (-1 : ℚ) ^ S.card -
          (-((S.card : ℚ) * ((-1 : ℚ) ^ (S.card - 1)))) =
        (2 : ℚ) ^ (S ∩ T).card * (-1) ^ (S \ T).card *
            (-1) ^ (T \ S).card -
          (((S ∩ T).card : ℚ) *
            (((2 : ℚ) * (-1) ^ (T.card - 1)) *
              ((-1 : ℚ) ^ (S.card - 1))) +
          ((S \ T).card : ℚ) *
            ((-((-1 : ℚ) ^ T.card)) *
              ((-1 : ℚ) ^ (S.card - 1))))) := by
  classical
  intro h
  let S : Finset (Fin N) := {j, k}
  have hScard : S.card = 2 := by
    simpa [S] using Finset.card_pair hjk
  have hSsubT : S ⊆ T := by
    intro x hx
    simp [S] at hx
    rcases hx with rfl | rfl
    · exact hj
    · exact hk
  have hInter : S ∩ T = S := by
    exact Finset.inter_eq_left.mpr hSsubT
  have hSdiff : S \ T = ∅ := by
    exact Finset.sdiff_eq_empty_iff_subset.mpr hSsubT
  have hTdiffCard : (T \ S).card = T.card - 2 := by
    rw [Finset.card_sdiff_of_subset hSsubT, hScard]
  have hcardTge : 2 ≤ T.card := by
    have hle := Finset.card_le_card hSsubT
    simpa [hScard] using hle
  have hEvenTdiff : Even (T.card - 2) := by
    obtain ⟨m, hm⟩ := hEvenT
    refine ⟨m - 1, ?_⟩
    omega
  have hpowT : (-1 : ℚ) ^ T.card = 1 :=
    Even.neg_one_pow hEvenT
  have hpowTpred : (-1 : ℚ) ^ (T.card - 1) = -1 := by
    have hodd : Odd (T.card - 1) := by
      obtain ⟨m, hm⟩ := hEvenT
      refine ⟨m - 1, ?_⟩
      omega
    exact Odd.neg_one_pow hodd
  have hpowTdiff : (-1 : ℚ) ^ (T \ S).card = 1 := by
    rw [hTdiffCard]
    exact Even.neg_one_pow hEvenTdiff
  have h' :
      ((-1 : ℚ) ^ S.card -
          (-((S.card : ℚ) * ((-1 : ℚ) ^ (S.card - 1)))) =
        (2 : ℚ) ^ (S ∩ T).card * (-1) ^ (S \ T).card *
            (-1) ^ (T \ S).card -
          (((S ∩ T).card : ℚ) *
            (((2 : ℚ) * (-1) ^ (T.card - 1)) *
              ((-1 : ℚ) ^ (S.card - 1))) +
          ((S \ T).card : ℚ) *
            ((-((-1 : ℚ) ^ T.card)) *
              ((-1 : ℚ) ^ (S.card - 1))))) := by
    simpa [S] using h
  simp [hScard, hInter, hSdiff, hpowT, hpowTpred, hpowTdiff] at h'
  norm_num at h'

/-- The same collapsed arithmetic obstruction persists for any three strict
source tags contained in an even derivative set.  This records the next
paper-faithful boundary after the two-tag marker: excluding only marked
coefficient pairs is not enough for a pointwise unit-shift coefficient target
if unmarked three-tag probes are still admitted. -/
theorem routeBPaperFaithfulTPhi_unitShift_collapsedArithmetic_threeTagSubset_noGo
    {N : ℕ} (S T : Finset (Fin N))
    (hScard : S.card = 3) (hSsubT : S ⊆ T)
    (hEvenT : Even T.card) :
    ¬
      ((-1 : ℚ) ^ S.card -
          (-((S.card : ℚ) * ((-1 : ℚ) ^ (S.card - 1)))) =
        (2 : ℚ) ^ (S ∩ T).card * (-1) ^ (S \ T).card *
            (-1) ^ (T \ S).card -
          (((S ∩ T).card : ℚ) *
            (((2 : ℚ) * (-1) ^ (T.card - 1)) *
              ((-1 : ℚ) ^ (S.card - 1))) +
          ((S \ T).card : ℚ) *
            ((-((-1 : ℚ) ^ T.card)) *
              ((-1 : ℚ) ^ (S.card - 1))))) := by
  classical
  intro h
  have hInter : S ∩ T = S := by
    exact Finset.inter_eq_left.mpr hSsubT
  have hSdiff : S \ T = ∅ := by
    exact Finset.sdiff_eq_empty_iff_subset.mpr hSsubT
  have hTdiffCard : (T \ S).card = T.card - 3 := by
    rw [Finset.card_sdiff_of_subset hSsubT, hScard]
  have hcardTge : 3 ≤ T.card := by
    have hle := Finset.card_le_card hSsubT
    simpa [hScard] using hle
  have hpowT : (-1 : ℚ) ^ T.card = 1 :=
    Even.neg_one_pow hEvenT
  have hpowTpred : (-1 : ℚ) ^ (T.card - 1) = -1 := by
    have hodd : Odd (T.card - 1) := by
      obtain ⟨m, hm⟩ := hEvenT
      refine ⟨m - 1, ?_⟩
      omega
    exact Odd.neg_one_pow hodd
  have hOddTdiff : Odd (T.card - 3) := by
    obtain ⟨m, hm⟩ := hEvenT
    refine ⟨m - 2, ?_⟩
    omega
  have hpowTdiff : (-1 : ℚ) ^ (T \ S).card = -1 := by
    rw [hTdiffCard]
    exact Odd.neg_one_pow hOddTdiff
  simp [hScard, hInter, hSdiff, hpowT, hpowTpred, hpowTdiff] at h
  norm_num at h

/-- Concrete no-go form for the broad normalized coefficient-balance target:
if an even derivative set contains two distinct strict source coordinates, the
collapsed arithmetic test rules out the current broad unit-shift balance. -/
theorem routeBPaperFaithfulTPhi_not_normalizedCoeffBalance_of_twoDifferentiatedStrictTags_even
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (T : Finset (Fin (n / 3))) (j k : Fin (n / 3))
    (hTcard : T.card = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (T.toList.map (cookLevinStrictFOBFlatMap n)))
    (hj : j ∈ T) (hk : k ∈ T) (hjk : j ≠ k)
    (hEvenT : Even T.card)
    (hα :
      ∀ i : Fin n,
        SymmetricPower.tagMonomial
          (({j, k} : Finset (Fin (n / 3))).map
            ⟨cookLevinStrictFOBFlatMap n,
              cookLevinStrictFOBFlatMap_injective n⟩) ≠
          Finsupp.single i 1) :
    ¬ RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns := by
  intro hbalance
  have hcollapsed :=
    routeBPaperFaithfulTPhi_normalizedCoeffBalance_forces_unitShift_collapsedArithmetic
      M n hn2 htb hns hbalance ({j, k} : Finset (Fin (n / 3))) T
      hTcard hadm hα
  exact
    routeBPaperFaithfulTPhi_unitShift_collapsedArithmetic_twoTag_noGo
      T j k hj hk hjk hEvenT hcollapsed

/-- The compact non-singleton normalized coefficient identity has the same
two-tag obstruction as the expanded balance form.  Thus the range-wide
non-singleton target is still too broad; the paper-faithful route must use the
narrowed canonical/profile row family. -/
theorem routeBPaperFaithfulTPhi_not_normalizedNonSingletonCoeffIdentity_of_twoDifferentiatedStrictTags_even
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (T : Finset (Fin (n / 3))) (j k : Fin (n / 3))
    (hTcard : T.card = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (T.toList.map (cookLevinStrictFOBFlatMap n)))
    (hj : j ∈ T) (hk : k ∈ T) (hjk : j ≠ k)
    (hEvenT : Even T.card)
    (hα :
      ∀ i : Fin n,
        SymmetricPower.tagMonomial
          (({j, k} : Finset (Fin (n / 3))).map
            ⟨cookLevinStrictFOBFlatMap n,
              cookLevinStrictFOBFlatMap_injective n⟩) ≠
          Finsupp.single i 1) :
    ¬ RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
        M n hn2 htb hns := by
  intro hcoeff
  exact
    routeBPaperFaithfulTPhi_not_normalizedCoeffBalance_of_twoDifferentiatedStrictTags_even
      M n hn2 htb hns T j k hTcard hadm hj hk hjk hEvenT hα
      (routeBPaperFaithfulTPhi_coeffBalance_of_normalizedNonSingletonCoeffIdentity
        M n hn2 htb hns hcoeff)

/-- The same two-tag arithmetic obstruction rules out the restricted residual
balance for the canonical singleton quotient projection.  This pins the exact
failure point for the current restricted-row route: if the row family admits an
even derivative set containing two distinct strict source tags, then the
restricted residual identity would imply the already-refuted normalized
coefficient balance. -/
theorem routeBPaperFaithfulTPhi_not_restrictedResidualBalance_of_twoDifferentiatedStrictTags_even
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (T : Finset (Fin (n / 3))) (j k : Fin (n / 3))
    (hTcard : T.card = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (T.toList.map (cookLevinStrictFOBFlatMap n)))
    (hj : j ∈ T) (hk : k ∈ T) (hjk : j ≠ k)
    (hEvenT : Even T.card)
    (hα :
      ∀ i : Fin n,
        SymmetricPower.tagMonomial
          (({j, k} : Finset (Fin (n / 3))).map
            ⟨cookLevinStrictFOBFlatMap n,
              cookLevinStrictFOBFlatMap_injective n⟩) ≠
          Finsupp.single i 1) :
    ¬ RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) := by
  intro hres
  exact
    routeBPaperFaithfulTPhi_not_normalizedCoeffBalance_of_twoDifferentiatedStrictTags_even
      M n hn2 htb hns T j k hTcard hadm hj hk hjk hEvenT hα
      (routeBPaperFaithfulTPhi_coeffBalance_of_restrictedResidualBalance
        M n hn2 htb hns hres)

/-- Consequently the restricted zero-profile row identity itself cannot be
proved for the canonical singleton quotient projection over such a two-tag
even derivative set.  This is the formal obstruction requested instead of a
fake close: the broad restricted identity remains too strong unless the
row-family/canonical-profile gate excludes or absorbs these multi-tag probes. -/
theorem routeBPaperFaithfulTPhi_not_restrictedZeroProfileRowIdentity_of_twoDifferentiatedStrictTags_even
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (T : Finset (Fin (n / 3))) (j k : Fin (n / 3))
    (hTcard : T.card = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (T.toList.map (cookLevinStrictFOBFlatMap n)))
    (hj : j ∈ T) (hk : k ∈ T) (hjk : j ≠ k)
    (hEvenT : Even T.card)
    (hα :
      ∀ i : Fin n,
        SymmetricPower.tagMonomial
          (({j, k} : Finset (Fin (n / 3))).map
            ⟨cookLevinStrictFOBFlatMap n,
              cookLevinStrictFOBFlatMap_injective n⟩) ≠
          Finsupp.single i 1) :
    ¬ RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) := by
  exact
    routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_noGo_of_not_restrictedResidualBalance
      M n hn2 htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
      (routeBPaperFaithfulTPhi_not_restrictedResidualBalance_of_twoDifferentiatedStrictTags_even
        M n hn2 htb hns T j k hTcard hadm hj hk hjk hEvenT hα)

/-- Actual constant coefficient of the intended strict `TΦ` derivative row,
for the list-shaped source-row interface.  Repeated derivative coordinates are
excluded by `hSnd`; the coefficient is the expected Boolean sign
`(-1)^|S'|`. -/
theorem routeBPaperFaithfulTPhi_unitShift_derivative_constantCoeff
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S' : List (Fin (n / 3)))
    (hSnd : S'.Nodup) :
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    MvPolynomial.coeff (0 : Fin n →₀ ℕ)
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
            SPDP.iterDerivList S' r))) =
      (-1 : ℚ) ^ S'.length := by
  classical
  let T : Finset (Fin (n / 3)) := S'.toFinset
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  have hperm : S'.Perm T.toList := by
    simpa [T] using (List.toFinset_toList hSnd).symm
  have hiter :
      SPDP.iterDerivList S' r = SPDP.iterDerivList T.toList r := by
    exact IterDerivHelpers.iterDerivList_perm hperm r
  have hfinset :=
    routeBPaperFaithfulTPhi_unitShift_derivative_constantCoeff_finset
      M n hn2 htb hns T
  have hcard : T.card = S'.length := by
    simpa [T] using List.toFinset_card_of_nodup hSnd
  simpa [p, r, hiter, hcard] using hfinset

/-- The narrowed strict paper-faithful coefficient target closes for the
selected zero-profile unit-shift canonical rows.

All formerly failing probes are outside
`routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRowFamily`: two-tag and
higher multi-tag probes are not in the zero coefficient profile, and odd
unit-shift rows are excluded by the even-length field.  The remaining equality
is the constant-coefficient computation: the zero-profile side is `1`, the
strict derivative side is `(-1)^|S'| = 1`, and singleton correction sums vanish
at the constant monomial. -/
theorem routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance_proved
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance
      M n hn2 htb hns := by
  classical
  intro S' shift hSlen hshiftDegree hshiftVars hadm α _hα hrow
  rcases hrow with ⟨_hrowUnmarked, hshiftUnit, hαzero, hSnd, hEven⟩
  subst shift
  subst α
  let factors : Fin (cookLevinFactorList M n hn2 htb hns).length →
      MvPolynomial (Fin n) ℚ :=
    fun i => (cookLevinFactorList M n hn2 htb hns).get i
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (1 : MvPolynomial (Fin (n / 3)) ℚ) *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
        SPDP.iterDerivList S' r))
  have hq : MvPolynomial.coeff (0 : Fin n →₀ ℕ) q = (1 : ℚ) := by
    simpa [q] using
      routeBPaperFaithfulTPhi_unitShift_zeroProfileRow_constantCoeff
        M n hn2 htb hns
  have hdPow : MvPolynomial.coeff (0 : Fin n →₀ ℕ) d =
      (-1 : ℚ) ^ S'.length := by
    simpa [p, r, d] using
      routeBPaperFaithfulTPhi_unitShift_derivative_constantCoeff
        M n hn2 htb hns S' hSnd
  have hpow : (-1 : ℚ) ^ S'.length = (1 : ℚ) :=
    Even.neg_one_pow hEven
  have hd : MvPolynomial.coeff (0 : Fin n →₀ ℕ) d = (1 : ℚ) := by
    rw [hdPow, hpow]
  have hsumq :
      (∑ i : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1) q *
            MvPolynomial.coeff (0 : Fin n →₀ ℕ)
              (mlProj (MvPolynomial.X i * Finset.univ.prod factors))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _hi
    rw [coeff_zero_mlProj_X_mul, mul_zero]
  have hsumd :
      (∑ i : Fin n,
          MvPolynomial.coeff (Finsupp.single i 1) d *
            MvPolynomial.coeff (0 : Fin n →₀ ℕ)
              (mlProj (MvPolynomial.X i * Finset.univ.prod factors))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _hi
    rw [coeff_zero_mlProj_X_mul, mul_zero]
  dsimp only
  rw [hq, hd, hsumq, hsumd]

/-- Expanded algebraic form of the proved narrowed coefficient target. -/
theorem routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffAlgebra_proved
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffAlgebra
      M n hn2 htb hns :=
  (routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance_iff_algebra
    M n hn2 htb hns).mp
    (routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance_proved
      M n hn2 htb hns)


/-- Direct corollary: the proved narrowed coefficient balance supplies the
narrowed normalized coefficient identity without passing the balance as an
argument. -/
theorem routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRestrictedNormalizedCoeffIdentity_proved
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRestrictedNormalizedCoeffIdentity
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalRestrictedNormalizedCoeffIdentity_of_balance
    M n hn2 htb hns
    (routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance_proved
      M n hn2 htb hns)

/-- Direct corollary: the proved narrowed coefficient balance packages the
paper-faithful canonical/profile residual-balance data with the strict
paper-faithful row family. -/
def routeBPaperFaithfulTPhi_canonicalProfileResidualBalance_strictPaperFaithful_proved
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiCanonicalProfileResidualBalance
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_canonicalProfileResidualBalance_of_strictPaperFaithfulCoeffBalance
    M n hn2 htb hns
    (routeBPaperFaithfulTPhiStrictPaperFaithfulCanonicalCoeffBalance_proved
      M n hn2 htb hns)

/-- Even strict derivative rows pass the unit-shift constant-coefficient test:
their extracted derivative constant term is `1`. -/
theorem routeBPaperFaithfulTPhi_unitShift_derivative_constantCoeff_one_of_even_length
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S' : List (Fin (n / 3)))
    (hSnd : S'.Nodup)
    (hEven : Even S'.length) :
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    MvPolynomial.coeff (0 : Fin n →₀ ℕ)
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj
          ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
            SPDP.iterDerivList S' r))) = (1 : ℚ) := by
  classical
  have hcoeff :=
    routeBPaperFaithfulTPhi_unitShift_derivative_constantCoeff
      M n hn2 htb hns S' hSnd
  have hpow : (-1 : ℚ) ^ S'.length = 1 :=
    Even.neg_one_pow hEven
  simpa [hpow] using hcoeff

/-- Unit-shift no-go form: one admissible strict derivative list whose
extracted derivative row has constant coefficient different from `1` rules out
the singleton-residual target. -/
theorem routeBPaperFaithfulTPhi_not_singletonResidual_of_unitShift_derivative_constantCoeff_ne_one
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S' : List (Fin (n / 3)))
    (hSlen : S'.length = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)))
    (hcoeff_ne :
      let p : MvPolynomial (Fin n) ℚ :=
        compiledPoly (cook_levin_compilation M n hn2 htb hns)
      let r : MvPolynomial (Fin (n / 3)) ℚ :=
        MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n) p
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj
            ((1 : MvPolynomial (Fin (n / 3)) ℚ) *
              SPDP.iterDerivList S' r))) ≠ (1 : ℚ)) :
    ¬ RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns := by
  intro hres
  exact hcoeff_ne
    (routeBPaperFaithfulTPhi_singletonResidual_forces_unitShift_derivative_constantCoeff_one
      M n hn2 htb hns hres S' hSlen hadm)

/-- Odd strict derivative rows fail the unit-shift singleton-residual constant
test.  Thus the residual target can only be viable for strict row families
whose intended row length is even, or after an additional normalization that
changes this sign. -/
theorem routeBPaperFaithfulTPhi_not_singletonResidual_of_unitShift_odd_length
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S' : List (Fin (n / 3)))
    (hSnd : S'.Nodup)
    (hSlen : S'.length = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)))
    (hOdd : Odd S'.length) :
    ¬ RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns := by
  classical
  refine
    routeBPaperFaithfulTPhi_not_singletonResidual_of_unitShift_derivative_constantCoeff_ne_one
      M n hn2 htb hns S' hSlen hadm ?_
  have hcoeff :=
    routeBPaperFaithfulTPhi_unitShift_derivative_constantCoeff
      M n hn2 htb hns S' hSnd
  have hpow : (-1 : ℚ) ^ S'.length = -1 := by
    exact (neg_one_pow_eq_neg_one_iff_odd
      (by norm_num : (-1 : ℚ) ≠ 1)).mpr hOdd
  dsimp only
  intro hEq
  have hbad : (-1 : ℚ) ^ S'.length = 1 := hcoeff.symm.trans hEq
  rw [hpow] at hbad
  norm_num at hbad

/-- The broad strict-unmarked algebra target is still too wide if it admits an
odd unit-shift strict derivative row.  The zero coefficient profile is
unmarked and canonical for the strict normal-form scheme, so the algebra would
force the same constant-coefficient equality that the existing Cook-Levin
unit-shift computation refutes. -/
theorem routeBPaperFaithfulTPhi_not_strictUnmarkedCanonicalCoeffAlgebra_of_unitShift_odd_length
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S' : List (Fin (n / 3)))
    (hSnd : S'.Nodup)
    (hSlen : S'.length = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)))
    (hOdd : Odd S'.length) :
    ¬ RouteBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffAlgebra
        M n hn2 htb hns := by
  classical
  intro halgebra
  have hbalance :=
    routeBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffAlgebra_forces_unitShift_constantCoeff_balance
      M n hn2 htb hns halgebra S' hSlen hadm
  have hleft :=
    routeBPaperFaithfulTPhi_unitShift_zeroProfileRow_constantCoeff
      M n hn2 htb hns
  have hright :=
    routeBPaperFaithfulTPhi_unitShift_derivative_constantCoeff
      M n hn2 htb hns S' hSnd
  have hpow : (-1 : ℚ) ^ S'.length = -1 := by
    exact (neg_one_pow_eq_neg_one_iff_odd
      (by norm_num : (-1 : ℚ) ≠ 1)).mpr hOdd
  dsimp only at hbalance hright
  have hbad : (1 : ℚ) = (-1 : ℚ) ^ S'.length :=
    hleft.symm.trans (hbalance.trans hright)
  rw [hpow] at hbad
  norm_num at hbad

/-- The old broad unmarked canonical balance is refuted by the same odd
unit-shift zero-profile probe.  This records that the remaining positive
Route B target must use the paper-faithful parity/normalization/profile row
family, not merely canonicality plus the two-tag marker exclusion. -/
theorem routeBPaperFaithfulTPhi_not_strictUnmarkedCanonicalCoeffBalance_of_unitShift_odd_length
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S' : List (Fin (n / 3)))
    (hSnd : S'.Nodup)
    (hSlen : S'.length = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)))
    (hOdd : Odd S'.length) :
    ¬ RouteBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffBalance
        M n hn2 htb hns := by
  intro hbalance
  exact
    routeBPaperFaithfulTPhi_not_strictUnmarkedCanonicalCoeffAlgebra_of_unitShift_odd_length
      M n hn2 htb hns S' hSnd hSlen hadm hOdd
      ((routeBPaperFaithfulTPhiStrictUnmarkedCanonicalCoeffBalance_iff_algebra
        M n hn2 htb hns).mp hbalance)

/-- Any proof of the strict singleton-normal-form identity must prove that the
renamed restricted derivative row has no degree-one singleton coefficients.
This is the concrete coefficient test for the semantic normalizer target. -/
theorem routeBPaperFaithfulTPhi_singletonNormalFormIdentity_forces_derivativeSingletonCoeff_zero
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormIdentity
        M n hn2 htb hns)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (hSlen : S'.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)))
    (i : Fin n) :
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    MvPolynomial.coeff (Finsupp.single i 1)
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj (shift * SPDP.iterDerivList S' r))) = 0 := by
  classical
  let p : MvPolynomial (Fin n) ℚ :=
    compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let r : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
      (cookLevinStrictFOBFlatMap_injective n) p
  let q : MvPolynomial (Fin n) ℚ :=
    mlProj
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
        cookLevinZeroProfileBaseProduct M n hn2 htb hns)
  let d : MvPolynomial (Fin n) ℚ :=
    MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
      (mlProj (shift * SPDP.iterDerivList S' r))
  have hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
          (Finset.univ.prod
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) =
        (1 : ℚ) := by
    simpa [cookLevinZeroProfileBaseProduct] using
      cookLevinZeroProfileBaseProduct_coeff_zero M n hn2 htb hns
  have hrow :
      zeroProfileSingletonNormalFormProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q = d := by
    simpa [p, r, q, d] using
      hnorm S' shift hSlen hshiftDegree hshiftVars hadm
  have hcoeff :
      MvPolynomial.coeff (Finsupp.single i 1)
          (zeroProfileSingletonNormalFormProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q) = 0 :=
    zeroProfileSingletonNormalFormProjection_coeff_single_eq_zero
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      hconst q i
  rw [hrow] at hcoeff
  simpa [p, r, d] using hcoeff

/-- Contrapositive obstruction for the explicit singleton-normal-form identity:
one strict query whose renamed restricted derivative row has a nonzero
degree-one singleton coefficient rules out the global identity. -/
theorem routeBPaperFaithfulTPhi_not_singletonNormalFormIdentity_of_derivativeSingletonCoeff_ne_zero
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ)
    (hSlen : S'.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars :
      (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
        (S'.map (cookLevinStrictFOBFlatMap n)).toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (S'.map (cookLevinStrictFOBFlatMap n)))
    (i : Fin n)
    (hcoeff_ne :
      let p : MvPolynomial (Fin n) ℚ :=
        compiledPoly (cook_levin_compilation M n hn2 htb hns)
      let r : MvPolynomial (Fin (n / 3)) ℚ :=
        MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n) p
      MvPolynomial.coeff (Finsupp.single i 1)
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * SPDP.iterDerivList S' r))) ≠ 0) :
    ¬ RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormIdentity
        M n hn2 htb hns := by
  intro hnorm
  exact hcoeff_ne
    (routeBPaperFaithfulTPhi_singletonNormalFormIdentity_forces_derivativeSingletonCoeff_zero
      M n hn2 htb hns hnorm S' shift
      hSlen hshiftDegree hshiftVars hadm i)

/-- Local Boolean-factor obstruction behind the failed raw normal-form row
identity: the singleton normalizer always erases degree-one coefficients, but
the actual Boolean Cook-Levin derivative has singleton coefficient `2`.

This is the coefficient-level reason the final row algebra must be a genuine
quotient/residual statement; it cannot be closed by asserting that the raw
Boolean derivative row is already the singleton-normal representative. -/
theorem routeBPaperFaithfulTPhi_boolFactorDerivative_not_singletonNormalForm
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hconst :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (Finset.univ.prod factors) = (1 : ℚ))
    (v : Fin n) :
    zeroProfileSingletonNormalFormProjection factors
        (mlProj (SymmetricPower.boolFactor n v :
          MvPolynomial (Fin n) ℚ)) ≠
      MvPolynomial.pderiv v
        (SymmetricPower.boolFactor n v : MvPolynomial (Fin n) ℚ) := by
  intro h
  have hleft :
      MvPolynomial.coeff (Finsupp.single v 1)
          (zeroProfileSingletonNormalFormProjection factors
            (mlProj (SymmetricPower.boolFactor n v :
              MvPolynomial (Fin n) ℚ))) = 0 :=
    zeroProfileSingletonNormalFormProjection_coeff_single_eq_zero
      factors hconst
      (mlProj (SymmetricPower.boolFactor n v :
        MvPolynomial (Fin n) ℚ)) v
  have hright :
      MvPolynomial.coeff (Finsupp.single v 1)
        (MvPolynomial.pderiv v
          (SymmetricPower.boolFactor n v :
            MvPolynomial (Fin n) ℚ)) = 2 :=
    SymmetricPower.coeff_single_pderiv_boolFactor v
  have hcoeff :=
    congrArg
      (fun p : MvPolynomial (Fin n) ℚ =>
        MvPolynomial.coeff (Finsupp.single v 1) p) h
  have hbad : (0 : ℚ) = 2 := by
    simpa [hleft, hright] using hcoeff
  norm_num at hbad

/-- The same Boolean-factor calculation rules out treating the raw Boolean
derivative as merely singleton-shift residual noise away from the
undifferentiated Boolean row.  The residual has constant coefficient `2`,
whereas every singleton-shift residual has constant coefficient `0`. -/
theorem routeBPaperFaithfulTPhi_boolFactorDerivative_not_singletonResidual
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (v : Fin n) :
    mlProj (SymmetricPower.boolFactor n v : MvPolynomial (Fin n) ℚ) -
        MvPolynomial.pderiv v
          (SymmetricPower.boolFactor n v : MvPolynomial (Fin n) ℚ) ∉
      zeroProfileSingletonShiftSubspace factors := by
  intro hmem
  have hzero :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (mlProj (SymmetricPower.boolFactor n v : MvPolynomial (Fin n) ℚ) -
          MvPolynomial.pderiv v
            (SymmetricPower.boolFactor n v : MvPolynomial (Fin n) ℚ)) = 0 :=
    routeBPaperFaithfulTPhi_zeroProfileSingletonShiftSubspace_coeff_zero
      factors hmem
  have hleft :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (mlProj (SymmetricPower.boolFactor n v :
          MvPolynomial (Fin n) ℚ)) = 1 := by
    rw [MultilinearSPDP.coeff_mlProj_of_isMultilinear_mono _ _
      (by intro i; simp)]
    exact SymmetricPower.coeff_zero_boolFactor v
  have hright :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (MvPolynomial.pderiv v
          (SymmetricPower.boolFactor n v :
            MvPolynomial (Fin n) ℚ)) = -1 :=
    SymmetricPower.coeff_zero_pderiv_boolFactor v
  have hcoeff :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (mlProj (SymmetricPower.boolFactor n v : MvPolynomial (Fin n) ℚ) -
          MvPolynomial.pderiv v
            (SymmetricPower.boolFactor n v : MvPolynomial (Fin n) ℚ)) = 2 := by
    rw [MvPolynomial.coeff_sub, hleft, hright]
    norm_num
  rw [hcoeff] at hzero
  norm_num at hzero

/-- Concrete decomposition form of the strict range-only singleton-quotient
residual gate.

For each strict source-coordinate query, the undifferentiated zero-profile row
`q` must decompose as the displayed differentiated representative `d` plus a
singleton-shift kernel row.  Because the singleton quotient is implemented as
projection onto a classically chosen complement, we must also require `d` to
lie in that chosen complement. -/
def RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientResidualDecomposition
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S' : List (Fin (n / 3)))
    (shift : MvPolynomial (Fin (n / 3)) ℚ),
    S'.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift).vars ⊆
      (S'.map (cookLevinStrictFOBFlatMap n)).toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition
      (S'.map (cookLevinStrictFOBFlatMap n)) →
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj (shift * SPDP.iterDerivList S' r))
    q - d ∈
        zeroProfileSingletonShiftSubspace
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) ∧
      d ∈
        zeroProfileSingletonShiftComplement
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)

private theorem routeBPaperFaithfulTPhi_singletonQuotient_apply_eq_of_decomposition
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    {q d : MvPolynomial (Fin n) ℚ}
    (hker : q - d ∈ zeroProfileSingletonShiftSubspace factors)
    (hcomp : d ∈ zeroProfileSingletonShiftComplement factors) :
    zeroProfileQuotientBySingletonShiftProjection factors q = d := by
  classical
  let S := zeroProfileSingletonShiftSubspace factors
  let C := zeroProfileSingletonShiftComplement factors
  let project := zeroProfileQuotientBySingletonShiftProjection factors
  let hSC : IsCompl S C :=
    zeroProfileSingletonShiftSubspace_isCompl_complement factors
  have hzero : project (q - d) = 0 := by
    exact LinearMap.mem_ker.mp
      (zeroProfileQuotientBySingletonShiftProjection_singletonShiftSubspace_le_ker
        factors hker)
  have hfix : project d = d := by
    simpa [project, zeroProfileQuotientBySingletonShiftProjection, C, hSC] using
      Submodule.IsCompl.projection_apply_left hSC.symm ⟨d, hcomp⟩
  have hsplit : q = (q - d) + d := by
    abel
  calc
    project q = project ((q - d) + d) := congrArg project hsplit
    _ = project (q - d) + project d := by rw [map_add]
    _ = d := by rw [hzero, hfix, zero_add]

private theorem routeBPaperFaithfulTPhi_singletonQuotient_decomposition_of_apply_eq
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    {q d : MvPolynomial (Fin n) ℚ}
    (hqd : zeroProfileQuotientBySingletonShiftProjection factors q = d) :
    q - d ∈ zeroProfileSingletonShiftSubspace factors ∧
      d ∈ zeroProfileSingletonShiftComplement factors := by
  classical
  let project := zeroProfileQuotientBySingletonShiftProjection factors
  let hSC :=
    zeroProfileSingletonShiftSubspace_isCompl_complement factors
  constructor
  · simpa [project, hqd] using
      zeroProfileQuotientBySingletonShiftProjection_residual_mem_singletonShiftSubspace
        factors q
  · rw [← hqd]
    simpa [project, zeroProfileQuotientBySingletonShiftProjection,
      zeroProfileSingletonShiftComplement, hSC] using
      Submodule.IsCompl.projection_apply_mem hSC.symm q

/-- Exact form of the strict range-only singleton-quotient gate: the residual
balance is equivalent to the concrete quotient decomposition above. -/
theorem routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_iff_decomposition
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) ↔
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientResidualDecomposition
        M n hn2 htb hns := by
  classical
  constructor
  · intro hres S' shift hSlen hshiftDegree hshiftVars hadm
    have hrow :
        RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
          M n hn2 htb hns
          (zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) :=
      (routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientRowIdentity_iff_restrictedResidualBalance
        M n hn2 htb hns).mpr hres
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj (shift * SPDP.iterDerivList S' r))
    have hqd :
        zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q = d := by
      have hrow' := hrow S' shift hSlen hshiftDegree hshiftVars hadm
      simpa [p, r, q, d] using hrow'.symm
    exact
      routeBPaperFaithfulTPhi_singletonQuotient_decomposition_of_apply_eq
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) hqd
  · intro hdecomp
    have hrow :
        RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
          M n hn2 htb hns
          (zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) := by
      intro S' shift hSlen hshiftDegree hshiftVars hadm
      let p : MvPolynomial (Fin n) ℚ :=
        compiledPoly (cook_levin_compilation M n hn2 htb hns)
      let r : MvPolynomial (Fin (n / 3)) ℚ :=
        MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
          (cookLevinStrictFOBFlatMap_injective n) p
      let q : MvPolynomial (Fin n) ℚ :=
        mlProj
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift *
            cookLevinZeroProfileBaseProduct M n hn2 htb hns)
      let d : MvPolynomial (Fin n) ℚ :=
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
          (mlProj (shift * SPDP.iterDerivList S' r))
      have hdec := hdecomp S' shift hSlen hshiftDegree hshiftVars hadm
      dsimp only [p, r, q, d] at hdec
      have hqd :
          zeroProfileQuotientBySingletonShiftProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i) q = d :=
        routeBPaperFaithfulTPhi_singletonQuotient_apply_eq_of_decomposition
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          hdec.1 hdec.2
      simpa [p, r, q, d] using hqd.symm
    exact
      (routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientRowIdentity_iff_restrictedResidualBalance
        M n hn2 htb hns).mp hrow

/-- Forward-use version: proving the concrete singleton quotient decomposition
closes the requested strict range-only residual-balance gate. -/
theorem routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_of_decomposition
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdecomp :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientResidualDecomposition
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
      M n hn2 htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) :=
  (routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_iff_decomposition
    M n hn2 htb hns).mpr hdecomp

/-- For the selected singleton quotient projection, the strict residual-balance
gate is exactly the quotient-normal-form residual statement plus the condition
that the extracted derivative row is already the chosen quotient
representative.  This is the semantic form of the remaining strict `TΦ`
algebra: normalized row equality alone is not enough for this raw quotient
consumer unless the derivative representative is fixed. -/
theorem routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_iff_singletonResidual_and_derivativeFixed
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) ↔
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
          M n hn2 htb hns ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
          M n hn2 htb hns := by
  constructor
  · intro hres
    exact
      ⟨routeBPaperFaithfulTPhi_singletonResidual_of_restrictedResidualBalance
          M n hn2 htb hns hres,
        routeBPaperFaithfulTPhi_derivativeFixed_of_restrictedResidualBalance
          M n hn2 htb hns hres⟩
  · rintro ⟨hresidual, hfix⟩
    have hquot :
        RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientRowIdentity
          M n hn2 htb hns :=
      routeBPaperFaithfulTPhi_singletonQuotientRowIdentity_of_singletonResidual
        M n hn2 htb hns hresidual
    have hrow :
        RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
          M n hn2 htb hns
          (zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) :=
      routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_of_singletonQuotientRowIdentity_fixedDerivative
        M n hn2 htb hns hquot hfix
    exact
      (routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientRowIdentity_iff_restrictedResidualBalance
        M n hn2 htb hns).mp hrow

/-- Forward-use form of the semantic strict `TΦ` quotient-residual criterion. -/
theorem routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_of_singletonResidual_derivativeFixed
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hresidual :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormResidual
        M n hn2 htb hns)
    (hfix :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
      M n hn2 htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) :=
  (routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_iff_singletonResidual_and_derivativeFixed
    M n hn2 htb hns).mpr ⟨hresidual, hfix⟩

/-- Normalized row equality is an equivalent way to supply the singleton
residual half of the strict quotient-residual criterion. -/
theorem routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_of_normalizedRows_derivativeFixed
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns)
    (hfix :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
      M n hn2 htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) :=
  routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_of_singletonResidual_derivativeFixed
    M n hn2 htb hns
    ((routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_iff_singletonResidual
      M n hn2 htb hns).mp hnorm)
    hfix

/-- The source-coordinate restricted equality implies the range-only row
identity by the all-range strict-FOB row reduction. -/
theorem routeBPaperFaithfulTPhi_rangePWindowZeroProfileRowIdentity_of_restricted
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns project) :
    RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
      M n hn2 htb hns project := by
  intro S' shift hSlen hshiftDegree hshiftVars hadm
  rw [routeBPaperFaithfulTPhi_rangePWindowRow_eq_renamedRestrictedRow
    M n hn2 htb hns S' shift]
  exact hrow S' shift hSlen hshiftDegree hshiftVars hadm

/-- Source-coordinate restricted row equality plus a projected zero-profile
common span closes the corrected range-only bounded common-span target.

This is the strongest currently honest strict-`TΦ` common-span consumer: after
all-range strict-FOB reduction, it needs exactly the restricted row equality
and the projected finite profile basis. -/
theorem routeBPaperFaithfulTPhi_rangePWindowCommonSpanWithBudget_of_restrictedRowIdentity_projectedCommonSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project (withinProfileBound (Nat.log 2 n)))
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns project) :
    RouteBPaperFaithfulTPhiRangePWindowCommonSpanWithBudget
      M n hn2 htb hns (withinProfileBound (Nat.log 2 n)) :=
  routeBPaperFaithfulTPhi_rangePWindowCommonSpanWithBudget_of_rowIdentity_projectedCommonSpan
    M n hn2 htb hns project hspan
    (routeBPaperFaithfulTPhi_rangePWindowZeroProfileRowIdentity_of_restricted
      M n hn2 htb hns project hrow)

/-- Projected zero-profile common span plus the restricted source-coordinate
row identity supplies the concrete strict profile-subspace classifier
obligation.

This is the paper-faithful replacement for the refuted unquotiented
local-type-normal-form route: the quotient/profile analysis provides the
projected span, while the strict row algebra is only required after projection
on source-coordinate rows. -/
theorem routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_restrictedRowIdentity_projectedCommonSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project (withinProfileBound (Nat.log 2 n)))
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns project) :
    RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
      M n hn2 htb hns :=
  (routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_iff_commonSpanWithBudget
    M n hn2 htb hns).mpr
    (routeBPaperFaithfulTPhi_rangePWindowCommonSpanWithBudget_of_restrictedRowIdentity_projectedCommonSpan
      M n hn2 htb hns project hspan hrow)

/-- Quotient-certificate semantic route to the strict profile-subspace
classifier obligation.

This is deliberately not the broad raw row identity.  The projected span comes
from the quotient type-space certificate, and the row algebra is the semantic
restricted residual-balance statement for that certificate's selected
projection. -/
theorem routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_quotientTypeCertificate_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (cert :
      ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        typeBudget)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns cert.project)
    (hbudget : typeBudget ≤ withinProfileBound (Nat.log 2 n)) :
    RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_restrictedRowIdentity_projectedCommonSpan
    M n hn2 htb hns cert.project
    (zeroProfileProjectedCommonSpanWithBudget_mono
      (κ := Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      cert.project
      (cookLevinZeroProfileProjectedCommonSpanWithBudget_of_quotientTypeCertificate
        M n hn2 htb hns cert)
      hbudget)
    (routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_of_restrictedResidualBalance
      M n hn2 htb hns cert.project hres)

/-- Existential quotient-normal-form version of the semantic classifier route.
The residual-balance proof is required only for the selected quotient
certificate; no raw range-wide identity is asserted. -/
theorem routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_quotientTypeNormalFormObligation_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (hquot :
      CookLevinZeroProfileQuotientTypeNormalFormObligation
        M n hn2 htb hns typeBudget)
    (hres :
      ∀ cert :
        ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          typeBudget,
        RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
          M n hn2 htb hns cert.project)
    (hbudget : typeBudget ≤ withinProfileBound (Nat.log 2 n)) :
    RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
      M n hn2 htb hns := by
  rcases hquot with ⟨cert⟩
  exact
    routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_quotientTypeCertificate_restrictedResidualBalance
      M n hn2 htb hns cert (hres cert) hbudget

/-- Concrete singleton-quotient certificate route from the semantic
normal-form row algebra.

This is the projected/quotient strict `TΦ` close-out used by the paper-faithful
branch: the singleton quotient certificate supplies the bounded type space, the
normalized non-singleton coefficient computation supplies the singleton
residual, and the derivative-fixed condition is the explicit representative
condition needed to turn quotient residuals into the selected projected row
identity. -/
theorem routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_singletonQuotientTypeCertificate_normalizedCoeff_derivativeFixed
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcoeff :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
        M n hn2 htb hns)
    (hfix :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
        M n hn2 htb hns)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) ≤
        withinProfileBound (Nat.log 2 n)) :
    RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
      M n hn2 htb hns := by
  let cert :=
    zeroProfileSingletonQuotientTypeSpaceCertificate_projectedFinrank
      (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
  have hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns :=
    routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_normalizedNonSingletonCoeff
      M n hn2 htb hns hcoeff
  have hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns cert.project := by
    simpa [cert, zeroProfileSingletonQuotientTypeSpaceCertificate_projectedFinrank] using
      routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_of_normalizedRows_derivativeFixed
        M n hn2 htb hns hnorm hfix
  exact
    routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_quotientTypeCertificate_restrictedResidualBalance
      M n hn2 htb hns cert hres hbudget

private theorem routeBPaperFaithfulTPhi_strictFOB_preimageList
    (n : ℕ) (S : List (Fin n))
    (hS : ∀ v ∈ S, v ∈ Set.range (cookLevinStrictFOBFlatMap n)) :
    ∃ S' : List (Fin (n / 3)),
      S'.map (cookLevinStrictFOBFlatMap n) = S := by
  induction S with
  | nil =>
      exact ⟨[], rfl⟩
  | cons v rest ih =>
      rcases hS v (by simp) with ⟨v', rfl⟩
      have hrest :
          ∀ w ∈ rest, w ∈ Set.range (cookLevinStrictFOBFlatMap n) := by
        intro w hw
        exact hS w (by simp [hw])
      rcases ih hrest with ⟨rest', hrest'⟩
      exact ⟨v' :: rest', by simp [hrest']⟩

/-- The corrected range-only row identity is enough for every generator of the
existing strict-`TΦ` projected P-window: off-range derivative lists contribute
the zero row, and all-range rows are pulled back to `Fin (n / 3)`. -/
theorem routeBPaperFaithfulTPhi_projectedPWindowGenerator_mem_zeroProfileProjection_of_rangeRowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
        M n hn2 htb hns project)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (hSlen : S.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars : shift.vars ⊆ S.toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S) :
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      zeroProfileProjectedShiftSpan (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project := by
  classical
  by_cases hoff :
      ∃ v ∈ S, v ∉ Set.range (cookLevinStrictFOBFlatMap n)
  · have hlhs :
        mlProj
            (shift * SPDP.iterDerivList S
              ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
                (compiledPoly
                  (cook_levin_compilation M n hn2 htb hns)))) = 0 := by
      rw [routeBPaperFaithfulTPhiAmbientGauge_compiledPoly_eq_reexpandedStrictFOB
        M n hn2 htb hns]
      exact
        routeBPaperFaithfulTPhi_strictFOB_offRangeDerivativeRow_zero
          n S shift
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) hoff
    rw [hlhs]
    exact Submodule.zero_mem _
  · have hall :
        ∀ v ∈ S, v ∈ Set.range (cookLevinStrictFOBFlatMap n) := by
      intro v hv
      by_contra hvnot
      exact hoff ⟨v, hv, hvnot⟩
    rcases routeBPaperFaithfulTPhi_strictFOB_preimageList n S hall with
      ⟨S', hS'⟩
    let shift' :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) shift
    have hshiftRange :
        ↑shift.vars ⊆ Set.range (cookLevinStrictFOBFlatMap n) := by
      intro v hv
      exact hall v (List.mem_toFinset.mp (hshiftVars hv))
    have hrename :
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift' = shift := by
      simpa [shift'] using
        routeBPaperFaithfulTPhi_rename_restrictStrictFOB_of_vars_range
          n shift hshiftRange
    have hSlen' : S'.length = Nat.log 2 n := by
      have hmapLen :
          (S'.map (cookLevinStrictFOBFlatMap n)).length =
            Nat.log 2 n := by
        rw [hS']
        exact hSlen
      simpa [List.length_map] using hmapLen
    have hshiftDegree' : shift'.totalDegree ≤ Nat.log 2 n :=
      (MultilinearSPDP.restrictPoly_totalDegree_le ℚ
        (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) shift).trans hshiftDegree
    have hshiftVars' :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift').vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset := by
      rw [hrename, hS']
      exact hshiftVars
    have hadm' :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)) := by
      rw [hS']
      exact hadm
    have hmem :=
      routeBPaperFaithfulTPhi_rangePWindowGenerator_mem_zeroProfileProjection
        M n hn2 htb hns project hrow S' shift'
        hSlen' hshiftDegree' hshiftVars' hadm'
    rw [← hrename, ← hS']
    exact hmem

/-- The corrected range-only strict-`TΦ` row identity feeds the existing
projected zero-profile consumer without requiring the false full derivative
erasure statement. -/
theorem routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rangeRowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
        M n hn2 htb hns project) :
    RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
      M n hn2 htb hns project := by
  rw [RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection]
  unfold mlBlockedSpdpSubspace
  refine Submodule.span_le.mpr ?_
  intro q hq
  rcases hq with
    ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  exact
    routeBPaperFaithfulTPhi_projectedPWindowGenerator_mem_zeroProfileProjection_of_rangeRowIdentity
      M n hn2 htb hns project hrow S shift hSlen
      hshiftDegree hshiftVars hadm

/-- Source-coordinate restricted rows are an even smaller sufficient surface
for the projected zero-profile consumer. -/
theorem routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rangeRestrictedRowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns project) :
    RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
      M n hn2 htb hns project :=
  routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rangeRowIdentity
    M n hn2 htb hns project
    (routeBPaperFaithfulTPhi_rangePWindowZeroProfileRowIdentity_of_restricted
      M n hn2 htb hns project hrow)

/-- The strict `TΦ` row identity is exactly the re-expanded strict-FOB
derivative-erasure statement. -/
theorem routeBPaperFaithfulTPhi_projectedPWindowZeroProfileRowIdentity_iff_strictFOBDerivativeErasure
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) :
    RouteBPaperFaithfulTPhiProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns project ↔
      RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
        M n hn2 htb hns project := by
  constructor
  · intro hrow S shift hSlen hshiftDegree hshiftVars hadm
    rw [← routeBPaperFaithfulTPhiAmbientGauge_compiledPoly_eq_reexpandedStrictFOB
      M n hn2 htb hns]
    rw [hrow S shift hSlen hshiftDegree hshiftVars hadm]
    simp [cookLevinZeroProfileBaseProduct]
  · intro herase S shift hSlen hshiftDegree hshiftVars hadm
    rw [routeBPaperFaithfulTPhiAmbientGauge_compiledPoly_eq_reexpandedStrictFOB
      M n hn2 htb hns]
    rw [herase S shift hSlen hshiftDegree hshiftVars hadm]
    simp [cookLevinZeroProfileBaseProduct]

/-- Exact generator-membership reduction for the strict `TΦ` projected
P-window containment. -/
def RouteBPaperFaithfulTPhiProjectedPWindowZeroProfileGeneratorReduction
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      zeroProfileProjectedShiftSpan (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project

/-- The strict `TΦ` pointwise row identity gives membership of every
projected P-window generator in the projected zero-profile shifted span. -/
theorem routeBPaperFaithfulTPhi_projectedPWindowGenerator_mem_zeroProfileProjection
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hrow :
      RouteBPaperFaithfulTPhiProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns project)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (hSlen : S.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars : shift.vars ⊆ S.toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S) :
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      zeroProfileProjectedShiftSpan (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project := by
  classical
  have hzero :
      mlProj
          (shift *
            Finset.univ.prod
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) ∈
        zeroProfileShiftImageSet (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) := by
    simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
      Set.mem_singleton_iff]
    exact ⟨S, le_of_eq hSlen, shift, hshiftVars, rfl⟩
  have hproject :
      project
          (mlProj
            (shift *
              Finset.univ.prod
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) ∈
        zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          project := by
    exact Submodule.mem_map_of_mem (Submodule.subset_span hzero)
  rw [hrow S shift hSlen hshiftDegree hshiftVars hadm]
  exact hproject

/-- The strict `TΦ` projected P-window containment is exactly the concrete
generator-by-generator zero-profile membership check. -/
theorem routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_iff_generatorReduction
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) :
    RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project ↔
      RouteBPaperFaithfulTPhiProjectedPWindowZeroProfileGeneratorReduction
        M n hn2 htb hns project := by
  classical
  constructor
  · intro hcontrol S shift hSlen hshiftDegree hshiftVars hadm
    apply hcontrol
    unfold mlBlockedSpdpSubspace
    exact Submodule.subset_span
      ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  · intro hgen
    rw [RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection]
    unfold mlBlockedSpdpSubspace
    refine Submodule.span_le.mpr ?_
    intro q hq
    rcases hq with
      ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
    exact hgen S shift hSlen hshiftDegree hshiftVars hadm

/-- The pointwise strict `TΦ` row identity proves the full projected P-window
containment needed by the projected zero-profile hook. -/
theorem routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hrow :
      RouteBPaperFaithfulTPhiProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns project) :
    RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
      M n hn2 htb hns project := by
  exact
    (routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_iff_generatorReduction
      M n hn2 htb hns project).mpr
    (fun S shift hSlen hshiftDegree hshiftVars hadm =>
      routeBPaperFaithfulTPhi_projectedPWindowGenerator_mem_zeroProfileProjection
        M n hn2 htb hns project hrow S shift
        hSlen hshiftDegree hshiftVars hadm)

/-- Re-expanded strict-FOB derivative erasure is the exact missing algebra
which closes the strict `TΦ` projected P-window containment. -/
theorem routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_strictFOBDerivativeErasure
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (herase :
      RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
        M n hn2 htb hns project) :
    RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
      M n hn2 htb hns project :=
  routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rowIdentity
    M n hn2 htb hns project
    ((routeBPaperFaithfulTPhi_projectedPWindowZeroProfileRowIdentity_iff_strictFOBDerivativeErasure
      M n hn2 htb hns project).mpr herase)

/-- The small arithmetic envelope used by the strict-`TΦ` projected
zero-profile hook. -/
theorem routeBPaperFaithfulTPhi_withinProfileBound_log_le_pow_200
    (n : ℕ) (hn2 : n ≥ 2) :
    withinProfileBound (Nat.log 2 n) ≤ n ^ 200 := by
  rw [WithinProfileBound.withinProfileBound_eq_pow8]
  have hbase : Nat.log 2 n + 1 ≤ 2 * n := by
    have hlog : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
    omega
  calc
    (Nat.log 2 n + 1) ^ 8 ≤ (2 * n) ^ 8 :=
      Nat.pow_le_pow_left hbase 8
    _ = 2 ^ 8 * n ^ 8 := by ring
    _ ≤ n ^ 192 * n ^ 8 := by
      apply Nat.mul_le_mul_right
      calc
        (2 : ℕ) ^ 8 = 256 := by norm_num
        _ ≤ 2 ^ 192 := by norm_num
        _ ≤ n ^ 192 := by
          exact Nat.pow_le_pow_left hn2 192
    _ = n ^ 200 := by ring

/-- The corrected paper budget also fits under the ambient `n^200` gauge
envelope.  This is the arithmetic envelope for the §9.3--§9.4
sum-over-profiles route: profile count times local dimension is
`combinedProfileBound κ = (κ+1)^12`, still far below the final `n^200`
budget used by Route B. -/
theorem routeBPaperFaithfulTPhi_combinedProfileBound_log_le_pow_200
    (n : ℕ) (hn2 : n ≥ 2) :
    combinedProfileBound (Nat.log 2 n) ≤ n ^ 200 := by
  rw [SymmetricPowerBound.combinedProfileBound_eq]
  have hbase : Nat.log 2 n + 1 ≤ 2 * n := by
    have hlog : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
    omega
  calc
    (Nat.log 2 n + 1) ^ 12 ≤ (2 * n) ^ 12 :=
      Nat.pow_le_pow_left hbase 12
    _ = 2 ^ 12 * n ^ 12 := by ring
    _ ≤ n ^ 188 * n ^ 12 := by
      apply Nat.mul_le_mul_right
      calc
        (2 : ℕ) ^ 12 = 4096 := by norm_num
        _ ≤ 2 ^ 188 := by norm_num
        _ ≤ n ^ 188 := by
          exact Nat.pow_le_pow_left hn2 188
    _ = n ^ 200 := by ring

/-- Corrected paper-shaped ambient global span cover for the assembled
local-monoid profile basis.  This mirrors the older orbit-rank cover, but
keeps the paper's combined profile budget instead of forcing the data through
the one-profile `withinProfileBound` package. -/
def RouteBPaperFaithfulTPhiStrictPaperAmbientGlobalProfileSpanCover
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
      M n hn2 htb hns) : Prop :=
  MultilinearSPDP.mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
    Submodule.span ℚ
      (↑(routeBPaperFaithfulTPhiStrictPaperGlobalProfileBasis D) :
        Set (MvPolynomial (Fin n) ℚ))

/-- Generator-by-generator form of the corrected paper ambient profile cover. -/
def RouteBPaperFaithfulTPhiStrictPaperAmbientGlobalProfileGeneratorCover
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
      M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      Submodule.span ℚ
        (↑(routeBPaperFaithfulTPhiStrictPaperGlobalProfileBasis D) :
          Set (MvPolynomial (Fin n) ℚ))

/-- The corrected paper ambient cover is equivalent to its generator form. -/
theorem routeBPaperFaithfulTPhi_strictPaperAmbientGlobalProfileSpanCover_iff_generatorCover
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
      M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperAmbientGlobalProfileSpanCover D ↔
      RouteBPaperFaithfulTPhiStrictPaperAmbientGlobalProfileGeneratorCover D := by
  constructor
  · intro hcover S shift hSlen hshiftDegree hshiftVars hadm
    apply hcover
    unfold MultilinearSPDP.mlBlockedSpdpSubspace
    exact Submodule.subset_span
      ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  · intro hgen
    unfold RouteBPaperFaithfulTPhiStrictPaperAmbientGlobalProfileSpanCover
    unfold MultilinearSPDP.mlBlockedSpdpSubspace
    refine Submodule.span_le.mpr ?_
    intro q hq
    rcases hq with ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
    exact hgen S shift hSlen hshiftDegree hshiftVars hadm

/-- Range rows assemble into the corrected paper ambient cover.  The proof is
the same strict first-of-block reduction as the orbit-rank route, but the
target basis is the corrected finite union of local-monoid profile bases. -/
theorem routeBPaperFaithfulTPhi_strictPaperAmbientGlobalProfileSpanCover_of_rangeRows
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
      M n hn2 htb hns)
    (hrange : RouteBPaperFaithfulTPhiStrictPaperRangeRowsGlobalProfileSpanCover D) :
    RouteBPaperFaithfulTPhiStrictPaperAmbientGlobalProfileSpanCover D := by
  classical
  refine
    (routeBPaperFaithfulTPhi_strictPaperAmbientGlobalProfileSpanCover_iff_generatorCover D).mpr ?_
  intro S shift hSlen hshiftDegree hshiftVars hadm
  by_cases hoff : ∃ v ∈ S, v ∉ Set.range (cookLevinStrictFOBFlatMap n)
  · have hlhs :
        mlProj
            (shift * SPDP.iterDerivList S
              ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) = 0 := by
      rw [routeBPaperFaithfulTPhiAmbientGauge_compiledPoly_eq_reexpandedStrictFOB
        M n hn2 htb hns]
      exact
        routeBPaperFaithfulTPhi_strictFOB_offRangeDerivativeRow_zero
          n S shift
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) hoff
    rw [hlhs]
    exact Submodule.zero_mem _
  · have hall : ∀ v ∈ S, v ∈ Set.range (cookLevinStrictFOBFlatMap n) := by
      intro v hv
      by_contra hvnot
      exact hoff ⟨v, hv, hvnot⟩
    rcases routeBPaperFaithfulTPhi_strictFOB_preimageList n S hall with
      ⟨S', hS'⟩
    let shift' :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) shift
    have hshiftRange :
        ↑shift.vars ⊆ Set.range (cookLevinStrictFOBFlatMap n) := by
      intro v hv
      exact hall v (List.mem_toFinset.mp (hshiftVars hv))
    have hrename :
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift' = shift := by
      simpa [shift'] using
        routeBPaperFaithfulTPhi_rename_restrictStrictFOB_of_vars_range
          n shift hshiftRange
    have hSlen' : S'.length = Nat.log 2 n := by
      have hmapLen :
          (S'.map (cookLevinStrictFOBFlatMap n)).length = Nat.log 2 n := by
        rw [hS']
        exact hSlen
      simpa [List.length_map] using hmapLen
    have hshiftDegree' : shift'.totalDegree ≤ Nat.log 2 n :=
      (MultilinearSPDP.restrictPoly_totalDegree_le ℚ
        (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) shift).trans hshiftDegree
    have hshiftVars' :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift').vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset := by
      rw [hrename, hS']
      exact hshiftVars
    have hadm' :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)) := by
      rw [hS']
      exact hadm
    have hmem := hrange S' shift' hSlen' hshiftDegree' hshiftVars' hadm'
    rw [← hrename, ← hS']
    simpa [routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow] using hmem

/-- The corrected paper ambient cover gives the strict ambient rank bound
against `#profiles * localDim`. -/
theorem routeBPaperFaithfulTPhi_strictPaperAmbientMlRankUpper_of_globalProfileSpanCover
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
      M n hn2 htb hns)
    (hcover : RouteBPaperFaithfulTPhiStrictPaperAmbientGlobalProfileSpanCover D) :
    MultilinearSPDP.mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
      Fintype.card D.profileType * D.localDim := by
  unfold MultilinearSPDP.mlBlockedSpdpRank
  have hmono :
      Module.finrank ℚ
          (MultilinearSPDP.mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ≤
        Module.finrank ℚ
          (Submodule.span ℚ
            (↑(routeBPaperFaithfulTPhiStrictPaperGlobalProfileBasis D) :
              Set (MvPolynomial (Fin n) ℚ))) :=
    Submodule.finrank_mono hcover
  exact hmono.trans
    ((finrank_span_finset_le_card
        (routeBPaperFaithfulTPhiStrictPaperGlobalProfileBasis D)).trans
      (routeBPaperFaithfulTPhi_strictPaperGlobalProfileBasis_card_le D))

/-- Corrected paper-shaped P-side close-out from the local-monoid profile
range-row cover.  This is the intended §9.3--§9.4 route: row membership in
canonical-window profile spans, finite union over profiles, combined budget,
then the ambient `n^200` gauge envelope. -/
theorem routeBPaperFaithfulTPhi_pSideBound_of_strictPaperRangeRowsGlobalProfileSpanCover
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
      M n hn2 htb hns)
    (hrange : RouteBPaperFaithfulTPhiStrictPaperRangeRowsGlobalProfileSpanCover D) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) := by
  unfold SATDeciderGaugePSideBound
  exact
    (routeBPaperFaithfulTPhi_strictPaperAmbientMlRankUpper_of_globalProfileSpanCover
      D
      (routeBPaperFaithfulTPhi_strictPaperAmbientGlobalProfileSpanCover_of_rangeRows
        D hrange)).trans
      (D.profileBudget_le.trans
        (routeBPaperFaithfulTPhi_combinedProfileBound_log_le_pow_200 n hn2))

/-- The actual canonical-window local-monoid/profile analysis closes the
P-side bound through the corrected paper-shaped range-row cover. -/
theorem routeBPaperFaithfulTPhi_pSideBound_of_strictCanonicalWindowLocalMonoidProfileAnalysis
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileAnalysis
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) := by
  rcases
    routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover_of_localMonoidProfileCover
      M n hn2 htb hns A with
    ⟨D, hrange⟩
  exact
    routeBPaperFaithfulTPhi_pSideBound_of_strictPaperRangeRowsGlobalProfileSpanCover
      M n hn2 htb hns D hrange

/-- P-side close-out from the separated paper Lemma 29/Lemma 31 local-monoid
profile data. -/
theorem routeBPaperFaithfulTPhi_pSideBound_of_strictCanonicalWindowLocalMonoidProfileData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileData
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) :=
  routeBPaperFaithfulTPhi_pSideBound_of_strictCanonicalWindowLocalMonoidProfileAnalysis
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileAnalysis_of_data
      M n hn2 htb hns D)

/-- P-side close-out from the actual local-monoid/profile analysis, routed
through the separated paper Lemma 29/Lemma 31 data object. -/
theorem routeBPaperFaithfulTPhi_pSideBound_of_strictLocalMonoidProfileAnalysis
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A :
      RouteBPaperFaithfulTPhiStrictLocalMonoidProfileAnalysis
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) :=
  routeBPaperFaithfulTPhi_pSideBound_of_strictCanonicalWindowLocalMonoidProfileData
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData_of_localMonoidProfileAnalysis
      M n hn2 htb hns A)

/-- The paper-faithful global assembly immediately gives the strict ambient
`TΦ` P-side rank bound for the actual gauge.  This is the replacement for the
failed arbitrary-projection row-containment route: once the §9 profile/orbit
matrix assembly is proved, the SAT-decider P-side bound follows directly by
`profileBudget_le` and the landed `withinProfileBound ≤ n^200` arithmetic. -/
theorem routeBPaperFaithfulTPhi_pSideBound_of_strictPaperProfileOrbitGlobalAssembly
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hassembly :
      RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) := by
  rcases hassembly with ⟨D, hrank⟩
  unfold SATDeciderGaugePSideBound
  exact hrank.trans
    (D.profileBudget_le.trans
      (routeBPaperFaithfulTPhi_withinProfileBound_log_le_pow_200 n hn2))

/-- A single chosen orbit package with an ambient matrix-rank upper bound is
the same paper route in constructor form. -/
theorem routeBPaperFaithfulTPhi_pSideBound_of_strictAmbientMlRankUpper
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns)
    (hrank :
      RouteBPaperFaithfulTPhiStrictAmbientMlRankUpper M n hn2 htb hns D) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) :=
  routeBPaperFaithfulTPhi_pSideBound_of_strictPaperProfileOrbitGlobalAssembly
    M n hn2 htb hns ⟨D, hrank⟩

/-- All ambient strict-`TΦ` rows reduce to range rows: off-range derivative
queries vanish, and all-range queries pull back along the strict first-of-block
embedding.  Thus a range-row assembled-profile cover proves the full ambient
assembled-profile cover. -/
theorem routeBPaperFaithfulTPhi_strictAmbientGlobalProfileSpanCover_of_rangeRows
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns)
    (hrange : RouteBPaperFaithfulTPhiStrictRangeRowsGlobalProfileSpanCover D) :
    RouteBPaperFaithfulTPhiStrictAmbientGlobalProfileSpanCover D := by
  classical
  refine
    (routeBPaperFaithfulTPhi_strictAmbientGlobalProfileSpanCover_iff_generatorCover D).mpr ?_
  intro S shift hSlen hshiftDegree hshiftVars hadm
  by_cases hoff : ∃ v ∈ S, v ∉ Set.range (cookLevinStrictFOBFlatMap n)
  · have hlhs :
        mlProj
            (shift * SPDP.iterDerivList S
              ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) = 0 := by
      rw [routeBPaperFaithfulTPhiAmbientGauge_compiledPoly_eq_reexpandedStrictFOB
        M n hn2 htb hns]
      exact
        routeBPaperFaithfulTPhi_strictFOB_offRangeDerivativeRow_zero
          n S shift
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) hoff
    rw [hlhs]
    exact Submodule.zero_mem _
  · have hall : ∀ v ∈ S, v ∈ Set.range (cookLevinStrictFOBFlatMap n) := by
      intro v hv
      by_contra hvnot
      exact hoff ⟨v, hv, hvnot⟩
    rcases routeBPaperFaithfulTPhi_strictFOB_preimageList n S hall with
      ⟨S', hS'⟩
    let shift' :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) shift
    have hshiftRange :
        ↑shift.vars ⊆ Set.range (cookLevinStrictFOBFlatMap n) := by
      intro v hv
      exact hall v (List.mem_toFinset.mp (hshiftVars hv))
    have hrename :
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift' = shift := by
      simpa [shift'] using
        routeBPaperFaithfulTPhi_rename_restrictStrictFOB_of_vars_range
          n shift hshiftRange
    have hSlen' : S'.length = Nat.log 2 n := by
      have hmapLen :
          (S'.map (cookLevinStrictFOBFlatMap n)).length = Nat.log 2 n := by
        rw [hS']
        exact hSlen
      simpa [List.length_map] using hmapLen
    have hshiftDegree' : shift'.totalDegree ≤ Nat.log 2 n :=
      (MultilinearSPDP.restrictPoly_totalDegree_le ℚ
        (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) shift).trans hshiftDegree
    have hshiftVars' :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift').vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset := by
      rw [hrename, hS']
      exact hshiftVars
    have hadm' :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)) := by
      rw [hS']
      exact hadm
    have hmem := hrange S' shift' hSlen' hshiftDegree' hshiftVars' hadm'
    rw [← hrename, ← hS']
    simpa [routeBPaperFaithfulTPhiStrictCanonicalDerivativeRow] using hmem

/-- The full ambient assembled-profile cover is equivalent to the range-row
assembled-profile cover.  Off-range strict-FOB rows vanish; all-range rows are
exactly the source-coordinate rows re-expanded along `cookLevinStrictFOBFlatMap`.
This packages the remaining proof obligation in its paper-faithful range-row
form, with no arbitrary projected-containment detour. -/
theorem routeBPaperFaithfulTPhi_strictAmbientGlobalProfileSpanCover_iff_rangeRows
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictAmbientGlobalProfileSpanCover D ↔
      RouteBPaperFaithfulTPhiStrictRangeRowsGlobalProfileSpanCover D := by
  constructor
  · intro hcover S' shift hSlen hshiftDegree hshiftVars hadm
    apply hcover
    unfold MultilinearSPDP.mlBlockedSpdpSubspace
    exact Submodule.subset_span
      ⟨S'.map (cookLevinStrictFOBFlatMap n),
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift,
        by simpa [List.length_map] using hSlen,
        (MvPolynomial.totalDegree_rename_le (cookLevinStrictFOBFlatMap n) shift).trans
          hshiftDegree,
        hshiftVars,
        hadm,
        rfl⟩
  · exact routeBPaperFaithfulTPhi_strictAmbientGlobalProfileSpanCover_of_rangeRows D

/-- Constructor from the exact remaining range-row cover to the paper global
assembly. -/
theorem routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_rangeRows
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (D : RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
      M n hn2 htb hns)
    (hrange : RouteBPaperFaithfulTPhiStrictRangeRowsGlobalProfileSpanCover D) :
    RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_globalProfileSpanCover
    D
    ((routeBPaperFaithfulTPhi_strictAmbientGlobalProfileSpanCover_iff_rangeRows D).mpr
      hrange)

/-- Range-row profile-cover data closes the paper-faithful strict global
profile/orbit assembly. -/
theorem routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_rangeRowProfileCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D :
      RouteBPaperFaithfulTPhiStrictRangeRowProfileCoverData
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_rangeRows
    (routeBPaperFaithfulTPhi_strictOrbitRankData_of_rangeRowProfileCoverData
      M n hn2 htb hns D)
    (routeBPaperFaithfulTPhi_strictRangeRowsGlobalProfileSpanCover_of_rangeRowProfileCoverData
      M n hn2 htb hns D)

/-- The strict local-monoid/profile classifier closes the paper-faithful global
profile/orbit assembly through the range-row cover theorem. -/
theorem routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_profileSubspaceClassifier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (C :
      RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifier
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_rangeRowProfileCoverData
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_strictRangeRowProfileCoverData_of_classifier
      M n hn2 htb hns C)

/-- Obligation form: proving the actual local-monoid/profile classifier is
enough for the strict paper-faithful global assembly. -/
theorem routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_profileSubspaceClassifierObligation
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hclassifier :
      RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
        M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
      M n hn2 htb hns := by
  rcases hclassifier with ⟨C⟩
  exact
    routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_profileSubspaceClassifier
      M n hn2 htb hns C

/-- A Cook-Levin local-monoid normal-form map plus the strict range row
identity closes the strict paper-faithful profile/orbit global assembly. -/
theorem routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_localTypeNormalForm_rowIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hlocal :
      CookLevinZeroProfileLocalTypeNormalFormObligation M n hn2 htb hns)
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
        M n hn2 htb hns
        (LinearMap.id :
          MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)) :
    RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_profileSubspaceClassifier
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_strictProfileSubspaceClassifier_of_localTypeNormalForm_rowIdentity
      M n hn2 htb hns hlocal hrow)

/-- The source-coordinate restricted zero-profile row identity supplies the
identity-projection strict range-row identity needed by the local-type
normal-form classifier route. -/
theorem routeBPaperFaithfulTPhi_identityRangeRowIdentity_of_restrictedIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hrestricted :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns
        (LinearMap.id :
          MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)) :
    RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
      M n hn2 htb hns
      (LinearMap.id :
        MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) :=
  routeBPaperFaithfulTPhi_rangePWindowZeroProfileRowIdentity_of_restricted
    M n hn2 htb hns
    (LinearMap.id :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    hrestricted

/-- Restricted source-coordinate row equality is enough for the strict
local-type normal-form route, after all-range strict-FOB reduction. -/
theorem routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_localTypeNormalForm_restrictedIdentity
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hlocal :
      CookLevinZeroProfileLocalTypeNormalFormObligation M n hn2 htb hns)
    (hrestricted :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns
        (LinearMap.id :
          MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)) :
    RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
      M n hn2 htb hns :=
  routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_localTypeNormalForm_rowIdentity
    M n hn2 htb hns hlocal
    (routeBPaperFaithfulTPhi_identityRangeRowIdentity_of_restrictedIdentity
      M n hn2 htb hns hrestricted)

/-- Paper-scale obstruction for trying to close the strict local-type route by
proving the full unquotiented Cook-Levin local normal-form obligation.  The
remaining paper-faithful route must use a projected/quotiented profile
condition instead of this full zero-profile local type target. -/
theorem routeBPaperFaithfulTPhi_not_localTypeNormalFormObligation_two_pow_804
    (M : DTM)
    (hn : (2 : ℕ) ^ 804 ≥ 2)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ (2 : ℕ) ^ 804) :
    ¬ CookLevinZeroProfileLocalTypeNormalFormObligation M
      ((2 : ℕ) ^ 804) hn htb hns :=
  not_CookLevinZeroProfileLocalTypeNormalFormObligation_two_pow_804
    M hn htb hns

/-- The requested full local normal-form obligation together with the
identity-projection strict range-row identity is inconsistent at paper scale:
the unquotiented local normal-form side already hits the singleton-shift
budget obstruction. -/
theorem routeBPaperFaithfulTPhi_not_localTypeNormalForm_and_identityRangeRowIdentity_two_pow_804
    (M : DTM)
    (hn : (2 : ℕ) ^ 804 ≥ 2)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ (2 : ℕ) ^ 804) :
    ¬ (CookLevinZeroProfileLocalTypeNormalFormObligation M
        ((2 : ℕ) ^ 804) hn htb hns ∧
      RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
        M ((2 : ℕ) ^ 804) hn htb hns
        (LinearMap.id :
          MvPolynomial (Fin ((2 : ℕ) ^ 804)) ℚ →ₗ[ℚ]
            MvPolynomial (Fin ((2 : ℕ) ^ 804)) ℚ)) := by
  intro h
  exact
    (routeBPaperFaithfulTPhi_not_localTypeNormalFormObligation_two_pow_804
      M hn htb hns) h.1

/-- A budgeted projected zero-profile common span gives the strict-`TΦ`
projected P-side bound once the strict projected P-window is contained in that
span. -/
theorem routeBPaperFaithfulTPhi_projectedPSideBound_of_zeroProfileProjectedCommonSpanWithBudget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    {budget : ℕ}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project budget)
    (hcontrol :
      RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project)
    (hbudget : budget ≤ n ^ 200) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) := by
  unfold SATDeciderGaugePSideBound mlBlockedSpdpRank
  have htargetFinite :
      Module.Finite ℚ
        ↥(zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          project) :=
    zeroProfileProjectedShiftSpan_finite (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      project
  let T :
      Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    zeroProfileProjectedShiftSpan (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      project
  let S :
      Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
  have htargetFinite' : Module.Finite ℚ ↥T := by
    simpa [T] using htargetFinite
  have hcontrol' : S ≤ T := by
    simpa [T] using hcontrol
  have hmono :
      Module.finrank ℚ
          ↥(mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ≤
        Module.finrank ℚ
          ↥(zeroProfileProjectedShiftSpan (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            project) := by
    have hmono' : Module.finrank ℚ
          ↥S ≤
        Module.finrank ℚ ↥T := by
      exact
        @Submodule.finrank_mono ℚ (MvPolynomial (Fin n) ℚ)
          _ _ _ _ S T htargetFinite' hcontrol'
    simpa [S, T] using hmono'
  exact
    hmono.trans
      ((zeroProfileProjectedShiftSpan_finrank_le_of_commonSpanWithBudget
        (κ := Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project hspan).trans hbudget)

/-- A quotient/projected Cook-Levin local type normal-form certificate is the
paper-faithful replacement for the refuted unquotiented local type target.
Together with strict projected P-window containment, it gives the strict
`TΦ` P-side bound. -/
theorem routeBPaperFaithfulTPhi_projectedPSideBound_of_quotientTypeNormalFormObligation
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (hquot :
      CookLevinZeroProfileQuotientTypeNormalFormObligation
        M n hn2 htb hns typeBudget)
    (hcontrol :
      ∀ project :
        MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ,
        CookLevinZeroProfileProjectedCommonSpanObligation
            M n hn2 htb hns typeBudget →
          RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
            M n hn2 htb hns project)
    (hbudget : typeBudget ≤ n ^ 200) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) := by
  rcases
    cookLevinZeroProfileProjectedCommonSpanObligation_of_quotientTypeNormalFormObligation
      M n hn2 htb hns hquot with
    ⟨project, hidem, hkills, hspan⟩
  exact
    routeBPaperFaithfulTPhi_projectedPSideBound_of_zeroProfileProjectedCommonSpanWithBudget
      M n hn2 htb hns project hspan
      (hcontrol project ⟨project, hidem, hkills, hspan⟩)
      hbudget

/-- Certificate-level quotient route: the quotient certificate supplies the
projected common span, and the strict row algebra is exactly the restricted
residual-balance identity for the certificate's selected projection. -/
theorem routeBPaperFaithfulTPhi_projectedPSideBound_of_quotientTypeCertificate_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (cert :
      ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        typeBudget)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns cert.project)
    (hbudget : typeBudget ≤ n ^ 200) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) :=
  routeBPaperFaithfulTPhi_projectedPSideBound_of_zeroProfileProjectedCommonSpanWithBudget
    M n hn2 htb hns cert.project
    (cookLevinZeroProfileProjectedCommonSpanWithBudget_of_quotientTypeCertificate
      M n hn2 htb hns cert)
    (routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rangeRestrictedRowIdentity
      M n hn2 htb hns cert.project
      (routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_of_restrictedResidualBalance
        M n hn2 htb hns cert.project hres))
    hbudget

/-- Obligation-level quotient route with the selected certificate exposed to
the row algebra.  This is the non-overfitted form of the remaining target:
prove restricted residual balance for whichever quotient certificate witnesses
the projected normal form. -/
theorem routeBPaperFaithfulTPhi_projectedPSideBound_of_quotientTypeNormalFormObligation_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (hquot :
      CookLevinZeroProfileQuotientTypeNormalFormObligation
        M n hn2 htb hns typeBudget)
    (hres :
      ∀ cert :
        ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          typeBudget,
        RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
          M n hn2 htb hns cert.project)
    (hbudget : typeBudget ≤ n ^ 200) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) := by
  rcases hquot with ⟨cert⟩
  exact
    routeBPaperFaithfulTPhi_projectedPSideBound_of_quotientTypeCertificate_restrictedResidualBalance
      M n hn2 htb hns cert (hres cert) hbudget

/-- Concrete singleton-quotient close-out for the residual-balance route.
Normalized strict rows provide the singleton residual, and the fixed-derivative
condition says the derivative row is already the quotient representative. -/
theorem routeBPaperFaithfulTPhi_projectedPSideBound_of_singletonQuotientTypeCertificate_normalizedRows_derivativeFixed
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns)
    (hfix :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
        M n hn2 htb hns)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) ≤
        n ^ 200) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) := by
  let cert :=
    zeroProfileSingletonQuotientTypeSpaceCertificate_projectedFinrank
      (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
  have hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns cert.project := by
    simpa [cert, zeroProfileSingletonQuotientTypeSpaceCertificate_projectedFinrank] using
      routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_of_normalizedRows_derivativeFixed
        M n hn2 htb hns hnorm hfix
  exact
    routeBPaperFaithfulTPhi_projectedPSideBound_of_quotientTypeCertificate_restrictedResidualBalance
      M n hn2 htb hns cert hres hbudget

/-- Concrete singleton-quotient P-side bound from the normalized
non-singleton coefficient computation and the selected derivative
representative condition. -/
theorem routeBPaperFaithfulTPhi_projectedPSideBound_of_singletonQuotientTypeCertificate_normalizedCoeff_derivativeFixed
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcoeff :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
        M n hn2 htb hns)
    (hfix :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
        M n hn2 htb hns)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) ≤
        n ^ 200) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) :=
  routeBPaperFaithfulTPhi_projectedPSideBound_of_singletonQuotientTypeCertificate_normalizedRows_derivativeFixed
    M n hn2 htb hns
    (routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_normalizedNonSingletonCoeff
      M n hn2 htb hns hcoeff)
    hfix hbudget

private theorem routeBPaperFaithfulTPhi_finrank_sup_le_add
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (U W : Submodule ℚ V)
    [Module.Finite ℚ ↥U] [Module.Finite ℚ ↥W] :
    Module.finrank ℚ ↥(U ⊔ W) ≤
      Module.finrank ℚ ↥U + Module.finrank ℚ ↥W := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

private theorem routeBPaperFaithfulTPhi_singletonShiftSubspace_finrank_le_ambient
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    Module.finrank ℚ ↥(zeroProfileSingletonShiftSubspace factors) ≤ n := by
  classical
  let B := zeroProfileSingletonShiftBasis factors
  have hfinite :
      Module.Finite ℚ
        ↥(Submodule.span ℚ (↑B : Set (MvPolynomial (Fin n) ℚ))) :=
    Module.Finite.span_of_finite ℚ (Finset.finite_toSet B)
  have hle :
      zeroProfileSingletonShiftSubspace factors ≤
        Submodule.span ℚ (↑B : Set (MvPolynomial (Fin n) ℚ)) := by
    rw [zeroProfileSingletonShiftSubspace_eq_span_singletonShiftBasis]
  calc
    Module.finrank ℚ ↥(zeroProfileSingletonShiftSubspace factors) ≤
        Module.finrank ℚ
          ↥(Submodule.span ℚ (↑B : Set (MvPolynomial (Fin n) ℚ))) :=
      @Submodule.finrank_mono ℚ (MvPolynomial (Fin n) ℚ)
        _ _ _ _ (zeroProfileSingletonShiftSubspace factors)
        (Submodule.span ℚ (↑B : Set (MvPolynomial (Fin n) ℚ)))
        hfinite hle
    _ ≤ B.card := finrank_span_finset_le_card B
    _ ≤ n := zeroProfileSingletonShiftBasis_card_le_ambient factors

private theorem routeBPaperFaithfulTPhi_singletonShiftSubspace_finite
    {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    Module.Finite ℚ ↥(zeroProfileSingletonShiftSubspace factors) := by
  classical
  let B := zeroProfileSingletonShiftBasis factors
  rw [zeroProfileSingletonShiftSubspace_eq_span_singletonShiftBasis]
  exact Module.Finite.span_of_finite ℚ (Finset.finite_toSet B)

/-- Normalized strict-`TΦ` row equality is enough to place every strict
projected P-window generator in the sum of the normalized zero-profile span
and the finite singleton-shift residual span.  This is the paper-faithful
replacement for the refuted raw derivative-as-normal-form target. -/
theorem routeBPaperFaithfulTPhi_projectedPWindowControlledBy_singletonNormalForm_sup_singletonResidual
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns) :
    mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
      zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          (zeroProfileSingletonNormalFormProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) ⊔
        zeroProfileSingletonShiftSubspace
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) := by
  classical
  let factors :=
    fun i => (cookLevinFactorList M n hn2 htb hns).get i
  unfold mlBlockedSpdpSubspace
  refine Submodule.span_le.mpr ?_
  intro row hrow
  rcases hrow with
    ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  change List (Fin n) at S
  change MvPolynomial (Fin n) ℚ at shift
  by_cases hoff :
      ∃ v ∈ S, v ∉ Set.range (cookLevinStrictFOBFlatMap n)
  · have hlhs :
        mlProj
            (shift * SPDP.iterDerivList S
              ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
                (compiledPoly
                  (cook_levin_compilation M n hn2 htb hns)))) = 0 := by
      rw [routeBPaperFaithfulTPhiAmbientGauge_compiledPoly_eq_reexpandedStrictFOB
        M n hn2 htb hns]
      exact
        routeBPaperFaithfulTPhi_strictFOB_offRangeDerivativeRow_zero
          n S shift
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) hoff
    rw [hlhs]
    exact Submodule.zero_mem _
  · have hall :
        ∀ v ∈ S, v ∈ Set.range (cookLevinStrictFOBFlatMap n) := by
      intro v hv
      by_contra hvnot
      exact hoff ⟨v, hv, hvnot⟩
    rcases routeBPaperFaithfulTPhi_strictFOB_preimageList n S hall with
      ⟨S', hS'⟩
    let shift' :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) shift
    have hshiftRange :
        ↑shift.vars ⊆ Set.range (cookLevinStrictFOBFlatMap n) := by
      intro v hv
      exact hall v (List.mem_toFinset.mp (hshiftVars hv))
    have hrename :
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift' = shift := by
      simpa [shift'] using
        routeBPaperFaithfulTPhi_rename_restrictStrictFOB_of_vars_range
          n shift hshiftRange
    have hSlen' : S'.length = Nat.log 2 n := by
      have hmapLen :
          (S'.map (cookLevinStrictFOBFlatMap n)).length =
            Nat.log 2 n := by
        rw [hS']
        exact hSlen
      simpa [List.length_map] using hmapLen
    have hshiftDegree' : shift'.totalDegree ≤ Nat.log 2 n :=
      (MultilinearSPDP.restrictPoly_totalDegree_le ℚ
        (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) shift).trans hshiftDegree
    have hshiftVars' :
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift').vars ⊆
          (S'.map (cookLevinStrictFOBFlatMap n)).toFinset := by
      rw [hrename, hS']
      exact hshiftVars
    have hadm' :
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition
          (S'.map (cookLevinStrictFOBFlatMap n)) := by
      rw [hS']
      exact hadm
    let p : MvPolynomial (Fin n) ℚ :=
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
    let r : MvPolynomial (Fin (n / 3)) ℚ :=
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n) p
    let q : MvPolynomial (Fin n) ℚ :=
      mlProj
        (MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift' *
          cookLevinZeroProfileBaseProduct M n hn2 htb hns)
    let d : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
        (mlProj (shift' * SPDP.iterDerivList S' r))
    have hqset :
        q ∈ zeroProfileShiftImageSet (Nat.log 2 n) factors := by
      simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
        Set.mem_singleton_iff]
      have hmapLen :
          (S'.map (cookLevinStrictFOBFlatMap n)).length =
            Nat.log 2 n := by
        simpa [List.length_map] using hSlen'
      exact ⟨S'.map (cookLevinStrictFOBFlatMap n), le_of_eq hmapLen,
        MvPolynomial.rename (cookLevinStrictFOBFlatMap n) shift',
        hshiftVars', rfl⟩
    have hnf_mem :
        zeroProfileSingletonNormalFormProjection factors q ∈
          zeroProfileProjectedShiftSpan (Nat.log 2 n) factors
            (zeroProfileSingletonNormalFormProjection factors) := by
      exact Submodule.mem_map_of_mem (Submodule.subset_span hqset)
    have hres_norm :
        q -
          zeroProfileSingletonNormalFormProjection factors q ∈
            zeroProfileSingletonShiftSubspace factors :=
      zeroProfileSingletonNormalFormProjection_residual_mem_singletonShiftSubspace
        factors q
    have hres_row :
        q - d ∈ zeroProfileSingletonShiftSubspace factors := by
      have hresidual :=
        (routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_iff_singletonResidual
          M n hn2 htb hns).mp hnorm
      simpa [factors, p, r, q, d] using
        hresidual S' shift' hSlen' hshiftDegree' hshiftVars' hadm'
    have hd_minus_nf :
        d - zeroProfileSingletonNormalFormProjection factors q ∈
          zeroProfileSingletonShiftSubspace factors := by
      have hsub :
          (q - zeroProfileSingletonNormalFormProjection factors q) -
              (q - d) ∈ zeroProfileSingletonShiftSubspace factors :=
        Submodule.sub_mem _ hres_norm hres_row
      convert hsub using 1
      abel
    have hd_mem :
        d ∈
          zeroProfileProjectedShiftSpan (Nat.log 2 n) factors
              (zeroProfileSingletonNormalFormProjection factors) ⊔
            zeroProfileSingletonShiftSubspace factors := by
      have hleft :
          zeroProfileSingletonNormalFormProjection factors q ∈
            zeroProfileProjectedShiftSpan (Nat.log 2 n) factors
                (zeroProfileSingletonNormalFormProjection factors) ⊔
              zeroProfileSingletonShiftSubspace factors :=
        Submodule.mem_sup_left hnf_mem
      have hright :
          d - zeroProfileSingletonNormalFormProjection factors q ∈
            zeroProfileProjectedShiftSpan (Nat.log 2 n) factors
                (zeroProfileSingletonNormalFormProjection factors) ⊔
              zeroProfileSingletonShiftSubspace factors :=
        Submodule.mem_sup_right hd_minus_nf
      have hsum := Submodule.add_mem _ hleft hright
      convert hsum using 1
      abel
    rw [← hrename, ← hS']
    simpa [p, r, d] using
      (by
        rw [routeBPaperFaithfulTPhi_rangePWindowRow_eq_renamedRestrictedRow
          M n hn2 htb hns S' shift']
        exact hd_mem)


/-- Exact full projected containment follows from the semantic singleton
normalizer route exactly when the finite singleton residual has also been
absorbed into the same projected zero-profile span.

The already-proved theorem
`routeBPaperFaithfulTPhi_projectedPWindowControlledBy_singletonNormalForm_sup_singletonResidual`
places the full strict ambient `TΦ` SPDP subspace in
`projectedZeroProfileSpan ⊔ singletonResidual`.  This lemma is the sharp
remaining condition for the stronger target requested here: if the residual
subspace is itself contained in the projected span, then the exact projected
containment follows. -/
theorem routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_singletonNormalForm_residualAbsorbed
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns)
    (hresidual :
      zeroProfileSingletonShiftSubspace
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) ≤
        zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          (zeroProfileSingletonNormalFormProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
      M n hn2 htb hns
      (zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) := by
  classical
  let factors :=
    fun i => (cookLevinFactorList M n hn2 htb hns).get i
  let A : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    zeroProfileProjectedShiftSpan (Nat.log 2 n) factors
      (zeroProfileSingletonNormalFormProjection factors)
  let R : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    zeroProfileSingletonShiftSubspace factors
  have hsup :
      MultilinearSPDP.mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
        A ⊔ R := by
    simpa [A, R, factors] using
      routeBPaperFaithfulTPhi_projectedPWindowControlledBy_singletonNormalForm_sup_singletonResidual
        M n hn2 htb hns hnorm
  have hsup_le : A ⊔ R ≤ A := by
    exact sup_le le_rfl (by simpa [A, R, factors] using hresidual)
  exact hsup.trans hsup_le

/-- If the singleton residual is not absorbed by the semantic normalizer's
projected zero-profile span, the existing normalized-row theorem can only give
the honest `span ⊔ residual` containment, not the exact projected containment.
This names the precise obstruction to the stronger target. -/
def RouteBPaperFaithfulTPhiSingletonResidualAbsorbed
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  zeroProfileSingletonShiftSubspace
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i) ≤
    zeroProfileProjectedShiftSpan (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      (zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))

/-- Named version of the exact containment proof using the semantic singleton
normalizer, isolated behind the real residual-absorption condition. -/
theorem routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_singletonNormalForm_residualAbsorbed'
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns)
    (hresidual :
      RouteBPaperFaithfulTPhiSingletonResidualAbsorbed M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
      M n hn2 htb hns
      (zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) :=
  routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_singletonNormalForm_residualAbsorbed
    M n hn2 htb hns hnorm hresidual

/-- A budgeted common span for the singleton normalizer image, plus normalized
strict-`TΦ` row equality, gives the strict projected P-side bound after paying
the finite singleton residual at ambient cost `n`. -/
theorem routeBPaperFaithfulTPhi_projectedPSideBound_of_singletonNormalFormCommonSpan_normalizedRows
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {budget : ℕ}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileSingletonNormalFormProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        budget)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns)
    (hbudget : budget + n ≤ n ^ 200) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) := by
  classical
  unfold SATDeciderGaugePSideBound mlBlockedSpdpRank
  let factors :=
    fun i => (cookLevinFactorList M n hn2 htb hns).get i
  let T :
      Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    zeroProfileProjectedShiftSpan (Nat.log 2 n) factors
      (zeroProfileSingletonNormalFormProjection factors)
  let R :
      Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    zeroProfileSingletonShiftSubspace factors
  let S :
      Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
  haveI hTfinite : Module.Finite ℚ ↥T := by
    simpa [T, factors] using
      zeroProfileProjectedShiftSpan_finite (Nat.log 2 n) factors
        (zeroProfileSingletonNormalFormProjection factors)
  haveI hRfinite : Module.Finite ℚ ↥R := by
    simpa [R, factors] using
      routeBPaperFaithfulTPhi_singletonShiftSubspace_finite factors
  have hcontrol : S ≤ T ⊔ R := by
    simpa [S, T, R, factors] using
      routeBPaperFaithfulTPhi_projectedPWindowControlledBy_singletonNormalForm_sup_singletonResidual
        M n hn2 htb hns hnorm
  have hmono :
      Module.finrank ℚ
          ↥(mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            ((routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ≤
        Module.finrank ℚ ↥(T ⊔ R) := by
    have hmono' : Module.finrank ℚ ↥S ≤ Module.finrank ℚ ↥(T ⊔ R) :=
      @Submodule.finrank_mono ℚ (MvPolynomial (Fin n) ℚ)
        _ _ _ _ S (T ⊔ R) (by infer_instance) hcontrol
    simpa [S] using hmono'
  have hTbudget : Module.finrank ℚ ↥T ≤ budget := by
    simpa [T, factors] using
      zeroProfileProjectedShiftSpan_finrank_le_of_commonSpanWithBudget
        (κ := Nat.log 2 n) factors
        (zeroProfileSingletonNormalFormProjection factors) hspan
  have hRbudget : Module.finrank ℚ ↥R ≤ n := by
    simpa [R, factors] using
      routeBPaperFaithfulTPhi_singletonShiftSubspace_finrank_le_ambient factors
  have hsup :
      Module.finrank ℚ ↥(T ⊔ R) ≤ budget + n := by
    calc
      Module.finrank ℚ ↥(T ⊔ R) ≤
          Module.finrank ℚ ↥T + Module.finrank ℚ ↥R :=
        routeBPaperFaithfulTPhi_finrank_sup_le_add T R
      _ ≤ budget + n := Nat.add_le_add hTbudget hRbudget
  exact hmono.trans (hsup.trans hbudget)

/-- A quotiented zero-profile common span is a direct strict-`TΦ` projected
P-side source, provided it contains the strict projected P-window. -/
theorem routeBPaperFaithfulTPhi_projectedPSideBound_of_zeroProfileQuotientedShiftCommonSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project)
    (hcontrol :
      RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) :=
  routeBPaperFaithfulTPhi_projectedPSideBound_of_zeroProfileProjectedCommonSpanWithBudget
    M n hn2 htb hns project hquot.2.2 hcontrol
    (routeBPaperFaithfulTPhi_withinProfileBound_log_le_pow_200 n hn2)

/-- The strict `TΦ` ambient gauge preserves the projected NP identity-minor
lower bound.  The proof uses the floor-sized strict FOB lower bound and
injective-rename rank preservation, not the head-span projection. -/
theorem routeBPaperFaithfulTPhiAmbientGauge_npPreservation
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns) := by
  intro _hdec
  have hrestrict :=
    cookLevinStrictFOB_restrict_compiled_lower_bound
      M n hn hn2 htb hns
  have hrename :
      mlBlockedSpdpRank
          (MultilinearSPDP.pullbackPartition
            (cook_levin_compilation M n hn2 htb hns).partition
            (cookLevinStrictFOBFlatMap n))
          (Nat.log 2 n) (Nat.log 2 n)
          (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
            (cookLevinStrictFOBFlatMap_injective n)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (MvPolynomial.rename (cookLevinStrictFOBFlatMap n)
            (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
              (cookLevinStrictFOBFlatMap_injective n)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) :=
    PaperFaithfulCompilation.mlBlockedSpdpRank_rename_ge
      (cookLevinStrictFOBFlatMap n) (cookLevinStrictFOBFlatMap_injective n)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
  exact le_trans hrestrict (by
    simpa [routeBPaperFaithfulTPhiAmbientGauge] using hrename)

/-- A strict-`TΦ` projected P-side bound contradicts bounded SAT deciders via
the same projected/log-window incompatibility lemma used by the final
certificate path. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hp :
      SATDeciderGaugePSideBound M n hn2 htb hns
        (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)) :
    False :=
  satDeciderGauge_pSide_and_npIdentityMinor_incompatible_at_large_n
    M n hn hn2 htb hns
    (routeBPaperFaithfulTPhiAmbientGauge M n hn2 htb hns)
    hdec hp
    (routeBPaperFaithfulTPhiAmbientGauge_npPreservation
      M n hn hn2 htb hns)

/-- Strict-`TΦ` projected/log-window final hook from a budgeted projected
zero-profile common span and the strict projected P-window containment. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroProfileProjectedCommonSpanWithBudget
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    {budget : ℕ}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project budget)
    (hcontrol :
      RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project)
    (hbudget : budget ≤ n ^ 200) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_projectedPSideBound_of_zeroProfileProjectedCommonSpanWithBudget
      M n hn2 htb hns project hspan hcontrol hbudget)

/-- Final strict-`TΦ` hook from the quotient/projected local type normal-form
obligation.  This is the paper-faithful replacement for the refuted
unquotiented local normal-form route: the quotient certificate supplies the
projected common span, and the remaining load-bearing input is strict projected
P-window containment for that quotient projection. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_quotientTypeNormalFormObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    {typeBudget : ℕ}
    (hquot :
      CookLevinZeroProfileQuotientTypeNormalFormObligation
        M n hn2 htb hns typeBudget)
    (hcontrol :
      ∀ project :
        MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ,
        CookLevinZeroProfileProjectedCommonSpanObligation
            M n hn2 htb hns typeBudget →
          RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
            M n hn2 htb hns project)
    (hbudget : typeBudget ≤ n ^ 200) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_projectedPSideBound_of_quotientTypeNormalFormObligation
      M n hn2 htb hns hquot hcontrol hbudget)

/-- Source-coordinate restricted row equality is enough to supply the
projected-containment side of the quotient/type normal-form final hook. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_quotientTypeNormalFormObligation_rangeRestrictedRowIdentity
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    {typeBudget : ℕ}
    (hquot :
      CookLevinZeroProfileQuotientTypeNormalFormObligation
        M n hn2 htb hns typeBudget)
    (hrow :
      ∀ project :
        MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ,
        CookLevinZeroProfileProjectedCommonSpanObligation
            M n hn2 htb hns typeBudget →
          RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
            M n hn2 htb hns project)
    (hbudget : typeBudget ≤ n ^ 200) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_quotientTypeNormalFormObligation
    M n hn hn2 htb hns hdec hquot
    (fun project hproject =>
      routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rangeRestrictedRowIdentity
        M n hn2 htb hns project (hrow project hproject))
    hbudget

/-- Final strict-`TΦ` hook from an explicit quotient type certificate and the
restricted residual-balance row algebra for its selected projection. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_quotientTypeCertificate_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    {typeBudget : ℕ}
    (cert :
      ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        typeBudget)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns cert.project)
    (hbudget : typeBudget ≤ n ^ 200) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_projectedPSideBound_of_quotientTypeCertificate_restrictedResidualBalance
      M n hn2 htb hns cert hres hbudget)

/-- Final strict-`TΦ` hook from the existential quotient normal-form
obligation, with the residual-balance proof stated for the selected quotient
certificate. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_quotientTypeNormalFormObligation_restrictedResidualBalance
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    {typeBudget : ℕ}
    (hquot :
      CookLevinZeroProfileQuotientTypeNormalFormObligation
        M n hn2 htb hns typeBudget)
    (hres :
      ∀ cert :
        ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          typeBudget,
        RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
          M n hn2 htb hns cert.project)
    (hbudget : typeBudget ≤ n ^ 200) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_projectedPSideBound_of_quotientTypeNormalFormObligation_restrictedResidualBalance
      M n hn2 htb hns hquot hres hbudget)

/-- Final strict-`TΦ` close-out for the concrete singleton quotient
certificate, from the normalized row identity and fixed-derivative
representative condition. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotientTypeCertificate_normalizedRows_derivativeFixed
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns)
    (hfix :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
        M n hn2 htb hns)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) ≤
        n ^ 200) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_projectedPSideBound_of_singletonQuotientTypeCertificate_normalizedRows_derivativeFixed
      M n hn2 htb hns hnorm hfix hbudget)

/-- Strict-`TΦ` projected/log-window final hook from quotiented zero-profile
data and the strict projected P-window containment. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroProfileQuotientedShiftCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project)
    (hcontrol :
      RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_projectedPSideBound_of_zeroProfileQuotientedShiftCommonSpan
      M n hn2 htb hns project hquot hcontrol)

/-- Strict-`TΦ` projected/log-window final hook from a budgeted projected
zero-profile span and the corrected range-only restricted row equality. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroProfileProjectedCommonSpanWithBudget_rangeRestrictedRowIdentity
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    {budget : ℕ}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project budget)
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns project)
    (hbudget : budget ≤ n ^ 200) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroProfileProjectedCommonSpanWithBudget
    M n hn hn2 htb hns hdec project (budget := budget) hspan
    (routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rangeRestrictedRowIdentity
      M n hn2 htb hns project hrow)
    hbudget

/-- Strict-`TΦ` projected/log-window final hook for the explicit singleton
normal-form representative.  The remaining mathematical inputs are exactly a
budgeted common span for the normalizer image and the semantic normal-form row
identity. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    {budget : ℕ}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileSingletonNormalFormProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        budget)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormIdentity
        M n hn2 htb hns)
    (hbudget : budget ≤ n ^ 200) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroProfileProjectedCommonSpanWithBudget_rangeRestrictedRowIdentity
    M n hn hn2 htb hns hdec
    (zeroProfileSingletonNormalFormProjection
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
    hspan
    (routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_of_singletonNormalFormIdentity
      M n hn2 htb hns hnorm)
    hbudget

/-- Strict-`TΦ` projected/log-window final hook for the semantic singleton
normalizer route with explicit singleton-residual payment.  This consumes the
paper-faithful normalized row identity, not the refuted raw derivative
representative equality: the normalizer-image span is budgeted by `budget`,
and the discarded singleton directions are paid separately by `n`. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_normalizedRows
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    {budget : ℕ}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileSingletonNormalFormProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        budget)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns)
    (hbudget : budget + n ≤ n ^ 200) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_projectedPSideBound_of_singletonNormalFormCommonSpan_normalizedRows
      M n hn2 htb hns hspan hnorm hbudget)

/-- Strict-`TΦ` projected/log-window final hook from quotiented zero-profile
data and the corrected range-only restricted row equality. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroProfileQuotientedShiftCommonSpan_rangeRestrictedRowIdentity
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project)
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns project) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroProfileQuotientedShiftCommonSpan
    M n hn hn2 htb hns hdec project hquot
    (routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rangeRestrictedRowIdentity
      M n hn2 htb hns project hrow)

/-- The strict paper-faithful `TΦ` target consumes the concrete per-type
spanning bundle at the selected `concreteW` local type-space family.

This is the direct profile-spanning Route B surface: unlike
`CookLevinPerTypeSpanning_universal`, it does not quantify over arbitrary
submodule families `W`; it uses the paper's chosen local chart/type spaces. -/
theorem false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hn4 : n ≥ 4)
    (hSpan :
      PallLean.Paper93.Spanning.CookLevinPerTypeSpanning M n hn2 htb hns
        (fun tau =>
          PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) tau)) :
    False :=
  false_of_routeBPaperFaithfulTPhi_canonical_from_boundedProfileTemplateCollapse
    M n hn hn2 htb hns hdec
    (cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_concreteW_perTypeSpanning
      M n hn2 htb hns hn4 hSpan)

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

/-- The strict paper-faithful `TΦ` target consumes the corrected
endpoint-augmented active-profile route.

This is the profile-local/charged replacement for the refuted raw
same-profile `concreteW` frontier: zero-profile rows are supplied separately by
the common-span blocker, while live active profiles are closed in the
endpoint-augmented type spaces. -/
theorem false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_activeProfileSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hn4 : n ≥ 4)
    (hzero :
      CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hactiveSpan :
      ∀ (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            ActiveProfileSupport h →
              cookLevinPostSpanAt M n hn2 htb hns h ≤
                cookLevinProfileSubspace (admissibleToBounded hadm)
                  (endpointAugmentedConcreteW n hn4)) :
    False :=
  false_of_routeBPaperFaithfulTPhi_qRankUpper
    M n hn hn2 htb hns hdec
    (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) rfl
    (by
      have hp : RouteBSATUnprojectedPSideRankBound M n hn2 htb hns :=
        routeBSATUnprojectedPSideRankBound_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
          M n hn2 htb hns hn4 hzero
          (cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_activeProfileSpan
            M n hn2 htb hns hn4 hactiveSpan)
      have hpart :=
        PaperFaithfulCompilation.pullback_eq_cook_levin_partition
          M n hn2 htb hns
      rw [hpart]
      convert hp using 2)

/-- The strict paper-faithful `TΦ` target consumes direct endpoint-augmented
per-profile spanning slices for every active profile.

This is the corrected active/profile proof surface: it asks for the local
profile span directly and avoids the refuted same-profile self-targeting
charged frontier. -/
theorem false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_spanningAtBoundedProfile
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hn4 : n ≥ 4)
    (hzero :
      CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hSpanAt :
      ∀ (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            ActiveProfileSupport h →
              CookLevinPerTypeSpanningAtBoundedProfile M n hn2 htb hns
                (endpointAugmentedConcreteW n hn4)
                (admissibleToBounded hadm)) :
    False :=
  false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_activeProfileSpan
    M n hn hn2 htb hns hdec hn4 hzero
    (by
      intro h hadm htr hactive
      exact
        cookLevinProfileSubspace_contains_postSpan_at_bp_of_perTypeSpanningAtBoundedProfile
          M n hn2 htb hns (endpointAugmentedConcreteW n hn4)
          (admissibleToBounded hadm)
          (hSpanAt h hadm htr hactive))

/-- Concrete per-type row embeddings supply the endpoint-augmented
per-profile active spanning slices consumed by the strict paper-faithful
`TΦ` route.

The active/profile part is therefore routed through actual profile-local
spanning and the monotone inclusion into `endpointAugmentedConcreteW`, not
through the refuted same-profile endpoint closure or self-targeting charged
frontier. -/
theorem false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_concreteW_rowEmbeddings_activeProfiles
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (hn4 : n ≥ 4)
    (hzero :
      CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4) :
    False :=
  false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_spanningAtBoundedProfile
    M n hn hn2 htb hns hdec hn4 hzero
    (endpointAugmented_spanningAtActiveProfiles_of_concreteW_rowEmbeddings
      M n hn2 htb hns hn4 hRowEmbeddings)

/-- Charged endpoint-augmented active-profile frontiers close the strict
paper-faithful `TΦ` target once the zero-profile common-span blocker is
supplied.  This is the paper-faithful active route: charged local movement and
endpoint-augmented normal forms, not raw same-profile self-closure. -/
theorem false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_chargedFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (charge : ProfileCharge n)
    (hn4 : n ≥ 4)
    (hzero :
      CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hFrontier :
      EndpointAugmentedActiveProfileChargedFrontier
        M n hn2 htb hns charge hn4) :
    False :=
  false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_activeProfileSpan
    M n hn hn2 htb hns hdec hn4 hzero
    (by
      intro h hadm htr hactive
      exact
        cookLevinProfileSubspace_contains_postSpan_at_bp_of_perTypeSpanningAtBoundedProfile
          M n hn2 htb hns (endpointAugmentedConcreteW n hn4)
          (admissibleToBounded hadm)
          (cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_chargedClosureAtProfile
            M n hn2 htb hns charge hn4 (admissibleToBounded hadm)
            (hFrontier.2 h hadm htr
              (by
                intro hzeroProfile
                cases hactive with
                | inl hbool =>
                    rw [hzeroProfile] at hbool
                    simp [zeroProfileHistogram] at hbool
                | inr hrest =>
                    cases hrest with
                    | inl hboundary =>
                        rw [hzeroProfile] at hboundary
                        simp [zeroProfileHistogram] at hboundary
                    | inr htransition =>
                        rw [hzeroProfile] at htransition
                        simp [zeroProfileHistogram] at htransition)
              hactive)))

/-- Strict paper-faithful `TΦ` target from a charged target-profile active
cover.

This is the retargeted active consumer for the concrete endpoint charge: the
source active post-span need not self-target.  It is enough to cover it by
charged/restricted rows landing in admissible target profiles, then use the
endpoint-augmented target-profile budget. -/
theorem false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_chargedTargetCover
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (charge : ProfileCharge n)
    (hn4 : n ≥ 4)
    (hzero :
      CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hFactor :
      CookLevinFactorMemPerType M n hn2 htb hns
        (endpointAugmentedConcreteW n hn4))
    (hI1 :
      PallLean.Paper93.Closure.PerTypeProductGrouping
        (endpointAugmentedConcreteW n hn4))
    (hI2c :
      PerTypeChargedShiftClosure (n := n) charge
        (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PallLean.Paper93.Closure.PerTypeMlprojClosure
        (endpointAugmentedConcreteW n hn4))
    (hCover :
      ∀ (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                CookLevinEndpointChargedTargetProfileCoverAt
                  M n hn2 htb hns charge h hadm) :
    False :=
  false_of_routeBPaperFaithfulTPhi_qRankUpper
    M n hn hn2 htb hns hdec
    (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) rfl
    (by
      have hCharged :
          PerTypeShiftMlprojClosureCharged (n := n) charge
            (endpointAugmentedConcreteW n hn4) :=
        perTypeShiftMlprojClosure_charged_discharged
          (n := n) charge (endpointAugmentedConcreteW n hn4)
          hI1 hI2c hI3
      have hp : RouteBSATUnprojectedPSideRankBound M n hn2 htb hns :=
        routeBSATUnprojectedPSideRankBound_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
          M n hn2 htb hns hn4 hzero
          (cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_chargedTargetCover
            M n hn2 htb hns charge hn4 hFactor hCharged
            (endpointAugmentedActiveProfileSubspaceBudget n hn4) hCover)
      have hpart :=
        PaperFaithfulCompilation.pullback_eq_cook_levin_partition
          M n hn2 htb hns
      rw [hpart]
      convert hp using 2)

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

/-- A uniform concrete per-type spanning theorem closes the strict `TΦ`
contradiction-strength consumer.  This is the paper-faithful profile-spanning
frontier at the selected `concreteW` local type spaces, avoiding the overly
strong arbitrary-`W` universal target. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteW_perTypeSpanning
    (hSpan :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        PallLean.Paper93.Spanning.CookLevinPerTypeSpanning M n hn2 htb hns
          (fun tau =>
            PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) tau)) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  have hn4 : n ≥ 4 := routeB_paperScale_ge_four hn
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_perTypeSpanning
      M n hn hn2 htb hns hdec hn4
      (hSpan M n hn2 hn4 htb hns)

/-- Uniform endpoint-augmented active-profile span plus the zero-profile
common-span blocker closes the strict paper-faithful `TΦ` route at the paper
scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_activeProfileSpan
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hactiveSpan :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        ∀ (h : ProfileHistogram)
          (hadm : ProfileAdmissible (Nat.log 2 n) h),
            h ConstraintType.transitionRight = 0 →
              ActiveProfileSupport h →
                cookLevinPostSpanAt M n hn2 htb hns h ≤
                  cookLevinProfileSubspace (admissibleToBounded hadm)
                    (endpointAugmentedConcreteW n hn4)) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  have hn4 : n ≥ 4 := routeB_paperScale_ge_four hn
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_activeProfileSpan
      M n hn hn2 htb hns hdec hn4
      (hzero M n hn2 htb hns)
      (hactiveSpan M n hn2 hn4 htb hns)

/-- Uniform endpoint-augmented per-profile spanning slices plus the
zero-profile common-span blocker close the strict paper-faithful `TΦ` route at
the paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_spanningAtBoundedProfile
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hSpanAt :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        ∀ (h : ProfileHistogram)
          (hadm : ProfileAdmissible (Nat.log 2 n) h),
            h ConstraintType.transitionRight = 0 →
              ActiveProfileSupport h →
                CookLevinPerTypeSpanningAtBoundedProfile M n hn2 htb hns
                  (endpointAugmentedConcreteW n hn4)
                  (admissibleToBounded hadm)) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  have hn4 : n ≥ 4 := routeB_paperScale_ge_four hn
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_spanningAtBoundedProfile
      M n hn hn2 htb hns hdec hn4
      (hzero M n hn2 htb hns)
      (hSpanAt M n hn2 hn4 htb hns)

/-- Uniform concrete row embeddings close the endpoint-augmented active
profile-local spanning side of the strict `TΦ` route, once the separate
zero-profile common-span blocker is supplied. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_concreteW_rowEmbeddings_activeProfiles
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hRowEmbeddings :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn2 htb hns hn4) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  have hn4 : n ≥ 4 := routeB_paperScale_ge_four hn
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_concreteW_rowEmbeddings_activeProfiles
      M n hn hn2 htb hns hdec hn4
      (hzero M n hn2 htb hns)
      (hRowEmbeddings M n hn2 hn4 htb hns)

/-- Compatibility hook: the legacy universal per-type spanning package supplies
the concrete row embeddings needed by the endpoint-augmented active-profile
strict `TΦ` route.

The paper-faithful proof target remains the selected canonical/concrete local
type spaces.  This theorem only records that, if the older arbitrary-`W`
package is available, it also feeds the corrected endpoint-active consumer. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_perTypeSpanning_universal_activeProfiles
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hSpan_univ : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning_universal) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_concreteW_rowEmbeddings_activeProfiles
    hzero
    (CookLevinPerTypeRowEmbeddings_concreteW_of_universalSpanning hSpan_univ)

/-- Uniform charged endpoint-augmented active-profile frontiers plus the
zero-profile common-span blocker close the strict paper-faithful `TΦ` route at
the paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_chargedFrontier
    (charge : ∀ n : ℕ, ProfileCharge n)
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hFrontier :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        EndpointAugmentedActiveProfileChargedFrontier
          M n hn2 htb hns (charge n) hn4) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  have hn4 : n ≥ 4 := routeB_paperScale_ge_four hn
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_chargedFrontier
      M n hn hn2 htb hns hdec (charge n) hn4
      (hzero M n hn2 htb hns)
      (hFrontier M n hn2 hn4 htb hns)

/-- Uniform charged target-profile covers plus zero-profile common-span close
the strict paper-faithful `TΦ` route at the paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_chargedTargetCover
    (charge : ∀ n : ℕ, ProfileCharge n)
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hFactor :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinFactorMemPerType M n hn2 htb hns
          (endpointAugmentedConcreteW n hn4))
    (hI1 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeProductGrouping
          (endpointAugmentedConcreteW n hn4))
    (hI2c :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PerTypeChargedShiftClosure (charge n)
          (endpointAugmentedConcreteW n hn4))
    (hI3 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeMlprojClosure
          (endpointAugmentedConcreteW n hn4))
    (hCover :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        ∀ (h : ProfileHistogram)
          (hadm : ProfileAdmissible (Nat.log 2 n) h),
            h ConstraintType.transitionRight = 0 →
              h ≠ zeroProfileHistogram →
                ActiveProfileSupport h →
                  CookLevinEndpointChargedTargetProfileCoverAt
                    M n hn2 htb hns (charge n) h hadm) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  have hn4 : n ≥ 4 := routeB_paperScale_ge_four hn
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_chargedTargetCover
      M n hn hn2 htb hns hdec (charge n) hn4
      (hzero M n hn2 htb hns)
      (hFactor M n hn2 hn4 htb hns)
      (hI1 n hn4)
      (hI2c n hn4)
      (hI3 n hn4)
      (hCover M n hn2 hn4 htb hns)

/-- Strict `TΦ` Route B through charged target-profile covers, specialized to
the concrete one-step endpoint charge.  This discharges the charged-shift
input and avoids both fixed canonical row transport and self-targeting. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_concreteEndpointCharge_chargedTargetCover
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hFactor :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinFactorMemPerType M n hn2 htb hns
          (endpointAugmentedConcreteW n hn4))
    (hI1 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeProductGrouping
          (endpointAugmentedConcreteW n hn4))
    (hI3 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeMlprojClosure
          (endpointAugmentedConcreteW n hn4))
    (hCover :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        ∀ (h : ProfileHistogram)
          (hadm : ProfileAdmissible (Nat.log 2 n) h),
            h ConstraintType.transitionRight = 0 →
              h ≠ zeroProfileHistogram →
                ActiveProfileSupport h →
                  CookLevinEndpointChargedTargetProfileCoverAt
                    M n hn2 htb hns
                    (concreteWEndpointSpanOneStepCharge n hn4) h hadm) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  have hn4 : n ≥ 4 := routeB_paperScale_ge_four hn
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_chargedTargetCover
      M n hn hn2 htb hns hdec
      (concreteWEndpointSpanOneStepCharge n hn4) hn4
      (hzero M n hn2 htb hns)
      (hFactor M n hn2 hn4 htb hns)
      (hI1 n hn4)
      (endpointAugmentedConcreteW_chargedShiftClosure_concreteWEndpointSpanOneStepCharge
        n hn4)
      (hI3 n hn4)
      (hCover M n hn2 hn4 htb hns)

/-- Strict `TΦ` Route B from canonical endpoint-augmented active-profile
components.

Canonical concreteW shape witnesses supply H3; the remaining inputs are the
genuine local profile obligations: budget, product grouping, charged shift,
mlProj closure, and active-profile charge self-targeting. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_canonicalShape_chargedComponents
    (charge : ∀ n : ℕ, ProfileCharge n)
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hBudget :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        EndpointAugmentedActiveProfileSubspaceBudget n hn4)
    (hShape :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinCanonicalConcreteWShapeWitnesses M n hn2 htb hns hn4)
    (hI1 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeProductGrouping
          (endpointAugmentedConcreteW n hn4))
    (hI2c :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PerTypeChargedShiftClosure (charge n)
          (endpointAugmentedConcreteW n hn4))
    (hI3 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeMlprojClosure
          (endpointAugmentedConcreteW n hn4))
    (hSelf :
      ∀ (n : ℕ) (_hn4 : n ≥ 4)
        (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                ProfileChargeSelfAtBoundedProfile (charge n)
                  (admissibleToBounded hadm)) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_chargedFrontier
    charge hzero
    (fun M n hn2 hn4 htb hns =>
      endpointAugmentedActiveProfileChargedFrontier_of_canonicalShape_components
        M n hn2 htb hns (charge n) hn4
        (hBudget n hn4)
        (hShape M n hn2 hn4 htb hns)
        (hI1 n hn4)
        (hI2c n hn4)
        (hI3 n hn4)
        (hSelf n hn4))

/-- Strict `TΦ` Route B from canonical endpoint-augmented active-profile
components, with the active-profile budget discharged by the checked
endpoint-augmented dimension theorem. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_canonicalShape_chargedComponents_checkedBudget
    (charge : ∀ n : ℕ, ProfileCharge n)
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hShape :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinCanonicalConcreteWShapeWitnesses M n hn2 htb hns hn4)
    (hI1 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeProductGrouping
          (endpointAugmentedConcreteW n hn4))
    (hI2c :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PerTypeChargedShiftClosure (charge n)
          (endpointAugmentedConcreteW n hn4))
    (hI3 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeMlprojClosure
          (endpointAugmentedConcreteW n hn4))
    (hSelf :
      ∀ (n : ℕ) (_hn4 : n ≥ 4)
        (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                ProfileChargeSelfAtBoundedProfile (charge n)
                  (admissibleToBounded hadm)) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_chargedFrontier
    charge hzero
    (fun M n hn2 hn4 htb hns =>
      endpointAugmentedActiveProfileChargedFrontier_of_canonicalShape_components_checkedBudget
        M n hn2 htb hns (charge n) hn4
        (hShape M n hn2 hn4 htb hns)
        (hI1 n hn4)
        (hI2c n hn4)
        (hI3 n hn4)
        (hSelf n hn4))

/-- Strict `TΦ` Route B with direct transported Cook-Levin branch shapes and
universal I1/I3.  This is the endpoint-active consumer closest to the paper's
canonical-window row-map story: factor rows are transported into canonical
local spaces, while product grouping and multilinear projection are supplied
by the universal local algebra packages. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_directBranchTransport_universal_I1_I3_checkedBudget
    (charge : ∀ n : ℕ, ProfileCharge n)
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hShape :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hI1_univ : PallLean.Paper93.Wiring.PerTypeProductGrouping_universal)
    (hI2c :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PerTypeChargedShiftClosure (charge n)
          (endpointAugmentedConcreteW n hn4))
    (hI3_univ : PallLean.Paper93.Wiring.PerTypeMlprojClosure_universal)
    (hSelf :
      ∀ (n : ℕ) (_hn4 : n ≥ 4)
        (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                ProfileChargeSelfAtBoundedProfile (charge n)
                  (admissibleToBounded hadm)) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_chargedFrontier
    charge hzero
    (fun M n hn2 hn4 htb hns =>
      endpointAugmentedActiveProfileChargedFrontier_of_directBranchShapes_transport_universal_I1_I3_checkedBudget
        M n hn2 htb hns (charge n) hn4
        (hShape M n hn2 hn4 htb hns)
        (hTransport M n hn2 hn4 htb hns)
        hI1_univ
        (hI2c n hn4)
        hI3_univ
        (hSelf n hn4))

/-- Strict `TΦ` Route B with the concrete one-step endpoint charge.

The charged-shift field is discharged by
`endpointAugmentedConcreteW_chargedShiftClosure_concreteWEndpointSpanOneStepCharge`.
The remaining active side condition is still the old self-targeting field,
which is intentionally explicit because the concrete one-step endpoint charge
is known not to satisfy it. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_directBranchTransport_universal_I1_I3_concreteEndpointCharge_checkedBudget
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hShape :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hI1_univ : PallLean.Paper93.Wiring.PerTypeProductGrouping_universal)
    (hI3_univ : PallLean.Paper93.Wiring.PerTypeMlprojClosure_universal)
    (hSelf :
      ∀ (n : ℕ) (hn4 : n ≥ 4)
        (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                ProfileChargeSelfAtBoundedProfile
                  (concreteWEndpointSpanOneStepCharge n hn4)
                  (admissibleToBounded hadm)) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  have hn4 : n ≥ 4 := routeB_paperScale_ge_four hn
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_chargedFrontier
      M n hn hn2 htb hns hdec
      (concreteWEndpointSpanOneStepCharge n hn4) hn4
      (hzero M n hn2 htb hns)
      (endpointAugmentedActiveProfileChargedFrontier_of_directBranchShapes_transport_universal_I1_I3_checkedBudget
        M n hn2 htb hns (concreteWEndpointSpanOneStepCharge n hn4) hn4
        (hShape M n hn2 hn4 htb hns)
        (hTransport M n hn2 hn4 htb hns)
        hI1_univ
        (endpointAugmentedConcreteW_chargedShiftClosure_concreteWEndpointSpanOneStepCharge
          n hn4)
        hI3_univ
        (hSelf n hn4))

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

/-- Legacy rich-projection discharge from the strict `TΦ` concrete per-type
spanning route, mediated only by the established no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteW_perTypeSpanning
    (hSpan :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        PallLean.Paper93.Spanning.CookLevinPerTypeSpanning M n hn2 htb hns
          (fun tau =>
            PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) tau)) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteW_perTypeSpanning
      hSpan)

/-- Legacy rich-projection discharge from the endpoint-augmented active-span
strict `TΦ` route, mediated only by the established no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_activeProfileSpan
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hactiveSpan :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        ∀ (h : ProfileHistogram)
          (hadm : ProfileAdmissible (Nat.log 2 n) h),
            h ConstraintType.transitionRight = 0 →
              ActiveProfileSupport h →
                cookLevinPostSpanAt M n hn2 htb hns h ≤
                  cookLevinProfileSubspace (admissibleToBounded hadm)
                    (endpointAugmentedConcreteW n hn4)) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_activeProfileSpan
      hzero hactiveSpan)

/-- Legacy rich-projection discharge from endpoint-augmented per-profile
spanning slices, mediated only by the established no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_spanningAtBoundedProfile
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hSpanAt :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        ∀ (h : ProfileHistogram)
          (hadm : ProfileAdmissible (Nat.log 2 n) h),
            h ConstraintType.transitionRight = 0 →
              ActiveProfileSupport h →
                CookLevinPerTypeSpanningAtBoundedProfile M n hn2 htb hns
                  (endpointAugmentedConcreteW n hn4)
                  (admissibleToBounded hadm)) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_spanningAtBoundedProfile
      hzero hSpanAt)

/-- Legacy rich-projection discharge from concrete row embeddings feeding
endpoint-augmented active profile-local spans, mediated only by the
established no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_concreteW_rowEmbeddings_activeProfiles
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hRowEmbeddings :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn2 htb hns hn4) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_concreteW_rowEmbeddings_activeProfiles
      hzero hRowEmbeddings)

/-- Legacy rich-projection discharge from the endpoint-augmented active-profile
route with the compatibility universal per-type spanning input. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_perTypeSpanning_universal_activeProfiles
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hSpan_univ : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning_universal) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_perTypeSpanning_universal_activeProfiles
      hzero hSpan_univ)

/-- Legacy rich-projection discharge from the charged endpoint-augmented
strict `TΦ` route, mediated only by the established no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_chargedFrontier
    (charge : ∀ n : ℕ, ProfileCharge n)
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hFrontier :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        EndpointAugmentedActiveProfileChargedFrontier
          M n hn2 htb hns (charge n) hn4) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_chargedFrontier
      charge hzero hFrontier)

/-- Legacy rich-projection discharge from charged target-profile covers. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_chargedTargetCover
    (charge : ∀ n : ℕ, ProfileCharge n)
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hFactor :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinFactorMemPerType M n hn2 htb hns
          (endpointAugmentedConcreteW n hn4))
    (hI1 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeProductGrouping
          (endpointAugmentedConcreteW n hn4))
    (hI2c :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PerTypeChargedShiftClosure (charge n)
          (endpointAugmentedConcreteW n hn4))
    (hI3 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeMlprojClosure
          (endpointAugmentedConcreteW n hn4))
    (hCover :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        ∀ (h : ProfileHistogram)
          (hadm : ProfileAdmissible (Nat.log 2 n) h),
            h ConstraintType.transitionRight = 0 →
              h ≠ zeroProfileHistogram →
                ActiveProfileSupport h →
                  CookLevinEndpointChargedTargetProfileCoverAt
                    M n hn2 htb hns (charge n) h hadm) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_chargedTargetCover
      charge hzero hFactor hI1 hI2c hI3 hCover)

/-- Legacy rich-projection discharge from concrete endpoint charged
target-profile covers. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_concreteEndpointCharge_chargedTargetCover
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hFactor :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinFactorMemPerType M n hn2 htb hns
          (endpointAugmentedConcreteW n hn4))
    (hI1 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeProductGrouping
          (endpointAugmentedConcreteW n hn4))
    (hI3 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeMlprojClosure
          (endpointAugmentedConcreteW n hn4))
    (hCover :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        ∀ (h : ProfileHistogram)
          (hadm : ProfileAdmissible (Nat.log 2 n) h),
            h ConstraintType.transitionRight = 0 →
              h ≠ zeroProfileHistogram →
                ActiveProfileSupport h →
                  CookLevinEndpointChargedTargetProfileCoverAt
                    M n hn2 htb hns
                    (concreteWEndpointSpanOneStepCharge n hn4) h hadm) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_concreteEndpointCharge_chargedTargetCover
      hzero hFactor hI1 hI3 hCover)

/-- Legacy rich-projection discharge from canonical endpoint-augmented
active-profile components. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_canonicalShape_chargedComponents
    (charge : ∀ n : ℕ, ProfileCharge n)
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hBudget :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        EndpointAugmentedActiveProfileSubspaceBudget n hn4)
    (hShape :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinCanonicalConcreteWShapeWitnesses M n hn2 htb hns hn4)
    (hI1 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeProductGrouping
          (endpointAugmentedConcreteW n hn4))
    (hI2c :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PerTypeChargedShiftClosure (charge n)
          (endpointAugmentedConcreteW n hn4))
    (hI3 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeMlprojClosure
          (endpointAugmentedConcreteW n hn4))
    (hSelf :
      ∀ (n : ℕ) (_hn4 : n ≥ 4)
        (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                ProfileChargeSelfAtBoundedProfile (charge n)
                  (admissibleToBounded hadm)) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_canonicalShape_chargedComponents
      charge hzero hBudget hShape hI1 hI2c hI3 hSelf)

/-- Legacy rich-projection discharge from canonical endpoint-augmented
active-profile components, with the budget discharged by the checked
dimension theorem. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_canonicalShape_chargedComponents_checkedBudget
    (charge : ∀ n : ℕ, ProfileCharge n)
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hShape :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinCanonicalConcreteWShapeWitnesses M n hn2 htb hns hn4)
    (hI1 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeProductGrouping
          (endpointAugmentedConcreteW n hn4))
    (hI2c :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PerTypeChargedShiftClosure (charge n)
          (endpointAugmentedConcreteW n hn4))
    (hI3 :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PallLean.Paper93.Closure.PerTypeMlprojClosure
          (endpointAugmentedConcreteW n hn4))
    (hSelf :
      ∀ (n : ℕ) (_hn4 : n ≥ 4)
        (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                ProfileChargeSelfAtBoundedProfile (charge n)
                  (admissibleToBounded hadm)) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_canonicalShape_chargedComponents_checkedBudget
      charge hzero hShape hI1 hI2c hI3 hSelf)

/-- Legacy rich-projection discharge from direct transported Cook-Levin branch
shapes, universal I1/I3, and charged endpoint-active local inputs. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_directBranchTransport_universal_I1_I3_checkedBudget
    (charge : ∀ n : ℕ, ProfileCharge n)
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hShape :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hI1_univ : PallLean.Paper93.Wiring.PerTypeProductGrouping_universal)
    (hI2c :
      ∀ (n : ℕ) (hn4 : n ≥ 4),
        PerTypeChargedShiftClosure (charge n)
          (endpointAugmentedConcreteW n hn4))
    (hI3_univ : PallLean.Paper93.Wiring.PerTypeMlprojClosure_universal)
    (hSelf :
      ∀ (n : ℕ) (_hn4 : n ≥ 4)
        (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                ProfileChargeSelfAtBoundedProfile (charge n)
                  (admissibleToBounded hadm)) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_directBranchTransport_universal_I1_I3_checkedBudget
      charge hzero hShape hTransport hI1_univ hI2c hI3_univ hSelf)

/-- Legacy rich-projection discharge from direct transported Cook-Levin branch
shapes, universal I1/I3, and the concrete one-step endpoint charge. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_directBranchTransport_universal_I1_I3_concreteEndpointCharge_checkedBudget
    (hzero :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hShape :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport :
      ∀ (M : DTM) (n : ℕ) (hn2 : n ≥ 2) (hn4 : n ≥ 4)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hI1_univ : PallLean.Paper93.Wiring.PerTypeProductGrouping_universal)
    (hI3_univ : PallLean.Paper93.Wiring.PerTypeMlprojClosure_universal)
    (hSelf :
      ∀ (n : ℕ) (hn4 : n ≥ 4)
        (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                ProfileChargeSelfAtBoundedProfile
                  (concreteWEndpointSpanOneStepCharge n hn4)
                  (admissibleToBounded hadm)) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_directBranchTransport_universal_I1_I3_concreteEndpointCharge_checkedBudget
      hzero hShape hTransport hI1_univ hI3_univ hSelf)

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

/-- A universal per-type spanning theorem is enough for the strict paper
`TΦ` final path.  This is the current narrow P-side Route B frontier after
retargeting away from the legacy global rank seam. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_perTypeSpanning_universal
    (hSpan_univ : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning_universal) :
    PallLean.Paper93.DeepMath.PathB.NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_perTypeSpanning_universal
      M n hn hn2 htb hns hdec hSpan_univ

/-- A uniform post-span symmetric-product generator theorem is enough for the
strict paper `TΦ` final path.  This is narrower than the legacy landed P-side
rank theorem: it asks only for the bounded-profile concrete Cook-Levin
post-span finite-generator statement isolated in `WithinProfileBound`. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_postSpanBoundedBySymProduct
    (hpostSpan :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinPostSpanBoundedBySymProduct
          M n hn2 htb hns) :
    PallLean.Paper93.DeepMath.PathB.NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_postSpanBoundedBySymProduct
      M n hn hn2 htb hns hdec
      (hpostSpan M n hn hn2 htb hns)

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

/-- Legacy rich-projection discharge from the strict `TΦ` per-type spanning
route, mediated only by the established no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_perTypeSpanning_universal
    (hSpan_univ : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning_universal) :
    PallLean.Paper93.DeepMath.PathB.CookLevinRichProjectionDischarge :=
  PallLean.Paper93.DeepMath.PathB.cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_perTypeSpanning_universal
      hSpan_univ)

/-- Legacy rich-projection discharge from the strict `TΦ` post-span
symmetric-product generator route, mediated only by the established no-decider
equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_postSpanBoundedBySymProduct
    (hpostSpan :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinPostSpanBoundedBySymProduct
          M n hn2 htb hns) :
    PallLean.Paper93.DeepMath.PathB.CookLevinRichProjectionDischarge :=
  PallLean.Paper93.DeepMath.PathB.cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_postSpanBoundedBySymProduct
      hpostSpan)

/-! ## Axiom audit anchors -/

#print axioms routeBPaperFaithfulTPhiMap_injective
#print axioms routeBPaperFaithfulTPhi_restrict_embedded_Q_eq_restrict_compiledPoly
#print axioms routeBPaperFaithfulTPhi_canonical_projection_stage
#print axioms routeBPaperFaithfulTPhi_extraction_transfer
#print axioms routeBPaperFaithfulTPhi_identity_minor_data
#print axioms routeBPaperFaithfulTPhi_extraction_and_identity_minor
#print axioms routeBPaperFaithfulTPhi_normalizedCoupledSheetRowIdentity
#print axioms false_of_routeBPaperFaithfulTPhi_normalizedCoupledSheet_components
#print axioms false_of_routeBPaperFaithfulTPhi_normalizedCoupledSheet_sourceTransport
#print axioms false_of_routeBPaperFaithfulTPhi_normalizedCoupledSheet_sourceTransport_sameTargetMinor
#print axioms false_of_routeBPaperFaithfulTPhi_normalizedCoupledSheet_from_sourceTransportData
#print axioms false_of_routeBPaperFaithfulTPhi_qRankUpper
#print axioms false_of_routeBPaperFaithfulTPhi_from_p_side
#print axioms false_of_routeBPaperFaithfulTPhi_from_templateCollapse
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_templateCollapse
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_boundedProfileTemplateCollapse
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_postSpanBoundedBySymProduct
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_perTypeSpanning
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_activeProfileSpan
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_endpointAugmented_chargedFrontier
#print axioms routeB_paperScale_ge_four
#print axioms routeBPaperFaithfulTPhiAmbientGauge_compiledPoly_eq_reexpandedStrictFOB
#print axioms RouteBPaperFaithfulTPhiProjectedPWindowZeroProfileRowIdentity
#print axioms RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
#print axioms routeBPaperFaithfulTPhi_strictFOB_offRangeDerivativeRow_zero
#print axioms routeBPaperFaithfulTPhi_rename_restrictStrictFOB_of_vars_range
#print axioms routeBPaperFaithfulTPhi_strictFOB_renamedDerivativeRow
#print axioms routeBPaperFaithfulTPhi_strictFOB_renamedDerivativeRow_restrict
#print axioms routeBPaperFaithfulTPhi_rangePWindowRow_eq_renamedRestrictedRow
#print axioms routeBPaperFaithfulTPhi_strictFOB_allRangeDerivativeRow
#print axioms routeBPaperFaithfulTPhi_strictFOB_offRangeSingletonShiftRow_singletonQuotient
#print axioms routeBPaperFaithfulTPhi_strictFOB_allRangeDerivativeRow_singletonQuotient_iff_projected
#print axioms routeBPaperFaithfulTPhi_zeroProfileSingletonShiftSubspace_coeff_zero
#print axioms routeBPaperFaithfulTPhi_zeroProfileQuotientBySingletonShiftProjection_apply_eq_zero_iff
#print axioms routeBPaperFaithfulTPhi_singletonQuotientProjection_baseRow_ne_zero
#print axioms routeBPaperFaithfulTPhi_strictFOB_offRangeRow_forces_singletonQuotient_zero
#print axioms routeBPaperFaithfulTPhi_strictFOB_singletonQuotient_offRangeConstantRow_noGo
#print axioms routeBPaperFaithfulTPhiRangePWindowSubspace
#print axioms RouteBPaperFaithfulTPhiRangePWindowControlledByZeroProfileProjection
#print axioms RouteBPaperFaithfulTPhiRangePWindowZeroProfileRowIdentity
#print axioms RouteBPaperFaithfulTPhiRangePWindowZeroProfileGeneratorReduction
#print axioms routeBPaperFaithfulTPhi_rangePWindowGenerator_mem_zeroProfileProjection
#print axioms routeBPaperFaithfulTPhi_rangePWindowControlledByZeroProfileProjection_iff_generatorReduction
#print axioms routeBPaperFaithfulTPhi_rangePWindowControlledByZeroProfileProjection_of_rowIdentity
#print axioms RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
#print axioms RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
#print axioms routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_iff_restrictedResidualBalance
#print axioms routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_of_restrictedResidualBalance
#print axioms routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_noGo_of_not_restrictedResidualBalance
#print axioms routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientRowIdentity_iff_restrictedResidualBalance
#print axioms routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_iff_singletonResidual_and_derivativeFixed
#print axioms routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_of_singletonResidual_derivativeFixed
#print axioms routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_of_normalizedRows_derivativeFixed
#print axioms routeBPaperFaithfulTPhi_normalizedNonSingletonCoeffIdentity_iff_coeffBalance
#print axioms routeBPaperFaithfulTPhi_not_normalizedNonSingletonCoeffIdentity_of_twoDifferentiatedStrictTags_even
#print axioms routeBPaperFaithfulTPhi_rangePWindowZeroProfileRowIdentity_of_restricted
#print axioms routeBPaperFaithfulTPhi_projectedPWindowGenerator_mem_zeroProfileProjection_of_rangeRowIdentity
#print axioms routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rangeRowIdentity
#print axioms routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rangeRestrictedRowIdentity
#print axioms routeBPaperFaithfulTPhi_projectedPWindowZeroProfileRowIdentity_iff_strictFOBDerivativeErasure
#print axioms RouteBPaperFaithfulTPhiProjectedPWindowZeroProfileGeneratorReduction
#print axioms routeBPaperFaithfulTPhi_projectedPWindowGenerator_mem_zeroProfileProjection
#print axioms routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_iff_generatorReduction
#print axioms routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rowIdentity
#print axioms routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_strictFOBDerivativeErasure
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroProfileProjectedCommonSpanWithBudget_rangeRestrictedRowIdentity
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroProfileQuotientedShiftCommonSpan_rangeRestrictedRowIdentity
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_rowEmbeddings
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_closureFrontier
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteW_perTypeSpanning
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteW_perTypeSpanning
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_activeProfileSpan
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_chargedFrontier
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_activeProfileSpan
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_endpointAugmented_chargedFrontier
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_templateCollapse
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_templateCollapse
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_boundedProfileTemplateCollapse
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_boundedProfileTemplateCollapse
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_postSpanBoundedBySymProduct
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_postSpanBoundedBySymProduct
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteW_rowEmbeddings
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteW_rowEmbeddings
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteW_closureFrontier
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteW_closureFrontier
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_p_side
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_p_side

end PallLean.Paper93.Paper283
