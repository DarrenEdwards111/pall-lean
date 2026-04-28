import PallLean.Step4Compiler
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingBridge
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingsClosure
import PallLean.Paper93.Paper283.RouteBZeroProfileProjectedPWindowProgress

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
#print axioms false_of_routeBPaperFaithfulTPhi_qRankUpper
#print axioms false_of_routeBPaperFaithfulTPhi_from_p_side
#print axioms false_of_routeBPaperFaithfulTPhi_from_templateCollapse
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_templateCollapse
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_boundedProfileTemplateCollapse
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_postSpanBoundedBySymProduct
#print axioms routeB_paperScale_ge_four
#print axioms routeBPaperFaithfulTPhiAmbientGauge_compiledPoly_eq_reexpandedStrictFOB
#print axioms RouteBPaperFaithfulTPhiProjectedPWindowZeroProfileRowIdentity
#print axioms RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
#print axioms routeBPaperFaithfulTPhi_strictFOB_offRangeDerivativeRow_zero
#print axioms routeBPaperFaithfulTPhi_rename_restrictStrictFOB_of_vars_range
#print axioms routeBPaperFaithfulTPhi_strictFOB_renamedDerivativeRow
#print axioms routeBPaperFaithfulTPhi_strictFOB_allRangeDerivativeRow
#print axioms routeBPaperFaithfulTPhi_strictFOB_offRangeSingletonShiftRow_singletonQuotient
#print axioms routeBPaperFaithfulTPhi_strictFOB_allRangeDerivativeRow_singletonQuotient_iff_projected
#print axioms routeBPaperFaithfulTPhi_zeroProfileSingletonShiftSubspace_coeff_zero
#print axioms routeBPaperFaithfulTPhi_zeroProfileQuotientBySingletonShiftProjection_apply_eq_zero_iff
#print axioms routeBPaperFaithfulTPhi_singletonQuotientProjection_baseRow_ne_zero
#print axioms routeBPaperFaithfulTPhi_strictFOB_offRangeRow_forces_singletonQuotient_zero
#print axioms routeBPaperFaithfulTPhi_strictFOB_singletonQuotient_offRangeConstantRow_noGo
#print axioms routeBPaperFaithfulTPhi_projectedPWindowZeroProfileRowIdentity_iff_strictFOBDerivativeErasure
#print axioms RouteBPaperFaithfulTPhiProjectedPWindowZeroProfileGeneratorReduction
#print axioms routeBPaperFaithfulTPhi_projectedPWindowGenerator_mem_zeroProfileProjection
#print axioms routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_iff_generatorReduction
#print axioms routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rowIdentity
#print axioms routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_strictFOBDerivativeErasure
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_rowEmbeddings
#print axioms false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_closureFrontier
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
