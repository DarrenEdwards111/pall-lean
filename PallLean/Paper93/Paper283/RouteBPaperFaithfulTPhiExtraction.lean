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
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i) d)) :
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
