import PallLean.PaperFaithfulSeparation
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRealFrontier
import PallLean.Paper93.DeepMath.PathB.RouteBWidthRankPSide
import PallLean.Paper93.DeepMath.PathB.RouteBPlacedQuotientDescentKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedExtractorKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedConcreteWindowKR

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation

/-- Bridge lemma: any paper-scale no-bounded-SAT-decider statement implies
`PeqNP_Paper → False` by instantiating the witness machine at `n = 2^804`.

This is purely arithmetic/structural glue and introduces no new custom axiom
surface beyond the input proposition itself. -/
theorem noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (hno : NoBoundedSATDeciderAtPaperScale) :
    ∀ (_ : PeqNP_Paper), False := by
  intro hPeqNP
  let n : ℕ := 2 ^ 804
  have hn : n ≥ 2 ^ 804 := by
    simpa [n]
  have hn2 : n ≥ 2 := by
    calc
      2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = n := by simp [n]
  have hns : hPeqNP.decider.numStates ≤ n := by
    exact le_trans hPeqNP.numStates_bound (by simpa [n])
  exact (hno hPeqNP.decider n hn hn2 hPeqNP.timeBound_le hns) hPeqNP.decides_3sat

#print axioms noBoundedSATDeciderAtPaperScale_implies_not_PeqNP

/-- Legacy no-seam paper-level closeout.

This is intentionally kept only as a historical comparison point: it forwards
to `PaperFaithfulSeparation.P_ne_NP_unconditional_step4_constructive`, whose
body uses the old arbitrary-compiled-polynomial sandwich.  Route-B work below
must use the SAT-decider-specific `T_Φ` extraction bridge instead. -/
theorem P_ne_NP_paper_no_routeB_seams_constructive :
    ∀ (_ : PeqNP_Paper), False :=
  PaperFaithfulSeparation.P_ne_NP_unconditional_step4_constructive

#print axioms P_ne_NP_paper_no_routeB_seams_constructive

/-- Type-form alias for the legacy no-seam closeout. -/
theorem isEmpty_PeqNP_Paper_no_routeB_seams_constructive :
    IsEmpty PeqNP_Paper :=
  ⟨P_ne_NP_paper_no_routeB_seams_constructive⟩

#print axioms isEmpty_PeqNP_Paper_no_routeB_seams_constructive

/-- Paper-faithful Route-B closeout from the SAT-decider-specific projected
P-side theorem.

This is the replacement for the old arbitrary-compiled-polynomial sandwich:
`Step247UniformProjectedPSideTheorem` bounds the full Step247 compiler output,
`noBoundedSATDeciderAtPaperScale_of_cookLevin_TPhi_projectedPSideBound`
transports that bound through the actual `T_Φ` extraction, and the NP lower
bound fires on the extracted coupled sheet `Q ×_Φ`, not on an arbitrary
`compiledPoly`. -/
theorem not_PeqNP_of_step247UniformProjectedPSideTheorem_TPhi
    (hP : Step247UniformProjectedPSideTheorem) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_of_cookLevin_TPhi_projectedPSideBound hP)

#print axioms not_PeqNP_of_step247UniformProjectedPSideTheorem_TPhi

/-- Width⇒Rank form of the paper-faithful Route-B closeout.

A §40.2 `Theorem216SpanningSet` witness for the full Step247 compiler output
is first turned into the projected P-side theorem, then closed only via the
`T_Φ` extraction sandwich. -/
theorem P_ne_NP_canonical_routeB_widthRank_TPhi_conditional
    (hWR : Step247UniformWidthRankData) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_of_widthRankData_TPhi hWR)

#print axioms P_ne_NP_canonical_routeB_widthRank_TPhi_conditional

/-- Conditional paper-faithful closeout: if the Step247 selected-profile
template-span Route-B seam is available uniformly, then `PeqNP_Paper` is
contradictory.  This composes the Route-B no-decider theorem with the bridge
above and keeps the closure statement at the `PeqNP_Paper` level. -/
theorem not_PeqNP_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData
      hData)

#print axioms not_PeqNP_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData

/-- Canonical Route-B paper-faithful conditional closure statement at the
`PeqNP_Paper` level.

If the uniform Step247 selected-profile template-span seam is available, then
`P = NP` (in the paper bundle form) is contradictory. -/
theorem P_ne_NP_canonical_routeB_profileTemplateSpan_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData) :
    ∀ (_ : PeqNP_Paper), False :=
  not_PeqNP_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData
    hData

#print axioms P_ne_NP_canonical_routeB_profileTemplateSpan_conditional

/-- Route-B closeout in the literal paper Lemma-31/Profile-Compression shape:
selected profile-template span data (the symmetric-profile subspace seam) implies
`PeqNP_Paper → False`.  This is definitionally the same closure as
`P_ne_NP_canonical_routeB_profileTemplateSpan_conditional`, kept as an explicit
paper-text anchor. -/
theorem P_ne_NP_canonical_routeB_lemma31_profileSubspace_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_profileTemplateSpan_conditional hData

#print axioms P_ne_NP_canonical_routeB_lemma31_profileSubspace_conditional

/-- Paper-faithful Route-B closeout from the actual Lemma-31 term-local
profile-template family.

This is the non-deviating path: term-dependent local types assemble into the
row-selected interface-anonymous profile subspace, the sum-over-profiles bound
closes the strict `TΦ` P-side rank, and the SAT-decider-specific lower bound
fires on the extracted target.  It does not use arbitrary row uniqueness. -/
theorem not_PeqNP_of_step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData
      hData)

#print axioms not_PeqNP_of_step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData

/-- Canonical Route-B conditional closure at the corrected paper surface:
canonical windows/profile selection → term-local types → selected profile
subspace containment/dimension → strict `TΦ` extraction. -/
theorem P_ne_NP_canonical_routeB_profileTemplateTermFamily_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData) :
    ∀ (_ : PeqNP_Paper), False :=
  not_PeqNP_of_step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData
    hData

#print axioms P_ne_NP_canonical_routeB_profileTemplateTermFamily_conditional

/-- Route-B closeout through exact-profile template-collapse data, routed into
the literal Lemma-31 profile-subspace seam. -/
theorem P_ne_NP_canonical_routeB_lemma31_profileSubspace_from_exactProfileTemplateCollapse_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizExactProfileTemplateCollapseData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_lemma31_profileSubspace_conditional
    (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData_of_exactProfileTemplateCollapseData
      hData)

#print axioms P_ne_NP_canonical_routeB_lemma31_profileSubspace_from_exactProfileTemplateCollapse_conditional

/-- Route-B closeout from the currently available canonical-row exact-profile
collapse seam (decider-parameterized), with no stronger slot/fiber assumptions. -/
theorem P_ne_NP_canonical_routeB_lemma31_profileSubspace_from_canonicalRowExactProfileTemplateCollapse_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceCanonicalRowExactProfileTemplateCollapseData) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceCanonicalRowExactProfileTemplateCollapseData
      hData)

#print axioms P_ne_NP_canonical_routeB_lemma31_profileSubspace_from_canonicalRowExactProfileTemplateCollapse_conditional

/-- Route-B closeout from the source local-monoid classifier seam (the
algebra-facing Lemma-31 frontier). -/
theorem P_ne_NP_canonical_routeB_lemma31_profileSubspace_from_sourceLocalMonoidClassifier_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidClassifierData) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidClassifierData
      hData)

#print axioms P_ne_NP_canonical_routeB_lemma31_profileSubspace_from_sourceLocalMonoidClassifier_conditional

/-- Same closeout routed through Step247-uniform source generator maps
(profile-local derivative-row type maps). -/
theorem P_ne_NP_canonical_routeB_lemma31_profileSubspace_from_sourceLocalMonoidGeneratorMaps_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidGeneratorMapsData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_lemma31_profileSubspace_from_sourceLocalMonoidClassifier_conditional
    (step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidClassifierData_of_sourceLocalMonoidGeneratorMapsData
      hData)

#print axioms P_ne_NP_canonical_routeB_lemma31_profileSubspace_from_sourceLocalMonoidGeneratorMaps_conditional

/-- Canonical conditional closure via the literal source canonical row-span
surface.

This is the manuscript-faithful Lemma-32 endpoint: canonical windows select a
profile, `V_h` is the span of selected canonical source rows of that profile,
that row span has the within-profile bound, and only then the strict `TΦ`
extraction/lower-bound bridge is applied. -/
theorem P_ne_NP_canonical_routeB_sourceCanonicalProfileRowSpan_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceCanonicalProfileRowSpanData) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceCanonicalProfileRowSpanData
      hData)

#print axioms P_ne_NP_canonical_routeB_sourceCanonicalProfileRowSpan_conditional

/-- Canonical conditional closure from source local-type compression, routed
through the literal canonical row-span/profile bound rather than the old raw-row
expansion target. -/
theorem P_ne_NP_canonical_routeB_sourceLocalTypeCompression_rowSpan_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLocalTypeCompressionData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_sourceCanonicalProfileRowSpan_conditional
    (step247UniformRouteBPaperFaithfulTPhiSourceCanonicalProfileRowSpanData_of_sourceLocalTypeCompressionData
      hData)

#print axioms P_ne_NP_canonical_routeB_sourceLocalTypeCompression_rowSpan_conditional

/-- One-shot canonical Route-B closure from the term-local Lemma-31 compression
surface.

This is the full corrected chain in one theorem:
term-local Leibniz compression → selected source `V_h` for the whole canonical
row → literal canonical profile row-span → strict `TΦ` extraction → SAT
lower-bound contradiction → `PeqNP_Paper → False`. -/
theorem P_ne_NP_canonical_routeB_oneShot_from_sourceLeibnizLocalTypeCompression_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_sourceLocalTypeCompression_rowSpan_conditional
    (step247UniformRouteBPaperFaithfulTPhiSourceLocalTypeCompressionData_of_sourceLeibnizLocalTypeCompressionData
      hData)

#print axioms P_ne_NP_canonical_routeB_oneShot_from_sourceLeibnizLocalTypeCompression_conditional

/-- Canonical one-shot closeout from the lowest coherent bottom seam:
factor-fiber slot partitions plus local-algebra selected-shift closure first
construct the literal source Leibniz local-type compression witness, then the
canonical row-span/`TΦ` bridge contradicts `PeqNP_Paper`. -/
theorem P_ne_NP_canonical_routeB_oneShot_from_fiberPartition_and_localAlgebra_sourceLeibnizLocalTypeCompression_conditional
    (hFib : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData)
    (hLocal : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        DLoc.sourcePartition = DFib.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        ∀ w hw, DLoc.profileOfCanonicalWindow w hw = DFib.profileOfCanonicalWindow w hw) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_oneShot_from_sourceLeibnizLocalTypeCompression_conditional
    (step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_fiberPartitionData_and_localAlgebraData
      hFib hLocal hPartEq hProfEq)

#print axioms P_ne_NP_canonical_routeB_oneShot_from_fiberPartition_and_localAlgebra_sourceLeibnizLocalTypeCompression_conditional

/-- Canonical conditional closure via the direct local compiled-coordinate
profile-subspace row surface.

This is the paper-faithful Lemma-31 Route-B target: selected canonical rows land
in their selected `profileSubspace ρ.val W`; no arbitrary shifted Leibniz
summand is required to preserve the selected profile. -/
theorem P_ne_NP_canonical_routeB_localCompiledProfileSubspaceRow_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData
      hData)

#print axioms P_ne_NP_canonical_routeB_localCompiledProfileSubspaceRow_conditional

/-- Canonical conditional closure via the explicit placed-quotient/descent Route B
surface. -/
theorem P_ne_NP_canonical_routeB_placedQuotientDescent_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_localCompiledProfileSubspaceRow_conditional
    (step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData_of_placedQuotientDescent
      hData)

#print axioms P_ne_NP_canonical_routeB_placedQuotientDescent_conditional

/-- Canonical conditional closure from the renamed-canonical Lemma-31 expansion
through the active local `W_σ` row-containment target.  This is the direct
paper-faithful four-step route: local `W_σ` construction, slot membership,
profile-product assembly, and selected `TΦ` row equality. -/
theorem P_ne_NP_canonical_routeB_renamedCanonicalLocalW_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiRenamedCanonicalInterfaceExpansionData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_localCompiledProfileSubspaceRow_conditional
    (step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData_of_renamedCanonicalInterfaceExpansionData
      hData)

#print axioms P_ne_NP_canonical_routeB_renamedCanonicalLocalW_conditional

/-- Canonical conditional closure through the selected projected quotient
normal-form route.

This is the sound quotient/normalisation replacement for the false ambient
selected-place equality route: the supplied datum chooses a quotient certificate,
proves its projected type budget, and proves residual balance for that chosen
projection; the closeout then runs through the strict `T_Φ` extraction target. -/
theorem P_ne_NP_canonical_routeB_projectedQuotientNormalForm_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData
      hData)

#print axioms P_ne_NP_canonical_routeB_projectedQuotientNormalForm_conditional

/-- Canonical conditional closure from extractor-form touched KR data.

This is the local-state/Khatri--Rao version of the paper Route-B row
classification: each row is classified by a per-position local-state extractor,
then interpreted as a length-`log₂ n` word over a fixed local alphabet. -/
theorem P_ne_NP_canonical_routeB_touchedExtractorKR_conditional
    (hData : Step247UniformTouchedExtractorKRData) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_of_touchedExtractorKRData_TPhi hData)

#print axioms P_ne_NP_canonical_routeB_touchedExtractorKR_conditional

/-- Canonical conditional closure from concrete-window touched KR data.

This is one level more concrete than the extractor surface: each local KR
position is backed by an actual row variable, an optional touched Cook--Levin
constraint, support witnesses, and a finite interface symbol. -/
theorem P_ne_NP_canonical_routeB_touchedConcreteWindowKR_conditional
    (hData : Step247UniformTouchedConcreteWindowKRData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_touchedExtractorKR_conditional
    (step247UniformTouchedExtractorKRData_of_touchedWindowKRData
      (step247UniformTouchedWindowKRData_of_touchedConcreteWindowKRData hData))

#print axioms P_ne_NP_canonical_routeB_touchedConcreteWindowKR_conditional

/-- Canonical conditional closure from the concrete placed-expansion plus
ambient-quotient-soundness seam, routed through placed quotient/descent. -/
theorem P_ne_NP_canonical_routeB_placedExpansion_conditional
    (hExp : Step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData)
    (hQ : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_placedQuotientDescent_conditional
    (step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData_of_placedExpansionData_and_ambientQuotientSoundness
      hExp hQ)

#print axioms P_ne_NP_canonical_routeB_placedExpansion_conditional

/-- Canonical conditional closure from placed expansion plus the concrete
via-canonical bridge decomposition of ambient quotient soundness. -/
theorem P_ne_NP_canonical_routeB_placedExpansion_viaCanonicalInterface_conditional
    (hExp : Step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData)
    (hVia : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaCanonicalInterfaceExpansionData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_placedExpansion_conditional hExp
    (step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessData_of_viaCanonicalInterfaceExpansionData hVia)

#print axioms P_ne_NP_canonical_routeB_placedExpansion_viaCanonicalInterface_conditional

/-- Canonical conditional closure from placed expansion plus the finer
renamed-local-chart decomposition of the ambient quotient soundness bridge. -/
theorem P_ne_NP_canonical_routeB_placedExpansion_viaRenamedLocalChart_conditional
    (hExp : Step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData)
    (hRenamed : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaRenamedLocalChartExpansionData)
    (hChart : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessChartTrivialityData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_placedExpansion_viaCanonicalInterface_conditional hExp
    (step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaCanonicalInterfaceExpansionData_of_renamedLocalChartData
      hRenamed hChart)

#print axioms P_ne_NP_canonical_routeB_placedExpansion_viaRenamedLocalChart_conditional

/-- Same closure, using the already exposed uniform renamed-canonical
interface-expansion seam to provide renamed-local-chart data. -/
theorem P_ne_NP_canonical_routeB_placedExpansion_viaRenamedCanonicalAndChart_conditional
    (hExp : Step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData)
    (hRenamedCanonical : Step247UniformRouteBPaperFaithfulTPhiRenamedCanonicalInterfaceExpansionData)
    (hChart : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessChartTrivialityData) :
    ∀ (_ : PeqNP_Paper), False := by
  have hRenamed :
      Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaRenamedLocalChartExpansionData := by
    intro M n hn hn2 htb hns
    rcases hRenamedCanonical M n hn hn2 htb hns with ⟨D⟩
    exact
      ⟨{ rowExpansionData :=
            PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedRowInterfaceSlotExpansionData_of_renamedCanonicalInterfaceExpansionData
              M n hn2 htb hns D
         , rowExpansionCanonicalSlot := D.rowExpansionCanonicalSlot
         , rowExpansionChartMap := D.rowExpansionChartMap
         , rowExpansionSlot_transport_to_renamedCanonicalChart := by
              intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ t σ j
              rfl }⟩
  exact
    P_ne_NP_canonical_routeB_placedExpansion_viaRenamedLocalChart_conditional
      hExp hRenamed hChart

#print axioms P_ne_NP_canonical_routeB_placedExpansion_viaRenamedCanonicalAndChart_conditional

/-- Same closure, with chart-transport witnesses produced from explicit
chart-map identity on canonical slots. -/
theorem P_ne_NP_canonical_routeB_placedExpansion_viaRenamedCanonicalAndChartMapIdentity_conditional
    (hExp : Step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData)
    (hRenamedCanonical : Step247UniformRouteBPaperFaithfulTPhiRenamedCanonicalInterfaceExpansionData)
    (hId : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessChartTrivialityData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_placedExpansion_viaRenamedCanonicalAndChart_conditional
    hExp hRenamedCanonical hId

#print axioms P_ne_NP_canonical_routeB_placedExpansion_viaRenamedCanonicalAndChartMapIdentity_conditional

/-- Canonical Route-B closure from uniform canonical-interface expansion data.
This removes the chart-transport seam entirely by using the already checked
canonical-interface -> placed-quotient-descent adapter. -/
theorem P_ne_NP_canonical_routeB_canonicalInterfaceExpansion_conditional
    (hCan : Step247UniformRouteBPaperFaithfulTPhiCanonicalInterfaceExpansionData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_placedQuotientDescent_conditional
    (step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData_of_canonicalInterfaceExpansionData
      hCan)

#print axioms P_ne_NP_canonical_routeB_canonicalInterfaceExpansion_conditional

/-- Canonical Route-B closure from explicit row-interface-slot expansion data. -/
theorem P_ne_NP_canonical_routeB_interfaceSlotExpansion_conditional
    (hSlot : Step247UniformRouteBPaperFaithfulTPhiInterfaceSlotExpansionData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_canonicalInterfaceExpansion_conditional
    (step247UniformRouteBPaperFaithfulTPhiCanonicalInterfaceExpansionData_of_interfaceSlotExpansionData
      hSlot)

#print axioms P_ne_NP_canonical_routeB_interfaceSlotExpansion_conditional

/-- Canonical Route-B closure from direct compiled-basis profile-subspace row
membership (the literal Lemma-31 row-subspace surface). -/
theorem P_ne_NP_canonical_routeB_compiledBasisProfileSubspaceRow_conditional
    (hRow : Step247UniformRouteBPaperFaithfulTPhiCompiledBasisProfileSubspaceRowData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_localCompiledProfileSubspaceRow_conditional
    (step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData_of_compiledBasisProfileSubspaceRowData
      hRow)

#print axioms P_ne_NP_canonical_routeB_compiledBasisProfileSubspaceRow_conditional

/-- Canonical Route-B closure from shifted branch-atom compiled-basis profile
membership via the checked linear assembly into selected-row profile-subspace
membership. -/
theorem P_ne_NP_canonical_routeB_shiftedBranchAtomCompiledBasisProfile_conditional
    (hBranch : Step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_compiledBasisProfileSubspaceRow_conditional
    (step247UniformRouteBPaperFaithfulTPhiCompiledBasisProfileSubspaceRowData_of_shiftedBranchAtomCompiledBasisProfileData
      hBranch)

#print axioms P_ne_NP_canonical_routeB_shiftedBranchAtomCompiledBasisProfile_conditional

/-- Canonical Route-B closure from shifted Leibniz-product local-algebra data,
following the paper-faithful chain:
local-algebra -> shifted-product profile -> shifted-branch-atom profile ->
selected-row profile-subspace -> canonical closure. -/
theorem P_ne_NP_canonical_routeB_shiftedLeibnizProductLocalAlgebra_conditional
    (hLocalAlg : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_shiftedBranchAtomCompiledBasisProfile_conditional
    (step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData_of_localAlgebraData
      hLocalAlg)

#print axioms P_ne_NP_canonical_routeB_shiftedLeibnizProductLocalAlgebra_conditional

/-- Canonical Route-B closure from shifted Leibniz-product interface-slot
factorization data (paper-faithful slot-factorization seam). -/
theorem P_ne_NP_canonical_routeB_shiftedLeibnizProductInterfaceSlotFactorization_conditional
    (hSlotFac : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_shiftedLeibnizProductLocalAlgebra_conditional
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData_of_interfaceSlotFactorizationData
      hSlotFac)

#print axioms P_ne_NP_canonical_routeB_shiftedLeibnizProductInterfaceSlotFactorization_conditional

/-- Paper-faithful constructive split for witnessed slot-factorization closure:
a paired exact-slot payload with its selected-shift closure field suffices. -/
theorem P_ne_NP_canonical_routeB_shiftedLeibnizProductInterfaceSlotFactorization_of_exactSlotWithSelectedShiftClosure_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData) :
    ∀ (_ : PeqNP_Paper), False := by
  apply P_ne_NP_canonical_routeB_shiftedLeibnizProductInterfaceSlotFactorization_conditional
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D, hClosure⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductInterfaceSlotFactorizationData_of_exactInterfaceSlotFactorizationData
    M n hn2 htb hns D hClosure⟩

#print axioms P_ne_NP_canonical_routeB_shiftedLeibnizProductInterfaceSlotFactorization_of_exactSlotWithSelectedShiftClosure_conditional

/-- Canonical Route-B closure from uniform-shift-closure slot-product data,
through the paired paper-faithful exact-slot + selected-shift witness seam. -/
theorem P_ne_NP_canonical_routeB_shiftedLeibnizProductUniformShiftClosure_conditional
    (hUniform : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductUniformShiftClosureData) :
    ∀ (_ : PeqNP_Paper), False := by
  apply P_ne_NP_canonical_routeB_shiftedLeibnizProductInterfaceSlotFactorization_of_exactSlotWithSelectedShiftClosure_conditional
  intro M n hn hn2 htb hns
  rcases hUniform M n hn hn2 htb hns with ⟨D⟩
  let Dslot :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductInterfaceSlotFactorizationData_of_slotProductUniformShiftClosureData
      M n hn2 htb hns D
  let Dexact :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductExactInterfaceSlotFactorizationData_of_interfaceSlotFactorizationData
      M n hn2 htb hns Dslot
  refine ⟨Dexact, ?_⟩
  intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ p hp
  have hρ' :
      Dslot.profileOfCanonicalWindow
          (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
          hrow.1 = ρ := by
    simpa [Dexact, Dslot] using hρ
  simpa [Dexact, Dslot] using Dslot.selectedShift_mlProj_closure_compiledBasisProfileSubspace
    ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ' p hp

#print axioms P_ne_NP_canonical_routeB_shiftedLeibnizProductUniformShiftClosure_conditional

/-- Canonical Route-B closure from shifted Leibniz-product compiled-basis
profile membership. -/
theorem P_ne_NP_canonical_routeB_shiftedLeibnizProductCompiledBasisProfile_conditional
    (hProf : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_shiftedBranchAtomCompiledBasisProfile_conditional
    (step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData_of_shiftedLeibnizProductData
      hProf)

#print axioms P_ne_NP_canonical_routeB_shiftedLeibnizProductCompiledBasisProfile_conditional

/-- Canonical Route-B closure from row-specific shifted slot-product row-shift
seam. -/
theorem P_ne_NP_canonical_routeB_shiftedLeibnizProductRowShift_conditional
    (hRowShift : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_shiftedLeibnizProductCompiledBasisProfile_conditional
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData_of_interfaceSlotProductRowShiftData
      hRowShift)

#print axioms P_ne_NP_canonical_routeB_shiftedLeibnizProductRowShift_conditional

/-- Canonical Route-B closure from coherent indexed-slot + branch-atom row-shift
seam. -/
theorem P_ne_NP_canonical_routeB_shiftedLeibnizProductIndexedBranchRowShift_conditional
    (hIdx : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtomData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_shiftedLeibnizProductRowShift_conditional
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_indexedBranchAtomData
      hIdx)

#print axioms P_ne_NP_canonical_routeB_shiftedLeibnizProductIndexedBranchRowShift_conditional

/-- Canonical Route-B closure from coherent indexed-fiber-partition +
branch-atom row-shift seam (the lower indexed-fiber branch). -/
theorem P_ne_NP_canonical_routeB_shiftedLeibnizProductIndexedFiberBranchRowShift_conditional
    (hFib : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedFiberPartitionBranchAtomData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_shiftedLeibnizProductIndexedBranchRowShift_conditional
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtomData_of_indexedFiberPartitionBranchAtomData
      hFib)

#print axioms P_ne_NP_canonical_routeB_shiftedLeibnizProductIndexedFiberBranchRowShift_conditional

/-- Canonical Route-B closure from paired lower seams:
(indexed fiber-partition slot data) + (shifted branch-atom data), together with
uniform source-partition/profile compatibility, assembled into the coherent
indexed-fiber+branch-atom row-shift seam. -/
theorem P_ne_NP_canonical_routeB_shiftedLeibnizProductIndexedFiberPlusBranchPaired_conditional
    (hFib : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData)
    (hBranch : Step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DBr := Classical.choice (hBranch M n _hn hn2 htb hns)
        DBr.sourcePartition = DFib.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DBr := Classical.choice (hBranch M n _hn hn2 htb hns)
        ∀ w hw, DBr.profileOfCanonicalWindow w hw = DFib.profileOfCanonicalWindow w hw) :
    ∀ (_ : PeqNP_Paper), False := by
  have hCoherent :
      Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedFiberPartitionBranchAtomData := by
    intro M n hn hn2 htb hns
    let DFib := Classical.choice (hFib M n hn hn2 htb hns)
    let DBr := Classical.choice (hBranch M n hn hn2 htb hns)
    refine ⟨{ indexedSlotPartitionData := DFib
            , branchAtomData := DBr
            , branchAtom_sourcePartition_eq_indexedSlotPartition := ?_
            , branchAtom_profileOfCanonicalWindow_eq_indexedSlotPartition := ?_ }⟩
    · simpa [DFib, DBr] using (hPartEq M n hn hn2 htb hns)
    · intro w hw
      simpa [DFib, DBr] using (hProfEq M n hn hn2 htb hns w hw)
  exact
    P_ne_NP_canonical_routeB_shiftedLeibnizProductIndexedFiberBranchRowShift_conditional hCoherent

#print axioms P_ne_NP_canonical_routeB_shiftedLeibnizProductIndexedFiberPlusBranchPaired_conditional

/-- Canonical Route-B closure from the two *separated* paper-faithful bottom
pieces: exact interface-slot factorization plus row-specific selected-shift
membership supplied by coherent branch-atom data.

This is deliberately weaker and more paper-faithful than the profile-uniform
operator-closure seam: it closes only the selected shifted slot products that
actually occur in the bounded Leibniz expansion. -/
theorem P_ne_NP_canonical_routeB_bottomSeam_rowSpecific_from_exactSlot_and_branchAtom_conditional
    (hExact : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData)
    (hBranch : Step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DSlot := Classical.choice (hExact M n _hn hn2 htb hns)
        let DBr := Classical.choice (hBranch M n _hn hn2 htb hns)
        DBr.sourcePartition = DSlot.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DSlot := Classical.choice (hExact M n _hn hn2 htb hns)
        let DBr := Classical.choice (hBranch M n _hn hn2 htb hns)
        ∀ w hw, DBr.profileOfCanonicalWindow w hw = DSlot.profileOfCanonicalWindow w hw) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_shiftedLeibnizProductRowShift_conditional
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_slotProductBranchAtomData
      (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_exactSlotData_and_branchAtomData
        hExact hBranch hPartEq hProfEq))

#print axioms P_ne_NP_canonical_routeB_bottomSeam_rowSpecific_from_exactSlot_and_branchAtom_conditional

/-- Canonical Route-B closure from the fully lower paper-local pair: a
factor-fiber partition constructs the exact interface slots, and coherent
branch-atom data supplies selected-shift membership on those exact slot
products. -/
theorem P_ne_NP_canonical_routeB_bottomSeam_rowSpecific_from_fiberPartition_and_branchAtom_conditional
    (hFib : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData)
    (hBranch : Step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DBr := Classical.choice (hBranch M n _hn hn2 htb hns)
        DBr.sourcePartition = DFib.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DBr := Classical.choice (hBranch M n _hn hn2 htb hns)
        ∀ w hw, DBr.profileOfCanonicalWindow w hw = DFib.profileOfCanonicalWindow w hw) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_shiftedLeibnizProductRowShift_conditional
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_slotProductBranchAtomData
      (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_fiberPartitionData_and_branchAtomData
        hFib hBranch hPartEq hProfEq))

#print axioms P_ne_NP_canonical_routeB_bottomSeam_rowSpecific_from_fiberPartition_and_branchAtom_conditional

/-- Canonical Route-B closure from factor-fiber slots plus local-algebra
selected-shift data.  The branch-atom membership required by the row-specific
slot seam is derived internally from the local-algebra payload via the checked
shifted-Leibniz/product-to-branch-atom bridge. -/
theorem P_ne_NP_canonical_routeB_bottomSeam_rowSpecific_from_fiberPartition_and_localAlgebra_conditional
    (hFib : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData)
    (hLocal : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        DLoc.sourcePartition = DFib.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        ∀ w hw, DLoc.profileOfCanonicalWindow w hw = DFib.profileOfCanonicalWindow w hw) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_shiftedLeibnizProductRowShift_conditional
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_slotProductBranchAtomData
      (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_fiberPartitionData_and_localAlgebraData
        hFib hLocal hPartEq hProfEq))

#print axioms P_ne_NP_canonical_routeB_bottomSeam_rowSpecific_from_fiberPartition_and_localAlgebra_conditional

/-- Canonical Route-B closure from factor-fiber slots plus local-algebra
selected-shift data, routed through the **primary** paper-faithful bottom seam.

This is the paired exact-slot + selected-shift-closure version of the
row-specific theorem above: the exact slots come from the factor-fiber
partition, and the selected-shift closure is transported from the coherent
local-algebra payload. -/
theorem P_ne_NP_canonical_routeB_bottomSeam_primary_from_fiberPartition_and_localAlgebra_conditional
    (hFib : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData)
    (hLocal : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        DLoc.sourcePartition = DFib.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        ∀ w hw, DLoc.profileOfCanonicalWindow w hw = DFib.profileOfCanonicalWindow w hw) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_shiftedLeibnizProductInterfaceSlotFactorization_of_exactSlotWithSelectedShiftClosure_conditional
    (step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData_of_fiberPartitionData_and_localAlgebraData
      hFib hLocal hPartEq hProfEq)

#print axioms P_ne_NP_canonical_routeB_bottomSeam_primary_from_fiberPartition_and_localAlgebra_conditional

/-- Canonical paper-faithful **primary** bottom-seam closure for Route B.

Primary seam is the paired exact-slot + selected-shift-closure witnessed
surface (closest paper-faithful decomposition, without the stronger global
profile-agnostic closure requirement).
From this seam alone, `PeqNP_Paper` is contradictory. -/
theorem P_ne_NP_canonical_routeB_bottomSeam_primary_paperFaithful_conditional
    (hPair :
      Step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_shiftedLeibnizProductInterfaceSlotFactorization_of_exactSlotWithSelectedShiftClosure_conditional hPair

#print axioms P_ne_NP_canonical_routeB_bottomSeam_primary_paperFaithful_conditional

/-- Canonical primary bottom-seam closure from separated exact-slot existence
and selected-shift closure.  This is the final-existence-theorem shape: the
proof may now construct exact slots and the shift-closure rule independently,
then pair them constructively before closing `PeqNP_Paper`. -/
theorem P_ne_NP_canonical_routeB_bottomSeam_primary_from_exactSlot_and_selectedShiftClosure_conditional
    (hExact : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData)
    (hClosure : Step247UniformRouteBPaperFaithfulTPhiSelectedShiftClosureOnExactInterfaceSlotFactorizationData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_bottomSeam_primary_paperFaithful_conditional
    (step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData_of_exactInterfaceSlotFactorizationData_and_selectedShiftClosure
      hExact hClosure)

#print axioms P_ne_NP_canonical_routeB_bottomSeam_primary_from_exactSlot_and_selectedShiftClosure_conditional

/-- Canonical bottom-seam closure bundle for Route B.

If **any** one of these paper-faithful bottom seams is available, then
`PeqNP_Paper` is contradictory:
1) primary paired exact-slot + selected-shift-closure seam,
2) indexed-fiber + branch-atom paired seam (with compatibility),
3) indexed-fiber + local-algebra paired seam (with compatibility).

This theorem is a citation-friendly aggregator over the direct canonical
closures already proved above. -/
theorem P_ne_NP_canonical_routeB_bottomSeams_bundle_conditional
    (hUniform :
      Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData
      ∨
      Step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData
      ∨
      (∃ hFib : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData,
        ∃ hBranch : Step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData,
        (∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
          (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
          let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
          let DBr := Classical.choice (hBranch M n _hn hn2 htb hns)
          DBr.sourcePartition = DFib.sourcePartition) ∧
        (∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
          (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
          let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
          let DBr := Classical.choice (hBranch M n _hn hn2 htb hns)
          ∀ w hw, DBr.profileOfCanonicalWindow w hw = DFib.profileOfCanonicalWindow w hw))
      ∨
      (∃ hFib : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData,
        ∃ hLocal : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData,
        (∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
          (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
          let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
          let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
          DLoc.sourcePartition = DFib.sourcePartition) ∧
        (∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
          (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
          let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
          let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
          ∀ w hw, DLoc.profileOfCanonicalWindow w hw = DFib.profileOfCanonicalWindow w hw))) :
    ∀ (_ : PeqNP_Paper), False := by
  rcases hUniform with hProf | hRest
  · exact P_ne_NP_canonical_routeB_profileTemplateSpan_conditional hProf
  · rcases hRest with hShift | hRest
    · exact P_ne_NP_canonical_routeB_shiftedLeibnizProductInterfaceSlotFactorization_of_exactSlotWithSelectedShiftClosure_conditional hShift
    · rcases hRest with hBranchPair | hLocalPair
      · rcases hBranchPair with ⟨hFib, hBranch, hPartEq, hProfEq⟩
        exact
          P_ne_NP_canonical_routeB_shiftedLeibnizProductIndexedFiberPlusBranchPaired_conditional
            hFib hBranch hPartEq hProfEq
      · rcases hLocalPair with ⟨hFib, hLocal, hPartEq, hProfEq⟩
        exact
          P_ne_NP_canonical_routeB_bottomSeam_primary_from_fiberPartition_and_localAlgebra_conditional
            hFib hLocal hPartEq hProfEq

#print axioms P_ne_NP_canonical_routeB_bottomSeams_bundle_conditional

end PallLean.Paper93.DeepMath.PathB
