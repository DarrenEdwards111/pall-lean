import PallLean.PaperFaithfulSeparation
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRealFrontier
import PallLean.Paper93.DeepMath.PathB.RouteBPlacedQuotientDescentKR

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

/-- Canonical conditional closure via the explicit placed-quotient/descent Route B
surface. -/
theorem P_ne_NP_canonical_routeB_placedQuotientDescent_conditional
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescent
      hData)

#print axioms P_ne_NP_canonical_routeB_placedQuotientDescent_conditional

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
  P_ne_NP_canonical_routeB_interfaceSlotExpansion_conditional
    (step247UniformRouteBPaperFaithfulTPhiInterfaceSlotExpansionData_of_compiledBasisProfileSubspaceRowData
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

/-- Canonical Route-B closure from uniform-shift-closure slot-product data,
by instantiating interface-slot factorization first. -/
theorem P_ne_NP_canonical_routeB_shiftedLeibnizProductUniformShiftClosure_conditional
    (hUniform : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductUniformShiftClosureData) :
    ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_canonical_routeB_shiftedLeibnizProductInterfaceSlotFactorization_conditional
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData_of_slotProductUniformShiftClosureData
      hUniform)

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

/-- Canonical bottom-seam closure bundle for Route B.

If **any** one of these paper-faithful bottom seams is available, then
`PeqNP_Paper` is contradictory:
1) uniform-shift-closure slot-product seam,
2) indexed-fiber + branch-atom paired seam (with compatibility).

This theorem is a citation-friendly aggregator over the direct canonical
closures already proved above. -/
theorem P_ne_NP_canonical_routeB_bottomSeams_bundle_conditional
    (hUniform :
      Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductUniformShiftClosureData
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
          ∀ w hw, DBr.profileOfCanonicalWindow w hw = DFib.profileOfCanonicalWindow w hw))) :
    ∀ (_ : PeqNP_Paper), False := by
  rcases hUniform with hShift | hPair
  · exact P_ne_NP_canonical_routeB_shiftedLeibnizProductUniformShiftClosure_conditional hShift
  · rcases hPair with ⟨hFib, hBranch, hPartEq, hProfEq⟩
    exact
      P_ne_NP_canonical_routeB_shiftedLeibnizProductIndexedFiberPlusBranchPaired_conditional
        hFib hBranch hPartEq hProfEq

#print axioms P_ne_NP_canonical_routeB_bottomSeams_bundle_conditional

end PallLean.Paper93.DeepMath.PathB
