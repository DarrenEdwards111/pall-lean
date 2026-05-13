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

end PallLean.Paper93.DeepMath.PathB
