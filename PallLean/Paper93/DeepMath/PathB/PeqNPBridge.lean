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

end PallLean.Paper93.DeepMath.PathB
