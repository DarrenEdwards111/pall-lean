import GodMoveMachineDiscoveryPrecision

/-!
# The logical scope of the revised SAT-machine discovery

The revised selector is conditional on a supplied globally correct SAT
machine. Composing it with the earlier sampled SAT program reproduces that
machine's language. It does not eliminate the SAT computation assumption.

The verified discovery guarantees add no restriction to the hypothesis that
SAT has a polynomial-clock decider: every such hypothetical decider already
satisfies them. The package below deliberately contains no assertion about
the full runtime of the host discovery program.

The final theorem states the still-missing lower-bound premise on exactly
the machine-dependent wire rank. It proves only a conditional implication.
-/

namespace GodMoveDiscoveryQuantifierAudit

open GodMoveBooleanInterpolation GodMoveSamplingBarrier GodMoveComputedWireRank
open GodMoveMachineDiscovery GodMoveMachineDiscoveryPrecision GodMoveSampledSAT
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine (Machine Decides decideOut)
open PvsNPSeparatingInvariant (PolyBounded)

def revisedSelector (M : Machine) (T : ℕ → ℕ) : SampleSelector :=
  fun _ c => machineSamples M T c

theorem revisedSelector_separates (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) (n : ℕ) (c : List (CGate n)) :
    SeparatesWires c (revisedSelector M T n c) := machineSamples_separates M T hD c

/-- The earlier selector-to-SAT reduction still applies to the new selector.
Its correctness is inherited from the supplied SAT decider. -/
theorem revised_sampledSATWord_correct (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) (x : List Bool) :
    sampledSATWord (revisedSelector M T) x = SeparationTarget.SATLang x :=
  sampledSATWord_eq_SATLang (revisedSelector M T) (revisedSelector_separates M T hD) x

/-- This semantic round trip returns the original SAT machine's answer;
neither the machine nor its correctness has been constructed by the selector. -/
theorem revised_sampledSATWord_eq_original (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) (x : List Bool) :
    sampledSATWord (revisedSelector M T) x = decideOut M x (T x.length) :=
  (revised_sampledSATWord_correct M T hD x).trans (hD x).2.symm

/-- Precisely selected proved guarantees: separation, exact basis size,
direct-query count, and coefficient precision along the executed branch.
This is not a full implementation-runtime specification. -/
def DiscoveryGuarantees (M : Machine) (T : ℕ → ℕ) : Prop :=
  (∀ n (c : List (CGate n)), SeparatesWires c (machineSamples M T c)) ∧
  (∀ n (c : List (CGate n)), (machineBasisIndices M T c).length = wireRank c) ∧
  (∀ n (c : List (CGate n)),
    (machineSearch M T c).queries ≤ (c.length + 1) * (c.length * (n + 1))) ∧
  (∀ n (c : List (CGate n)),
    DiscoveryPrecision M T c (c.length + 1) (GodMoveRationalRowBasis.empty c.length))

theorem discoveryGuarantees_of_decides (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) : DiscoveryGuarantees M T :=
  ⟨fun _ c => machineSamples_separates M T hD c,
   fun _ c => machineBasis_length_eq_wireRank M T hD c,
   fun _ c => machineSearch_queries_le M T c,
   fun _ c => machineSearch_precision M T c⟩

/-- A hypothetical polynomial-clock SAT decider equipped with the revised
proved guarantees. No efficient independent selector is postulated here. -/
def RevisedPolynomialCandidate : Prop :=
  ∃ (M : Machine) (T : ℕ → ℕ),
    PolyBounded T ∧ Decides M SeparationTarget.SATLang T ∧ DiscoveryGuarantees M T

/-- Adding the revised guarantees does not strengthen the hypothetical
membership of SAT in P: those guarantees follow for every correct decider. -/
theorem revisedPolynomialCandidate_iff_SAT_in_P :
    RevisedPolynomialCandidate ↔ SeparationTarget.InP SeparationTarget.SATLang := by
  constructor
  · rintro ⟨M, T, hT, hD, _⟩
    exact ⟨M, T, hT, hD⟩
  · rintro ⟨M, T, hT, hD⟩
    exact ⟨M, T, hT, hD, discoveryGuarantees_of_decides M T hD⟩

theorem separation_iff_no_revisedPolynomialCandidate :
    SeparationTarget.SAT_not_in_P ↔ ¬ RevisedPolynomialCandidate :=
  not_congr revisedPolynomialCandidate_iff_SAT_in_P.symm

noncomputable def actualWireRank (M : Machine) (T : ℕ → ℕ) (L : ℕ) : ℕ :=
  wireRank (ComposablePpolyDischarge.circuitFor M L (T L))

/-- Exact discovery does not amplify the invariant. Polynomial boundedness
of the returned basis sizes is equivalent to that of the original wire rank. -/
theorem discoveredBasis_polyBounded_iff (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) :
    PolyBounded (fun L =>
      (machineBasisIndices M T (ComposablePpolyDischarge.circuitFor M L (T L))).length) ↔
      PolyBounded (actualWireRank M T) := by
  unfold actualWireRank
  simp only [machineBasis_length_eq_wireRank M T hD]

theorem discoveredBasis_polyBounded (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SeparationTarget.SATLang T) (hT : PolyBounded T) :
    PolyBounded (fun L =>
      (machineBasisIndices M T (ComposablePpolyDischarge.circuitFor M L (T L))).length) :=
  (discoveredBasis_polyBounded_iff M T hD).mpr (unrolled_wireRank_polynomial M hT)

/-- The precise additional universal hardness obligation. This declaration
defines a proposition; it does not assert that the proposition is true. -/
def UnavoidableWireLower : Prop :=
  ∀ (M : Machine) (T : ℕ → ℕ),
    Decides M SeparationTarget.SATLang T → ¬ PolyBounded (actualWireRank M T)

/-- The revised construction can be used under a hypothetical SAT decider,
but a contradiction still requires this separate unproved lower bound. -/
theorem separation_of_unavoidableWireLower (hLower : UnavoidableWireLower) :
    SeparationTarget.SAT_not_in_P := by
  rintro ⟨M, T, hT, hD⟩
  exact hLower M T hD (unrolled_wireRank_polynomial M hT)

end GodMoveDiscoveryQuantifierAudit

#print axioms GodMoveDiscoveryQuantifierAudit.revisedSelector_separates
#print axioms GodMoveDiscoveryQuantifierAudit.revised_sampledSATWord_correct
#print axioms GodMoveDiscoveryQuantifierAudit.revised_sampledSATWord_eq_original
#print axioms GodMoveDiscoveryQuantifierAudit.discoveryGuarantees_of_decides
#print axioms GodMoveDiscoveryQuantifierAudit.revisedPolynomialCandidate_iff_SAT_in_P
#print axioms GodMoveDiscoveryQuantifierAudit.separation_iff_no_revisedPolynomialCandidate
#print axioms GodMoveDiscoveryQuantifierAudit.discoveredBasis_polyBounded_iff
#print axioms GodMoveDiscoveryQuantifierAudit.discoveredBasis_polyBounded
#print axioms GodMoveDiscoveryQuantifierAudit.separation_of_unavoidableWireLower
