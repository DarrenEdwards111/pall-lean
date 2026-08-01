import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDynamicObserverBoundaryLink
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPForcedAssignmentFamily
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPTseitinExpanderRHAExtraction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPHardResidualFamily

/-!
# Route G audit: self-reduction output versus dynamic boundary rank

This file performs the first attempted instantiation of the dynamic P/NP boundary
link and records two obstructions that must be fixed before it can be a P-vs-NP
proof.

1. The current `HardSATResidualFamily` and `TseitinExpanderResidualFamily`
   annotations contain arbitrary proposition payloads.  They can therefore package
   the repository's explicitly easy forced-assignment family.  They are interfaces,
   not yet concrete hardness certificates.
2. Polynomial (even zero) runtime does not bound the number of states realized
   across a family of runs.  A zero-step machine can retain its input and expose
   `2^m` distinct states while its final decision exposes at most two.

Finally, a generic theorem shows what SAT self-reduction can and cannot do.  If a
search output really decodes every injective residual label, then the output family
itself is injective and already has image rank `2^m`.  Decision-to-search correctness
does not compress this family into a polynomial-cardinality carrier.
-/

namespace PallLean.Paper93.DeepMath.PathB.RouteGSelfReductionBoundaryAudit

open SATDepthMachine
open PvsNPRunIndexedFaithfulTPhi
open PvsNPRunIndexedFaithfulTPhi.ActualDecisionRun
open PvsNPObserverSwitchToy
open PvsNPTranscriptObserver
open PvsNPForcedAssignmentFamily
open PvsNPHardResidualFamily
open PvsNPTseitinExpanderRHAExtraction
open BranchSpanningDynamicHolonomy
open PvsNPNFrameDynamicMERAHolonomy

/-! ## The present hardness wrappers are not yet certificates -/

/-- The explicitly easy forced-assignment family satisfies the current abstract
`HardSATResidualFamily` interface by choosing all payload propositions to be `True`.
This proves the interface itself does not certify NP-hardness. -/
def easyForcedFamilyAsHardSATResidualFamily (m : ℕ) : HardSATResidualFamily m where
  fam := forcedAssignmentFamily m
  residual_semantics := True
  residual_semantics_realized := True.intro
  np_complete_payload := True
  np_complete_realized := True.intro
  not_easy_linear_payload := True
  not_easy_linear_realized := True.intro

/-- Likewise, a genuine K4 expander certificate plus an arbitrary `True` payload can
wrap the same easy forced family as a `TseitinExpanderResidualFamily`.  The current
wrapper does not yet prove that its CNFs are Tseitin residuals. -/
def easyForcedFamilyAsTseitinExpanderResidualFamily (m : ℕ) :
    TseitinExpanderResidualFamily m where
  certificate := K4_tseitinExpanderCertificate
  fam := forcedAssignmentFamily m
  residualPayload := True
  residual_realized := True.intro

theorem easy_hardSAT_wrapper_underlying_family (m : ℕ) :
    (easyForcedFamilyAsHardSATResidualFamily m).fam = forcedAssignmentFamily m := rfl

theorem easy_tseitin_wrapper_underlying_family (m : ℕ) :
    (easyForcedFamilyAsTseitinExpanderResidualFamily m).fam =
      forcedAssignmentFamily m := rfl

/-! ## Polynomial time does not bound family-state cardinality -/

/-- A zero-transition actual run that simply retains an `m`-bit input.  Its final
answer is the easy full-AND decision. -/
def zeroClockFullAndRun (m : ℕ) :
    ActualDecisionRun (Assignment m) (Assignment m) where
  encode := id
  step := fun _ state => state
  steps := 0
  observe := fun a => decide (∀ i, a i = true)

theorem zeroClockFullAndRun_steps (m : ℕ) :
    (zeroClockFullAndRun m).steps = 0 := rfl

/-- Despite using zero transitions, the raw-state observer realizes all `2^m`
family states. -/
theorem zeroClock_rawState_rank_eq_two_pow (m : ℕ) :
    branchHolonomyRankAt (zeroClockFullAndRun m) id 0 = 2 ^ m := by
  simpa [branchHolonomyRankAt, zeroClockFullAndRun,
    ActualDecisionRun.stateAt, runFrom] using rawInput_rank_eq_two_pow m

/-- The same zero-clock run's decision-only observer still has rank at most two.
This is the easy-family guardrail in an operational example. -/
theorem zeroClock_finalAnswer_rank_le_two (m : ℕ) :
    familyImageRank (zeroClockFullAndRun m).finalAnswer ≤ 2 :=
  finalAnswer_familyImageRank_le_two (zeroClockFullAndRun m)

/-- For every nonempty input width, raw family-state rank is not bounded by the
machine clock.  Hence a P-side clock bound cannot justify the shared carrier-cardinality
field used by the dynamic boundary link. -/
theorem zeroClock_rawState_rank_not_le_clock (m : ℕ) :
    ¬ branchHolonomyRankAt (zeroClockFullAndRun (m + 1)) id 0 ≤
      (zeroClockFullAndRun (m + 1)).steps := by
  rw [zeroClock_rawState_rank_eq_two_pow, zeroClockFullAndRun_steps]
  have hpos : 0 < 2 ^ (m + 1) := by positivity
  omega

/-! ## What a label-decoding self-reduction would actually imply -/

/-- If one search/transcript output decodes the injective semantic label of every
residual branch, then that output is itself injective on the branch family. -/
theorem searchOutput_injective_of_decodes_labels
    {m : ℕ} {Output : Type*}
    (fam : FoolingResidualFamily m)
    (searchOutput : Assignment m → Output)
    (decode : Output → Assignment m)
    (hdecode : ∀ a, decode (searchOutput a) = fam.label a) :
    Function.Injective searchOutput := by
  intro a b hab
  apply fam.label_injective
  rw [← hdecode a, ← hdecode b, hab]

/-- Consequently a fully label-decoding self-reduction output has exact image rank
`2^m`.  Correct decision-to-search may produce such outputs, but it does not make
their family cardinality polynomial. -/
theorem searchOutput_rank_eq_two_pow_of_decodes_labels
    {m : ℕ} {Output : Type*}
    (fam : FoolingResidualFamily m)
    (searchOutput : Assignment m → Output)
    (decode : Output → Assignment m)
    (hdecode : ∀ a, decode (searchOutput a) = fam.label a) :
    familyImageRank searchOutput = 2 ^ m := by
  rw [familyImageRank_eq_card_of_injective searchOutput
    (searchOutput_injective_of_decodes_labels fam searchOutput decode hdecode)]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- A finite output carrier that decodes all residual labels cannot also have
polynomial cardinality below the exponential gap. -/
theorem no_polynomial_searchOutput_carrier_of_decodes_labels
    {m k : ℕ} {Output : Type*} [Fintype Output]
    (fam : FoolingResidualFamily m)
    (searchOutput : Assignment m → Output)
    (decode : Output → Assignment m)
    (hdecode : ∀ a, decode (searchOutput a) = fam.label a)
    (hpoly : Fintype.card Output ≤ m ^ k)
    (hgap : m ^ k < 2 ^ m) : False := by
  have hinj := searchOutput_injective_of_decodes_labels
    fam searchOutput decode hdecode
  have hexp : 2 ^ m ≤ Fintype.card Output := by
    have hcard := Fintype.card_le_of_injective searchOutput hinj
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using hcard
  omega

/-!
## Audit verdict

Ordinary SAT self-reduction supplies one satisfying assignment using polynomially
many decision queries.  Across a `2^m` residual family, however, exact recovery of
injective labels forces `2^m` distinct outputs.  Thus neither polynomial runtime nor
self-reduction correctness proves the polynomial-cardinality P boundary required by
the current image-counting Route G link.

A viable next invariant must measure observer-accessible algebraic dimension or
multiplicative holonomy without equating it to the number of possible machine states,
and its concrete hard family must replace the `True` hardness payloads above.
-/

end PallLean.Paper93.DeepMath.PathB.RouteGSelfReductionBoundaryAudit

#print axioms PallLean.Paper93.DeepMath.PathB.RouteGSelfReductionBoundaryAudit.zeroClock_rawState_rank_eq_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.RouteGSelfReductionBoundaryAudit.searchOutput_rank_eq_two_pow_of_decodes_labels
#print axioms PallLean.Paper93.DeepMath.PathB.RouteGSelfReductionBoundaryAudit.no_polynomial_searchOutput_carrier_of_decodes_labels
