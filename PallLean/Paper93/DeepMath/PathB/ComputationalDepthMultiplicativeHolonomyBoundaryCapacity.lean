import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRouteGSelfReductionBoundaryAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicHolonomyQueryTranscriptBridge

/-!
# Multiplicative dynamic holonomy: corrected observer-boundary capacity

Counting all boundary states confuses two different units.  A boundary exposing `g`
independent Boolean directions has only `g` generators but supports up to `2^g`
multiplicative signatures.  This file defines that operational generator model on
actual runs and proves the exact capacity law.

The calibration is deliberately strict:

* zero exposed generators give one class even if the physical state retains the input;
* one decision generator gives at most two classes, including full-AND;
* ignored labels do not change the signature family;
* decoding all `m`-bit residual labels forces only `m ≤ g`, not `2^m ≤ g`;
* `m` exposed bits already realize all `2^m` patterns.

Thus multiplicative holonomy fixes the raw-state false positive, but state-count
growth alone does not separate P from NP.  A full Route G proof now needs a theorem
that hard SAT forces superpolynomially many *independent observer generators* while
P exposes only polynomially many.  That is a genuine algebraic/circuit lower bound,
not a consequence of polynomial runtime.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiplicativeHolonomyBoundaryCapacity

open SATDepthMachine
open PvsNPRunIndexedFaithfulTPhi
open PvsNPRunIndexedFaithfulTPhi.ActualDecisionRun
open PvsNPObserverSwitchToy
open PvsNPTranscriptObserver
open BranchSpanningDynamicHolonomy
open PvsNPDynamicHolonomyDecisionRelevance
open PvsNPDynamicHolonomyQueryTranscriptBridge

variable {Input State : Type*}

/-- A bank of `g` Boolean directions exposed from the actual state at one dynamic
time.  Only these observer-visible generators contribute to multiplicative rank. -/
structure DynamicGeneratorBank
    (R : ActualDecisionRun Input State) (g : ℕ) where
  generator : Fin g → State → Bool

namespace DynamicGeneratorBank

/-- Observer-visible multiplicative signature of one input at one actual run time. -/
def signature {R : ActualDecisionRun Input State} {g : ℕ}
    (B : DynamicGeneratorBank R g) (time : ℕ) (x : Input) : Fin g → Bool :=
  fun i => B.generator i (R.stateAt time x)

/-- Number of multiplicative signature classes realized across a finite input family. -/
noncomputable def classRank [Fintype Input]
    {R : ActualDecisionRun Input State} {g : ℕ}
    (B : DynamicGeneratorBank R g) (time : ℕ) : ℕ :=
  familyImageRank (B.signature time)

/-- Exact universal capacity: `g` exposed Boolean directions support at most `2^g`
signature classes. -/
theorem classRank_le_two_pow [Fintype Input]
    {R : ActualDecisionRun Input State} {g : ℕ}
    (B : DynamicGeneratorBank R g) (time : ℕ) :
    B.classRank time ≤ 2 ^ g := by
  simpa [classRank, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
    familyImageRank_le_card (B.signature time)

/-- With no exposed generators, every input has the unique empty signature and the
class rank is one.  The physical state may still contain arbitrary hidden input data. -/
theorem zeroGenerator_classRank_eq_one [Fintype Input] [Nonempty Input]
    {R : ActualDecisionRun Input State}
    (B : DynamicGeneratorBank R 0) (time : ℕ) :
    B.classRank time = 1 := by
  have hle : B.classRank time ≤ 1 := by
    simpa using B.classRank_le_two_pow time
  have hpos : 0 < B.classRank time := by
    classical
    unfold classRank familyImageRank
    simp
  omega

/-- Ignored auxiliary labels remain invisible to every generator bank lifted from
the base run. -/
def liftIgnored
    {Base Label : Type*} (R : ActualDecisionRun Base State) (g : ℕ)
    (B : DynamicGeneratorBank R g) :
    DynamicGeneratorBank (labelIgnoredRun R Label) g where
  generator := B.generator

theorem liftIgnored_classRank
    {Base Label : Type*} [Fintype Base] [Fintype Label] [Nonempty Label]
    (R : ActualDecisionRun Base State) {g : ℕ}
    (B : DynamicGeneratorBank R g) (time : ℕ) :
    (liftIgnored (Label := Label) R g B).classRank time = B.classRank time := by
  change familyImageRank
      (fun x : Base × Label => B.signature time x.1) =
    familyImageRank (B.signature time)
  exact familyImageRank_prod_ignored _

/-- A single bank generator equal to the final decision exposes at most two classes. -/
def finalDecisionBank (R : ActualDecisionRun Input State) :
    DynamicGeneratorBank R 1 where
  generator := fun _ state => R.observe state

theorem finalDecisionBank_classRank_le_two [Fintype Input]
    (R : ActualDecisionRun Input State) :
    (finalDecisionBank R).classRank R.steps ≤ 2 := by
  exact (finalDecisionBank R).classRank_le_two_pow R.steps

/-- Operational full-AND calibration: one decision generator stays two-class even
though the hidden raw state family has `2^m` members. -/
theorem zeroClockFullAnd_decisionBank_rank_le_two (m : ℕ) :
    (finalDecisionBank
      (RouteGSelfReductionBoundaryAudit.zeroClockFullAndRun m)).classRank 0 ≤ 2 := by
  simpa using finalDecisionBank_classRank_le_two
    (RouteGSelfReductionBoundaryAudit.zeroClockFullAndRun m)

/-! ## Hard-label decoding and the corrected lower-bound unit -/

/-- If an observer-visible signature decodes an injective `m`-bit residual label,
the signature map is injective. -/
theorem signature_injective_of_decodes_labels
    {m g : ℕ}
    (R : ActualDecisionRun (Assignment m) State)
    (B : DynamicGeneratorBank R g) (time : ℕ)
    (label : Assignment m → Assignment m)
    (hlabel : Function.Injective label)
    (decode : (Fin g → Bool) → Assignment m)
    (hdecode : ∀ a, decode (B.signature time a) = label a) :
    Function.Injective (B.signature time) := by
  intro a b hab
  apply hlabel
  rw [← hdecode a, ← hdecode b, hab]

/-- Hence the multiplicative class count is exactly `2^m`. -/
theorem classRank_eq_two_pow_of_decodes_labels
    {m g : ℕ}
    (R : ActualDecisionRun (Assignment m) State)
    (B : DynamicGeneratorBank R g) (time : ℕ)
    (label : Assignment m → Assignment m)
    (hlabel : Function.Injective label)
    (decode : (Fin g → Bool) → Assignment m)
    (hdecode : ∀ a, decode (B.signature time a) = label a) :
    B.classRank time = 2 ^ m := by
  rw [classRank, familyImageRank_eq_card_of_injective _
    (signature_injective_of_decodes_labels R B time label hlabel decode hdecode)]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- Corrected dimension lower bound: decoding `m` independent bits forces at least
`m` Boolean generators.  It does *not* force `2^m` generators. -/
theorem label_decoding_forces_m_le_generators
    {m g : ℕ}
    (R : ActualDecisionRun (Assignment m) State)
    (B : DynamicGeneratorBank R g) (time : ℕ)
    (label : Assignment m → Assignment m)
    (hlabel : Function.Injective label)
    (decode : (Fin g → Bool) → Assignment m)
    (hdecode : ∀ a, decode (B.signature time a) = label a) :
    m ≤ g := by
  have hclasses : 2 ^ m = B.classRank time :=
    (classRank_eq_two_pow_of_decodes_labels
      R B time label hlabel decode hdecode).symm
  have hcap := B.classRank_le_two_pow time
  have hpowers : 2 ^ m ≤ 2 ^ g := by simpa [hclasses] using hcap
  exact (Nat.pow_le_pow_iff_right (by omega)).mp hpowers

/-! ## Tightness: `m` generators already realize all `2^m` classes -/

/-- The input-coordinate generator bank on the zero-clock run. -/
def coordinateBank (m : ℕ) : DynamicGeneratorBank
    (RouteGSelfReductionBoundaryAudit.zeroClockFullAndRun m) m where
  generator := fun i state => state i

@[simp] theorem coordinateBank_signature (m : ℕ) (a : Assignment m) :
    (coordinateBank m).signature 0 a = a := by
  rfl

theorem coordinateBank_classRank_eq_two_pow (m : ℕ) :
    (coordinateBank m).classRank 0 = 2 ^ m := by
  change familyImageRank (fun a : Assignment m => a) = 2 ^ m
  exact rawInput_rank_eq_two_pow m

/-- The generator lower bound is tight: exactly `m` observer bits decode every
`m`-bit label, even in a zero-clock easy computation. -/
theorem coordinateBank_decodes_identity (m : ℕ) :
    ∀ a : Assignment m, id ((coordinateBank m).signature 0 a) = a := by
  intro a
  rfl

/-! ## Concrete independent SAT-query calibration -/

/-- The concrete independent-query answer carrier is an `n`-bit boundary. -/
theorem independentSAT_answerBoundary_card (n : ℕ) :
    Fintype.card (HolonomySignature n) = 2 ^ n := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- A SAT-correct decider returns the decision-relevant `n`-bit holonomy label in
exactly `n` Boolean coordinates.  This is compatible with the corrected capacity
law: `n` generators support `2^n` answer patterns. -/
theorem independentSAT_answers_use_n_generators
    {n : ℕ} {U : MachineModel}
    (D : DecisionMachine U) (hD : DecidesSAT U D)
    (batch : (independentSATQueryFamily n).Instance) :
    (independentSATQueryFamily n).answers D batch =
      (independentSATQueryFamily n).label batch :=
  (independentSATQueryFamily n).answers_eq_label D hD batch

/-!
## Audit verdict

Multiplicative dynamic holonomy is the right way to avoid charging hidden raw state:
only exposed generators count.  But the corrected capacity law changes the desired
lower bound.  `2^m` observable patterns require only `m` Boolean generators, and an
ordinary polynomial-time machine can expose polynomially many bits.

Therefore a full P-vs-NP route needs a superpolynomial lower bound on the number of
independent *decision-relevant algebraic generators* for a concrete NP-complete
family, together with a polynomial upper bound for every P machine.  Establishing
that pair is essentially a general circuit lower bound and is not supplied by the
present observer or self-reduction machinery.
-/

end DynamicGeneratorBank

end PallLean.Paper93.DeepMath.PathB.MultiplicativeHolonomyBoundaryCapacity

#print axioms PallLean.Paper93.DeepMath.PathB.MultiplicativeHolonomyBoundaryCapacity.DynamicGeneratorBank.zeroGenerator_classRank_eq_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiplicativeHolonomyBoundaryCapacity.DynamicGeneratorBank.label_decoding_forces_m_le_generators
#print axioms PallLean.Paper93.DeepMath.PathB.MultiplicativeHolonomyBoundaryCapacity.DynamicGeneratorBank.coordinateBank_classRank_eq_two_pow
