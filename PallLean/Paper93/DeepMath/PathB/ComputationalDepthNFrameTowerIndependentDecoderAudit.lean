import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerKleeneQuotationAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerEffectiveDiagonalCompilerAudit

/-!
# N-Frame tower: independent compact-decoder audit

Kleene's second recursion theorem supplies compact behavioral self-names, but
the previous audit left the name-to-CNF decoder unconstrained.  Here we impose
the operational conditions suggested by the surviving route:

* one decoder, shared by every certified polynomial SAT machine;
* one fixed compiler program on an independently supplied compiler surface;
* polynomial time to emit the decoded CNF;
* a polynomial bound on the emitted CNF's concrete `CNF.size`;
* a genuine Kleene fixed-point name for every machine.

These conditions can all hold without diagonalizing against anything: a
constant decoder emitting `noCNF` is a concrete example.  The additional claim
that the decoded formula satisfies the SAT liar biconditional is exactly the
claim that the compiler emits a finite counterexample for every polynomial
machine.  Erasing the quotation and size data gives the earlier
`EffectiveCodeDiagonalizer`, and hence immediately gives `SAT ∉ P`.

Thus computability, compact naming, and polynomial output size do not derive
the missing semantics.  The load-bearing theorem remains the construction law
linking SAT truth of the decoded finite formula to rejection by the solver.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerIndependentDecoderAudit

open SATDepthMachine
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit
open PallLean.Paper93.DeepMath.PathB.NFrameTowerKleeneQuotationAudit

/-! ## A fixed operational compact decoder, before liar semantics -/

/-- Operational compact quotation with one fixed name-to-CNF decoder.

This structure deliberately contains no SAT correctness or diagonal failure
field.  It records only self-naming, effective emission, and polynomial
resource bounds. -/
structure PolynomialQuotedCNFDecoder
    (U : MachineModel) (V : CounterexampleCompilerModel) where
  compilerCode : Nat
  timeBudget : Nat → Nat
  timePolynomial : IsPolynomialBudget timeBudget
  compiler_steps : ∀ solverCode,
    V.compileSteps compilerCode solverCode ≤ timeBudget solverCode
  sizeBudget : Nat → Nat
  sizePolynomial : IsPolynomialBudget sizeBudget
  quote : DecisionMachine U → BehavioralFixedPointSkeleton
  decode : Code → CNF
  compiler_emits : ∀ M : DecisionMachine U,
    V.compileRun compilerCode M.code = some (decode (quote M).name)
  decoded_size : ∀ M : DecisionMachine U,
    (decode (quote M).name).size ≤ sizeBudget M.code

/-- The finite CNF emitted for a certified machine. -/
def PolynomialQuotedCNFDecoder.output
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (Q : PolynomialQuotedCNFDecoder U V) (M : DecisionMachine U) : CNF :=
  Q.decode (Q.quote M).name

/-- The missing construction theorem: every decoded fixed-point formula obeys
the SAT liar law against the machine whose code was supplied. -/
def ConstructionDerivedLiarLaw
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (Q : PolynomialQuotedCNFDecoder U V) : Prop :=
  ∀ M : DecisionMachine U, LiarOn U M.code (Q.output M)

/-- The same law stated without liar terminology: every emitted formula is a
genuine finite misclassification. -/
def DecoderDefeatsEveryMachine
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (Q : PolynomialQuotedCNFDecoder U V) : Prop :=
  ∀ M : DecisionMachine U, ¬ CorrectOn U M.code (Q.output M)

/-- **Semantic calibration.**  Construction-derived liar semantics is exactly
pointwise finite solver failure.  None of the quotation, runtime, or output
size fields enters this equivalence. -/
theorem constructionDerivedLiarLaw_iff_defeatsEveryMachine
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (Q : PolynomialQuotedCNFDecoder U V) :
    ConstructionDerivedLiarLaw Q ↔ DecoderDefeatsEveryMachine Q := by
  constructor
  · intro h M
    exact (liarOn_iff_not_correctOn U M.code (Q.output M)).mp (h M)
  · intro h M
    exact (liarOn_iff_not_correctOn U M.code (Q.output M)).mpr (h M)

/-! ## Erasure to the effective diagonal compiler -/

/-- Once liar semantics is supplied, compact quotation erases directly to the
previous effective code diagonalizer. -/
def effectiveCodeDiagonalizerOfQuotedDecoder
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (Q : PolynomialQuotedCNFDecoder U V)
    (hLiar : ConstructionDerivedLiarLaw Q) :
    EffectiveCodeDiagonalizer U V where
  code := Q.compilerCode
  budget := Q.timeBudget
  polyBudget := Q.timePolynomial
  steps_le_budget := Q.compiler_steps
  halts_with_counterexample := by
    intro M
    exact ⟨Q.output M, Q.compiler_emits M,
      (liarOn_iff_not_correctOn U M.code (Q.output M)).mp (hLiar M)⟩

/-- Therefore an independently operational, polynomial-size compact decoder
with the desired semantic construction theorem already proves the full SAT
decision lower bound. -/
theorem no_SATDecisionInP_of_quotedDecoderLiarLaw
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (Q : PolynomialQuotedCNFDecoder U V)
    (hLiar : ConstructionDerivedLiarLaw Q) :
    ¬ SATDecisionInP U :=
  no_SATDecisionInP_of_effectiveCodeDiagonalizer
    (effectiveCodeDiagonalizerOfQuotedDecoder Q hLiar)

/-- If a correct polynomial SAT decider exists, no operational compact decoder
can satisfy the liar construction law, regardless of its time and size
certificates. -/
theorem no_constructionDerivedLiarLaw_of_SATDecisionInP
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (hP : SATDecisionInP U) (Q : PolynomialQuotedCNFDecoder U V) :
    ¬ ConstructionDerivedLiarLaw Q := by
  intro hLiar
  exact no_SATDecisionInP_of_quotedDecoderLiarLaw Q hLiar hP

/-! ## The operational and quotation fields alone are harmless -/

/-- A fixed surface that emits the concrete unsatisfiable `noCNF` in one step,
independently of the supplied solver code. -/
def constantNoCNFCompilerModel : CounterexampleCompilerModel where
  compileRun := fun _ _ => some noCNF
  compileSteps := fun _ _ => 1

/-- Compact naming, a shared decoder, constant runtime, and constant output
size are simultaneously realizable for every SAT machine model.  What this
example lacks is precisely the liar construction law. -/
noncomputable def constantNoCNFQuotedDecoder
    (U : MachineModel) :
    PolynomialQuotedCNFDecoder U constantNoCNFCompilerModel where
  compilerCode := 0
  timeBudget := fun _ => 1
  timePolynomial := by
    refine ⟨0, 1, ?_⟩
    intro n
    simp
  compiler_steps := by
    intro solverCode
    rfl
  sizeBudget := fun _ => noCNF.size
  sizePolynomial := by
    refine ⟨0, noCNF.size, ?_⟩
    intro n
    simp
  quote := fun _ => canonicalBehavioralFixedPointSkeleton
  decode := fun _ => noCNF
  compiler_emits := by
    intro M
    rfl
  decoded_size := by
    intro M
    rfl

/-- Consequently, the non-semantic operational surface is inhabited
unconditionally. -/
theorem exists_polynomialQuotedCNFDecoder (U : MachineModel) :
    Nonempty (PolynomialQuotedCNFDecoder U constantNoCNFCompilerModel) :=
  ⟨constantNoCNFQuotedDecoder U⟩

end PallLean.Paper93.DeepMath.PathB.NFrameTowerIndependentDecoderAudit

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerIndependentDecoderAudit.constructionDerivedLiarLaw_iff_defeatsEveryMachine
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerIndependentDecoderAudit.effectiveCodeDiagonalizerOfQuotedDecoder
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerIndependentDecoderAudit.no_SATDecisionInP_of_quotedDecoderLiarLaw
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerIndependentDecoderAudit.no_constructionDerivedLiarLaw_of_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerIndependentDecoderAudit.exists_polynomialQuotedCNFDecoder
