import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerSyntacticFeedbackCollapse

/-!
# N-Frame tower: compact-quotation route closure

The preceding audits treated every concrete compact-name implementation
separately.  This file closes the branch by putting their surviving semantic
objects on one exact equivalence line.

For a fixed SAT machine model, the following are equivalent:

* a compact SAT liar for every certified polynomial machine;
* a semantic answer-feedback fixed point for every such machine;
* a finite code-indexed counterexample family;
* a Book 1 tower-decorated solver-indexed diagonalizer;
* `SATDecisionInP` is false.

An effective polynomial quoted decoder carrying its construction-derived liar
law maps into this line and therefore proves the lower bound.  Without that
law, the operational quotation infrastructure is inhabited unconditionally by
the constant `noCNF` decoder.

Literal syntactic feedback does not join the equivalence line.  It asks every
candidate machine to misclassify one of the same two trivial formulas.  The
presence of even one certified machine that answers `yesCNF` and `noCNF`
correctly rules out a uniform syntactic family, independently of how that
machine behaves on general SAT.

This is a closure theorem for the formalized N-Frame tower route, not a proof
of `P ≠ NP`: every semantically adequate surviving object is now proved to be
another exact presentation of the original SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerCompactRouteClosure

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerEffectiveDiagonalCompilerAudit
open PallLean.Paper93.DeepMath.PathB.NFrameTowerKleeneQuotationAudit
open PallLean.Paper93.DeepMath.PathB.NFrameTowerIndependentDecoderAudit
open PallLean.Paper93.DeepMath.PathB.NFrameTowerBoundedAnswerFeedbackNoGo
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSyntacticFeedbackCollapse

/-! ## Exact equivalence line -/

/-- Compact liar compilers and uniform semantic feedback are the same
lower-bound-strength object. -/
theorem compactSATLiarCompiler_iff_uniformSemanticAnswerFeedback
    (U : MachineModel) :
    Nonempty (CompactSATLiarCompiler U) ↔
      Nonempty (UniformSemanticAnswerFeedback U) :=
  (compactSATLiarCompiler_iff_no_SATDecisionInP U).trans
    (uniformSemanticAnswerFeedback_iff_no_SATDecisionInP U).symm

/-- Uniform semantic feedback is exactly a finite code-indexed diagonalizer. -/
theorem uniformSemanticAnswerFeedback_iff_codeIndexedFiniteDiagonalizer
    (U : MachineModel) :
    Nonempty (UniformSemanticAnswerFeedback U) ↔
      Nonempty (CodeIndexedFiniteDiagonalizer U) :=
  (uniformSemanticAnswerFeedback_iff_no_SATDecisionInP U).trans
    (codeIndexedFiniteDiagonalizer_iff_no_SATDecisionInP U).symm

/-- Adding the Book 1 tower escape does not change the endpoint. -/
theorem uniformSemanticAnswerFeedback_iff_solverIndexedTowerDiagonalizer
    (U : MachineModel) (T : UniformRosserTower) :
    Nonempty (UniformSemanticAnswerFeedback U) ↔
      Nonempty (SolverIndexedTowerDiagonalizer U T) :=
  (uniformSemanticAnswerFeedback_iff_no_SATDecisionInP U).trans
    (solverIndexedTowerDiagonalizer_iff_no_SATDecisionInP U T).symm

/-- The complete compact-route equivalence chain in one theorem. -/
theorem compactRoute_exact_endpoint
    (U : MachineModel) (T : UniformRosserTower) :
    (Nonempty (CompactSATLiarCompiler U) ↔ ¬ SATDecisionInP U) ∧
    (Nonempty (UniformSemanticAnswerFeedback U) ↔ ¬ SATDecisionInP U) ∧
    (Nonempty (CodeIndexedFiniteDiagonalizer U) ↔ ¬ SATDecisionInP U) ∧
    (Nonempty (SolverIndexedTowerDiagonalizer U T) ↔ ¬ SATDecisionInP U) := by
  exact ⟨compactSATLiarCompiler_iff_no_SATDecisionInP U,
    uniformSemanticAnswerFeedback_iff_no_SATDecisionInP U,
    codeIndexedFiniteDiagonalizer_iff_no_SATDecisionInP U,
    solverIndexedTowerDiagonalizer_iff_no_SATDecisionInP U T⟩

/-! ## Effective quotation enters the same line only through liar semantics -/

/-- An operational polynomial quoted decoder together with the missing
construction-derived liar theorem. -/
structure EffectiveQuotedLiarPackage
    (U : MachineModel) (V : CounterexampleCompilerModel) where
  decoder : PolynomialQuotedCNFDecoder U V
  liarLaw : ConstructionDerivedLiarLaw decoder

/-- Erase operational quotation to uniform semantic feedback. -/
def EffectiveQuotedLiarPackage.toUniformSemanticFeedback
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (K : EffectiveQuotedLiarPackage U V) :
    UniformSemanticAnswerFeedback U where
  feedback := by
    intro M
    exact {
      formula := K.decoder.output M
      semantic_fixedpoint :=
        (semanticAnswerFeedback_iff_liarOn U M
          (K.decoder.output M)).mpr (K.liarLaw M)
    }

/-- Therefore the effective quoted package proves the lower bound solely via
its liar-law field. -/
theorem no_SATDecisionInP_of_effectiveQuotedLiarPackage
    {U : MachineModel} {V : CounterexampleCompilerModel}
    (K : EffectiveQuotedLiarPackage U V) :
    ¬ SATDecisionInP U :=
  no_SATDecisionInP_of_uniformSemanticAnswerFeedback
    K.toUniformSemanticFeedback

/-- In contrast, polynomial quotation infrastructure without liar semantics
exists for every machine model on the fixed constant-output surface. -/
theorem quotationInfrastructure_inhabited_without_liarLaw
    (U : MachineModel) :
    Nonempty (PolynomialQuotedCNFDecoder U constantNoCNFCompilerModel) :=
  exists_polynomialQuotedCNFDecoder U

/-! ## Uniform syntactic feedback is a separate trivial-error condition -/

/-- Literal feedback points for every certified polynomial machine. -/
structure UniformSyntacticAnswerFeedback (U : MachineModel) where
  feedback : ∀ M : DecisionMachine U, SyntacticAnswerFeedbackFor U M

/-- Uniform syntactic feedback is exactly the assertion that every certified
machine fails one of the same two canonical formulas. -/
theorem uniformSyntacticAnswerFeedback_iff_all_canonical_error
    (U : MachineModel) :
    Nonempty (UniformSyntacticAnswerFeedback U) ↔
      ∀ M : DecisionMachine U,
        U.decisionRun M.code yesCNF = false ∨
        U.decisionRun M.code noCNF = true := by
  constructor
  · rintro ⟨F⟩ M
    exact (syntacticAnswerFeedback_iff_canonical_error U M).mp
      ⟨F.feedback M⟩
  · intro h
    exact ⟨{
      feedback := fun M =>
        Classical.choice
          ((syntacticAnswerFeedback_iff_canonical_error U M).mpr (h M))
    }⟩

/-- One certified machine that handles the canonical yes/no pair correctly
already refutes a uniform syntactic family, even without assuming that machine
decides general SAT. -/
theorem no_uniformSyntacticAnswerFeedback_of_one_canonical_correct
    {U : MachineModel} (M : DecisionMachine U)
    (hyes : U.decisionRun M.code yesCNF = true)
    (hno : U.decisionRun M.code noCNF = false) :
    ¬ Nonempty (UniformSyntacticAnswerFeedback U) := by
  rintro ⟨F⟩
  exact no_syntacticAnswerFeedback_of_canonical_correct U M hyes hno
    ⟨F.feedback M⟩

end PallLean.Paper93.DeepMath.PathB.NFrameTowerCompactRouteClosure

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerCompactRouteClosure.compactSATLiarCompiler_iff_uniformSemanticAnswerFeedback
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerCompactRouteClosure.compactRoute_exact_endpoint
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerCompactRouteClosure.EffectiveQuotedLiarPackage.toUniformSemanticFeedback
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerCompactRouteClosure.no_SATDecisionInP_of_effectiveQuotedLiarPackage
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerCompactRouteClosure.uniformSyntacticAnswerFeedback_iff_all_canonical_error
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerCompactRouteClosure.no_uniformSyntacticAnswerFeedback_of_one_canonical_correct
