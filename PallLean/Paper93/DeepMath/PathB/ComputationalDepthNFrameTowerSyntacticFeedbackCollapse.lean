import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerBoundedAnswerFeedbackNoGo

/-!
# N-Frame tower: syntactic answer-feedback collapse

The bounded feedback audit distinguished semantic consistency from literal CNF
equality.  This file completely classifies the stronger syntactic proposal.

Because rejection feedback emits only `yesCNF` or `noCNF`, every literal fixed
point is one of those two formulas.  It exists exactly when the alleged solver
rejects the canonical satisfiable formula or accepts the canonical
unsatisfiable formula.  Hence literal feedback can expose only mistakes on two
trivial instances.  A machine may fail elsewhere while answering both
canonical formulas correctly, in which case semantic feedback exists but no
syntactic feedback point exists.

This rules out the hope that literal equality might be supplied by a generic
syntax-level recursion theorem and then upgraded to the missing arbitrary
finite counterexample.  The syntax has collapsed before reaching the hard SAT
instances.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerSyntacticFeedbackCollapse

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerBoundedAnswerFeedbackNoGo
open PallLean.Paper93.DeepMath.PathB.NFrameTowerHaltingReflectionNoGo

attribute [local instance] Classical.propDecidable

/-! ## Exact output equalities -/

/-- The two canonical truth-coded formulas are syntactically distinct. -/
theorem yesCNF_ne_noCNF : yesCNF ≠ noCNF := by
  intro h
  have hclauses := congrArg CNF.clauses h
  simp [yesCNF, noCNF] at hclauses

theorem noCNF_ne_yesCNF : noCNF ≠ yesCNF :=
  Ne.symm yesCNF_ne_noCNF

/-- Rejection feedback emits `yesCNF` exactly on rejection. -/
theorem rejectionCodedCNF_eq_yes_iff
    (U : MachineModel) (code : Nat) (φ : CNF) :
    rejectionCodedCNF U code φ = yesCNF ↔
      U.decisionRun code φ = false := by
  cases h : U.decisionRun code φ <;>
    simp [rejectionCodedCNF, truthCodedCNF, h, noCNF_ne_yesCNF]

/-- Rejection feedback emits `noCNF` exactly on acceptance. -/
theorem rejectionCodedCNF_eq_no_iff
    (U : MachineModel) (code : Nat) (φ : CNF) :
    rejectionCodedCNF U code φ = noCNF ↔
      U.decisionRun code φ = true := by
  cases h : U.decisionRun code φ <;>
    simp [rejectionCodedCNF, truthCodedCNF, h, yesCNF_ne_noCNF]

/-! ## Complete classification of literal feedback -/

/-- Every syntactic feedback point is literally one of the two canonical
truth-coded formulas. -/
theorem syntacticAnswerFeedback_formula_eq_yes_or_no
    {U : MachineModel} {M : DecisionMachine U}
    (F : SyntacticAnswerFeedbackFor U M) :
    F.formula = yesCNF ∨ F.formula = noCNF := by
  rcases rejectionCodedCNF_eq_yes_or_no U M.code F.formula with h | h
  · exact Or.inl (F.syntactic_fixedpoint.trans h)
  · exact Or.inr (F.syntactic_fixedpoint.trans h)

/-- **Syntactic collapse.**  A literal feedback point exists exactly when the
solver gets `yesCNF` or `noCNF` wrong. -/
theorem syntacticAnswerFeedback_iff_canonical_error
    (U : MachineModel) (M : DecisionMachine U) :
    Nonempty (SyntacticAnswerFeedbackFor U M) ↔
      U.decisionRun M.code yesCNF = false ∨
      U.decisionRun M.code noCNF = true := by
  constructor
  · rintro ⟨F⟩
    rcases syntacticAnswerFeedback_formula_eq_yes_or_no F with hyes | hno
    · left
      have hout : rejectionCodedCNF U M.code F.formula = yesCNF :=
        F.syntactic_fixedpoint.symm.trans hyes
      have hrun : U.decisionRun M.code F.formula = false :=
        (rejectionCodedCNF_eq_yes_iff U M.code F.formula).mp hout
      simpa only [hyes] using hrun
    · right
      have hout : rejectionCodedCNF U M.code F.formula = noCNF :=
        F.syntactic_fixedpoint.symm.trans hno
      have hrun : U.decisionRun M.code F.formula = true :=
        (rejectionCodedCNF_eq_no_iff U M.code F.formula).mp hout
      simpa only [hno] using hrun
  · rintro (hyes | hno)
    · exact ⟨{
        formula := yesCNF
        syntactic_fixedpoint :=
          ((rejectionCodedCNF_eq_yes_iff U M.code yesCNF).mpr hyes).symm
      }⟩
    · exact ⟨{
        formula := noCNF
        syntactic_fixedpoint :=
          ((rejectionCodedCNF_eq_no_iff U M.code noCNF).mpr hno).symm
      }⟩

/-! ## Syntactic feedback detects only the canonical errors -/

/-- Correctness on the two canonical formulas alone already rules out literal
feedback equality, even if the machine fails elsewhere. -/
theorem no_syntacticAnswerFeedback_of_canonical_correct
    (U : MachineModel) (M : DecisionMachine U)
    (hyes : U.decisionRun M.code yesCNF = true)
    (hno : U.decisionRun M.code noCNF = false) :
    ¬ Nonempty (SyntacticAnswerFeedbackFor U M) := by
  rw [syntacticAnswerFeedback_iff_canonical_error]
  simp [hyes, hno]

/-- If a machine fails SAT somewhere else but answers both canonical formulas
correctly, semantic feedback exists while syntactic feedback does not.  This
is the exact gap between semantic and literal fixed points. -/
theorem semantic_exists_but_no_syntactic_of_noncanonical_failure
    (U : MachineModel) (M : DecisionMachine U)
    (hfail : ¬ DecidesSAT U M)
    (hyes : U.decisionRun M.code yesCNF = true)
    (hno : U.decisionRun M.code noCNF = false) :
    Nonempty (SemanticAnswerFeedbackFor U M) ∧
      ¬ Nonempty (SyntacticAnswerFeedbackFor U M) := by
  exact ⟨(semanticAnswerFeedback_iff_not_decidesSAT U M).mpr hfail,
    no_syntacticAnswerFeedback_of_canonical_correct U M hyes hno⟩

/-- Canonical solver errors are themselves exactly failures of `CorrectOn` on
the two fixed formulas. -/
theorem canonical_error_iff_not_correctOn
    (U : MachineModel) (M : DecisionMachine U) :
    (U.decisionRun M.code yesCNF = false ∨
      U.decisionRun M.code noCNF = true) ↔
    (¬ CorrectOn U M.code yesCNF) ∨
      (¬ CorrectOn U M.code noCNF) := by
  constructor
  · rintro (hyes | hno)
    · left
      unfold CorrectOn
      simp [hyes, yesCNF_satisfiable]
    · right
      unfold CorrectOn
      simp [hno, noCNF_not_satisfiable]
  · rintro (hyes | hno)
    · left
      unfold CorrectOn at hyes
      cases hrun : U.decisionRun M.code yesCNF
      · rfl
      · exfalso
        exact hyes (by simp [hrun, yesCNF_satisfiable])
    · right
      unfold CorrectOn at hno
      cases hrun : U.decisionRun M.code noCNF
      · exfalso
        apply hno
        simp [hrun, noCNF_not_satisfiable]
      · rfl

/-- Equivalent final form: literal feedback exists exactly when one of the two
trivial canonical instances is misclassified. -/
theorem syntacticAnswerFeedback_iff_canonical_not_correctOn
    (U : MachineModel) (M : DecisionMachine U) :
    Nonempty (SyntacticAnswerFeedbackFor U M) ↔
      (¬ CorrectOn U M.code yesCNF) ∨
      (¬ CorrectOn U M.code noCNF) :=
  (syntacticAnswerFeedback_iff_canonical_error U M).trans
    (canonical_error_iff_not_correctOn U M)

end PallLean.Paper93.DeepMath.PathB.NFrameTowerSyntacticFeedbackCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSyntacticFeedbackCollapse.rejectionCodedCNF_eq_yes_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSyntacticFeedbackCollapse.syntacticAnswerFeedback_formula_eq_yes_or_no
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSyntacticFeedbackCollapse.syntacticAnswerFeedback_iff_canonical_error
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSyntacticFeedbackCollapse.semantic_exists_but_no_syntactic_of_noncanonical_failure
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerSyntacticFeedbackCollapse.syntacticAnswerFeedback_iff_canonical_not_correctOn
