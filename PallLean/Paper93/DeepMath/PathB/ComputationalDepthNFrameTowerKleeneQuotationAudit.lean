import Mathlib.Computability.PartrecCode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerCookLevinSelfSizeBarrier

/-!
# N-Frame tower: Kleene compact-quotation audit

Literal Cook–Levin self-containment fails by size.  The remaining tower route
is compact quotation: use Kleene's second recursion theorem to obtain a small
program name whose *behavior* refers to that name, then decode the name into a
finite SAT instance.

This file applies mathlib's genuine theorem
`Nat.Partrec.Code.fixed_point₂`.  The behavioral fixed point exists
unconditionally.  We then isolate the extra SAT claim: the formula decoded
from the fixed-point name is satisfiable exactly when the alleged solver says
it is not satisfiable.

For Boolean decision output, that liar biconditional is exactly failure of the
solver on that formula.  If the name-to-CNF decoder is unconstrained, a missed
formula can simply be installed as a constant decoder; packaging this for
every polynomial solver is therefore equivalent to `SAT ∉ P`.  Thus Kleene
quotation solves the syntactic self-name problem but not the finite SAT
semantic bridge.  The surviving target is an independently computable,
size-controlled decoder whose liar semantics follows from its construction.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerKleeneQuotationAudit

open SATDepthMachine
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier

attribute [local instance] Classical.propDecidable

/-! ## Genuine compact behavioral fixed points -/

/-- A compact Kleene name for a binary partial-recursive generator. -/
structure BehavioralFixedPointSkeleton where
  generator : Code → Nat →. Nat
  generator_partrec : Partrec₂ generator
  name : Code
  behavior_fixedpoint : Code.eval name = generator name

/-- Kleene's second recursion theorem supplies the behavioral skeleton for
every partial-recursive generator. -/
theorem exists_behavioralFixedPointSkeleton
    (f : Code → Nat →. Nat) (hf : Partrec₂ f) :
    ∃ S : BehavioralFixedPointSkeleton, S.generator = f := by
  rcases Code.fixed_point₂ hf with ⟨c, hc⟩
  exact ⟨{
    generator := f
    generator_partrec := hf
    name := c
    behavior_fixedpoint := hc
  }, rfl⟩

/-- A canonical skeleton, using the universal evaluator itself as the
generator.  Its role is only to show that compact self-naming is available
without any SAT lower-bound assumption. -/
noncomputable def canonicalBehavioralFixedPointSkeleton :
    BehavioralFixedPointSkeleton := by
  let c := Classical.choose (Code.fixed_point₂ Code.eval_part)
  exact {
    generator := Code.eval
    generator_partrec := Code.eval_part
    name := c
    behavior_fixedpoint := Classical.choose_spec
      (Code.fixed_point₂ Code.eval_part)
  }

/-! ## The extra SAT semantic claim -/

/-- The desired liar semantics on one formula: the formula is satisfiable
exactly when the named solver rejects it. -/
def LiarOn
    (U : MachineModel) (code : Nat) (φ : CNF) : Prop :=
  Satisfiable φ ↔ U.decisionRun code φ = false

/-- For Boolean output, liar semantics is exactly misclassification of that
finite formula. -/
theorem liarOn_iff_not_correctOn
    (U : MachineModel) (code : Nat) (φ : CNF) :
    LiarOn U code φ ↔ ¬ CorrectOn U code φ := by
  cases hrun : U.decisionRun code φ <;>
    simp [LiarOn, CorrectOn, hrun]

/-- A compact quoted SAT liar for one certified polynomial machine.  The
Kleene skeleton is genuine; `formulaOf` is deliberately left unconstrained so
we can audit how much strength is hidden in `liar_semantics`. -/
structure CompactSATLiarFor
    (U : MachineModel) (M : DecisionMachine U) where
  skeleton : BehavioralFixedPointSkeleton
  formulaOf : Code → CNF
  liar_semantics : LiarOn U M.code (formulaOf skeleton.name)

/-- A correct SAT decider cannot possess such a quoted liar. -/
theorem no_compactSATLiarFor_of_decidesSAT
    (U : MachineModel) (M : DecisionMachine U)
    (hM : DecidesSAT U M) :
    ¬ Nonempty (CompactSATLiarFor U M) := by
  rintro ⟨L⟩
  have hfail : ¬ CorrectOn U M.code (L.formulaOf L.skeleton.name) :=
    (liarOn_iff_not_correctOn U M.code
      (L.formulaOf L.skeleton.name)).mp L.liar_semantics
  exact hfail (hM (L.formulaOf L.skeleton.name))

/-- Conversely, once a failing formula is already known, an unconstrained
decoder can be made constant and the Kleene skeleton adds no difficulty. -/
noncomputable def compactSATLiarFor_of_not_decidesSAT
    (U : MachineModel) (M : DecisionMachine U)
    (hnot : ¬ DecidesSAT U M) :
    CompactSATLiarFor U M := by
  let φ := Classical.choose
    (exists_finite_counterexample_of_not_decidesSAT M hnot)
  have hφ : ¬ CorrectOn U M.code φ :=
    Classical.choose_spec
      (exists_finite_counterexample_of_not_decidesSAT M hnot)
  exact {
    skeleton := canonicalBehavioralFixedPointSkeleton
    formulaOf := fun _ => φ
    liar_semantics :=
      (liarOn_iff_not_correctOn U M.code φ).mpr hφ
  }

/-- With an arbitrary name decoder, a compact quoted liar exists exactly when
the machine is not a correct SAT decider. -/
theorem compactSATLiarFor_iff_not_decidesSAT
    (U : MachineModel) (M : DecisionMachine U) :
    Nonempty (CompactSATLiarFor U M) ↔ ¬ DecidesSAT U M := by
  constructor
  · rintro ⟨L⟩ hcorrect
    exact no_compactSATLiarFor_of_decidesSAT U M hcorrect ⟨L⟩
  · intro hnot
    exact ⟨compactSATLiarFor_of_not_decidesSAT U M hnot⟩

/-! ## Uniform compact quotation is still the separation -/

/-- One compact quoted liar for every certified polynomial SAT machine. -/
structure CompactSATLiarCompiler (U : MachineModel) where
  compile : ∀ M : DecisionMachine U, CompactSATLiarFor U M

/-- A uniform compact-liar compiler rules out polynomial-time SAT decision. -/
theorem no_SATDecisionInP_of_compactSATLiarCompiler
    {U : MachineModel} (K : CompactSATLiarCompiler U) :
    ¬ SATDecisionInP U := by
  rintro ⟨M, hM⟩
  exact no_compactSATLiarFor_of_decidesSAT U M hM ⟨K.compile M⟩

/-- Assuming the lower bound, classical choice and a constant decoder package
the missed formulas into a compact-liar compiler. -/
noncomputable def compactSATLiarCompilerOfNoSATDecisionInP
    {U : MachineModel} (hno : ¬ SATDecisionInP U) :
    CompactSATLiarCompiler U where
  compile := by
    intro M
    apply compactSATLiarFor_of_not_decidesSAT U M
    intro hM
    exact hno ⟨M, hM⟩

/-- **Compact-quotation frontier.**  Kleene fixed points plus an arbitrary
name-to-CNF decoder yield the desired family exactly when `SAT ∉ P`. -/
theorem compactSATLiarCompiler_iff_no_SATDecisionInP
    (U : MachineModel) :
    Nonempty (CompactSATLiarCompiler U) ↔ ¬ SATDecisionInP U := by
  constructor
  · rintro ⟨K⟩
    exact no_SATDecisionInP_of_compactSATLiarCompiler K
  · intro hno
    exact ⟨compactSATLiarCompilerOfNoSATDecisionInP hno⟩

end PallLean.Paper93.DeepMath.PathB.NFrameTowerKleeneQuotationAudit

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerKleeneQuotationAudit.exists_behavioralFixedPointSkeleton
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerKleeneQuotationAudit.liarOn_iff_not_correctOn
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerKleeneQuotationAudit.no_compactSATLiarFor_of_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerKleeneQuotationAudit.compactSATLiarFor_iff_not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerKleeneQuotationAudit.no_SATDecisionInP_of_compactSATLiarCompiler
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerKleeneQuotationAudit.compactSATLiarCompiler_iff_no_SATDecisionInP
