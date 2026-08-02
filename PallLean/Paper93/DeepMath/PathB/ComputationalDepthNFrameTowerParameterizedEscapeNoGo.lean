import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerAsymptoticMismatchAudit

/-!
# N-Frame tower: parameterized SAT escape no-go

The fixed Rosser escape is all-true and therefore not a SAT-hard decision
family.  The obvious repair is to index the Gödel fixed-point law by arbitrary
CNFs, hoping that satisfiable formulas escape every level while unsatisfiable
formulas do not.

This file proves that repair is inconsistent with tower soundness.  For any
sound tower, a sentence satisfying

`True ψ ↔ ∀ n, ¬ Prov n ψ`

must be true: if it were false, soundness would make it unprovable at every
level, and the fixed point would make it true after all.  Consequently one
cannot impose this biconditional on the encodings of both satisfiable and
unsatisfiable CNFs while preserving their truth values.

More generally, a sound tower can never prove a truth-preserving encoding of
an unsatisfiable CNF at any level.  Hence the alternative rule “no instances
are captured by some rung” is also impossible when `Prov` means ordinary
sound provability of the encoded SAT statement.

The correct diagonal target must therefore be solver-indexed and meta-level:
for each alleged solver, construct a *true statement about that solver* which
escapes its observer level and yields a finite counterexample to the solver.
It cannot be an input-indexed fixed-point copy of the proposition “φ is
satisfiable.”  Building the uniform solver-to-counterexample translation is
the remaining complexity-theoretic bridge.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerParameterizedEscapeNoGo

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit
open PallLean.Paper93.DeepMath.PathB.NFrameTowerAsymptoticMismatchAudit
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge

attribute [local instance] Classical.propDecidable

/-! ## A mixed yes/no pointwise fixed-point schema is impossible -/

/-- The tempting but invalid parameterization: every arbitrary CNF encoding
is made into its own uniform tower fixed point. -/
structure SATIndexedUniformFixedPoint (T : UniformRosserTower) where
  encode : CNF → T.Sentence
  truth_preserving : ∀ φ, T.True_ (encode φ) ↔ Satisfiable φ
  fixedpoint : ∀ φ, T.True_ (encode φ) ↔
    ∀ n, ¬ T.Prov n (encode φ)

/-- In a sound tower, every pointwise uniform fixed-point sentence is forced
true. -/
theorem SATIndexedUniformFixedPoint.encoded_true
    {T : UniformRosserTower}
    (E : SATIndexedUniformFixedPoint T) (φ : CNF) :
    T.True_ (E.encode φ) := by
  by_contra hfalse
  have hall : ∀ n, ¬ T.Prov n (E.encode φ) := by
    intro n hp
    exact hfalse (T.sound n (E.encode φ) hp)
  exact hfalse ((E.fixedpoint φ).mpr hall)

/-- Therefore the invalid schema would make every CNF satisfiable. -/
theorem SATIndexedUniformFixedPoint.all_satisfiable
    {T : UniformRosserTower}
    (E : SATIndexedUniformFixedPoint T) (φ : CNF) :
    Satisfiable φ :=
  (E.truth_preserving φ).mp (E.encoded_true φ)

/-- The concrete empty-clause formula refutes existence of the pointwise
SAT-indexed fixed-point bridge. -/
theorem no_SATIndexedUniformFixedPoint (T : UniformRosserTower) :
    ¬ Nonempty (SATIndexedUniformFixedPoint T) := by
  rintro ⟨E⟩
  exact noCNF_not_satisfiable (E.all_satisfiable noCNF)

/-! ## Sound provability cannot capture false SAT encodings -/

/-- A plain truth-preserving interpretation, without any fixed-point law. -/
structure TruthPreservingSATInterpretation (T : UniformRosserTower) where
  encode : CNF → T.Sentence
  truth_preserving : ∀ φ, T.True_ (encode φ) ↔ Satisfiable φ

/-- If `φ` is unsatisfiable, no sound tower level can prove the sentence that
truthfully means “φ is satisfiable.” -/
theorem TruthPreservingSATInterpretation.unsat_unprovable
    {T : UniformRosserTower}
    (I : TruthPreservingSATInterpretation T)
    (φ : CNF) (hunsat : ¬ Satisfiable φ) :
    ∀ n, ¬ T.Prov n (I.encode φ) := by
  intro n hp
  have ht : T.True_ (I.encode φ) := T.sound n (I.encode φ) hp
  exact hunsat ((I.truth_preserving φ).mp ht)

/-- The alternative hoped-for bridge: every no instance is eventually
captured/proved by some finite tower rung. -/
def NegativeInstanceCapture
    {T : UniformRosserTower}
    (I : TruthPreservingSATInterpretation T) : Prop :=
  ∀ φ, ¬ Satisfiable φ → ∃ n, T.Prov n (I.encode φ)

/-- Negative-instance capture contradicts soundness already on `noCNF`. -/
theorem no_negativeInstanceCapture
    {T : UniformRosserTower}
    (I : TruthPreservingSATInterpretation T) :
    ¬ NegativeInstanceCapture I := by
  intro hcapture
  rcases hcapture noCNF noCNF_not_satisfiable with ⟨n, hn⟩
  exact I.unsat_unprovable noCNF noCNF_not_satisfiable n hn

/-! ## Correct replacement shape: solver-indexed true meta-escapes -/

/-- A structurally valid replacement target.  Each machine code receives a
true meta-sentence outside every tower rung and a finite CNF intended to expose
that code's failure.  The final `exposesFailure` field is deliberately
parametric: proving it for actual polynomial SAT machines is the missing
diagonal-to-finite-complexity theorem. -/
structure SolverIndexedMetaEscape (T : UniformRosserTower) where
  statement : Nat → T.Sentence
  statement_true : ∀ code, T.True_ (statement code)
  statement_escapes : ∀ code n, ¬ T.Prov n (statement code)
  counterexampleCNF : Nat → CNF
  ExposesFailure : Nat → CNF → Prop
  exposesFailure : ∀ code, ExposesFailure code (counterexampleCNF code)

/-- Every solver-indexed meta-escape is outside the finite tower union. -/
theorem SolverIndexedMetaEscape.not_in_union
    {T : UniformRosserTower}
    (E : SolverIndexedMetaEscape T) (code : Nat) :
    ¬ T.InUnion (E.statement code) := by
  rintro ⟨n, hn⟩
  exact E.statement_escapes code n hn

end PallLean.Paper93.DeepMath.PathB.NFrameTowerParameterizedEscapeNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerParameterizedEscapeNoGo.SATIndexedUniformFixedPoint.encoded_true
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerParameterizedEscapeNoGo.SATIndexedUniformFixedPoint.all_satisfiable
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerParameterizedEscapeNoGo.no_SATIndexedUniformFixedPoint
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerParameterizedEscapeNoGo.TruthPreservingSATInterpretation.unsat_unprovable
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerParameterizedEscapeNoGo.no_negativeInstanceCapture
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerParameterizedEscapeNoGo.SolverIndexedMetaEscape.not_in_union
