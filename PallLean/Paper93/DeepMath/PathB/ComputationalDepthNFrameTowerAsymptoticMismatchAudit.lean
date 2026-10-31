import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameGodelTowerSATBridgeAudit

/-!
# N-Frame tower: fixed escape versus asymptotic SAT audit

The Book 1 Gödel tower supplies one true Rosser sentence escaping every finite
observer level.  The next bridge question is whether finite CNF encodings of
that escape can themselves form a hard SAT decision family.

They cannot.  Every correct finite encoding of the true escape is satisfiable,
so any length-indexed family of such encodings has the constant truth profile
`true`.  A single uniform acceptor evaluates that profile with constant work,
and ordinary SAT cannot many-one reduce to an all-satisfiable target because
the fixed unsatisfiable CNF would have nowhere to go.

This exposes a precise type mismatch:

* Gödel/Rosser non-escape is unprovability of a true sentence across theories;
* P versus NP is asymptotic uniform decision complexity across both yes and no
  finite instances.

Therefore the needed bridge cannot merely encode the one tower escape at
larger sizes.  It must produce a decision-relevant parameterized family whose
truth values vary with arbitrary SAT inputs, while preserving the tower's
level-escape property.  Proving such a uniform reduction and finite-level
capture theorem remains the load-bearing complexity step.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTowerAsymptoticMismatchAudit

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.NFrameGodelTowerSATBridgeAudit
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge

attribute [local instance] Classical.propDecidable

/-! ## CNF families and uniform constant evaluation -/

abbrev CNFFamily := Nat → CNF

noncomputable def truthProfile (F : CNFFamily) (n : Nat) : Bool :=
  satTruth (F n)

def AllSatisfiable (F : CNFFamily) : Prop :=
  ∀ n, Satisfiable (F n)

theorem truthProfile_eq_true_of_allSatisfiable
    {F : CNFFamily} (hF : AllSatisfiable F) (n : Nat) :
    truthProfile F n = true := by
  exact (satTruth_eq_true_iff (F n)).2 (hF n)

/-- A uniform semantic evaluator for one length-indexed decision profile, with
an explicit work function and polynomial certificate. -/
structure FamilyDecisionEvaluator (F : CNFFamily) where
  answer : Nat → Bool
  work : Nat → Nat
  correct : ∀ n, answer n = truthProfile F n
  polyWork : IsPolynomialBudget work

/-- An all-satisfiable family has the uniform constant-true evaluator. -/
noncomputable def constantTrueEvaluator
    {F : CNFFamily} (hF : AllSatisfiable F) :
    FamilyDecisionEvaluator F where
  answer := fun _ => true
  work := fun _ => 1
  correct := by
    intro n
    exact (truthProfile_eq_true_of_allSatisfiable hF n).symm
  polyWork := by
    refine ⟨0, 1, ?_⟩
    intro n
    simp

/-! ## A uniform CNF representation of the tower escape -/

/-- At every scale, a finite CNF represents the same uniform Rosser escape.
The formulas may grow syntactically, but their semantic answer is always true. -/
structure UniformEscapeCNFFamily (T : UniformRosserTower) where
  formula : CNFFamily
  sentence : Nat → T.Sentence
  represents_escape : ∀ n, sentence n = T.escape
  truth_preserving : ∀ n, T.True_ (sentence n) ↔ Satisfiable (formula n)

theorem UniformEscapeCNFFamily.allSatisfiable
    {T : UniformRosserTower} (E : UniformEscapeCNFFamily T) :
    AllSatisfiable E.formula := by
  intro n
  apply (E.truth_preserving n).mp
  rw [E.represents_escape n]
  exact T.escape_true

/-- Hence every uniform finite encoding of the one tower escape has a
constant-work decision-profile evaluator. -/
noncomputable def UniformEscapeCNFFamily.constantEvaluator
    {T : UniformRosserTower} (E : UniformEscapeCNFFamily T) :
    FamilyDecisionEvaluator E.formula :=
  constantTrueEvaluator E.allSatisfiable

theorem UniformEscapeCNFFamily.truthProfile_constant_true
    {T : UniformRosserTower} (E : UniformEscapeCNFFamily T) :
    ∀ n, truthProfile E.formula n = true :=
  truthProfile_eq_true_of_allSatisfiable E.allSatisfiable

/-! ## No SAT reduction to the all-yes escape family -/

/-- Ordinary SAT cannot many-one reduce to any all-satisfiable CNF family:
the concrete `noCNF` instance is unsatisfiable, while every target is yes. -/
theorem SAT_not_reduces_to_allSatisfiableFamily
    (F : CNFFamily) (hF : AllSatisfiable F) :
    ¬ ManyOneReduces Satisfiable (fun n : Nat => Satisfiable (F n)) := by
  rintro ⟨reduce, hreduce⟩
  have htarget : Satisfiable (F (reduce noCNF)) := hF (reduce noCNF)
  have hsource : Satisfiable noCNF := (hreduce noCNF).mpr htarget
  exact noCNF_not_satisfiable hsource

/-- In particular, no family that merely re-encodes the single true tower
escape at every scale is SAT-hard under this direct many-one notion. -/
theorem UniformEscapeCNFFamily.not_SAT_hard
    {T : UniformRosserTower} (E : UniformEscapeCNFFamily T) :
    ¬ ManyOneReduces Satisfiable
      (fun n : Nat => Satisfiable (E.formula n)) :=
  SAT_not_reduces_to_allSatisfiableFamily E.formula E.allSatisfiable

/-! ## The necessary replacement object -/

/-- A decision-relevant tower interpretation must accept arbitrary finite SAT
inputs, not just repeat the one true escape.  This structure names the missing
kind of bridge without asserting that polynomial solvers are captured. -/
structure DecisionRelevantTowerInterpretation (T : UniformRosserTower) where
  encode : CNF → T.Sentence
  truth_preserving : ∀ φ, T.True_ (encode φ) ↔ Satisfiable φ
  /-- The image contains both a true and a false finite instance. -/
  yes_image : T.True_ (encode yesCNF)
  no_image : ¬ T.True_ (encode noCNF)

/-- Truth preservation itself supplies the required yes/no distinction. -/
theorem decisionRelevant_yes_no_distinct
    {T : UniformRosserTower}
    (I : DecisionRelevantTowerInterpretation T) :
    I.encode yesCNF ≠ I.encode noCNF := by
  intro heq
  apply I.no_image
  rw [← heq]
  exact I.yes_image

end PallLean.Paper93.DeepMath.PathB.NFrameTowerAsymptoticMismatchAudit

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerAsymptoticMismatchAudit.truthProfile_eq_true_of_allSatisfiable
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerAsymptoticMismatchAudit.constantTrueEvaluator
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerAsymptoticMismatchAudit.UniformEscapeCNFFamily.allSatisfiable
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerAsymptoticMismatchAudit.UniformEscapeCNFFamily.truthProfile_constant_true
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerAsymptoticMismatchAudit.SAT_not_reduces_to_allSatisfiableFamily
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerAsymptoticMismatchAudit.UniformEscapeCNFFamily.not_SAT_hard
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTowerAsymptoticMismatchAudit.decisionRelevant_yes_no_distinct
