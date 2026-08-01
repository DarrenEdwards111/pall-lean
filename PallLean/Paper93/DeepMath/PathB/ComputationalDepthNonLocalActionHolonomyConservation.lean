import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSolverSpecificExpanderCutAudit

/-!
# Non-local action holonomy: conservation and exact expander calibration

The crossing-selector route fails because a sound boundary must carry the full
residual width.  A possible escape is to replace a spatial cut by a non-local
action holonomy: the observer records a word of local actions and only later
evaluates its composed effect.

This file audits that proposal in its strongest representation-independent
form.  If a boundary family factors through `T` action slots with `q` choices
per slot, it realizes at most `q^T` observer classes.  Postprocessing cannot
increase this capacity.  This is the genuine P-side conservation law: local
composition adds logarithmic action rank even when its global action has
multiplicatively many outcomes.

The expander calibration is exact.  The natural `r`-bit Tseitin residual factors
through `r` binary action slots and realizes all `2^r` outcomes.  Conversely,
any binary action factorization of that residual needs at least `r` slots.
Thus non-local action holonomy avoids a single spatial cut, but ordinary
residual surjectivity still yields only a linear action lower bound, which is
tight and polynomial.  A P-vs-NP separation would require a new theorem forcing
superpolynomial *action length/rank*, not merely exponentially many outcomes.
-/

namespace PallLean.Paper93.DeepMath.PathB.NonLocalActionHolonomyConservation

open BranchSpanningDynamicHolonomy
open ExpanderSATQueryContinuation

variable {Input Boundary Feature : Type*}

/-- A family boundary factors through a length-`T` word over a `q`-letter local
action alphabet.  `realize` may compose the letters non-locally and
noncommutatively; the capacity theorem uses no algebraic shortcut. -/
structure ActionWordFactorization [Fintype Input]
    (boundary : Input → Boundary) (T q : ℕ) where
  realize : (Fin T → Fin q) → Boundary
  factors : ∀ x, ∃ word, boundary x = realize word

namespace ActionWordFactorization

/-- Observer classes realized by the factored boundary family. -/
noncomputable def classRank [Fintype Input]
    {boundary : Input → Boundary} {T q : ℕ}
    (_F : ActionWordFactorization boundary T q) : ℕ :=
  familyImageRank boundary

/-- **Non-local action conservation.**  `T` slots with `q` local choices
realize at most `q^T` global boundary actions, regardless of how the word is
composed or observed. -/
theorem classRank_le_pow [Fintype Input]
    {boundary : Input → Boundary} {T q : ℕ}
    (F : ActionWordFactorization boundary T q) :
    F.classRank ≤ q ^ T := by
  classical
  unfold classRank familyImageRank
  calc
    (Finset.univ.image boundary).card
        ≤ (Finset.univ.image F.realize).card := by
          apply Finset.card_le_card
          intro y hy
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy ⊢
          rcases hy with ⟨x, rfl⟩
          rcases F.factors x with ⟨word, hword⟩
          exact ⟨word, hword.symm⟩
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = q ^ T := by
      simp only [Fintype.card_fun, Fintype.card_fin, Finset.card_univ]

/-- Any observer postprocessing of an action-factored boundary remains factored
through the same action word. -/
def postcompose [Fintype Input]
    {boundary : Input → Boundary} {T q : ℕ}
    (F : ActionWordFactorization boundary T q) (observe : Boundary → Feature) :
    ActionWordFactorization (fun x ↦ observe (boundary x)) T q where
  realize := fun word ↦ observe (F.realize word)
  factors := by
    intro x
    rcases F.factors x with ⟨word, hword⟩
    exact ⟨word, congrArg observe hword⟩

/-- Observer quotients cannot exceed the original action-word capacity. -/
theorem postprocessed_classRank_le_pow [Fintype Input]
    {boundary : Input → Boundary} {T q : ℕ}
    (F : ActionWordFactorization boundary T q) (observe : Boundary → Feature) :
    (F.postcompose observe).classRank ≤ q ^ T :=
  (F.postcompose observe).classRank_le_pow

end ActionWordFactorization

/-! ## General image-rank calibration -/

/-- A surjective finite family realizes every feature value. -/
theorem familyImageRank_eq_card_of_surjective
    [Fintype Input] [Fintype Feature]
    (feature : Input → Feature) (hsurj : Function.Surjective feature) :
    familyImageRank feature = Fintype.card Feature := by
  classical
  unfold familyImageRank
  have himage : Finset.univ.image feature = (Finset.univ : Finset Feature) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      exact hsurj y
  calc
    (Finset.univ.image feature).card = (Finset.univ : Finset Feature).card :=
      congrArg Finset.card himage
    _ = Fintype.card Feature := Finset.card_univ

/-! ## Exact binary calibration -/

/-- Every Boolean boundary, easy or hard, factors through one binary action
slot.  This is the action-holonomy version of the final-decision guardrail. -/
noncomputable def booleanBoundaryFactorization [Fintype Input]
    (answer : Input → Bool) :
    ActionWordFactorization answer 1 2 where
  realize := fun word ↦ finTwoEquiv (word 0)
  factors := by
    intro x
    refine ⟨fun _ ↦ finTwoEquiv.symm (answer x), ?_⟩
    simp

theorem booleanBoundary_classRank_le_two [Fintype Input]
    (answer : Input → Bool) :
    (booleanBoundaryFactorization answer).classRank ≤ 2 := by
  simpa using (booleanBoundaryFactorization answer).classRank_le_pow

/-! ## Natural expander/Tseitin residual: the conservation law is tight -/

variable {V Edge ι : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype Edge] [DecidableEq Edge]
variable [Fintype ι] [DecidableEq ι]

/-- The natural `r`-bit residual is represented by exactly `r` binary action
slots: one local letter per residual coordinate. -/
noncomputable def expanderResidualBinaryActions
    (G : TseitinGraph V Edge) (readSet : ι → V) :
    ActionWordFactorization
      (expanderResidualBits G readSet) (Fintype.card ι) 2 where
  realize := fun word i ↦ finTwoEquiv (word i)
  factors := by
    intro x
    refine ⟨fun i ↦ finTwoEquiv.symm
      (expanderResidualBits G readSet x i), ?_⟩
    funext i
    simp

/-- Expansion makes the action bound tight: all `2^r` composed residual
actions occur. -/
theorem expanderResidual_actionRank_eq_two_pow
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    (expanderResidualBinaryActions G readSet).classRank =
      2 ^ Fintype.card ι := by
  rw [ActionWordFactorization.classRank,
    familyImageRank_eq_card_of_surjective
      (expanderResidualBits G readSet)
      (expanderResidualBits_surjective G hc hexp readSet hread hmed)]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- Any binary non-local action representation of the full expander residual
needs at least `r` slots.  The explicit construction above attains equality. -/
theorem expanderResidual_binary_actions_force_width
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    {T : ℕ}
    (F : ActionWordFactorization (expanderResidualBits G readSet) T 2) :
    Fintype.card ι ≤ T := by
  have hlower : F.classRank = 2 ^ Fintype.card ι := by
    rw [ActionWordFactorization.classRank,
      familyImageRank_eq_card_of_surjective
        (expanderResidualBits G readSet)
        (expanderResidualBits_surjective G hc hexp readSet hread hmed)]
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  have hcapacity : 2 ^ Fintype.card ι ≤ 2 ^ T := by
    simpa [hlower] using F.classRank_le_pow
  exact (Nat.pow_le_pow_iff_right (by omega)).mp hcapacity

/-!
## Audit verdict

Non-local multiplicative/action holonomy has a clean conservation law: its
class count is multiplicative but its logarithmic rank is additive in action
length.  This genuinely removes dependence on one spatial crossing cut.

However, the concrete expander residual already has an exact length-`r` binary
representation.  Its `2^r` outcomes therefore do not force superpolynomial
action.  The remaining Route-G theorem must show that *genuine SAT continuation
semantics*, not merely the residual vector itself, requires superpolynomial
action rank for every polynomial solver while easy functions admit short action
words.  That is new lower-bound mathematics; it is not supplied by composition
or residual surjectivity alone.
-/

end PallLean.Paper93.DeepMath.PathB.NonLocalActionHolonomyConservation

#print axioms PallLean.Paper93.DeepMath.PathB.NonLocalActionHolonomyConservation.ActionWordFactorization.classRank_le_pow
#print axioms PallLean.Paper93.DeepMath.PathB.NonLocalActionHolonomyConservation.ActionWordFactorization.postprocessed_classRank_le_pow
#print axioms PallLean.Paper93.DeepMath.PathB.NonLocalActionHolonomyConservation.booleanBoundary_classRank_le_two
#print axioms PallLean.Paper93.DeepMath.PathB.NonLocalActionHolonomyConservation.expanderResidual_actionRank_eq_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.NonLocalActionHolonomyConservation.expanderResidual_binary_actions_force_width
