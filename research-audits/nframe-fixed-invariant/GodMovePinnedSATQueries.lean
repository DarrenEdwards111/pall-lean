import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATVerifierSpec

/-!
# A faithful, assignment-pinned SAT query handshake

Adding one unit clause for each of a formula's variables turns satisfiability
into evaluation at that specified assignment.  Consequently an actual machine
deciding `SeparationTarget.SATLang` agrees with formula evaluation on these
concretely encoded queries, for every assignment.

This is a semantic theorem about a family of different machine inputs.  It
asserts neither rank-monotone extraction from a fixed-input compiler polynomial
nor a polynomial bound on a common derivative span.  In particular, agreement
on all Boolean assignments is not equality of arbitrary ambient polynomials.
-/

namespace GodMovePinnedSATQueries

open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.SeparationTarget (SATLang SATLang_encode)
open PallLean.Paper93.DeepMath.PathB.SATVerifierSpec (evalFormula_congr)

/-- Extend an `n`-bit assignment by `false` at all other variable indices. -/
def extendAssignment {n : ℕ} (a : Fin n → Bool) : ℕ → Bool :=
  fun i => if hi : i < n then a ⟨i, hi⟩ else false

@[simp] theorem extendAssignment_fin {n : ℕ} (a : Fin n → Bool) (i : Fin n) :
    extendAssignment a i.val = a i := by
  simp [extendAssignment, i.isLt]

/-- Every variable index actually occurring in the formula is below `n`. -/
def VariablesBelow (n : ℕ) (φ : Formula) : Prop :=
  ∀ c ∈ φ, ∀ l ∈ c, l.1 < n

/-- The concrete unit clauses pinning every one of the first `n` variables. -/
def assignmentUnits {n : ℕ} (a : Fin n → Bool) : Formula :=
  (List.finRange n).map fun i => [(i.val, a i)]

/-- The original formula with all its relevant variables pinned. -/
def pinnedFormula {n : ℕ} (φ : Formula) (a : Fin n → Bool) : Formula :=
  φ ++ assignmentUnits a

theorem eval_assignmentUnits_iff {n : ℕ} (a : Fin n → Bool) (b : ℕ → Bool) :
    evalFormula b (assignmentUnits a) = true ↔ ∀ i : Fin n, b i.val = a i := by
  simp [assignmentUnits, evalFormula, List.all_eq_true, evalClause, evalLit]

theorem eval_pinnedFormula_iff {n : ℕ} (φ : Formula) (a : Fin n → Bool)
    (b : ℕ → Bool) :
    evalFormula b (pinnedFormula φ a) = true ↔
      evalFormula b φ = true ∧ ∀ i : Fin n, b i.val = a i := by
  simp only [pinnedFormula, evalFormula, List.all_append, Bool.and_eq_true]
  exact and_congr Iff.rfl (eval_assignmentUnits_iff a b)

/-- Pinning all occurring variables removes precisely the existential freedom
in satisfiability, leaving evaluation at the chosen assignment. -/
theorem satisfiable_pinnedFormula_iff {n : ℕ} (φ : Formula)
    (hvars : VariablesBelow n φ) (a : Fin n → Bool) :
    Satisfiable (pinnedFormula φ a) ↔
      evalFormula (extendAssignment a) φ = true := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨hφ, hpin⟩ := (eval_pinnedFormula_iff φ a b).mp hb
    have heq : evalFormula b φ = evalFormula (extendAssignment a) φ := by
      apply evalFormula_congr
      intro c hc l hl
      have hi := hvars c hc l hl
      exact (hpin ⟨l.1, hi⟩).trans (extendAssignment_fin a ⟨l.1, hi⟩).symm
    rw [← heq]
    exact hφ
  · intro hφ
    refine ⟨extendAssignment a, (eval_pinnedFormula_iff φ a _).mpr ⟨hφ, ?_⟩⟩
    intro i
    exact extendAssignment_fin a i

/-- The actual clocked output on the faithful encoding of a pinned formula. -/
def queryOutput {n : ℕ} (M : Machine) (T : ℕ → ℕ) (φ : Formula)
    (a : Fin n → Bool) : Bool :=
  decideOut M (encodeFormula' (pinnedFormula φ a))
    (T (encodeFormula' (pinnedFormula φ a)).length)

/-- An operational SAT decider and concrete pinning agree with evaluation for
every assignment.  No polynomial identity or rank inequality is assumed. -/
theorem queryOutput_eq_eval {n : ℕ} (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) (φ : Formula)
    (hvars : VariablesBelow n φ) (a : Fin n → Bool) :
    queryOutput M T φ a = evalFormula (extendAssignment a) φ := by
  have hout := (hD (encodeFormula' (pinnedFormula φ a))).2
  change queryOutput M T φ a = SATLang (encodeFormula' (pinnedFormula φ a)) at hout
  rw [hout]
  have hiff := (SATLang_encode (pinnedFormula φ a)).trans
    (satisfiable_pinnedFormula_iff φ hvars a)
  cases hq : SATLang (encodeFormula' (pinnedFormula φ a)) <;>
    cases he : evalFormula (extendAssignment a) φ <;> simp_all

end GodMovePinnedSATQueries

#print axioms GodMovePinnedSATQueries.extendAssignment_fin
#print axioms GodMovePinnedSATQueries.eval_assignmentUnits_iff
#print axioms GodMovePinnedSATQueries.eval_pinnedFormula_iff
#print axioms GodMovePinnedSATQueries.satisfiable_pinnedFormula_iff
#print axioms GodMovePinnedSATQueries.queryOutput_eq_eval
