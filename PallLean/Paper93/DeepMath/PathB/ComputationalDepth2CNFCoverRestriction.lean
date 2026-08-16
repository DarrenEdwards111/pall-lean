import PallLean.Paper93.DeepMath.PathB.ComputationalDepth2CNFMatchingCoverCashout

/-!
# 2-CNF cover restriction semantics

This file supplies the semantic fact used by the small-cover arm.  A partial assignment deletes literals whose
variables it fixes; a clause already made true is marked satisfied.  If every width-two clause contains a variable
from the assigned cover, then every unsatisfied residual clause has at most one literal.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.XorCNFIdentityEmbedding

variable {n : ℕ}

/-- A partial Boolean assignment; `none` means the variable remains free. -/
abbrev PartialAssignment (n : ℕ) := Fin n → Option Bool

/-- A clause is already satisfied by the fixed part of a partial assignment. -/
def clauseSatisfied (ρ : PartialAssignment n) (clause : Finset (Literal n)) : Prop :=
  ∃ l ∈ clause, ρ l.1 = some l.2

/-- Literals left after deleting all fixed variables. -/
def residualClause (ρ : PartialAssignment n) (clause : Finset (Literal n)) : Finset (Literal n) :=
  clause.filter fun l => ρ l.1 = none

/-- Every cover variable is fixed by the partial assignment. -/
def AssignsCover (ρ : PartialAssignment n) (cover : Finset (Fin n)) : Prop :=
  ∀ v ∈ cover, ∃ b, ρ v = some b

/-- Every clause contains a literal whose variable belongs to the cover. -/
def LiteralCover (φ : CNF n) (cover : Finset (Fin n)) : Prop :=
  ∀ clause ∈ φ, ∃ l ∈ clause, l.1 ∈ cover

/-- **Cover restriction lemma (proved): surviving width-two clauses are unit or empty.** -/
theorem residualClause_card_le_one
    (φ : CNF n) (cover : Finset (Fin n)) (ρ : PartialAssignment n)
    (hwidth : ∀ clause ∈ φ, clause.card ≤ 2)
    (hcover : LiteralCover φ cover) (hassign : AssignsCover ρ cover)
    {clause : Finset (Literal n)} (hclause : clause ∈ φ) :
    (residualClause ρ clause).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  simp only [residualClause, Finset.mem_filter] at ha hb
  by_contra hab
  have hpCard : ({a, b} : Finset (Literal n)).card = 2 := by simp [hab]
  have hpSub : ({a, b} : Finset (Literal n)) ⊆ clause := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact ha.1
    · exact hb.1
  have hEq : ({a, b} : Finset (Literal n)) = clause :=
    Finset.eq_of_subset_of_card_le hpSub (by simpa [hpCard] using hwidth clause hclause)
  obtain ⟨l, hl, hlcover⟩ := hcover clause hclause
  have hlpair : l = a ∨ l = b := by
    have : l ∈ ({a, b} : Finset (Literal n)) := by simpa [hEq] using hl
    simpa using this
  obtain ⟨value, hvalue⟩ := hassign l.1 hlcover
  rcases hlpair with rfl | rfl
  · rw [ha.2] at hvalue
    contradiction
  · rw [hb.2] at hvalue
    contradiction

/-- A finite set of unit literals has no conflicting requirements on one variable. -/
def UnitConsistent (units : Finset (Literal n)) : Prop :=
  ∀ l₁ ∈ units, ∀ l₂ ∈ units, l₁.1 = l₂.1 → l₁.2 = l₂.2

/-- All unit requirements hold under an assignment. -/
def EvalUnits (x : Fin n → Bool) (units : Finset (Literal n)) : Prop :=
  ∀ l ∈ units, evalLiteral x l

/-- Canonical assignment chosen from a consistent unit set (arbitrary `false` off its support). -/
noncomputable def unitAssignment (units : Finset (Literal n)) : Fin n → Bool := fun i =>
  if h : ∃ b, (i, b) ∈ units then Classical.choose h else false

/-- The canonical assignment satisfies every consistent set of unit literals. -/
theorem unitAssignment_satisfies {units : Finset (Literal n)} (hconsistent : UnitConsistent units) :
    EvalUnits (unitAssignment units) units := by
  intro l hl
  unfold evalLiteral unitAssignment
  split
  · rename_i hex
    have hchosen : (l.1, Classical.choose hex) ∈ units := Classical.choose_spec hex
    exact hconsistent (l.1, Classical.choose hex) hchosen l hl rfl
  · rename_i hnone
    exact False.elim (hnone ⟨l.2, hl⟩)

/-- **General unit solver correctness (proved): consistency is exactly satisfiability.** -/
theorem unit_satisfiable_iff_consistent (units : Finset (Literal n)) :
    (∃ x, EvalUnits x units) ↔ UnitConsistent units := by
  constructor
  · rintro ⟨x, hx⟩ l₁ hl₁ l₂ hl₂ hvar
    have h₁ := hx l₁ hl₁
    have h₂ := hx l₂ hl₂
    unfold evalLiteral at h₁ h₂
    rw [hvar] at h₁
    exact h₁.symm.trans h₂
  · intro h
    exact ⟨unitAssignment units, unitAssignment_satisfies h⟩

end PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction

#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction.residualClause_card_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction.unit_satisfiable_iff_consistent
