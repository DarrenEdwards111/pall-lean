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

/-- A total assignment agrees with every value fixed by `ρ`. -/
def Completes (ρ : PartialAssignment n) (x : Fin n → Bool) : Prop :=
  ∀ v b, ρ v = some b → x v = b

/-- Delete satisfied clauses and retain only free literals in every other clause. -/
noncomputable def residualCNF (ρ : PartialAssignment n) (φ : CNF n) : CNF n :=
  (φ.filter fun clause => ¬clauseSatisfied ρ clause).image (residualClause ρ)

/-- Under a completion, an unsatisfied original clause is equivalent to its residual clause. -/
theorem evalClause_iff_residualClause
    (ρ : PartialAssignment n) (x : Fin n → Bool) (clause : Finset (Literal n))
    (hcomplete : Completes ρ x) (hunsat : ¬clauseSatisfied ρ clause) :
    evalClause x clause ↔ evalClause x (residualClause ρ clause) := by
  constructor
  · rintro ⟨l, hl, hxl⟩
    have hfree : ρ l.1 = none := by
      cases hρ : ρ l.1 with
      | none => rfl
      | some b =>
          have hxb : x l.1 = b := hcomplete l.1 b hρ
          have : b = l.2 := hxb.symm.trans hxl
          exact False.elim (hunsat ⟨l, hl, by simpa [this] using hρ⟩)
    exact ⟨l, by simp [residualClause, hl, hfree], hxl⟩
  · rintro ⟨l, hl, hxl⟩
    exact ⟨l, (Finset.mem_filter.mp hl).1, hxl⟩

/-- **Residual-CNF correctness (proved): restriction preserves semantics under every completion.** -/
theorem evalCNF_iff_residualCNF
    (ρ : PartialAssignment n) (x : Fin n → Bool) (φ : CNF n)
    (hcomplete : Completes ρ x) :
    evalCNF x φ ↔ evalCNF x (residualCNF ρ φ) := by
  constructor
  · intro hx residual hresidual
    simp only [residualCNF, Finset.mem_image] at hresidual
    obtain ⟨clause, hclause, rfl⟩ := hresidual
    have hcMem : clause ∈ φ := (Finset.mem_filter.mp hclause).1
    have hcUnsat : ¬clauseSatisfied ρ clause := (Finset.mem_filter.mp hclause).2
    exact (evalClause_iff_residualClause ρ x clause hcomplete hcUnsat).mp (hx clause hcMem)
  · intro hx clause hclause
    by_cases hsatisfied : clauseSatisfied ρ clause
    · obtain ⟨l, hl, hρl⟩ := hsatisfied
      exact ⟨l, hl, hcomplete l.1 l.2 hρl⟩
    · have hmem : residualClause ρ clause ∈ residualCNF ρ φ := by
        apply Finset.mem_image.mpr
        exact ⟨clause, Finset.mem_filter.mpr ⟨hclause, hsatisfied⟩, rfl⟩
      exact (evalClause_iff_residualClause ρ x clause hcomplete hsatisfied).mpr
        (hx (residualClause ρ clause) hmem)

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

/-- A CNF leaf is genuinely unit: every clause is nonempty and has at most one literal. -/
def IsUnitLeaf (ψ : CNF n) : Prop :=
  ∀ clause ∈ ψ, clause.Nonempty ∧ clause.card ≤ 1

/-- All literals occurring in a unit leaf. -/
def leafUnits (ψ : CNF n) : Finset (Literal n) := ψ.biUnion id

/-- A unit leaf is equivalent to the conjunction of its collected unit literals. -/
theorem evalCNF_iff_evalUnits_of_unitLeaf
    (ψ : CNF n) (hunit : IsUnitLeaf ψ) (x : Fin n → Bool) :
    evalCNF x ψ ↔ EvalUnits x (leafUnits ψ) := by
  constructor
  · intro hx l hl
    simp only [leafUnits, Finset.mem_biUnion] at hl
    obtain ⟨clause, hcψ, hlc⟩ := hl
    obtain ⟨w, hwc, hxw⟩ := hx clause hcψ
    have hlw : l = w := Finset.card_le_one_iff.mp (hunit clause hcψ).2 hlc hwc
    simpa [hlw] using hxw
  · intro hx clause hcψ
    obtain ⟨l, hlc⟩ := (hunit clause hcψ).1
    have hlu : l ∈ leafUnits ψ := by
      apply Finset.mem_biUnion.mpr
      exact ⟨clause, hcψ, hlc⟩
    exact ⟨l, hlc, hx l hlu⟩

/-- **Unit-leaf solver correctness (proved).** -/
theorem unitLeaf_satisfiable_iff_consistent (ψ : CNF n) (hunit : IsUnitLeaf ψ) :
    (∃ x, evalCNF x ψ) ↔ UnitConsistent (leafUnits ψ) := by
  rw [show (∃ x, evalCNF x ψ) ↔ ∃ x, EvalUnits x (leafUnits ψ) by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (evalCNF_iff_evalUnits_of_unitLeaf ψ hunit x).mp hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (evalCNF_iff_evalUnits_of_unitLeaf ψ hunit x).mpr hx⟩]
  exact unit_satisfiable_iff_consistent (leafUnits ψ)

/-- Merge fixed values from `ρ` with an assignment on the remaining free variables. -/
def mergeAssignment (ρ : PartialAssignment n) (free : Fin n → Bool) : Fin n → Bool := fun i =>
  match ρ i with
  | some b => b
  | none => free i

theorem mergeAssignment_completes (ρ : PartialAssignment n) (free : Fin n → Bool) :
    Completes ρ (mergeAssignment ρ free) := by
  intro v b hv
  simp [mergeAssignment, hv]

/-- Every literal occurring in a residual CNF is on a genuinely free variable. -/
theorem residualCNF_literal_free
    (ρ : PartialAssignment n) (φ : CNF n)
    {clause : Finset (Literal n)} (hc : clause ∈ residualCNF ρ φ)
    {l : Literal n} (hl : l ∈ clause) : ρ l.1 = none := by
  simp only [residualCNF, Finset.mem_image] at hc
  obtain ⟨source, -, rfl⟩ := hc
  exact (Finset.mem_filter.mp hl).2

/-- Merging fixed values cannot change evaluation of residual clauses. -/
theorem evalCNF_mergeAssignment_residual_iff
    (ρ : PartialAssignment n) (φ : CNF n) (free : Fin n → Bool) :
    evalCNF (mergeAssignment ρ free) (residualCNF ρ φ) ↔
      evalCNF free (residualCNF ρ φ) := by
  constructor
  · intro hx clause hc
    obtain ⟨l, hl, hval⟩ := hx clause hc
    refine ⟨l, hl, ?_⟩
    simpa [evalLiteral, mergeAssignment, residualCNF_literal_free ρ φ hc hl] using hval
  · intro hx clause hc
    obtain ⟨l, hl, hval⟩ := hx clause hc
    refine ⟨l, hl, ?_⟩
    simpa [evalLiteral, mergeAssignment, residualCNF_literal_free ρ φ hc hl] using hval

/-- The cover hypothesis makes every clause in the residual CNF have size at most one. -/
theorem residualCNF_clause_card_le_one
    (φ : CNF n) (cover : Finset (Fin n)) (ρ : PartialAssignment n)
    (hwidth : ∀ clause ∈ φ, clause.card ≤ 2)
    (hcover : LiteralCover φ cover) (hassign : AssignsCover ρ cover)
    {residual : Finset (Literal n)} (hresidual : residual ∈ residualCNF ρ φ) :
    residual.card ≤ 1 := by
  simp only [residualCNF, Finset.mem_image] at hresidual
  obtain ⟨source, hsource, rfl⟩ := hresidual
  exact residualClause_card_le_one φ cover ρ hwidth hcover hassign
    (Finset.mem_filter.mp hsource).1

/-- Executable logical condition checked at a cover branch. -/
def CoverLeafAccepts (ρ : PartialAssignment n) (φ : CNF n) : Prop :=
  (∀ clause ∈ residualCNF ρ φ, clause.Nonempty) ∧
    UnitConsistent (leafUnits (residualCNF ρ φ))

/-- **End-to-end cover-branch correctness (proved).** -/
theorem coverLeafAccepts_iff
    (φ : CNF n) (cover : Finset (Fin n)) (ρ : PartialAssignment n)
    (hwidth : ∀ clause ∈ φ, clause.card ≤ 2)
    (hcover : LiteralCover φ cover) (hassign : AssignsCover ρ cover) :
    CoverLeafAccepts ρ φ ↔ ∃ x, Completes ρ x ∧ evalCNF x φ := by
  let ψ := residualCNF ρ φ
  have hcard : ∀ clause ∈ ψ, clause.card ≤ 1 := by
    intro clause hc
    exact residualCNF_clause_card_le_one φ cover ρ hwidth hcover hassign hc
  constructor
  · rintro ⟨hnonempty, hconsistent⟩
    have hunit : IsUnitLeaf ψ := fun clause hc => ⟨hnonempty clause hc, hcard clause hc⟩
    obtain ⟨free, hfree⟩ := (unitLeaf_satisfiable_iff_consistent ψ hunit).mpr hconsistent
    let x := mergeAssignment ρ free
    refine ⟨x, mergeAssignment_completes ρ free, ?_⟩
    apply (evalCNF_iff_residualCNF ρ x φ (mergeAssignment_completes ρ free)).mpr
    exact (evalCNF_mergeAssignment_residual_iff ρ φ free).mpr hfree
  · rintro ⟨x, hcomplete, hx⟩
    have hψ : evalCNF x ψ := (evalCNF_iff_residualCNF ρ x φ hcomplete).mp hx
    have hnonempty : ∀ clause ∈ ψ, clause.Nonempty := by
      intro clause hc
      obtain ⟨l, hl, -⟩ := hψ clause hc
      exact ⟨l, hl⟩
    have hunit : IsUnitLeaf ψ := fun clause hc => ⟨hnonempty clause hc, hcard clause hc⟩
    exact ⟨hnonempty, (unitLeaf_satisfiable_iff_consistent ψ hunit).mp ⟨x, hψ⟩⟩

end PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction

#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction.residualClause_card_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction.unit_satisfiable_iff_consistent
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction.evalCNF_iff_residualCNF
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction.unitLeaf_satisfiable_iff_consistent
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction.coverLeafAccepts_iff
