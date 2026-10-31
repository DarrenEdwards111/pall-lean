import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResLinParityRestriction

/-!
# Restricted `Res(⊕)` instances

The local restriction algebra is useful for lower bounds only after it is lifted from individual
equations and clauses to an entire unsatisfiable instance.  This file supplies that semantic layer.

Given a partial assignment `ρ`, `complete ρ y` overwrites the fixed coordinates of an arbitrary
assignment `y`.  Restricted equations have zero coefficient on those coordinates, so their truth
value is invariant under completion.  Consequently an assignment satisfies all restricted
premises exactly when its completion satisfies all original premises.  In particular, every
restriction of an unsatisfiable instance is again unsatisfiable.

This is deliberately a semantic theorem.  Turning a checked dag refutation into a checked dag of
no greater size still requires syntactic pruning of restricted Boolean-axiom lines; that separate
step is where proof-complexity restrictions enter.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResLinParity

open Classical

/-- Complete a partial assignment, retaining the supplied values on free coordinates. -/
def complete {n : ℕ} (ρ : Restriction n) (y : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => (ρ i).getD (y i)

/-- Completion really extends the partial assignment. -/
theorem complete_extends {n : ℕ} (ρ : Restriction n) (y : Fin n → ZMod 2) :
    Extends (complete ρ y) ρ := by
  intro i v hiv
  simp [complete, hiv]

/-- A restricted equation has zero coefficient at every fixed coordinate. -/
theorem restrictEq_coeff_eq_zero_of_assigned {n : ℕ} (ρ : Restriction n)
    (e : Equation n) {i : Fin n} {v : ZMod 2} (hi : ρ i = some v) :
    (restrictEq ρ e).coeff i = 0 := by
  simp [restrictEq, hi]

/-- Completing an assignment cannot change the value of a restricted affine sum. -/
theorem restricted_sum_complete {n : ℕ} (ρ : Restriction n)
    (e : Equation n) (y : Fin n → ZMod 2) :
    (∑ i, (restrictEq ρ e).coeff i * complete ρ y i) =
      ∑ i, (restrictEq ρ e).coeff i * y i := by
  apply Finset.sum_congr rfl
  intro i _
  cases hi : ρ i with
  | none => simp [complete, hi]
  | some v => simp [complete, restrictEq, hi]

/-- Satisfaction of a residual equation is invariant under completion. -/
theorem satisfiesEq_restrict_complete_iff {n : ℕ} (ρ : Restriction n)
    (e : Equation n) (y : Fin n → ZMod 2) :
    SatisfiesEq (complete ρ y) (restrictEq ρ e) ↔
      SatisfiesEq y (restrictEq ρ e) := by
  simp only [SatisfiesEq]
  rw [restricted_sum_complete]

/-- Satisfaction of a residual clause is invariant under completion. -/
theorem satisfiesClause_restrict_complete_iff {n : ℕ} (ρ : Restriction n)
    (C : Clause n) (y : Fin n → ZMod 2) :
    SatisfiesClause (complete ρ y) (restrictClause ρ C) ↔
      SatisfiesClause y (restrictClause ρ C) := by
  constructor
  · rintro ⟨e', he', hsat⟩
    rw [restrictClause, Finset.mem_image] at he'
    rcases he' with ⟨e, he, rfl⟩
    exact ⟨restrictEq ρ e, Finset.mem_image.mpr ⟨e, he, rfl⟩,
      (satisfiesEq_restrict_complete_iff ρ e y).mp hsat⟩
  · rintro ⟨e', he', hsat⟩
    rw [restrictClause, Finset.mem_image] at he'
    rcases he' with ⟨e, he, rfl⟩
    exact ⟨restrictEq ρ e, Finset.mem_image.mpr ⟨e, he, rfl⟩,
      (satisfiesEq_restrict_complete_iff ρ e y).mpr hsat⟩

/-- Apply a restriction to every premise of an instance. -/
def restrictPremises {n : ℕ} (ρ : Restriction n) (Γ : Finset (Clause n)) :
    Finset (Clause n) :=
  Γ.image (restrictClause ρ)

/-- **Exact residual-instance semantics.**  A total assignment satisfies the restricted instance
iff its completion satisfies the original instance. -/
theorem models_restrictPremises_iff {n : ℕ} (ρ : Restriction n)
    (Γ : Finset (Clause n)) (y : Fin n → ZMod 2) :
    Models y (restrictPremises ρ Γ) ↔ Models (complete ρ y) Γ := by
  constructor
  · intro h C hC
    have hr : SatisfiesClause y (restrictClause ρ C) :=
      h _ (Finset.mem_image.mpr ⟨C, hC, rfl⟩)
    have hrc : SatisfiesClause (complete ρ y) (restrictClause ρ C) :=
      (satisfiesClause_restrict_complete_iff ρ C y).mpr hr
    exact (satisfiesClause_restrict_iff ρ C (complete ρ y) (complete_extends ρ y)).mp hrc
  · intro h RC hRC
    rw [restrictPremises, Finset.mem_image] at hRC
    rcases hRC with ⟨C, hC, rfl⟩
    have horig : SatisfiesClause (complete ρ y) C := h C hC
    have hrc : SatisfiesClause (complete ρ y) (restrictClause ρ C) :=
      (satisfiesClause_restrict_iff ρ C (complete ρ y) (complete_extends ρ y)).mpr horig
    exact (satisfiesClause_restrict_complete_iff ρ C y).mp hrc

/-- **Restriction preserves unsatisfiability.**  This is the semantic foundation for random
restriction arguments on lifted-Tseitin instances. -/
theorem restrictPremises_unsat {n : ℕ} {Γ : Finset (Clause n)}
    (hΓ : ¬ ∃ x : Fin n → ZMod 2, Models x Γ) (ρ : Restriction n) :
    ¬ ∃ y : Fin n → ZMod 2, Models y (restrictPremises ρ Γ) := by
  rintro ⟨y, hy⟩
  exact hΓ ⟨complete ρ y, (models_restrictPremises_iff ρ Γ y).mp hy⟩

#print axioms complete_extends
#print axioms models_restrictPremises_iff
#print axioms restrictPremises_unsat

end PallLean.Paper93.DeepMath.PathB.ResLinParity
