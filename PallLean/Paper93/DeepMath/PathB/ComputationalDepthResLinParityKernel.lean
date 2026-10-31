import Mathlib.Data.ZMod.Basic

/-!
# Resolution over parities: semantic kernel

This file starts the stronger-proof-system programme with the exact local object used by
`Res(⊕)`: clauses are disjunctions of affine equations over `𝔽₂`.  It defines the Boolean axioms,
weakening, deletion of a false constant equation, and the linear-resolution rule, then proves every
derivation sound and every derivation of the empty clause a genuine refutation.

The rules follow Raz--Tzameret, *Resolution over Linear Equations and Multilinear Proofs*,
Definition 3.1 (APAL 2008), specialized to characteristic two.  This is the proof-system substrate,
not a lower bound.  In particular, unrestricted dag-like super-polynomial size lower bounds for
`Res(⊕)` remain open; current lower bounds impose restrictions such as bounded proof depth.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResLinParity

open Classical BigOperators

/-- An affine equation `∑ᵢ aᵢxᵢ = b` over `𝔽₂`. -/
structure Equation (n : ℕ) where
  coeff : Fin n → ZMod 2
  rhs : ZMod 2
  deriving DecidableEq

@[ext]
theorem Equation.ext {n : ℕ} {e f : Equation n}
    (hcoeff : ∀ i, e.coeff i = f.coeff i) (hrhs : e.rhs = f.rhs) : e = f := by
  cases e
  cases f
  congr
  funext i
  exact hcoeff i

/-- A `Res(⊕)` line is a finite disjunction of affine equations. -/
abbrev Clause (n : ℕ) := Finset (Equation n)

/-- Evaluation of an affine equation on a Boolean (`𝔽₂`) assignment. -/
def SatisfiesEq {n : ℕ} (x : Fin n → ZMod 2) (e : Equation n) : Prop :=
  ∑ i, e.coeff i * x i = e.rhs

/-- Evaluation of a disjunction of affine equations. -/
def SatisfiesClause {n : ℕ} (x : Fin n → ZMod 2) (C : Clause n) : Prop :=
  ∃ e ∈ C, SatisfiesEq x e

/-- An assignment models every initial line. -/
def Models {n : ℕ} (x : Fin n → ZMod 2) (Γ : Finset (Clause n)) : Prop :=
  ∀ C ∈ Γ, SatisfiesClause x C

/-- Addition of equations, the characteristic-two form of both the `+` and `-` rules. -/
def Equation.add {n : ℕ} (e f : Equation n) : Equation n where
  coeff i := e.coeff i + f.coeff i
  rhs := e.rhs + f.rhs

/-- The Boolean axiom `(xᵢ = 0) ∨ (xᵢ = 1)`. -/
def booleanAxiom (n : ℕ) (i : Fin n) : Clause n :=
  {⟨fun j => if j = i then 1 else 0, 0⟩,
   ⟨fun j => if j = i then 1 else 0, 1⟩}

/-- The contradictory constant equation `0 = b`. -/
def falseConstant (n : ℕ) (b : ZMod 2) : Equation n :=
  ⟨fun _ => 0, b⟩

/-- Every `𝔽₂` assignment satisfies every Boolean axiom. -/
theorem booleanAxiom_valid {n : ℕ} (x : Fin n → ZMod 2) (i : Fin n) :
    SatisfiesClause x (booleanAxiom n i) := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (x i) with hi | hi
  · refine ⟨⟨fun j => if j = i then 1 else 0, 0⟩, by simp [booleanAxiom], ?_⟩
    simp [SatisfiesEq, hi]
  · refine ⟨⟨fun j => if j = i then 1 else 0, 1⟩, by simp [booleanAxiom], ?_⟩
    simp [SatisfiesEq, hi]

/-- Adding two true equations yields a true equation. -/
theorem Equation.satisfies_add {n : ℕ} (x : Fin n → ZMod 2) (e f : Equation n)
    (he : SatisfiesEq x e) (hf : SatisfiesEq x f) :
    SatisfiesEq x (e.add f) := by
  simp only [SatisfiesEq, Equation.add]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, he, hf]

/-- A nonzero false constant equation is never satisfied. -/
theorem not_satisfies_falseConstant {n : ℕ} (x : Fin n → ZMod 2) {b : ZMod 2}
    (hb : b ≠ 0) :
    ¬ SatisfiesEq x (falseConstant n b) := by
  simp only [SatisfiesEq, falseConstant, zero_mul, Finset.sum_const_zero]
  exact fun h => hb h.symm

/-- Derivability in the local `Res(⊕)` kernel.  Sharing and proof-size accounting are intentionally
left to the subsequent dag layer; these constructors are exactly the semantic inference rules that
that layer must validate. -/
inductive Derivation {n : ℕ} (Γ : Finset (Clause n)) : Clause n → Prop
  | premise {C : Clause n} (hC : C ∈ Γ) : Derivation Γ C
  | boolean (i : Fin n) : Derivation Γ (booleanAxiom n i)
  | weaken {C : Clause n} (d : Derivation Γ C) (e : Equation n) :
      Derivation Γ (insert e C)
  | simplify {C : Clause n} {b : ZMod 2} (hb : b ≠ 0)
      (d : Derivation Γ (insert (falseConstant n b) C)) : Derivation Γ C
  | linearResolve {C D : Clause n} {e f : Equation n}
      (left : Derivation Γ (insert e C)) (right : Derivation Γ (insert f D)) :
      Derivation Γ (insert (e.add f) (C ∪ D))

/-- Every line derived by the kernel is a semantic consequence of the premises. -/
theorem derivation_sound {n : ℕ} {Γ : Finset (Clause n)} {C : Clause n}
    (d : Derivation Γ C) (x : Fin n → ZMod 2) (hΓ : Models x Γ) :
    SatisfiesClause x C := by
  induction d with
  | premise hC => exact hΓ _ hC
  | boolean i => exact booleanAxiom_valid x i
  | weaken d e ih =>
      rcases ih with ⟨f, hf, hsat⟩
      exact ⟨f, Finset.mem_insert_of_mem hf, hsat⟩
  | simplify hb d ih =>
      rcases ih with ⟨e, he, hsat⟩
      rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · exact False.elim ((not_satisfies_falseConstant x hb) hsat)
      · exact ⟨e, he, hsat⟩
  | linearResolve left right ihLeft ihRight =>
      rcases ihLeft with ⟨g, hg, hgsat⟩
      rcases ihRight with ⟨h, hh, hhsat⟩
      rw [Finset.mem_insert] at hg hh
      rcases hg with rfl | hg
      · rcases hh with rfl | hh
        · exact ⟨_, Finset.mem_insert_self _ _, Equation.satisfies_add x _ _ hgsat hhsat⟩
        · exact ⟨h, Finset.mem_insert_of_mem (Finset.mem_union_right _ hh), hhsat⟩
      · exact ⟨g, Finset.mem_insert_of_mem (Finset.mem_union_left _ hg), hgsat⟩

/-- Deriving the empty clause certifies that the initial collection is unsatisfiable. -/
theorem refutation_unsat {n : ℕ} {Γ : Finset (Clause n)}
    (refute : Derivation Γ (∅ : Clause n)) :
    ¬ ∃ x : Fin n → ZMod 2, Models x Γ := by
  rintro ⟨x, hx⟩
  rcases derivation_sound refute x hx with ⟨e, he, _⟩
  simp at he

#print axioms derivation_sound
#print axioms refutation_unsat

end PallLean.Paper93.DeepMath.PathB.ResLinParity
