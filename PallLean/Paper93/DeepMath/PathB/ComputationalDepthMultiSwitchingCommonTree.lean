import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseAdapter

/-!
# Common decision-tree carrier for multi-switching

The ordinary simultaneous switching API stores one independent canonical tree per gate and unions
their bad events.  A reusable multi-switching lemma instead needs one common query tree whose leaves
carry the residual state of every gate.  This file introduces that missing representation without
assuming a counting theorem.

`CommonTree n α` is a decision tree with an arbitrary leaf payload.  Its monadic `bind` operation
refines every leaf by another query tree.  `commonRefine` uses this operation to combine a list of
Boolean decision trees into one tree whose reached leaf is exactly the list of all their outputs.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching

/-- A query tree with data of type `α` at each leaf. -/
inductive CommonTree (n : ℕ) (α : Type) where
  | leaf : α → CommonTree n α
  | query : Fin n → CommonTree n α → CommonTree n α → CommonTree n α

namespace CommonTree

/-- The payload reached by a complete assignment. -/
def run {n : ℕ} {α : Type} : CommonTree n α → (Fin n → Bool) → α
  | .leaf a, _ => a
  | .query i lo hi, x => if x i then run hi x else run lo x

/-- Replace every leaf by a further common query tree. -/
def bind {n : ℕ} {α β : Type} : CommonTree n α → (α → CommonTree n β) → CommonTree n β
  | .leaf a, f => f a
  | .query i lo hi, f => .query i (bind lo f) (bind hi f)

@[simp] theorem run_leaf {n : ℕ} {α : Type} (a : α) (x : Fin n → Bool) :
    run (.leaf a : CommonTree n α) x = a := rfl

@[simp] theorem run_query {n : ℕ} {α : Type} (i : Fin n)
    (lo hi : CommonTree n α) (x : Fin n → Bool) :
    run (.query i lo hi) x = if x i then run hi x else run lo x := rfl

/-- Executing a refined tree first reaches an old leaf and then executes its replacement. -/
theorem run_bind {n : ℕ} {α β : Type} (t : CommonTree n α)
    (f : α → CommonTree n β) (x : Fin n → Bool) :
    run (bind t f) x = run (f (run t x)) x := by
  induction t with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      simp only [bind, run]
      by_cases h : x i <;> simp [h, ihlo, ihhi]

/-- Regard an ordinary Boolean decision tree as a common tree with Boolean leaves. -/
def ofBool {n : ℕ} : BoolDecisionTree n → CommonTree n Bool
  | .leaf b => .leaf b
  | .query i lo hi => .query i (ofBool lo) (ofBool hi)

theorem run_ofBool {n : ℕ} (t : BoolDecisionTree n) (x : Fin n → Bool) :
    run (ofBool t) x = t.eval x := by
  induction t with
  | leaf b => rfl
  | query i lo hi ihlo ihhi =>
      simp only [ofBool, run, BoolDecisionTree.eval]
      by_cases h : x i <;> simp [h, ihlo, ihhi]

/-- Sequential common refinement of a finite family.  The payload order matches the input list. -/
def commonRefine {n : ℕ} : List (BoolDecisionTree n) → CommonTree n (List Bool)
  | [] => .leaf []
  | t :: ts => bind (ofBool t) fun b =>
      bind (commonRefine ts) fun bs => .leaf (b :: bs)

/-- The common tree records every member tree's value at the same assignment. -/
theorem run_commonRefine {n : ℕ} (ts : List (BoolDecisionTree n)) (x : Fin n → Bool) :
    run (commonRefine ts) x = ts.map (fun t => t.eval x) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [commonRefine, run_bind, run_ofBool, run_leaf, List.map_cons]
      rw [ih]

/-- Indexed-family form used by padded bottom-gate enumerations. -/
def commonRefineFin {n G : ℕ} (trees : Fin G → BoolDecisionTree n) :
    CommonTree n (Fin G → Bool) :=
  bind (commonRefine (List.ofFn trees)) fun values =>
    .leaf fun g => values.getD g.1 false

theorem run_commonRefineFin {n G : ℕ} (trees : Fin G → BoolDecisionTree n)
    (x : Fin n → Bool) (g : Fin G) :
    run (commonRefineFin trees) x g = (trees g).eval x := by
  simp only [commonRefineFin, run_bind, run_leaf, run_commonRefine]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

end CommonTree

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

/-- The exact common refinement of every canonical bottom-gate tree. -/
def canonicalFamilyTree {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) : CommonTree n (Fin G → Bool) :=
  CommonTree.commonRefineFin fun g => canonicalDT (gates g) fuel σ

/-- One common-tree execution simultaneously returns every canonical gate value. -/
theorem run_canonicalFamilyTree {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) (g : Fin G) :
    CommonTree.run (canonicalFamilyTree gates fuel σ) x g =
      (canonicalDT (gates g) fuel σ).eval x :=
  CommonTree.run_commonRefineFin _ x g

/-- With sufficient fuel, the common leaf payload is the vector of genuine DNF values on every
assignment extending the base restriction. -/
theorem run_canonicalFamilyTree_eq_dnf {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hstars : stars σ ≤ fuel) (hext : Rung4Restriction.Extends σ x)
    (g : Fin G) :
    CommonTree.run (canonicalFamilyTree gates fuel σ) x g = dnfEval (gates g) x := by
  rw [run_canonicalFamilyTree]
  exact canonicalDT_eval fuel σ x hstars hext

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_bind
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_commonRefine
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_commonRefineFin
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.run_canonicalFamilyTree_eq_dnf
