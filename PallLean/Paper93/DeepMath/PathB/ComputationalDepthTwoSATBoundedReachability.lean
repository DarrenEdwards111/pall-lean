import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTwoSATSCCLinearBudget

/-!
# Executable bounded reachability kernel for the 2-SAT implication graph

This file starts the certified traversal implementation without relying on Mathlib's unverified meta-level Tarjan
routine.  `ReachWithin edges fuel a b` is a finite, decidable search predicate.  It is sound for semantic implication
reachability, and every semantic reachability proof is found at some finite fuel.

The remaining step toward a total SCC decider is the finite-cutoff theorem: on the `2n` literal vertices, fuel
`2n-1` suffices after cycle deletion.  That theorem, followed by a work-efficient implementation, is intentionally not
assumed here.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoSATBoundedReachability

open Relation
open PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT
open PallLean.Paper93.DeepMath.PathB.TwoSATSCCLinearBudget

variable {n : ℕ}

/-- A path of at most `fuel` explicit edge-list steps. -/
def ReachWithin (edges : List (Lit n × Lit n)) : ℕ → Lit n → Lit n → Prop
  | 0, a, b => a = b
  | fuel + 1, a, b =>
      a = b ∨ ∃ e ∈ edges, ReachWithin edges fuel a e.1 ∧ e.2 = b

instance reachWithinDecidable (edges : List (Lit n × Lit n)) (fuel : ℕ) (a b : Lit n) :
    Decidable (ReachWithin edges fuel a b) := by
  induction fuel generalizing a b with
  | zero => simp [ReachWithin]; infer_instance
  | succ fuel ih =>
      simp only [ReachWithin]
      infer_instance

/-- Executable Boolean wrapper around bounded reachability. -/
def boundedReach (edges : List (Lit n × Lit n)) (fuel : ℕ) (a b : Lit n) : Bool :=
  decide (ReachWithin edges fuel a b)

theorem boundedReach_eq_true_iff (edges : List (Lit n × Lit n)) (fuel : ℕ) (a b : Lit n) :
    boundedReach edges fuel a b = true ↔ ReachWithin edges fuel a b := by
  simp [boundedReach]

/-- More fuel never loses a path. -/
theorem reachWithin_mono
    {edges : List (Lit n × Lit n)} {fuel : ℕ} {a b : Lit n}
    (h : ReachWithin edges fuel a b) : ReachWithin edges (fuel + 1) a b := by
  induction fuel generalizing a b with
  | zero =>
      left
      exact h
  | succ fuel ih =>
      rcases h with rfl | ⟨e, he, hprefix, heb⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨e, he, ih hprefix, heb⟩

/-- Bounded executable paths are sound for the semantic implication reachability relation. -/
theorem reachWithin_sound
    (cls : List (Clause n)) {fuel : ℕ} {a b : Lit n}
    (h : ReachWithin (implicationEdges cls) fuel a b) : Reach cls a b := by
  induction fuel generalizing a b with
  | zero =>
      have hab : a = b := h
      subst b
      exact ReflTransGen.refl
  | succ fuel ih =>
      rcases h with rfl | ⟨e, he, hprefix, heb⟩
      · exact ReflTransGen.refl
      · subst heb
        exact ReflTransGen.tail (ih hprefix) ((mem_implicationEdges_iff cls e.1 e.2).mp he)

/-- Every semantic reachability proof is witnessed by some finite executable fuel. -/
theorem reach_exists_fuel
    (cls : List (Clause n)) {a b : Lit n} (h : Reach cls a b) :
    ∃ fuel, ReachWithin (implicationEdges cls) fuel a b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
      obtain ⟨fuel, hfuel⟩ := ih
      refine ⟨fuel + 1, Or.inr ⟨(_, _), ?_, hfuel, rfl⟩⟩
      exact (mem_implicationEdges_iff cls _ _).mpr hbc

/-- A bounded mutual-reachability witness is already a genuine SCC witness. -/
theorem bounded_mutual_reach_sound
    (cls : List (Clause n)) (fuel : ℕ) (l : Lit n)
    (hforward : boundedReach (implicationEdges cls) fuel l (neg l) = true)
    (hbackward : boundedReach (implicationEdges cls) fuel (neg l) l = true) :
    Reach cls l (neg l) ∧ Reach cls (neg l) l := by
  exact ⟨reachWithin_sound cls ((boundedReach_eq_true_iff _ _ _ _).mp hforward),
    reachWithin_sound cls ((boundedReach_eq_true_iff _ _ _ _).mp hbackward)⟩

end PallLean.Paper93.DeepMath.PathB.TwoSATBoundedReachability

#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATBoundedReachability.boundedReach_eq_true_iff
#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATBoundedReachability.reachWithin_sound
#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATBoundedReachability.reach_exists_fuel
#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATBoundedReachability.bounded_mutual_reach_sound
