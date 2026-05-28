import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDNFEqualityLowerBound

/-!
# Equality upper bounds for stronger models

**STATUS: FORMAL COUNTERPOINT TO THE DNF LOWER BOUND.**

The exponential lower bound in `ComputationalDepthDNFEqualityLowerBound` is real,
but it cannot extend to full NC¹/TC⁰/width-5 BP for the equality function:
equality is easy once conjunctions can be nested/shared in the usual way.

This file proves the honest obstruction in a tiny split-formula model: equality
on two `n`-bit blocks has a formula of linear size.  Therefore any attempted
`2^n` lower bound for full formula/NC¹-style computation of equality would be
false, not merely unproved.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-- Small formulas over a split pair of `n`-bit blocks. -/
inductive SplitFormula (n : Nat) : Type where
  | const : Bool -> SplitFormula n
  | leftVar : Fin n -> SplitFormula n
  | rightVar : Fin n -> SplitFormula n
  | not : SplitFormula n -> SplitFormula n
  | and : SplitFormula n -> SplitFormula n -> SplitFormula n
  | or : SplitFormula n -> SplitFormula n -> SplitFormula n

namespace SplitFormula

/-- Evaluate a split formula. -/
def eval {n : Nat} : SplitFormula n -> (Fin n -> Bool) -> (Fin n -> Bool) -> Bool
  | const b, _, _ => b
  | leftVar i, a, _ => a i
  | rightVar i, _, b => b i
  | not A, a, b => !(A.eval a b)
  | and A B, a, b => A.eval a b && B.eval a b
  | or A B, a, b => A.eval a b || B.eval a b

/-- Syntactic size. -/
def size {n : Nat} : SplitFormula n -> Nat
  | const _ => 1
  | leftVar _ => 1
  | rightVar _ => 1
  | not A => A.size + 1
  | and A B => A.size + B.size + 1
  | or A B => A.size + B.size + 1

/-- Formula computes equality between the split blocks. -/
def ComputesEquality {n : Nat} (F : SplitFormula n) : Prop :=
  forall a b : Fin n -> Bool, F.eval a b = decide (a = b)

/-- Boolean equality gadget for one bit: `(x ∧ y) ∨ (¬x ∧ ¬y)`. -/
def bitEq {n : Nat} (i : Fin n) : SplitFormula n :=
  or (and (leftVar i) (rightVar i))
    (and (not (leftVar i)) (not (rightVar i)))

/-- Size of the one-bit equality gadget. -/
theorem size_bitEq {n : Nat} (i : Fin n) : (bitEq i).size = 9 := rfl

/-- Correctness of the one-bit equality gadget. -/
theorem eval_bitEq {n : Nat} (i : Fin n) (a b : Fin n -> Bool) :
    (bitEq i).eval a b = decide (a i = b i) := by
  cases hA : a i <;> cases hB : b i <;> simp [bitEq, eval, hA, hB]

/-- Conjunction of a list of formulas; empty conjunction is true. -/
def all {n : Nat} : List (SplitFormula n) -> SplitFormula n
  | [] => const true
  | F :: Fs => and F (all Fs)

/-- Size of `all` is bounded by the sum of child sizes plus one connective/leaf
per list element. -/
theorem size_all_le {n : Nat} (Fs : List (SplitFormula n)) :
    (all Fs).size <= (Fs.map size).sum + Fs.length + 1 := by
  induction Fs with
  | nil => simp [all, size]
  | cons F Fs ih =>
      simp [all, size]
      omega

/-- Evaluation of `all`: it is true iff every child evaluates to true. -/
theorem eval_all_eq_true_iff {n : Nat} (Fs : List (SplitFormula n))
    (a b : Fin n -> Bool) :
    (all Fs).eval a b = true ↔ forall F, F ∈ Fs -> F.eval a b = true := by
  induction Fs with
  | nil => simp [all, eval]
  | cons F Fs ih =>
      simp [all, eval, ih]

/-- Compact equality formula: conjunction of the one-bit equality gadgets. -/
def equalityFormula (n : Nat) : SplitFormula n :=
  all ((List.finRange n).map bitEq)

/-- The compact equality formula has linear size, bounded by `10*n + 1`. -/
theorem equalityFormula_size_le (n : Nat) :
    (equalityFormula n).size <= 10 * n + 1 := by
  unfold equalityFormula
  have h := size_all_le ((List.finRange n).map bitEq)
  have hsum : (((List.finRange n).map bitEq).map size).sum = 9 * n := by
    rw [List.map_map]
    change (List.map (fun i : Fin n => size (bitEq i)) (List.finRange n)).sum = 9 * n
    have hpoint : (fun i : Fin n => size (bitEq i)) = fun _ => 9 := by
      funext i
      rfl
    rw [hpoint]
    simp [Nat.mul_comm]
  have hlen : ((List.finRange n).map bitEq).length = n := by
    simp
  rw [hsum, hlen] at h
  omega

/-- Correctness of the compact equality formula. -/
theorem equalityFormula_computesEquality (n : Nat) :
    (equalityFormula n).ComputesEquality := by
  intro a b
  change (all ((List.finRange n).map bitEq)).eval a b = decide (a = b)
  by_cases h : a = b
  · subst h
    have hall : (all ((List.finRange n).map bitEq)).eval a a = true := by
      rw [eval_all_eq_true_iff]
      intro F hF
      rcases List.mem_map.mp hF with ⟨i, hi, rfl⟩
      simp [eval_bitEq]
    simp [hall]
  · have hne : ¬ (forall i : Fin n, a i = b i) := by
      intro hall
      apply h
      funext i
      exact hall i
    push_neg at hne
    rcases hne with ⟨i, hi⟩
    have hmem : bitEq i ∈ (List.finRange n).map bitEq := by
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have hchild : (bitEq i).eval a b = false := by
      rw [eval_bitEq]
      simp [hi]
    have hall_false : (all ((List.finRange n).map bitEq)).eval a b = false := by
      by_contra htrue
      have hall := (eval_all_eq_true_iff _ a b).1 (Bool.eq_true_of_not_eq_false htrue)
      have := hall (bitEq i) hmem
      rw [hchild] at this
      contradiction
    simp [hall_false, h]

/-- Linear-size upper-bound package for equality formulas. -/
structure EqualityFormulaLinearUpperBound : Prop where
  upper_bound : forall n : Nat, (equalityFormula n).size <= 10 * n + 1
  computes : forall n : Nat, (equalityFormula n).ComputesEquality

/-- Completed linear upper bound. -/
theorem equalityFormulaLinearUpperBound : EqualityFormulaLinearUpperBound where
  upper_bound := equalityFormula_size_le
  computes := equalityFormula_computesEquality

/-- A direct formal refutation of any universal claim that equality formulas need
more than `10*n+1` size. -/
theorem not_all_equalityFormulas_need_more_than_linear (n lower : Nat)
    (hlower : 10 * n + 1 < lower) :
    Not (forall F : SplitFormula n, F.ComputesEquality -> lower <= F.size) := by
  intro H
  have hlow := H (equalityFormula n) (equalityFormula_computesEquality n)
  have hup := equalityFormula_size_le n
  exact Nat.not_lt_of_ge (Nat.le_trans hlow hup) hlower

/-! ## Kernel-only trace -/

#print axioms eval_bitEq
#print axioms size_all_le
#print axioms eval_all_eq_true_iff
#print axioms equalityFormula_size_le
#print axioms equalityFormula_computesEquality
#print axioms equalityFormulaLinearUpperBound
#print axioms not_all_equalityFormulas_need_more_than_linear

end SplitFormula

end PallLean.Paper93.DeepMath.PathB
