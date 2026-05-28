import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSubfunctionObserverInvariant

/-!
# Exponential DNF lower bound for equality split

**STATUS: GENUINE SUPER-POLYNOMIAL RESTRICTED LOWER BOUND.**

This file proves a real exponential lower bound: any depth-2 DNF of ordinary
literal conjunctions computing equality between two `n`-bit blocks needs at least
`2^n` terms.

This is not a TC⁰/NC¹/width-5 BP breakthrough.  It is the first honest place
where the subfunction/interference idea produces an actual super-polynomial
lower bound inside the formal ladder.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-- A conjunction of literals over a split pair of `n`-bit blocks.  `none` means
the variable is absent; `some b` means the literal fixes the variable to `b`. -/
structure SplitTerm (n : Nat) where
  left : Fin n -> Option Bool
  right : Fin n -> Option Bool

namespace SplitTerm

/-- A term is satisfied by a left/right assignment pair when all mentioned
literals agree with the assignment. -/
def Eval {n : Nat} (T : SplitTerm n)
    (a b : Fin n -> Bool) : Prop :=
  (forall i v, T.left i = some v -> a i = v) ∧
  (forall i v, T.right i = some v -> b i = v)

/-- If a split term accepts `(a,a)` and `(a',a')`, then it also accepts the mixed
assignment `(a,a')`.  This is the core DNF rectangle argument. -/
theorem eval_mixed_of_eval_diag_pair
    {n : Nat} (T : SplitTerm n) {a a' : Fin n -> Bool}
    (ha : T.Eval a a) (ha' : T.Eval a' a') :
    T.Eval a a' := by
  exact ⟨ha.1, ha'.2⟩

end SplitTerm

/-- A DNF with exactly `m` terms over split `n`-bit inputs.  Terms are indexed by
`Fin m`, avoiding list-selection bureaucracy in the lower-bound proof. -/
structure SplitDNF (n m : Nat) where
  term : Fin m -> SplitTerm n

namespace SplitDNF

/-- DNF evaluation: some term is satisfied. -/
def Eval {n m : Nat} (D : SplitDNF n m)
    (a b : Fin n -> Bool) : Prop :=
  exists j : Fin m, (D.term j).Eval a b

/-- The DNF computes equality between the two blocks. -/
def ComputesEquality {n m : Nat} (D : SplitDNF n m) : Prop :=
  forall a b : Fin n -> Bool, D.Eval a b ↔ a = b

/-- Every diagonal assignment `(a,a)` must be covered by some term. -/
theorem exists_term_eval_diag_of_computesEquality
    {n m : Nat} (D : SplitDNF n m) (hcomp : D.ComputesEquality)
    (a : Fin n -> Bool) :
    exists j : Fin m, (D.term j).Eval a a := by
  exact (hcomp a a).2 rfl

/-- If the same term covers two diagonal points, those points are equal. -/
theorem diag_points_eq_of_same_term
    {n m : Nat} (D : SplitDNF n m) (hcomp : D.ComputesEquality)
    {a a' : Fin n -> Bool} {j : Fin m}
    (ha : (D.term j).Eval a a) (ha' : (D.term j).Eval a' a') :
    a = a' := by
  have hmixed : D.Eval a a' :=
    ⟨j, (D.term j).eval_mixed_of_eval_diag_pair ha ha'⟩
  exact (hcomp a a').1 hmixed

/-- Choose one covering term for each diagonal assignment. -/
noncomputable def coveringTerm {n m : Nat} (D : SplitDNF n m)
    (hcomp : D.ComputesEquality) :
    (Fin n -> Bool) -> Fin m := by
  classical
  intro a
  exact Classical.choose (D.exists_term_eval_diag_of_computesEquality hcomp a)

/-- The chosen covering term really covers the corresponding diagonal point. -/
theorem coveringTerm_spec {n m : Nat} (D : SplitDNF n m)
    (hcomp : D.ComputesEquality) (a : Fin n -> Bool) :
    (D.term (D.coveringTerm hcomp a)).Eval a a := by
  classical
  exact Classical.choose_spec (D.exists_term_eval_diag_of_computesEquality hcomp a)

/-- The covering-term map is injective: one term cannot cover two different
diagonal equality points without also accepting an unequal mixed point. -/
theorem coveringTerm_injective {n m : Nat} (D : SplitDNF n m)
    (hcomp : D.ComputesEquality) :
    Function.Injective (D.coveringTerm hcomp) := by
  classical
  intro a a' h
  have ha : (D.term (D.coveringTerm hcomp a)).Eval a a :=
    D.coveringTerm_spec hcomp a
  have ha' : (D.term (D.coveringTerm hcomp a)).Eval a' a' := by
    simpa [h] using D.coveringTerm_spec hcomp a'
  exact D.diag_points_eq_of_same_term hcomp ha ha'

/-- Exponential DNF lower bound for equality split: `2^n` terms are necessary. -/
theorem termCount_ge_two_pow_of_computesEquality
    {n m : Nat} (D : SplitDNF n m) (hcomp : D.ComputesEquality) :
    2 ^ n <= m := by
  classical
  have hcard : Fintype.card (Fin n -> Bool) <= Fintype.card (Fin m) :=
    Fintype.card_le_of_injective (D.coveringTerm hcomp)
      (D.coveringTerm_injective hcomp)
  simpa [Fintype.card_fun, Fintype.card_bool] using hcard

end SplitDNF

/-- Pointwise lower-bound interface for equality DNFs. -/
def EqualityDNFTermLowerBoundAt (n lower : Nat) : Prop :=
  forall m : Nat, forall D : SplitDNF n m,
    D.ComputesEquality -> lower <= m

/-- Equality DNFs require exponentially many terms. -/
theorem equalityDNF_termLowerBound (n : Nat) :
    EqualityDNFTermLowerBoundAt n (2 ^ n) := by
  intro m D hcomp
  exact D.termCount_ge_two_pow_of_computesEquality hcomp

/-- No DNF with fewer than `2^n` terms computes equality split. -/
theorem no_small_equalityDNF
    {n m : Nat} (hgap : m < 2 ^ n) :
    Not (exists D : SplitDNF n m, D.ComputesEquality) := by
  rintro ⟨D, hcomp⟩
  have hlower : 2 ^ n <= m := D.termCount_ge_two_pow_of_computesEquality hcomp
  exact Nat.not_lt_of_ge hlower hgap

/-- Package for the proved exponential DNF lower bound. -/
structure DNFEqualityExponentialLowerBound : Prop where
  lower_bound : forall n : Nat, EqualityDNFTermLowerBoundAt n (2 ^ n)
  no_small : forall {n m : Nat}, m < 2 ^ n ->
    Not (exists D : SplitDNF n m, D.ComputesEquality)

/-- Completed exponential DNF lower-bound theorem. -/
theorem dnfEqualityExponentialLowerBound : DNFEqualityExponentialLowerBound where
  lower_bound := equalityDNF_termLowerBound
  no_small := by
    intro n m hgap
    exact no_small_equalityDNF hgap

/-! ## Kernel-only trace -/

#print axioms SplitTerm.eval_mixed_of_eval_diag_pair
#print axioms SplitDNF.exists_term_eval_diag_of_computesEquality
#print axioms SplitDNF.diag_points_eq_of_same_term
#print axioms SplitDNF.coveringTerm_injective
#print axioms SplitDNF.termCount_ge_two_pow_of_computesEquality
#print axioms equalityDNF_termLowerBound
#print axioms no_small_equalityDNF
#print axioms dnfEqualityExponentialLowerBound

end PallLean.Paper93.DeepMath.PathB
