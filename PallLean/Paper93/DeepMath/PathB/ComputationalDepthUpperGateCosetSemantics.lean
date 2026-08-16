import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossBranchQuotientRankSaturation

/-!
# Upper-gate semantics on parity cosets

A depth-2 circuit applies an upper Boolean gate to profiles reachable from its lower parity layer.  For SAT, a branch
shift `s` asks whether the upper acceptance predicate holds anywhere on the affine coset `K+s`, where `K` is the kept
parity span.

This file proves the exact semantic boundary:

* shifts in the same coset always define equivalent SAT subproblems, for every upper predicate;
* distinct cosets can be separated by an upper predicate (take acceptance to be one chosen coset).

Therefore arbitrary nonlinear upper semantics does not guarantee any merging beyond the quotient-rank factorization.
A useful collapse theorem must exploit restrictions on the named upper gate class, not merely the existence of an
upper layer.
-/

namespace PallLean.Paper93.DeepMath.PathB.UpperGateCosetSemantics

open scoped Classical

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- SAT of an upper acceptance predicate on the affine residual profile set `K + shift`. -/
def upperSatOnCoset (K : Submodule F V) (Accept : V → Prop) (shift : V) : Prop :=
  ∃ x : V, x ∈ K ∧ Accept (x + shift)

/-- **Same coset ⇒ same upper-gate SAT subproblem (proved), for every acceptance predicate.** -/
theorem upperSatOnCoset_iff_of_sub_mem (K : Submodule F V) (Accept : V → Prop) {a b : V}
    (hab : a - b ∈ K) : upperSatOnCoset K Accept a ↔ upperSatOnCoset K Accept b := by
  constructor
  · rintro ⟨x, hx, hAccept⟩
    refine ⟨x + (a - b), K.add_mem hx hab, ?_⟩
    convert hAccept using 1 <;> abel
  · rintro ⟨x, hx, hAccept⟩
    have hba : b - a ∈ K := by simpa [sub_eq_add_neg, add_comm] using K.neg_mem hab
    refine ⟨x + (b - a), K.add_mem hx hba, ?_⟩
    convert hAccept using 1 <;> abel

/-- The predicate selecting the single affine coset `K + anchor`. -/
def acceptsCoset (K : Submodule F V) (anchor z : V) : Prop := z - anchor ∈ K

/-- The selected coset is satisfiable at its own anchor. -/
theorem upperSat_acceptsCoset_self (K : Submodule F V) (anchor : V) :
    upperSatOnCoset K (acceptsCoset K anchor) anchor := by
  refine ⟨0, K.zero_mem, ?_⟩
  simp [acceptsCoset]

/-- **Distinct cosets can be separated by a nonlinear upper predicate (proved).** -/
theorem not_upperSat_acceptsCoset_of_sub_not_mem (K : Submodule F V) {anchor other : V}
    (hsep : other - anchor ∉ K) :
    ¬ upperSatOnCoset K (acceptsCoset K anchor) other := by
  rintro ⟨x, hx, hAccept⟩
  apply hsep
  have hsum : x + (other - anchor) ∈ K := by
    change x + other - anchor ∈ K at hAccept
    convert hAccept using 1 <;> abel
  have := K.sub_mem hsum hx
  convert this using 1 <;> abel

/-- Hence two distinct cosets admit an upper predicate with different SAT answers. -/
theorem exists_upperPredicate_separating_cosets (K : Submodule F V) {a b : V}
    (hsep : b - a ∉ K) :
    ∃ Accept : V → Prop, upperSatOnCoset K Accept a ∧ ¬ upperSatOnCoset K Accept b := by
  exact ⟨acceptsCoset K a, upperSat_acceptsCoset_self K a,
    not_upperSat_acceptsCoset_of_sub_not_mem K hsep⟩

end PallLean.Paper93.DeepMath.PathB.UpperGateCosetSemantics

#print axioms PallLean.Paper93.DeepMath.PathB.UpperGateCosetSemantics.upperSatOnCoset_iff_of_sub_mem
#print axioms PallLean.Paper93.DeepMath.PathB.UpperGateCosetSemantics.exists_upperPredicate_separating_cosets
