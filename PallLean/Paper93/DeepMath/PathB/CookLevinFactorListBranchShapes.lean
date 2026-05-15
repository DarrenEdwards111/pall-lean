import PallLean.Paper93.DeepMath.PathB.ConcreteWFactorMembership

/-!
# Cook-Levin factor-list branch shapes

This file records kernel-clean bookkeeping for the actual `cookLevinFactorList`:
the booleanity prefix and adjacency middle segment have the expected concrete
factor shapes.  These are the safe, true pieces of the direct-branch-shape
frontier; the transition tail is intentionally not collapsed to the old fixed
`transitionLeftAmbientFactor` row here.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound
open PallLean.Paper93.Spanning

attribute [local instance] Classical.dec

/-- Any member of the concrete adjacency-constraint list is an `adjLC`, hence
its factor has the literal `1 - X_a * X_b` shape. -/
theorem adjConstraintList_factor_shape
    (n : ℕ) (lc : LocalConstraint n)
    (hlc : lc ∈ PaperFaithfulSeparation.adjConstraintList n) :
    ∃ (a b : Fin n), a ≠ b ∧
      (1 : MvPolynomial (Fin n) ℚ) - lc.poly =
        (1 - MvPolynomial.X a * MvPolynomial.X b : MvPolynomial (Fin n) ℚ) := by
  classical
  unfold PaperFaithfulSeparation.adjConstraintList at hlc
  simp only [List.mem_filterMap, List.mem_finRange, true_and] at hlc
  obtain ⟨i, hi_mem⟩ := hlc
  by_cases hi : i.val + 1 < n
  · simp only [hi, dite_true, Option.some.injEq] at hi_mem
    subst hi_mem
    refine ⟨i, ⟨i.val + 1, hi⟩, ?_, ?_⟩
    · intro h
      have hv : i.val = i.val + 1 := congrArg Fin.val h
      omega
    · unfold PaperFaithfulSeparation.adjLC PaperFaithfulSeparation.adjPoly
      ring
  · simp [hi] at hi_mem

/-- Booleanity-prefix factors in `cookLevinFactorList` have the literal
`1 - X_v + X_v^2` shape, with `v` equal to the prefix index. -/
theorem cookLevinFactorList_booleanity_prefix_shape
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : i.1 < n) :
    ∃ v : Fin n,
      cookLevinConstraintType M n hn htb hns i = ConstraintType.booleanity ∧
      (cookLevinFactorList M n hn htb hns).get i =
        (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ) := by
  classical
  let v : Fin n := ⟨i.1, hi⟩
  refine ⟨v, cookLevinConstraintType_eq_booleanity M n hn htb hns i hi, ?_⟩
  rw [List.get_eq_getElem]
  have hidx : i.1 < ((PaperFaithfulSeparation.boolConstraintList n).map
      (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly)).length := by
    simpa [PaperFaithfulSeparation.boolConstraintList_length] using hi
  have hget :
      (cookLevinFactorList M n hn htb hns)[i.1] =
        ((PaperFaithfulSeparation.boolConstraintList n).map
          (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly))[i.1]'hidx := by
    simp [cookLevinFactorList, PaperFaithfulSeparation.cook_levin_compilation,
      PaperFaithfulSeparation.boolConstraintList_length, hi]
  have hboolget :
      ((PaperFaithfulSeparation.boolConstraintList n).map
          (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly))[i.1]'hidx =
        (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ) := by
    simp [PaperFaithfulSeparation.boolConstraintList, v,
      PaperFaithfulSeparation.boolLC, PaperFaithfulSeparation.boolPoly']
    ring
  exact hget.trans hboolget

/-- Adjacency-segment factors in `cookLevinFactorList` have the literal
`1 - X_a * X_b` shape for some adjacent pair `(a,b)`. -/
theorem cookLevinFactorList_adjacency_segment_shape
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hlo : n ≤ i.1)
    (hhi : i.1 < n + (PaperFaithfulSeparation.adjConstraintList n).length) :
    ∃ a b : Fin n,
      a ≠ b ∧
      cookLevinConstraintType M n hn htb hns i = ConstraintType.adjacency ∧
      (cookLevinFactorList M n hn htb hns).get i =
        (1 - MvPolynomial.X a * MvPolynomial.X b :
          MvPolynomial (Fin n) ℚ) := by
  classical
  let j : Fin (PaperFaithfulSeparation.adjConstraintList n).length :=
    ⟨i.1 - n, by omega⟩
  have hidx_map : i.1 - n <
      ((PaperFaithfulSeparation.adjConstraintList n).map
        (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly)).length := by
    simpa [List.length_map, j] using j.2
  have hjlt : i.1 - n < (PaperFaithfulSeparation.adjConstraintList n).length := by
    simpa [List.length_map] using hidx_map
  have hfactor :
      (cookLevinFactorList M n hn htb hns).get i =
        (1 : MvPolynomial (Fin n) ℚ) -
          ((PaperFaithfulSeparation.adjConstraintList n).get j).poly := by
    rw [List.get_eq_getElem]
    have hget :
        (cookLevinFactorList M n hn htb hns)[i.1] =
          ((PaperFaithfulSeparation.adjConstraintList n).map
            (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly))[i.1 - n]'hidx_map := by
      simp [cookLevinFactorList, PaperFaithfulSeparation.cook_levin_compilation,
        List.getElem_append, PaperFaithfulSeparation.boolConstraintList_length,
        List.getElem_map]
      split
      · omega
      · simp
    simpa [j] using hget
  have hj_mem : (PaperFaithfulSeparation.adjConstraintList n).get j ∈
      PaperFaithfulSeparation.adjConstraintList n := List.get_mem _ _
  rcases adjConstraintList_factor_shape n
      ((PaperFaithfulSeparation.adjConstraintList n).get j) hj_mem with
    ⟨a, b, hab, hshape⟩
  refine ⟨a, b, hab,
    cookLevinConstraintType_eq_adjacency M n hn htb hns i hlo hhi, ?_⟩
  exact hfactor.trans hshape

/-- Transition-segment factors in `cookLevinFactorList` are the real
transition-skeleton two-variable factors: `1 - c * X_a * X_b`, classified as
`transitionLeft` by the current profile bookkeeping. -/
theorem cookLevinFactorList_transition_segment_cadj_shape
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hlo : n + (PaperFaithfulSeparation.adjConstraintList n).length ≤ i.1) :
    ∃ (c : ℚ) (a b : Fin n),
      a ≠ b ∧
      cookLevinConstraintType M n hn htb hns i = ConstraintType.transitionLeft ∧
      (cookLevinFactorList M n hn htb hns).get i =
        (1 - MvPolynomial.C c * (MvPolynomial.X a * MvPolynomial.X b) :
          MvPolynomial (Fin n) ℚ) := by
  classical
  let j : Fin (PaperFaithfulSeparation.transSkelConstraintList M n).length :=
    ⟨i.1 - n - (PaperFaithfulSeparation.adjConstraintList n).length, by
      have hi' :
          i.1 < n + (PaperFaithfulSeparation.adjConstraintList n).length +
            (PaperFaithfulSeparation.transSkelConstraintList M n).length := by
        simpa [cookLevinFactorList, PaperFaithfulSeparation.cook_levin_compilation,
          PaperFaithfulSeparation.boolConstraintList_length n,
          List.length_map, List.length_append, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using i.2
      omega⟩
  have hidx_map :
      i.1 - n - (PaperFaithfulSeparation.adjConstraintList n).length <
        (List.map (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly)
          (PaperFaithfulSeparation.transSkelConstraintList M n)).length := by
    simpa [List.length_map, j] using j.2
  have hfactor :
      (cookLevinFactorList M n hn htb hns).get i =
        (1 : MvPolynomial (Fin n) ℚ) -
          ((PaperFaithfulSeparation.transSkelConstraintList M n).get j).poly := by
    rw [List.get_eq_getElem]
    have hget :
        (cookLevinFactorList M n hn htb hns)[i.1] =
          (List.map (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly)
            (PaperFaithfulSeparation.transSkelConstraintList M n))[i.1 - n -
              (PaperFaithfulSeparation.adjConstraintList n).length]'hidx_map := by
      simp [cookLevinFactorList, PaperFaithfulSeparation.cook_levin_compilation,
        List.getElem_append, PaperFaithfulSeparation.boolConstraintList_length n,
        List.getElem_map]
      split
      · omega
      · split
        · omega
        · rfl
    simpa [j] using hget
  have hj_mem : (PaperFaithfulSeparation.transSkelConstraintList M n).get j ∈
      PaperFaithfulSeparation.transSkelConstraintList M n := List.get_mem _ _
  obtain ⟨c, a, ha, hpoly⟩ :=
    PaperFaithfulSeparation.rest_constraint_cadj_form M n
      ((PaperFaithfulSeparation.transSkelConstraintList M n).get j) (by
        rw [List.mem_append]
        exact Or.inr hj_mem)
  let b : Fin n := ⟨a.val + 1, ha⟩
  refine ⟨c, a, b, ?_,
    cookLevinConstraintType_eq_transitionLeft M n hn htb hns i hlo, ?_⟩
  · intro h
    have hv : a.val = a.val + 1 := congrArg Fin.val h
    omega
  · rw [hfactor, hpoly]

/-- The actual direct-branch-shape package for `cookLevinFactorList`.

Unlike the older `CookLevinDirectBranchShapeWitnesses`, the transition branch
uses the real transition-skeleton factor shape produced by the compiler,
`1 - c * X_a * X_b`, while still recording that the bookkeeping classifier is
`ConstraintType.transitionLeft`.  This is the unconditional shape statement
needed before any separate row-transport / enlarged-interface argument. -/
def CookLevinActualDirectBranchShapeWitnesses
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ i : Fin (cookLevinFactorList M n hn htb hns).length,
    (∃ v : Fin n,
        cookLevinConstraintType M n hn htb hns i =
          ConstraintType.booleanity ∧
        (cookLevinFactorList M n hn htb hns).get i =
          (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
              MvPolynomial (Fin n) ℚ)) ∨
    (∃ a b : Fin n,
        a ≠ b ∧
        cookLevinConstraintType M n hn htb hns i =
          ConstraintType.adjacency ∧
        (cookLevinFactorList M n hn htb hns).get i =
          (1 - MvPolynomial.X a * MvPolynomial.X b :
              MvPolynomial (Fin n) ℚ)) ∨
    (∃ (c : ℚ) (a b : Fin n),
        a ≠ b ∧
        cookLevinConstraintType M n hn htb hns i =
          ConstraintType.transitionLeft ∧
        (cookLevinFactorList M n hn htb hns).get i =
          (1 - MvPolynomial.C c * (MvPolynomial.X a * MvPolynomial.X b) :
              MvPolynomial (Fin n) ℚ))

/-- The actual branch-shape package is inhabited unconditionally for the
concrete Cook-Levin factor list. -/
theorem cookLevinActualDirectBranchShapeWitnesses
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    CookLevinActualDirectBranchShapeWitnesses M n hn htb hns := by
  classical
  intro i
  by_cases hbool : i.1 < n
  · left
    exact cookLevinFactorList_booleanity_prefix_shape M n hn htb hns i hbool
  · by_cases hadj : i.1 < n + (PaperFaithfulSeparation.adjConstraintList n).length
    · right; left
      exact cookLevinFactorList_adjacency_segment_shape M n hn htb hns i
        (Nat.le_of_not_gt hbool) hadj
    · right; right
      exact cookLevinFactorList_transition_segment_cadj_shape M n hn htb hns i
        (Nat.le_of_not_gt hadj)

/-- The remaining transition-tail shape obligation after the true booleanity
and adjacency branches have been discharged from the actual factor list.

This is intentionally just the old `transitionLeftAmbientFactor` tail equation:
if it is false for the concrete transition skeleton, the failure is isolated
here rather than hidden inside the booleanity/adjacency bookkeeping. -/
def CookLevinTransitionTailCanonicalShapeObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) : Prop :=
  ∀ i : Fin (cookLevinFactorList M n hn htb hns).length,
    n + (PaperFaithfulSeparation.adjConstraintList n).length ≤ i.1 →
      (cookLevinFactorList M n hn htb hns).get i =
        (transitionLeftAmbientFactor (Fin.castLEEmb hn4) :
          MvPolynomial (Fin n) ℚ)

/-- The full direct-branch-shape package reduces to the transition tail.

The booleanity prefix and adjacency segment are now proved directly from
`cookLevinFactorList`; no canonical fixed-row assumption is used for those
branches. -/
theorem CookLevinDirectBranchShapeWitnesses_of_transitionTailCanonicalShape
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hTail :
      CookLevinTransitionTailCanonicalShapeObligation M n hn htb hns hn4) :
    CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4 := by
  classical
  intro i
  by_cases hbool : i.1 < n
  · left
    exact cookLevinFactorList_booleanity_prefix_shape M n hn htb hns i hbool
  · by_cases hadj : i.1 < n + (PaperFaithfulSeparation.adjConstraintList n).length
    · right; left
      exact cookLevinFactorList_adjacency_segment_shape M n hn htb hns i
        (Nat.le_of_not_gt hbool) hadj
    · right; right
      have htail_le : n + (PaperFaithfulSeparation.adjConstraintList n).length ≤ i.1 :=
        Nat.le_of_not_gt hadj
      exact ⟨cookLevinConstraintType_eq_transitionLeft M n hn htb hns i htail_le,
        hTail i htail_le⟩

#print axioms adjConstraintList_factor_shape
#print axioms cookLevinFactorList_booleanity_prefix_shape
#print axioms cookLevinFactorList_adjacency_segment_shape
#print axioms cookLevinFactorList_transition_segment_cadj_shape
#print axioms cookLevinActualDirectBranchShapeWitnesses
#print axioms CookLevinDirectBranchShapeWitnesses_of_transitionTailCanonicalShape

end PallLean.Paper93.DeepMath.PathB
