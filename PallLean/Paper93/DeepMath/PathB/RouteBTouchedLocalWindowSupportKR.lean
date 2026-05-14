import PallLean.Paper93.DeepMath.PathB.RouteBTouchedMonomialCodedFiniteSpanKR
import PallLean.Paper93.DeepMath.PathB.RouteBTouchedCanonicalSourceKR

/-!
# Route B touched local-window support

The constant-alphabet KR argument must not count incident Cook--Levin factors:
the transition skeleton has one adjacent-pair factor for every machine state, so
that incidence count is not constant.  The paper-faithful invariant is instead
local-window support: every concrete factor touching a tableau variable `v` is
supported on `v` and its two immediate neighbours.  The arbitrarily many
machine-state transition factors therefore live in a fixed multilinear local
coordinate space; transition coefficients remain field scalars.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- The radius-1 one-dimensional tableau window around a compiled variable. -/
def cookLevinVarLocalWindow (n : ℕ) (v : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun w => w.1 + 1 = v.1 ∨ w = v ∨ v.1 + 1 = w.1)

@[simp] theorem mem_cookLevinVarLocalWindow_self (n : ℕ) (v : Fin n) :
    v ∈ cookLevinVarLocalWindow n v := by
  unfold cookLevinVarLocalWindow
  simp

/-- The local window has at most three variables. -/
theorem cookLevinVarLocalWindow_card_le_three (n : ℕ) (v : Fin n) :
    (cookLevinVarLocalWindow n v).card ≤ 3 := by
  classical
  have hsubset : cookLevinVarLocalWindow n v ⊆
      ({v} ∪
        ((Finset.univ : Finset (Fin n)).filter (fun w => w.1 + 1 = v.1)) ∪
        ((Finset.univ : Finset (Fin n)).filter (fun w => v.1 + 1 = w.1))) := by
    intro w hw
    unfold cookLevinVarLocalWindow at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases hw with h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
  have hleft : ((Finset.univ : Finset (Fin n)).filter (fun w => w.1 + 1 = v.1)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    simp at ha hb
    exact Fin.ext (by omega)
  have hright : ((Finset.univ : Finset (Fin n)).filter (fun w => v.1 + 1 = w.1)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    simp at ha hb
    exact Fin.ext (by omega)
  have hfinal := Finset.card_le_card hsubset
  let A : Finset (Fin n) := {v}
  let B : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun w => w.1 + 1 = v.1)
  let C : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun w => v.1 + 1 = w.1)
  have hA : A.card ≤ 1 := by simp [A]
  have hB : B.card ≤ 1 := by simpa [B] using hleft
  have hC : C.card ≤ 1 := by simpa [C] using hright
  have hAB : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
  have hABC : ((A ∪ B) ∪ C).card ≤ (A ∪ B).card + C.card :=
    Finset.card_union_le (A ∪ B) C
  have hunion :
      (({v} : Finset (Fin n)) ∪
        ((Finset.univ : Finset (Fin n)).filter (fun w => w.1 + 1 = v.1)) ∪
        ((Finset.univ : Finset (Fin n)).filter (fun w => v.1 + 1 = w.1))).card ≤ 3 := by
    change ((A ∪ B) ∪ C).card ≤ 3
    omega
  exact hfinal.trans hunion

/-- Booleanity support touching `v` lies in `v`'s local window. -/
theorem boolLC_support_subset_localWindow_of_mem
    (n : ℕ) (u v : Fin n)
    (hv : v ∈ (boolLC n u).support) :
    (boolLC n u).support ⊆ cookLevinVarLocalWindow n v := by
  intro w hw
  unfold boolLC at hv hw
  simp at hv hw
  subst hv
  subst hw
  simp

/-- Adjacency support touching `v` lies in `v`'s local window. -/
theorem adjLC_support_subset_localWindow_of_mem
    (n : ℕ) (i v : Fin n) (hi : i.val + 1 < n)
    (hv : v ∈ (adjLC n i hi).support) :
    (adjLC n i hi).support ⊆ cookLevinVarLocalWindow n v := by
  intro w hw
  unfold adjLC at hv hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
  unfold cookLevinVarLocalWindow
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · subst hv; subst hw; exact Or.inr (Or.inl rfl)
  · subst hv; subst hw; exact Or.inr (Or.inr rfl)
  · subst hv; subst hw; exact Or.inl rfl
  · subst hv; subst hw; exact Or.inr (Or.inl rfl)

/-- Transition-skeleton support touching `v` lies in `v`'s local window. -/
theorem transSkelLC_support_subset_localWindow_of_mem
    (M : DTM) (n : ℕ) (q : Fin M.numStates) (i v : Fin n) (hi : i.val + 1 < n)
    (hv : v ∈ (transSkelLC M n q i hi).support) :
    (transSkelLC M n q i hi).support ⊆ cookLevinVarLocalWindow n v := by
  intro w hw
  unfold transSkelLC at hv hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
  unfold cookLevinVarLocalWindow
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · subst hv; subst hw; exact Or.inr (Or.inl rfl)
  · subst hv; subst hw; exact Or.inr (Or.inr rfl)
  · subst hv; subst hw; exact Or.inl rfl
  · subst hv; subst hw; exact Or.inr (Or.inl rfl)

/-- Any booleanity-list member touching `v` has support inside `v`'s local
window. -/
theorem boolConstraintList_support_subset_localWindow_of_mem
    (n : ℕ) (c : LocalConstraint n) (v : Fin n)
    (hc : c ∈ boolConstraintList n) (hv : v ∈ c.support) :
    c.support ⊆ cookLevinVarLocalWindow n v := by
  unfold boolConstraintList at hc
  rcases List.mem_map.mp hc with ⟨u, _hu, rfl⟩
  exact boolLC_support_subset_localWindow_of_mem n u v hv

/-- Any adjacency-list member touching `v` has support inside `v`'s local
window. -/
theorem adjConstraintList_support_subset_localWindow_of_mem
    (n : ℕ) (c : LocalConstraint n) (v : Fin n)
    (hc : c ∈ adjConstraintList n) (hv : v ∈ c.support) :
    c.support ⊆ cookLevinVarLocalWindow n v := by
  unfold adjConstraintList at hc
  rcases List.mem_filterMap.mp hc with ⟨i, _hiMem, hiSome⟩
  split at hiSome
  · cases hiSome
    exact adjLC_support_subset_localWindow_of_mem n i v _ hv
  · cases hiSome

/-- Any transition-skeleton-list member touching `v` has support inside `v`'s
local window. -/
theorem transSkelConstraintList_support_subset_localWindow_of_mem
    (M : DTM) (n : ℕ) (c : LocalConstraint n) (v : Fin n)
    (hc : c ∈ transSkelConstraintList M n) (hv : v ∈ c.support) :
    c.support ⊆ cookLevinVarLocalWindow n v := by
  unfold transSkelConstraintList at hc
  rcases List.mem_flatMap.mp hc with ⟨q, _hq, hcq⟩
  unfold transSkelForState at hcq
  rcases List.mem_filterMap.mp hcq with ⟨i, _hiMem, hiSome⟩
  split at hiSome
  · cases hiSome
    exact transSkelLC_support_subset_localWindow_of_mem M n q i v _ hv
  · cases hiSome

/-- Concrete Cook--Levin local-window support theorem: every compiled constraint
whose support contains `v` is supported in the radius-1 window around `v`. -/
theorem cookLevinConstraint_support_subset_localWindow_of_mem
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (v : Fin (cookLevinTableau M n hn2 htb hns).numVars)
    (hv : v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support) :
    ((cookLevinTableau M n hn2 htb hns).constraints.get i).support ⊆
      cookLevinVarLocalWindow (cookLevinTableau M n hn2 htb hns).numVars v := by
  have hmem := List.get_mem (cookLevinTableau M n hn2 htb hns).constraints i
  change ((cook_levin_compilation M n hn2 htb hns).constraints.get i).support ⊆
      cookLevinVarLocalWindow (cook_levin_compilation M n hn2 htb hns).numVars v
  change v ∈ ((cook_levin_compilation M n hn2 htb hns).constraints.get i).support at hv
  change (cook_levin_compilation M n hn2 htb hns).constraints.get i ∈
      (cook_levin_compilation M n hn2 htb hns).constraints at hmem
  unfold cook_levin_compilation at hmem hv ⊢
  simp only at hmem hv ⊢
  rw [List.mem_append] at hmem
  rcases hmem with hleft | htrans
  · rw [List.mem_append] at hleft
    rcases hleft with hbool | hadj
    · exact boolConstraintList_support_subset_localWindow_of_mem n _ v hbool hv
    · exact adjConstraintList_support_subset_localWindow_of_mem n _ v hadj hv
  · exact transSkelConstraintList_support_subset_localWindow_of_mem M n _ v htrans hv

/-- Consequently every derivative allocated to a touched constraint is taken
within the local window of each selected source variable for that constraint. -/
theorem cookLevinAllocatedVars_subset_localWindow_of_source
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (v : Fin (cookLevinTableau M n hn2 htb hns).numVars)
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hv : v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support)
    (hcompat : ∀ j, ∀ w ∈ alloc j,
      w ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get j).support) :
    (alloc i).toFinset ⊆
      cookLevinVarLocalWindow (cookLevinTableau M n hn2 htb hns).numVars v := by
  intro w hw
  exact cookLevinConstraint_support_subset_localWindow_of_mem M n hn2 htb hns i v hv
    (hcompat i w (by simpa using hw))

/-- The whole support of the canonical source selected at a KR row position lies
in the radius-1 local window of the row variable at that position. -/
theorem cookLevinCanonicalTouchedSource_support_subset_localWindow
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n))
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (hi : canonicalTouchedSourceIdx M n hn2 htb hns S hlen j = some i) :
    ((cookLevinTableau M n hn2 htb hns).constraints.get i).support ⊆
      cookLevinVarLocalWindow (cookLevinTableau M n hn2 htb hns).numVars
        (touchedRowVarAt M n hn2 htb hns S hlen j) := by
  classical
  have hfibre :
      i ∈ touchedWindowSupportFibre M n hn2 htb hns S hlen j :=
    canonicalTouchedSourceIdx_mem_fibre M n hn2 htb hns S hlen j i hi
  have hv :
      touchedRowVarAt M n hn2 htb hns S hlen j ∈
        ((cookLevinTableau M n hn2 htb hns).constraints.get i).support := by
    unfold touchedWindowSupportFibre at hfibre
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hfibre
  exact cookLevinConstraint_support_subset_localWindow_of_mem
    M n hn2 htb hns i (touchedRowVarAt M n hn2 htb hns S hlen j) hv

/-- For the canonical source selected at a KR row position, every derivative
variable allocated to that source lies in the radius-1 local window of the row
variable at that position.

This is a concrete local-support step toward the real touched-window normal
form: once the source is no longer arbitrary but chosen from the actual support
fibre, compatibility of the derivative allocation forces all selected
derivative variables into the same constant-size local coordinate window. -/
theorem cookLevinAllocatedVars_subset_localWindow_of_canonicalTouchedSource
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hcompat : ∀ j, ∀ w ∈ alloc j,
      w ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get j).support)
    (j : Fin (Nat.log 2 n))
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (hi : canonicalTouchedSourceIdx M n hn2 htb hns S hlen j = some i) :
    (alloc i).toFinset ⊆
      cookLevinVarLocalWindow (cookLevinTableau M n hn2 htb hns).numVars
        (touchedRowVarAt M n hn2 htb hns S hlen j) := by
  classical
  have hsupport :=
    cookLevinCanonicalTouchedSource_support_subset_localWindow
      M n hn2 htb hns S hlen j i hi
  intro w hw
  exact hsupport (hcompat i w (by simpa using hw))

/-- The same local-window containment stated from the canonical source record
rather than directly from the option-valued source index. -/
theorem cookLevinAllocatedVars_subset_localWindow_of_canonicalTouchedWindowSource
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hcompat : ∀ j, ∀ w ∈ alloc j,
      w ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get j).support)
    (j : Fin (Nat.log 2 n))
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (hi : (canonicalTouchedWindowSource M n hn2 htb hns S hlen j).source = some i) :
    (alloc i).toFinset ⊆
      cookLevinVarLocalWindow (cookLevinTableau M n hn2 htb hns).numVars
        (touchedRowVarAt M n hn2 htb hns S hlen j) := by
  exact
    cookLevinAllocatedVars_subset_localWindow_of_canonicalTouchedSource
      M n hn2 htb hns S hlen alloc hcompat j i hi

/-! ## Axiom audit anchors -/

#print axioms cookLevinVarLocalWindow_card_le_three
#print axioms boolLC_support_subset_localWindow_of_mem
#print axioms adjLC_support_subset_localWindow_of_mem
#print axioms transSkelLC_support_subset_localWindow_of_mem
#print axioms boolConstraintList_support_subset_localWindow_of_mem
#print axioms adjConstraintList_support_subset_localWindow_of_mem
#print axioms transSkelConstraintList_support_subset_localWindow_of_mem
#print axioms cookLevinConstraint_support_subset_localWindow_of_mem
#print axioms cookLevinAllocatedVars_subset_localWindow_of_source
#print axioms cookLevinCanonicalTouchedSource_support_subset_localWindow
#print axioms cookLevinAllocatedVars_subset_localWindow_of_canonicalTouchedSource
#print axioms cookLevinAllocatedVars_subset_localWindow_of_canonicalTouchedWindowSource

end PallLean.Paper93.DeepMath.PathB
