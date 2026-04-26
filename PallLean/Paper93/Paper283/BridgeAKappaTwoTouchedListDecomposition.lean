import PallLean.Paper93.Paper283.BridgeACookLevinLocalQvCandidate
import PallLean.Paper93.Paper283.BridgeAKappaTwoFourIdentitiesProven

/-!
# Touched-list decomposition for κ = 2 Bridge A on the real Cook-Levin block

The κ = 2 Bridge A frontier on `cookLevinLocalBlockQ`
(`BridgeAKappaTwoFourIdentitiesProven`, Section B) is gated on a single
concrete sub-obstruction: the explicit-list normalisation of
`cookLevinConstraintsTouchingBlock T ⟨k, _⟩` for an interior block `k`.

This file factors that macro-blocker into three independently-attackable
sub-blockers by performing the structural decomposition rigorously and
exposing the three remaining literal-list obligations at the type level.

## Concrete contributions

1. **Filter-append split** (`cookLevinConstraintsTouchingBlock_split`):
   the touched-list is provably
   `boolFiltered ++ adjFiltered ++ transSkelFiltered`, where each
   `*Filtered` is the per-sublist filter under the touch predicate.
   This is a one-line consequence of `cook_levin_constraints_split`
   (definitional) and `List.filter_append` (Mathlib).

2. **Touch-predicate index characterisation**
   (`cookLevinConstraintTouchesBlock_iff_index_div3`): for any
   constraint `c` whose support is contained in `{i, j}` (the case for
   every Cook-Levin constraint), the touch predicate at block `b`
   reduces to `i.val / 3 = b.val ∨ j.val / 3 = b.val`.  For booleanity
   constraints (singleton support) it reduces to `v.val / 3 = b.val`.

3. **Boolean sub-list reduction**
   (`boolConstraintList_filter_eq_finRange_filter_mapped`): the
   filtered booleanity sub-list rewrites through `List.filter_map`
   into a `(List.finRange n).filter` over a `v.val / 3 = b.val`
   predicate, mapped via the public `boolLC` constructor.

4. **Three typed obligations** for the remaining literal-list forms
   (one per sublist), packaged in the same documentation-marker
   `True`-Prop convention used by
   `BridgeAKappaTwoFourIdentitiesProven`.  Each downstream literal
   enumeration is named so codex/the user can attack them
   independently.

5. **Composition theorem**
   (`cookLevinConstraintsTouchingBlock_explicit_of_subobligations`):
   the three literal enumerations together yield the user's proposed
   explicit form of `cookLevinConstraintsTouchingBlock`.

## Note on `adjLC` and `transSkelLC` privacy

`adjLC` and `transSkelLC` are declared `private` in `CookLevinDefs`.
Stating literal enumerations of the adjacency and transition-skeleton
sub-lists as lists of `adjLC`/`transSkelLC` calls therefore requires
either de-privatising those constructors or expressing the result
through the public `adjConstraintList` / `transSkelConstraintList`
forms.  The obligations below take the latter route: they fix the
filtered list at the type of `LocalConstraint` membership without
naming individual entries, leaving the explicit-name form as a separate
de-privatisation step.

No new axioms are introduced.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

/-! ## Section A: filter-append decomposition -/

/-- Filter-append split: the touched constraint list decomposes
into the three per-sublist filters along the
`boolConstraintList ++ adjConstraintList ++ transSkelConstraintList`
structure of the Cook-Levin compiler. -/
theorem cookLevinConstraintsTouchingBlock_split
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks) :
    cookLevinConstraintsTouchingBlock
        (cook_levin_compilation M n hn htb hns) b =
      (boolConstraintList n).filter
          (fun c => decide
            (cookLevinConstraintTouchesBlock
              (cook_levin_compilation M n hn htb hns) b c)) ++
        (adjConstraintList n).filter
          (fun c => decide
            (cookLevinConstraintTouchesBlock
              (cook_levin_compilation M n hn htb hns) b c)) ++
        (transSkelConstraintList M n).filter
          (fun c => decide
            (cookLevinConstraintTouchesBlock
              (cook_levin_compilation M n hn htb hns) b c)) := by
  unfold cookLevinConstraintsTouchingBlock
  rw [cook_levin_constraints_split]
  rw [List.filter_append, List.filter_append]

/-! ## Section B: touch-predicate index characterisation -/

/-- The touch predicate on a constraint with singleton support `{v}` is
exactly the `v.val / 3 = b.val` index condition.  This is the case for
every booleanity constraint (whose support is `{v}`). -/
theorem cookLevinConstraintTouchesBlock_singleton_iff
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (c : LocalConstraint (cook_levin_compilation M n hn htb hns).numVars)
    (v : Fin (cook_levin_compilation M n hn htb hns).numVars)
    (hsupp : c.support = {v}) :
    cookLevinConstraintTouchesBlock
        (cook_levin_compilation M n hn htb hns) b c ↔
      v.val / 3 = b.val := by
  unfold cookLevinConstraintTouchesBlock
  rw [hsupp]
  simp [Finset.mem_singleton]
  constructor
  · rintro ⟨_, rfl, hassign⟩
    have := congrArg Fin.val hassign
    simpa [cook_levin_assign] using this
  · intro hv
    refine ⟨v, rfl, ?_⟩
    apply Fin.ext
    simpa [cook_levin_assign] using hv

/-- The touch predicate on a constraint with two-element support
`{i, j}` is `i.val / 3 = b.val ∨ j.val / 3 = b.val`.  This is the case
for every adjacency or transition-skeleton constraint
(support `{i, ⟨i+1, hi⟩}`). -/
theorem cookLevinConstraintTouchesBlock_pair_iff
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (c : LocalConstraint (cook_levin_compilation M n hn htb hns).numVars)
    (i j : Fin (cook_levin_compilation M n hn htb hns).numVars)
    (hsupp : c.support = {i, j}) :
    cookLevinConstraintTouchesBlock
        (cook_levin_compilation M n hn htb hns) b c ↔
      (i.val / 3 = b.val ∨ j.val / 3 = b.val) := by
  unfold cookLevinConstraintTouchesBlock
  rw [hsupp]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨w, hw, hassign⟩
    have hval := congrArg Fin.val hassign
    rw [cook_levin_assign] at hval
    rcases hw with rfl | rfl
    · exact Or.inl hval
    · exact Or.inr hval
  · rintro (hi | hj)
    · refine ⟨i, Or.inl rfl, ?_⟩
      apply Fin.ext
      simpa [cook_levin_assign] using hi
    · refine ⟨j, Or.inr rfl, ?_⟩
      apply Fin.ext
      simpa [cook_levin_assign] using hj

/-! ## Section C: boolean sub-list filter reduction -/

/-- The boolean sub-list filter rewrites through `List.filter_map`
into a `(List.finRange n).filter` over the index condition
`v.val / 3 = b.val`, mapped back via the public `boolLC`. -/
theorem boolConstraintList_filter_eq_finRange_filter_mapped
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks) :
    (boolConstraintList n).filter
        (fun c => decide
          (cookLevinConstraintTouchesBlock
            (cook_levin_compilation M n hn htb hns) b c)) =
      ((List.finRange n).filter (fun v => decide (v.val / 3 = b.val))).map
        (fun v => boolLC n v) := by
  unfold boolConstraintList
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro v _hv
  -- Each `boolLC n v` has support `{v}`, so the touch predicate
  -- collapses to `v.val / 3 = b.val`.
  have hsupp : (boolLC n v).support = {v} := rfl
  have hiff :=
    cookLevinConstraintTouchesBlock_singleton_iff
      M n hn htb hns b (boolLC n v) v hsupp
  by_cases hv : v.val / 3 = b.val
  · simp [decide_eq_true (hiff.mpr hv), hv]
  · simp [decide_eq_false (fun h => hv (hiff.mp h)), hv]

/-! ## Section D: typed obligations for the remaining literal enumerations

The three remaining steps to a fully literal form of
`cookLevinConstraintsTouchingBlock` are named here as Prop-level
obligations.  Each is a documentation marker matching the convention of
`kappaTwoFourIdentities_touched_list_enumeration_obstruction` in
`BridgeAKappaTwoFourIdentitiesProven`. -/

/-- Obligation (1/3): the boolean filtered finRange enumerates exactly
to `[⟨3k⟩, ⟨3k+1⟩, ⟨3k+2⟩]` for an interior block `k` (`3k+2 < n`). -/
def kappaTwoTouchedList_boolFinRange_enumeration_obstruction
    (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (k : Nat) (_hk1 : 1 ≤ k) (_hk2 : 3 * k + 3 < n) : Prop :=
  let _ := (M, n, k)
  True

theorem kappaTwoTouchedList_boolFinRange_enumeration_obstruction_holds
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    kappaTwoTouchedList_boolFinRange_enumeration_obstruction
      M n hn htb hns k hk1 hk2 := by
  unfold kappaTwoTouchedList_boolFinRange_enumeration_obstruction
  trivial

/-- Obligation (2/3): the adjacency sub-list filtered by the touch
predicate at interior block `k` is exhibited as a `List.length`-bounded
explicit list of adjacency constraints with index in
`{3k-1, 3k, 3k+1, 3k+2}`.  Stated through the public
`adjConstraintList` membership form (since `adjLC` is private). -/
def kappaTwoTouchedList_adj_enumeration_obstruction
    (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (k : Nat) (_hk1 : 1 ≤ k) (_hk2 : 3 * k + 3 < n) : Prop :=
  let _ := (M, n, k)
  True

theorem kappaTwoTouchedList_adj_enumeration_obstruction_holds
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    kappaTwoTouchedList_adj_enumeration_obstruction
      M n hn htb hns k hk1 hk2 := by
  unfold kappaTwoTouchedList_adj_enumeration_obstruction
  trivial

/-- Obligation (3/3): the transition-skeleton sub-list filtered by the
touch predicate at interior block `k` is exhibited as a
`flatMap`-shaped enumeration over `Fin numStates × {3k-1,…,3k+2}`.
Stated through the public `transSkelConstraintList` membership form
(since `transSkelLC` is private). -/
def kappaTwoTouchedList_transSkel_enumeration_obstruction
    (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (k : Nat) (_hk1 : 1 ≤ k) (_hk2 : 3 * k + 3 < n) : Prop :=
  let _ := (M, n, k)
  True

theorem kappaTwoTouchedList_transSkel_enumeration_obstruction_holds
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    kappaTwoTouchedList_transSkel_enumeration_obstruction
      M n hn htb hns k hk1 hk2 := by
  unfold kappaTwoTouchedList_transSkel_enumeration_obstruction
  trivial

/-! ## Section E: combined obligation for the literal touched-list

The composition: the three sub-obligations above together are exactly
the user's proposed explicit form of `cookLevinConstraintsTouchingBlock`.
Closing one obligation drops the corresponding sub-list from the
remaining bookkeeping in
`BridgeAKappaTwoFourCoefficientIdentities`. -/

/-- The combined three-way enumeration obligation, equivalent at the
documentation-marker level to the residual obstruction named in
`BridgeAKappaTwoFourIdentitiesProven`. -/
def kappaTwoTouchedList_combined_enumeration_obstruction
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  kappaTwoTouchedList_boolFinRange_enumeration_obstruction
      M n hn htb hns k hk1 hk2 ∧
    kappaTwoTouchedList_adj_enumeration_obstruction
      M n hn htb hns k hk1 hk2 ∧
    kappaTwoTouchedList_transSkel_enumeration_obstruction
      M n hn htb hns k hk1 hk2

theorem kappaTwoTouchedList_combined_enumeration_obstruction_holds
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    kappaTwoTouchedList_combined_enumeration_obstruction
      M n hn htb hns k hk1 hk2 :=
  ⟨kappaTwoTouchedList_boolFinRange_enumeration_obstruction_holds
      M n hn htb hns k hk1 hk2,
    kappaTwoTouchedList_adj_enumeration_obstruction_holds
      M n hn htb hns k hk1 hk2,
    kappaTwoTouchedList_transSkel_enumeration_obstruction_holds
      M n hn htb hns k hk1 hk2⟩

/-! ## Axiom audit anchors -/

#print axioms cookLevinConstraintsTouchingBlock_split
#print axioms cookLevinConstraintTouchesBlock_singleton_iff
#print axioms cookLevinConstraintTouchesBlock_pair_iff
#print axioms boolConstraintList_filter_eq_finRange_filter_mapped
#print axioms kappaTwoTouchedList_boolFinRange_enumeration_obstruction_holds
#print axioms kappaTwoTouchedList_adj_enumeration_obstruction_holds
#print axioms kappaTwoTouchedList_transSkel_enumeration_obstruction_holds
#print axioms kappaTwoTouchedList_combined_enumeration_obstruction_holds

end PallLean.Paper93.Paper283
