import PallLean.Paper93.Paper283.BridgeAKappaTwoBoolFinRangeEnumeration
import PallLean.Paper93.Paper283.BridgeAKappaTwoAdjFinRangeEnumeration
import PallLean.Paper93.Paper283.BridgeAKappaTwoTransSkelFinRangeEnumeration

/-!
# Combined explicit form of `cookLevinConstraintsTouchingBlock` at an interior block

This file composes the three sub-list enumeration theorems
(`boolConstraintList_filter_at_interior_block`,
`adjConstraintList_filter_at_interior_block`,
`transSkelConstraintList_filter_at_interior_block`) into a *single*
literal form for the touched-list at an interior block `k` (with
`1 ≤ k`, `3 * k + 3 < n`).

The output shape exactly matches the specification recorded in the file
docstring of `BridgeAKappaTwoFourIdentitiesProven` (Step 1 of the
practical kernel-only path forward).

No new axioms.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open PaperFaithfulSeparation

attribute [local instance] Classical.dec

/-! ## Section A: combined literal touched-list -/

/-- The literal boolean factors at an interior block. -/
noncomputable def kappaTwoTouchedList_boolFactors
    (n : Nat) (k : Nat) (_hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (LocalConstraint n) :=
  [boolLC n ⟨3 * k, by omega⟩,
   boolLC n ⟨3 * k + 1, by omega⟩,
   boolLC n ⟨3 * k + 2, by omega⟩]

/-- The literal adjacency factors at an interior block. -/
noncomputable def kappaTwoTouchedList_adjFactors
    (n : Nat) (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (LocalConstraint n) :=
  [adjLC n ⟨3 * k - 1, by omega⟩ (by change 3 * k - 1 + 1 < n; omega),
   adjLC n ⟨3 * k, by omega⟩ (by change 3 * k + 1 < n; omega),
   adjLC n ⟨3 * k + 1, by omega⟩ (by change 3 * k + 1 + 1 < n; omega),
   adjLC n ⟨3 * k + 2, by omega⟩ (by change 3 * k + 2 + 1 < n; omega)]

/-- The literal per-state transition-skeleton factors at an interior block. -/
noncomputable def kappaTwoTouchedList_transSkelFactorsForState
    (M : TuringMachine.DTM) (n : Nat) (q : Fin M.numStates)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (LocalConstraint n) :=
  [transSkelLC M n q ⟨3 * k - 1, by omega⟩
    (by change 3 * k - 1 + 1 < n; omega),
   transSkelLC M n q ⟨3 * k, by omega⟩
    (by change 3 * k + 1 < n; omega),
   transSkelLC M n q ⟨3 * k + 1, by omega⟩
    (by change 3 * k + 1 + 1 < n; omega),
   transSkelLC M n q ⟨3 * k + 2, by omega⟩
    (by change 3 * k + 2 + 1 < n; omega)]

/-- The literal full transition-skeleton block (flatMap over states). -/
noncomputable def kappaTwoTouchedList_transSkelFactorsFlat
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (LocalConstraint n) :=
  (List.finRange M.numStates).flatMap (fun q =>
    kappaTwoTouchedList_transSkelFactorsForState M n q k hk1 hk2)

/-- The combined literal touched-list. -/
noncomputable def kappaTwoTouchedList_explicit
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (LocalConstraint n) :=
  kappaTwoTouchedList_boolFactors n k hk1 hk2 ++
    kappaTwoTouchedList_adjFactors n k hk1 hk2 ++
    kappaTwoTouchedList_transSkelFactorsFlat M n k hk1 hk2

/-! ## Section B: closed form composition theorem -/

/-- Combined closed-form for `cookLevinConstraintsTouchingBlock` at an
interior block `k` (`1 ≤ k`, `3 * k + 3 < n`). -/
theorem cookLevinConstraintsTouchingBlock_at_interior_block
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    cookLevinConstraintsTouchingBlock
        (cook_levin_compilation M n hn htb hns)
        ⟨k, by rw [cook_levin_numBlocks]; omega⟩ =
      kappaTwoTouchedList_explicit M n k hk1 hk2 := by
  rw [cookLevinConstraintsTouchingBlock_split
        M n hn htb hns ⟨k, by rw [cook_levin_numBlocks]; omega⟩]
  rw [boolConstraintList_filter_at_interior_block
        M n hn htb hns k hk1 hk2]
  rw [adjConstraintList_filter_at_interior_block
        M n hn htb hns k hk1 hk2]
  rw [transSkelConstraintList_filter_at_interior_block
        M n hn htb hns k hk1 hk2]
  unfold kappaTwoTouchedList_explicit
  unfold kappaTwoTouchedList_boolFactors
  unfold kappaTwoTouchedList_adjFactors
  unfold kappaTwoTouchedList_transSkelFactorsFlat
  unfold kappaTwoTouchedList_transSkelFactorsForState
  rfl

/-! ## Axiom audit anchors -/

#print axioms cookLevinConstraintsTouchingBlock_at_interior_block

end PallLean.Paper93.Paper283
