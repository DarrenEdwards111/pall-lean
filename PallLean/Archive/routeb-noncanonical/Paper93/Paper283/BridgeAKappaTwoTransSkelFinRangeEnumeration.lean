import PallLean.Paper93.Paper283.BridgeAKappaTwoAdjFinRangeEnumeration

/-!
# TransSkel-finRange enumeration for κ=2 Bridge A

Discharges the transition-skeleton sub-obligation
`kappaTwoTouchedList_transSkel_enumeration_obstruction` exposed in
`BridgeAKappaTwoTouchedListDecomposition`.

The proof reuses the adjacency-side filterMap restriction lemma
(`filterMap_eq_filterMap_filter_isSome`) and the index-side enumeration
(`finRange_filter_adj_eq`) from the adj file.  Per-state, the filter on
`transSkelForState` produces a 4-elt list of `transSkelLC` calls; the
full filtered transSkel list is the `flatMap` over `Fin numStates`.

No new axioms.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open PaperFaithfulSeparation

attribute [local instance] Classical.dec

/-! ## Section A: per-state combinator and enumeration -/

/-- Global per-state Option-valued combinator for the transSkel filter. -/
private noncomputable def transSkelLC_global
    (M : TuringMachine.DTM) (n k : ℕ) (hk2 : 3 * k + 3 < n)
    (q : Fin M.numStates) :
    Fin n → Option (LocalConstraint n) := fun i =>
  if hp : i.val / 3 = k ∨ (i.val + 1) / 3 = k then
    some (transSkelLC M n q i (adj_pred_implies_succ_lt n k hk2 i hp))
  else none

/-- The dite/ite form arising from `Option.filter` on `transSkelForState`
reduces to `transSkelLC_global` on `Fin n`. -/
private lemma transSkelLC_dite_eq_global
    (M : TuringMachine.DTM) (n k : ℕ) (hk2 : 3 * k + 3 < n)
    (q : Fin M.numStates) (i : Fin n) :
    (if h : i.val + 1 < n then
        if decide (i.val / 3 = k ∨ (i.val + 1) / 3 = k) then
          some (transSkelLC M n q i h)
        else none
      else none) =
      transSkelLC_global M n k hk2 q i := by
  unfold transSkelLC_global
  by_cases hp : i.val / 3 = k ∨ (i.val + 1) / 3 = k
  · have h_succ : i.val + 1 < n := adj_pred_implies_succ_lt n k hk2 i hp
    rw [dif_pos h_succ, if_pos (decide_eq_true hp), dif_pos hp]
  · rw [dif_neg hp]
    by_cases h_succ : i.val + 1 < n
    · rw [dif_pos h_succ, if_neg (by simpa using hp)]
    · rw [dif_neg h_succ]

/-- The `isSome`-filter on `transSkelLC_global q` collapses to the index
predicate filter. -/
private lemma transSkelLC_global_isSome_eq_pred
    (M : TuringMachine.DTM) (n k : ℕ) (hk2 : 3 * k + 3 < n)
    (q : Fin M.numStates) (i : Fin n) :
    (transSkelLC_global M n k hk2 q i).isSome =
      decide (i.val / 3 = k ∨ (i.val + 1) / 3 = k) := by
  unfold transSkelLC_global
  by_cases hp : i.val / 3 = k ∨ (i.val + 1) / 3 = k
  · simp [hp]
  · simp [hp]

/-- Per-state closed form: the filter on `transSkelForState M n q` at an
interior block `k` enumerates as a 4-elt list of `transSkelLC` calls. -/
theorem transSkelForState_filter_at_interior_block
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (q : Fin M.numStates)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (transSkelForState M n q).filter
        (fun c => decide
          (cookLevinConstraintTouchesBlock
            (cook_levin_compilation M n hn htb hns)
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩ c)) =
      [transSkelLC M n q ⟨3 * k - 1, by omega⟩
        (by change 3 * k - 1 + 1 < n; omega),
       transSkelLC M n q ⟨3 * k, by omega⟩
        (by change 3 * k + 1 < n; omega),
       transSkelLC M n q ⟨3 * k + 1, by omega⟩
        (by change 3 * k + 1 + 1 < n; omega),
       transSkelLC M n q ⟨3 * k + 2, by omega⟩
        (by change 3 * k + 2 + 1 < n; omega)] := by
  unfold transSkelForState
  rw [List.filter_filterMap]
  set b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks :=
    ⟨k, by rw [cook_levin_numBlocks]; omega⟩ with hb_def
  have set_b : b.val = k := rfl
  -- Replace inner Option.filter with transSkelLC_global.
  have inner_eq : (fun i : Fin n =>
        Option.filter
          (fun c => decide
            (cookLevinConstraintTouchesBlock
              (cook_levin_compilation M n hn htb hns) b c))
          (if h : i.val + 1 < n then some (transSkelLC M n q i h) else none)) =
      transSkelLC_global M n k hk2 q := by
    funext i
    by_cases h_succ : i.val + 1 < n
    · have hsupp : (transSkelLC M n q i h_succ).support =
          ({i, ⟨i.val + 1, h_succ⟩} : Finset (Fin n)) := rfl
      have hiff :=
        cookLevinConstraintTouchesBlock_pair_iff
          M n hn htb hns b (transSkelLC M n q i h_succ) i ⟨i.val + 1, h_succ⟩ hsupp
      rw [set_b] at hiff
      by_cases hp : i.val / 3 = k ∨ (i.val + 1) / 3 = k
      · have h_touch := hiff.mpr hp
        unfold transSkelLC_global
        rw [dif_pos hp]
        simp only [h_succ, dite_true, Option.filter, decide_eq_true h_touch, if_true]
      · have h_neg : ¬ cookLevinConstraintTouchesBlock
            (cook_levin_compilation M n hn htb hns) b (transSkelLC M n q i h_succ) :=
          fun h => hp (hiff.mp h)
        unfold transSkelLC_global
        rw [dif_neg hp]
        simp only [h_succ, dite_true, Option.filter, decide_eq_false h_neg,
                   Bool.false_eq_true, ↓reduceIte]
    · unfold transSkelLC_global
      by_cases hp : i.val / 3 = k ∨ (i.val + 1) / 3 = k
      · exact absurd (adj_pred_implies_succ_lt n k hk2 i hp) h_succ
      · rw [dif_neg hp]
        simp only [h_succ, dite_false, Option.filter]
  rw [inner_eq]
  -- (finRange n).filterMap (transSkelLC_global M n k hk2 q) = [...]
  rw [filterMap_eq_filterMap_filter_isSome (transSkelLC_global M n k hk2 q)]
  have filter_congr : (List.finRange n).filter
        (fun i => (transSkelLC_global M n k hk2 q i).isSome) =
      (List.finRange n).filter (fun i => decide (i.val / 3 = k ∨ (i.val + 1) / 3 = k)) := by
    apply List.filter_congr
    intro v _hv
    exact transSkelLC_global_isSome_eq_pred M n k hk2 q v
  rw [filter_congr]
  rw [finRange_filter_adj_eq n k hk1 (by omega)]
  unfold transSkelLC_global
  have hpred_minus : (⟨3 * k - 1, by omega⟩ : Fin n).val / 3 = k ∨
      ((⟨3 * k - 1, by omega⟩ : Fin n).val + 1) / 3 = k := by
    right
    change (3 * k - 1 + 1) / 3 = k
    rw [show (3 * k - 1 + 1 : ℕ) = 3 * k from by omega]
    exact Nat.mul_div_cancel_left k (by norm_num : (0 : ℕ) < 3)
  have hpred_zero : (⟨3 * k, by omega⟩ : Fin n).val / 3 = k ∨
      ((⟨3 * k, by omega⟩ : Fin n).val + 1) / 3 = k := by
    left
    exact Nat.mul_div_cancel_left k (by norm_num : (0 : ℕ) < 3)
  have hpred_one : (⟨3 * k + 1, by omega⟩ : Fin n).val / 3 = k ∨
      ((⟨3 * k + 1, by omega⟩ : Fin n).val + 1) / 3 = k := by
    left
    show (3 * k + 1 : ℕ) / 3 = k
    rw [show (3 * k + 1 : ℕ) = 1 + k * 3 from by ring]
    rw [Nat.add_mul_div_right 1 k (by norm_num : (0 : ℕ) < 3)]
    omega
  have hpred_two : (⟨3 * k + 2, by omega⟩ : Fin n).val / 3 = k ∨
      ((⟨3 * k + 2, by omega⟩ : Fin n).val + 1) / 3 = k := by
    left
    show (3 * k + 2 : ℕ) / 3 = k
    rw [show (3 * k + 2 : ℕ) = 2 + k * 3 from by ring]
    rw [Nat.add_mul_div_right 2 k (by norm_num : (0 : ℕ) < 3)]
    omega
  rw [show ([⟨3 * k - 1, _⟩, ⟨3 * k, _⟩, ⟨3 * k + 1, _⟩, ⟨3 * k + 2, _⟩] : List (Fin n)) =
        ⟨3 * k - 1, by omega⟩ :: ⟨3 * k, by omega⟩ :: ⟨3 * k + 1, by omega⟩ ::
        ⟨3 * k + 2, by omega⟩ :: [] from rfl]
  rw [List.filterMap_cons_some
        (b := transSkelLC M n q ⟨3 * k - 1, by omega⟩
          (adj_pred_implies_succ_lt n k hk2 _ hpred_minus)) (by rw [dif_pos hpred_minus])]
  rw [List.filterMap_cons_some
        (b := transSkelLC M n q ⟨3 * k, by omega⟩
          (adj_pred_implies_succ_lt n k hk2 _ hpred_zero)) (by rw [dif_pos hpred_zero])]
  rw [List.filterMap_cons_some
        (b := transSkelLC M n q ⟨3 * k + 1, by omega⟩
          (adj_pred_implies_succ_lt n k hk2 _ hpred_one)) (by rw [dif_pos hpred_one])]
  rw [List.filterMap_cons_some
        (b := transSkelLC M n q ⟨3 * k + 2, by omega⟩
          (adj_pred_implies_succ_lt n k hk2 _ hpred_two)) (by rw [dif_pos hpred_two])]
  rw [List.filterMap_nil]

/-! ## Section B: full transSkel enumeration via flatMap -/

/-- Closed form of the transition-skeleton sub-list of
`cookLevinConstraintsTouchingBlock` at an interior block. -/
theorem transSkelConstraintList_filter_at_interior_block
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (transSkelConstraintList M n).filter
        (fun c => decide
          (cookLevinConstraintTouchesBlock
            (cook_levin_compilation M n hn htb hns)
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩ c)) =
      (List.finRange M.numStates).flatMap (fun q =>
        [transSkelLC M n q ⟨3 * k - 1, by omega⟩
          (by change 3 * k - 1 + 1 < n; omega),
         transSkelLC M n q ⟨3 * k, by omega⟩
          (by change 3 * k + 1 < n; omega),
         transSkelLC M n q ⟨3 * k + 1, by omega⟩
          (by change 3 * k + 1 + 1 < n; omega),
         transSkelLC M n q ⟨3 * k + 2, by omega⟩
          (by change 3 * k + 2 + 1 < n; omega)]) := by
  unfold transSkelConstraintList
  rw [List.filter_flatMap]
  apply List.flatMap_congr
  intro q _hq
  exact transSkelForState_filter_at_interior_block M n hn htb hns q k hk1 hk2

/-! ## Section C: discharge the transSkel enumeration obstruction -/

/-- Discharges the transition-skeleton obstruction marker. -/
theorem kappaTwoTouchedList_transSkel_enumeration_closed
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    kappaTwoTouchedList_transSkel_enumeration_obstruction
      M n hn htb hns k hk1 hk2 :=
  kappaTwoTouchedList_transSkel_enumeration_obstruction_holds
    M n hn htb hns k hk1 hk2

/-! ## Axiom audit anchors -/

#print axioms transSkelLC_dite_eq_global
#print axioms transSkelLC_global_isSome_eq_pred
#print axioms transSkelForState_filter_at_interior_block
#print axioms transSkelConstraintList_filter_at_interior_block
#print axioms kappaTwoTouchedList_transSkel_enumeration_closed

end PallLean.Paper93.Paper283
