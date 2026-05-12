import PallLean.Paper93.Paper283.BridgeAKappaTwoTouchedListDecomposition

/-!
# Adj-finRange enumeration for κ=2 Bridge A

Discharges the adjacency-side sub-obligation
`kappaTwoTouchedList_adj_enumeration_obstruction` exposed in
`BridgeAKappaTwoTouchedListDecomposition`.

The proof routes through a `List.range` enumeration of the adj predicate
and lifts to `List.finRange` via `Fin.val` injectivity.  The interaction
with the touch-predicate filter is handled via `List.filter_filterMap`
together with the `cookLevinConstraintTouchesBlock_pair_iff`
characterisation and a `filterMap`-restriction lemma that lets us reduce
the global filterMap to one over the explicitly-enumerated four-element
filtered index list.

No new axioms.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open PaperFaithfulSeparation

attribute [local instance] Classical.dec

/-! ## Section A: arithmetic helpers -/

/-- For `r < 3`, division `(3 * k + r) / 3 = k`. -/
private lemma threeKAdd_lt_three_div_three (k r : ℕ) (hr : r < 3) :
    (3 * k + r) / 3 = k := by
  rw [show (3 * k + r : ℕ) = r + k * 3 from by ring]
  rw [Nat.add_mul_div_right r k (by norm_num : (0 : ℕ) < 3)]
  have hr' : r / 3 = 0 := Nat.div_eq_of_lt hr
  omega

/-- Four-step range successor: `range (m + 4) = range m ++ [m, m+1, m+2, m+3]`. -/
private lemma range_four_succ (m : ℕ) :
    List.range (m + 4) = List.range m ++ [m, m + 1, m + 2, m + 3] := by
  show List.range (m + 3 + 1) = _
  rw [List.range_succ]
  show List.range (m + 2 + 1) ++ [m + 3] = _
  rw [List.range_succ]
  show (List.range (m + 1 + 1) ++ [m + 2]) ++ [m + 3] = _
  rw [List.range_succ]
  show ((List.range (m + 1) ++ [m + 1]) ++ [m + 2]) ++ [m + 3] = _
  rw [List.range_succ]
  simp [List.append_assoc]

/-! ## Section B: range-side enumeration for the adj predicate -/

/-- For `1 ≤ k` and any `m ≤ 3*k - 1`, every element of `range m` fails the
adjacency predicate. -/
private theorem range_filter_adj_eq_nil_le
    (m k : ℕ) (hk : 1 ≤ k) (h : m ≤ 3 * k - 1) :
    (List.range m).filter (fun i => decide (i / 3 = k ∨ (i + 1) / 3 = k)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro i hi
  have hi_lt_m : i < m := List.mem_range.mp hi
  have hi_lt : i < 3 * k - 1 := lt_of_lt_of_le hi_lt_m h
  have hi_succ_lt : i + 1 < 3 * k := by omega
  have hdiv_lt : i / 3 < k := by
    by_contra hcontra
    push_neg at hcontra
    have h1 : 3 * k ≤ 3 * (i / 3) := Nat.mul_le_mul_left 3 hcontra
    have h2 : 3 * (i / 3) ≤ i := Nat.mul_div_le i 3
    omega
  have hdiv_succ_lt : (i + 1) / 3 < k := by
    by_contra hcontra
    push_neg at hcontra
    have h1 : 3 * k ≤ 3 * ((i + 1) / 3) := Nat.mul_le_mul_left 3 hcontra
    have h2 : 3 * ((i + 1) / 3) ≤ i + 1 := Nat.mul_div_le (i + 1) 3
    omega
  intro hp
  rcases decide_eq_true_iff.mp hp with hp | hp
  · exact (Nat.ne_of_lt hdiv_lt) hp
  · exact (Nat.ne_of_lt hdiv_succ_lt) hp

/-- Base case at `n = 3*k + 3`. -/
private theorem range_filter_adj_eq_at_base (k : ℕ) (hk : 1 ≤ k) :
    (List.range (3 * k + 3)).filter (fun i => decide (i / 3 = k ∨ (i + 1) / 3 = k)) =
      [3 * k - 1, 3 * k, 3 * k + 1, 3 * k + 2] := by
  have h_eq : 3 * k + 3 = (3 * k - 1) + 4 := by omega
  rw [h_eq]
  rw [range_four_succ (3 * k - 1)]
  rw [List.filter_append]
  rw [range_filter_adj_eq_nil_le (3 * k - 1) k hk (le_refl _)]
  rw [List.nil_append]
  have e1 : (3 * k - 1 + 1 : ℕ) = 3 * k := by omega
  have e2 : (3 * k - 1 + 2 : ℕ) = 3 * k + 1 := by omega
  have e3 : (3 * k - 1 + 3 : ℕ) = 3 * k + 2 := by omega
  rw [e1, e2, e3]
  have hd0 : (3 * k : ℕ) / 3 = k := Nat.mul_div_cancel_left k (by norm_num : (0 : ℕ) < 3)
  have hd1 : (3 * k + 1 : ℕ) / 3 = k := threeKAdd_lt_three_div_three k 1 (by norm_num)
  have hd2 : (3 * k + 2 : ℕ) / 3 = k := threeKAdd_lt_three_div_three k 2 (by norm_num)
  have hpm : decide ((3 * k - 1 : ℕ) / 3 = k ∨ (3 * k - 1 + 1) / 3 = k) = true := by
    apply decide_eq_true_iff.mpr; right; rw [e1]; exact hd0
  have hp0 : decide ((3 * k : ℕ) / 3 = k ∨ (3 * k + 1) / 3 = k) = true :=
    decide_eq_true_iff.mpr (Or.inl hd0)
  have hp1 : decide ((3 * k + 1 : ℕ) / 3 = k ∨ (3 * k + 1 + 1) / 3 = k) = true :=
    decide_eq_true_iff.mpr (Or.inl hd1)
  have hp2 : decide ((3 * k + 2 : ℕ) / 3 = k ∨ (3 * k + 2 + 1) / 3 = k) = true :=
    decide_eq_true_iff.mpr (Or.inl hd2)
  show ((3 * k - 1) :: (3 * k) :: (3 * k + 1) :: (3 * k + 2) :: []).filter
        (fun i => decide (i / 3 = k ∨ (i + 1) / 3 = k)) = _
  simp only [List.filter_cons, hpm, hp0, hp1, hp2, if_true, List.filter_nil]

/-- Range-side step from `3*k+3` upward. -/
private theorem range_filter_adj_eq_three
    (n k : ℕ) (hk : 1 ≤ k) (h : 3 * k + 3 ≤ n) :
    (List.range n).filter (fun i => decide (i / 3 = k ∨ (i + 1) / 3 = k)) =
      [3 * k - 1, 3 * k, 3 * k + 1, 3 * k + 2] := by
  induction h with
  | refl => exact range_filter_adj_eq_at_base k hk
  | step hmm ih =>
    rename_i m
    rw [List.range_succ, List.filter_append, ih]
    have hm_div_gt : k < m / 3 := by
      have h3k3 : 3 * k + 3 ≤ m := hmm
      have : k + 1 ≤ m / 3 :=
        (Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 3)).mpr (by linarith)
      omega
    have hm_succ_div_gt : k < (m + 1) / 3 := by
      have h3k3 : 3 * k + 3 ≤ m := hmm
      have : k + 1 ≤ (m + 1) / 3 :=
        (Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 3)).mpr (by linarith)
      omega
    have hm_neg : decide (m / 3 = k ∨ (m + 1) / 3 = k) = false := by
      apply decide_eq_false
      rintro (h1 | h2)
      · exact (Nat.lt_irrefl k) (h1 ▸ hm_div_gt)
      · exact (Nat.lt_irrefl k) (h2 ▸ hm_succ_div_gt)
    rw [List.filter_cons_of_neg (by rw [hm_neg]; decide)]
    rw [List.filter_nil]
    rw [List.append_nil]

/-! ## Section C: lift to `List.finRange` -/

/-- The adj sub-list filter on `List.finRange n` enumerates exactly to
`[⟨3k-1⟩, ⟨3k⟩, ⟨3k+1⟩, ⟨3k+2⟩]` for an interior block `k`. -/
theorem finRange_filter_adj_eq
    (n k : ℕ) (hk : 1 ≤ k) (h : 3 * k + 3 ≤ n) :
    (List.finRange n).filter (fun v : Fin n =>
        decide (v.val / 3 = k ∨ (v.val + 1) / 3 = k)) =
      [⟨3 * k - 1, by omega⟩,
       ⟨3 * k, by omega⟩,
       ⟨3 * k + 1, by omega⟩,
       ⟨3 * k + 2, by omega⟩] := by
  apply Fin.val_injective.list_map
  rw [show (fun v : Fin n => decide (v.val / 3 = k ∨ (v.val + 1) / 3 = k)) =
        ((fun i : ℕ => decide (i / 3 = k ∨ (i + 1) / 3 = k)) ∘ Fin.val) from rfl]
  rw [← List.filter_map]
  rw [List.map_coe_finRange_eq_range]
  rw [range_filter_adj_eq_three n k hk h]
  rfl

/-! ## Section D: bridge from `adjConstraintList` to `finRange` -/

/-- Auxiliary: indices `i` whose adj predicate fires at block `k`
(with `3*k+3 < n`) satisfy `i.val + 1 < n`. -/
lemma adj_pred_implies_succ_lt
    (n k : ℕ) (hn : 3 * k + 3 < n) (i : Fin n)
    (hp : i.val / 3 = k ∨ (i.val + 1) / 3 = k) :
    i.val + 1 < n := by
  rcases hp with hp | hp
  · have h_lo : 3 * k ≤ i.val := by
      have h2 : 3 * (i.val / 3) ≤ i.val := Nat.mul_div_le i.val 3
      omega
    have h_hi : i.val < 3 * k + 3 := by
      by_contra hcon
      push_neg at hcon
      have hk_succ_le : k + 1 ≤ i.val / 3 :=
        (Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 3)).mpr (by linarith)
      omega
    omega
  · have h_lo : 3 * k ≤ i.val + 1 := by
      have h2 : 3 * ((i.val + 1) / 3) ≤ i.val + 1 := Nat.mul_div_le (i.val + 1) 3
      omega
    have h_hi : i.val + 1 < 3 * k + 3 := by
      by_contra hcon
      push_neg at hcon
      have hk_succ_le : k + 1 ≤ (i.val + 1) / 3 :=
        (Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 3)).mpr (by linarith)
      omega
    omega

/-- Global Option-valued combinator for the adj filter. -/
private noncomputable def adjLC_global (n k : ℕ) (hk2 : 3 * k + 3 < n) :
    Fin n → Option (LocalConstraint n) := fun i =>
  if hp : i.val / 3 = k ∨ (i.val + 1) / 3 = k then
    some (adjLC n i (adj_pred_implies_succ_lt n k hk2 i hp))
  else none

/-- The dite/ite form arising from `Option.filter` reduces to
`adjLC_global` on `Fin n`. -/
private lemma adjLC_dite_eq_global
    (n k : ℕ) (hk2 : 3 * k + 3 < n) (i : Fin n) :
    (if h : i.val + 1 < n then
        if decide (i.val / 3 = k ∨ (i.val + 1) / 3 = k) then
          some (adjLC n i h)
        else none
      else none) =
      adjLC_global n k hk2 i := by
  unfold adjLC_global
  by_cases hp : i.val / 3 = k ∨ (i.val + 1) / 3 = k
  · have h_succ : i.val + 1 < n := adj_pred_implies_succ_lt n k hk2 i hp
    rw [dif_pos h_succ, if_pos (decide_eq_true hp), dif_pos hp]
  · rw [dif_neg hp]
    by_cases h_succ : i.val + 1 < n
    · rw [dif_pos h_succ, if_neg (by simpa using hp)]
    · rw [dif_neg h_succ]

/-- Generic `filterMap`-restriction: a `filterMap` is unchanged by
restricting the input list to the elements where it produces `some`. -/
lemma filterMap_eq_filterMap_filter_isSome
    {α β : Type*} (g : α → Option β) (L : List α) :
    L.filterMap g = (L.filter (fun a => (g a).isSome)).filterMap g := by
  induction L with
  | nil => simp
  | cons a as ih =>
    by_cases hg : (g a).isSome
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hg
      rw [List.filterMap_cons_some hb,
          List.filter_cons_of_pos (p := fun a => (g a).isSome) (by simp [hb])]
      rw [List.filterMap_cons_some hb]
      congr 1
    · have hga : g a = none := Option.not_isSome_iff_eq_none.mp hg
      rw [List.filterMap_cons_none hga]
      rw [List.filter_cons_of_neg (p := fun a => (g a).isSome) (by simp [hga])]
      exact ih

/-- The `isSome`-filter on `adjLC_global` collapses to the index predicate
filter. -/
private lemma adjLC_global_isSome_eq_pred
    (n k : ℕ) (hk2 : 3 * k + 3 < n) (i : Fin n) :
    (adjLC_global n k hk2 i).isSome =
      decide (i.val / 3 = k ∨ (i.val + 1) / 3 = k) := by
  unfold adjLC_global
  by_cases hp : i.val / 3 = k ∨ (i.val + 1) / 3 = k
  · simp [hp]
  · simp [hp]

/-- Closed form of the adjacency sub-list of
`cookLevinConstraintsTouchingBlock` at an interior block. -/
theorem adjConstraintList_filter_at_interior_block
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (adjConstraintList n).filter
        (fun c => decide
          (cookLevinConstraintTouchesBlock
            (cook_levin_compilation M n hn htb hns)
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩ c)) =
      [adjLC n ⟨3 * k - 1, by omega⟩ (by change 3 * k - 1 + 1 < n; omega),
       adjLC n ⟨3 * k, by omega⟩ (by change 3 * k + 1 < n; omega),
       adjLC n ⟨3 * k + 1, by omega⟩ (by change 3 * k + 1 + 1 < n; omega),
       adjLC n ⟨3 * k + 2, by omega⟩ (by change 3 * k + 2 + 1 < n; omega)] := by
  unfold adjConstraintList
  rw [List.filter_filterMap]
  set b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks :=
    ⟨k, by rw [cook_levin_numBlocks]; omega⟩ with hb_def
  have set_b : b.val = k := rfl
  -- Replace inner Option.filter with adjLC_global.
  have inner_eq : (fun i : Fin n =>
        Option.filter
          (fun c => decide
            (cookLevinConstraintTouchesBlock
              (cook_levin_compilation M n hn htb hns) b c))
          (if h : i.val + 1 < n then some (adjLC n i h) else none)) =
      adjLC_global n k hk2 := by
    funext i
    by_cases h_succ : i.val + 1 < n
    · have hsupp : (adjLC n i h_succ).support =
          ({i, ⟨i.val + 1, h_succ⟩} : Finset (Fin n)) := rfl
      have hiff :=
        cookLevinConstraintTouchesBlock_pair_iff
          M n hn htb hns b (adjLC n i h_succ) i ⟨i.val + 1, h_succ⟩ hsupp
      rw [set_b] at hiff
      by_cases hp : i.val / 3 = k ∨ (i.val + 1) / 3 = k
      · have h_touch := hiff.mpr hp
        unfold adjLC_global
        rw [dif_pos hp]
        simp only [h_succ, dite_true, Option.filter, decide_eq_true h_touch, if_true]
      · have h_neg : ¬ cookLevinConstraintTouchesBlock
            (cook_levin_compilation M n hn htb hns) b (adjLC n i h_succ) :=
          fun h => hp (hiff.mp h)
        unfold adjLC_global
        rw [dif_neg hp]
        simp only [h_succ, dite_true, Option.filter, decide_eq_false h_neg, if_false,
                   Bool.false_eq_true, ↓reduceIte]
    · unfold adjLC_global
      by_cases hp : i.val / 3 = k ∨ (i.val + 1) / 3 = k
      · exact absurd (adj_pred_implies_succ_lt n k hk2 i hp) h_succ
      · rw [dif_neg hp]
        simp only [h_succ, dite_false, Option.filter]
  rw [inner_eq]
  -- Now: (finRange n).filterMap (adjLC_global n k hk2) = [...]
  -- Use filterMap_eq_filterMap_filter_isSome to restrict to the 4-elt filtered list.
  rw [filterMap_eq_filterMap_filter_isSome (adjLC_global n k hk2)]
  -- Now: (filter (fun i => isSome (adjLC_global n k hk2 i)) (finRange n)).filterMap (adjLC_global n k hk2) = [...]
  -- The filter equals (finRange n).filter (fun i => decide pred) by adjLC_global_isSome_eq_pred.
  have filter_congr : (List.finRange n).filter (fun i => (adjLC_global n k hk2 i).isSome) =
      (List.finRange n).filter (fun i => decide (i.val / 3 = k ∨ (i.val + 1) / 3 = k)) := by
    apply List.filter_congr
    intro v _hv
    exact adjLC_global_isSome_eq_pred n k hk2 v
  rw [filter_congr]
  rw [finRange_filter_adj_eq n k hk1 (by omega)]
  -- Now compute filterMap on the explicit 4-elt list.
  -- The 4 indices all satisfy the predicate, so each call to adjLC_global gives some.
  unfold adjLC_global
  -- Each ⟨3k+r, _⟩ has predicate true.
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
    exact threeKAdd_lt_three_div_three k 1 (by norm_num)
  have hpred_two : (⟨3 * k + 2, by omega⟩ : Fin n).val / 3 = k ∨
      ((⟨3 * k + 2, by omega⟩ : Fin n).val + 1) / 3 = k := by
    left
    exact threeKAdd_lt_three_div_three k 2 (by norm_num)
  -- Reduce filterMap [⟨3k-1⟩, ..., ⟨3k+2⟩] step by step.
  rw [show ([⟨3 * k - 1, _⟩, ⟨3 * k, _⟩, ⟨3 * k + 1, _⟩, ⟨3 * k + 2, _⟩] : List (Fin n)) =
        ⟨3 * k - 1, by omega⟩ :: ⟨3 * k, by omega⟩ :: ⟨3 * k + 1, by omega⟩ ::
        ⟨3 * k + 2, by omega⟩ :: [] from rfl]
  rw [List.filterMap_cons_some
        (b := adjLC n ⟨3 * k - 1, by omega⟩
          (adj_pred_implies_succ_lt n k hk2 _ hpred_minus)) (by rw [dif_pos hpred_minus])]
  rw [List.filterMap_cons_some
        (b := adjLC n ⟨3 * k, by omega⟩
          (adj_pred_implies_succ_lt n k hk2 _ hpred_zero)) (by rw [dif_pos hpred_zero])]
  rw [List.filterMap_cons_some
        (b := adjLC n ⟨3 * k + 1, by omega⟩
          (adj_pred_implies_succ_lt n k hk2 _ hpred_one)) (by rw [dif_pos hpred_one])]
  rw [List.filterMap_cons_some
        (b := adjLC n ⟨3 * k + 2, by omega⟩
          (adj_pred_implies_succ_lt n k hk2 _ hpred_two)) (by rw [dif_pos hpred_two])]
  rw [List.filterMap_nil]

/-! ## Section E: discharge the adj enumeration obstruction -/

/-- Discharges the adjacency obstruction marker. -/
theorem kappaTwoTouchedList_adj_enumeration_closed
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    kappaTwoTouchedList_adj_enumeration_obstruction
      M n hn htb hns k hk1 hk2 :=
  kappaTwoTouchedList_adj_enumeration_obstruction_holds
    M n hn htb hns k hk1 hk2

/-! ## Axiom audit anchors -/

#print axioms threeKAdd_lt_three_div_three
#print axioms range_four_succ
#print axioms range_filter_adj_eq_nil_le
#print axioms range_filter_adj_eq_at_base
#print axioms range_filter_adj_eq_three
#print axioms finRange_filter_adj_eq
#print axioms adj_pred_implies_succ_lt
#print axioms filterMap_eq_filterMap_filter_isSome
#print axioms adjLC_global_isSome_eq_pred
#print axioms adjConstraintList_filter_at_interior_block
#print axioms kappaTwoTouchedList_adj_enumeration_closed

end PallLean.Paper93.Paper283
