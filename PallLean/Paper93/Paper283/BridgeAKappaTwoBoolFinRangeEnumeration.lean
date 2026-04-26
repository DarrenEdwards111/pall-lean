import PallLean.Paper93.Paper283.BridgeAKappaTwoTouchedListDecomposition

/-!
# Bool-finRange enumeration for κ=2 Bridge A

Discharges the boolean-side sub-obligation
`kappaTwoTouchedList_boolFinRange_enumeration_obstruction` exposed in
`BridgeAKappaTwoTouchedListDecomposition`.  The technical core is

```
∀ n k, 3*k+3 ≤ n →
  (List.finRange n).filter (fun v : Fin n => decide (v.val / 3 = k)) =
    [⟨3*k⟩, ⟨3*k+1⟩, ⟨3*k+2⟩]
```

The proof routes through the `List.range` version (where the arithmetic is
cleanest) and lifts to `List.finRange` via the projection
`(finRange n).map Fin.val = range n` plus `Fin.val` injectivity on `List.map`.

Combined with `boolConstraintList_filter_eq_finRange_filter_mapped` from the
decomposition file, this yields the closed-form
`boolConstraintList_filter_at_interior_block`, removing one of the three
sub-blockers recorded in `BridgeAKappaTwoFourIdentitiesProven`.

No new axioms.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

attribute [local instance] Classical.dec

/-! ## Section A: division and range arithmetic helpers -/

/-- For `r < 3`, division `(3 * k + r) / 3 = k`. -/
private lemma threeKAdd_lt_three_div_three (k r : ℕ) (hr : r < 3) :
    (3 * k + r) / 3 = k := by
  rw [show (3 * k + r : ℕ) = r + k * 3 from by ring]
  rw [Nat.add_mul_div_right r k (by norm_num : (0 : ℕ) < 3)]
  have hr' : r / 3 = 0 := Nat.div_eq_of_lt hr
  omega

/-- Three-step range successor: `range (m + 3) = range m ++ [m, m+1, m+2]`. -/
private lemma range_three_succ (m : ℕ) :
    List.range (m + 3) = List.range m ++ [m, m + 1, m + 2] := by
  show List.range (m + 2 + 1) = _
  rw [List.range_succ]
  show List.range (m + 1 + 1) ++ [m + 2] = _
  rw [List.range_succ]
  rw [List.range_succ]
  -- Goal: ((List.range m ++ [m]) ++ [m + 1]) ++ [m + 2] = List.range m ++ [m, m + 1, m + 2]
  simp [List.append_assoc]

/-- For any bound `m ≤ 3 * k`, every element of `range m` has `i / 3 < k`,
so the `decide (· / 3 = k)` filter is empty. -/
private theorem range_filter_div3_eq_nil_le
    (m k : ℕ) (h : m ≤ 3 * k) :
    (List.range m).filter (fun i => decide (i / 3 = k)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro i hi
  have hi_lt_m : i < m := List.mem_range.mp hi
  have hi_lt : i < 3 * k := lt_of_lt_of_le hi_lt_m h
  have hdiv_lt : i / 3 < k := by
    by_contra hcontra
    push_neg at hcontra
    have h1 : 3 * k ≤ 3 * (i / 3) := Nat.mul_le_mul_left 3 hcontra
    have h2 : 3 * (i / 3) ≤ i := Nat.mul_div_le i 3
    omega
  intro hp
  exact (Nat.ne_of_lt hdiv_lt) (decide_eq_true_iff.mp hp)

/-! ## Section B: range-side base case at `n = 3*k+3` -/

private theorem range_filter_div3_eq_at_base (k : ℕ) :
    (List.range (3 * k + 3)).filter (fun i => decide (i / 3 = k)) =
      [3 * k, 3 * k + 1, 3 * k + 2] := by
  -- range (3k+3) = range (3k) ++ [3k, 3k+1, 3k+2]
  rw [range_three_succ (3 * k), List.filter_append]
  rw [range_filter_div3_eq_nil_le (3 * k) k (le_refl _)]
  rw [List.nil_append]
  -- Goal: [3k, 3k+1, 3k+2].filter (fun i => decide (i/3 = k)) = [3k, 3k+1, 3k+2]
  -- All three pass.
  have hd0 : (3 * k : ℕ) / 3 = k :=
    Nat.mul_div_cancel_left k (by norm_num : (0 : ℕ) < 3)
  have hd1 : (3 * k + 1 : ℕ) / 3 = k :=
    threeKAdd_lt_three_div_three k 1 (by norm_num)
  have hd2 : (3 * k + 2 : ℕ) / 3 = k :=
    threeKAdd_lt_three_div_three k 2 (by norm_num)
  have hp0 : decide ((3 * k : ℕ) / 3 = k) = true := decide_eq_true_iff.mpr hd0
  have hp1 : decide ((3 * k + 1 : ℕ) / 3 = k) = true := decide_eq_true_iff.mpr hd1
  have hp2 : decide ((3 * k + 2 : ℕ) / 3 = k) = true := decide_eq_true_iff.mpr hd2
  show ((3 * k) :: (3 * k + 1) :: (3 * k + 2) :: ([] : List ℕ)).filter
        (fun i => decide (i / 3 = k)) = _
  rw [List.filter_cons_of_pos hp0]
  rw [List.filter_cons_of_pos hp1]
  rw [List.filter_cons_of_pos hp2]
  rw [List.filter_nil]

/-! ## Section C: range-side step from `3*k+3` upward -/

private theorem range_filter_div3_eq_three
    (n k : ℕ) (h : 3 * k + 3 ≤ n) :
    (List.range n).filter (fun i => decide (i / 3 = k)) =
      [3 * k, 3 * k + 1, 3 * k + 2] := by
  induction h with
  | refl => exact range_filter_div3_eq_at_base k
  | step hmm ih =>
    rename_i m
    rw [List.range_succ, List.filter_append, ih]
    -- New tail element `m` has `m / 3 > k` (since `m ≥ 3*k+3`).
    have hm_div_gt : k < m / 3 := by
      have h3k3 : 3 * k + 3 ≤ m := hmm
      have : k + 1 ≤ m / 3 :=
        (Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 3)).mpr (by linarith)
      omega
    have hm_ne : m / 3 ≠ k := Nat.ne_of_gt hm_div_gt
    have hm_neg : decide (m / 3 = k) = false := decide_eq_false hm_ne
    -- [m].filter p = [] when p m = false; then [3k, 3k+1, 3k+2] ++ [] reduces.
    simp [hm_neg]

/-! ## Section D: lift to `List.finRange` via `Fin.val` injectivity -/

/-- The boolean sub-list filter on `List.finRange n` enumerates exactly to
`[⟨3k⟩, ⟨3k+1⟩, ⟨3k+2⟩]` for an interior block `k` (`3*k+3 ≤ n`). -/
theorem finRange_filter_div3_eq
    (n k : ℕ) (h : 3 * k + 3 ≤ n) :
    (List.finRange n).filter (fun v : Fin n => decide (v.val / 3 = k)) =
      [⟨3 * k, by omega⟩,
       ⟨3 * k + 1, by omega⟩,
       ⟨3 * k + 2, by omega⟩] := by
  apply Fin.val_injective.list_map
  -- Goal: ((finRange n).filter (fun v => decide (v.val/3 = k))).map Fin.val
  --       = [⟨3k⟩, ⟨3k+1⟩, ⟨3k+2⟩].map Fin.val
  rw [show (fun v : Fin n => decide (v.val / 3 = k)) =
        ((fun i : ℕ => decide (i / 3 = k)) ∘ Fin.val) from rfl]
  rw [← List.filter_map]
  rw [List.map_coe_finRange_eq_range]
  rw [range_filter_div3_eq_three n k h]
  rfl

/-! ## Section E: closed form for the boolean sub-list of touchedList

Combines the `finRange` enumeration above with
`boolConstraintList_filter_eq_finRange_filter_mapped` to give an explicit
list of `boolLC` calls for the boolean sub-list of
`cookLevinConstraintsTouchingBlock` at an interior block. -/

/-- Closed form of the boolean sub-list of
`cookLevinConstraintsTouchingBlock` at an interior block whose index is
`k` (with the canonical `Fin _` packaging via `cook_levin_numBlocks`). -/
theorem boolConstraintList_filter_at_interior_block
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (boolConstraintList n).filter
        (fun c => decide
          (cookLevinConstraintTouchesBlock
            (cook_levin_compilation M n hn htb hns)
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩ c)) =
      [boolLC n ⟨3 * k, by omega⟩,
       boolLC n ⟨3 * k + 1, by omega⟩,
       boolLC n ⟨3 * k + 2, by omega⟩] := by
  rw [boolConstraintList_filter_eq_finRange_filter_mapped
        M n hn htb hns ⟨k, by rw [cook_levin_numBlocks]; omega⟩]
  rw [show ((⟨k, by rw [cook_levin_numBlocks]; omega⟩ :
            Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks).val) =
        k from rfl]
  rw [finRange_filter_div3_eq n k (by omega)]
  rfl

/-! ## Axiom audit anchors -/

#print axioms threeKAdd_lt_three_div_three
#print axioms range_three_succ
#print axioms range_filter_div3_eq_nil_le
#print axioms range_filter_div3_eq_at_base
#print axioms range_filter_div3_eq_three
#print axioms finRange_filter_div3_eq
#print axioms boolConstraintList_filter_at_interior_block

end PallLean.Paper93.Paper283
