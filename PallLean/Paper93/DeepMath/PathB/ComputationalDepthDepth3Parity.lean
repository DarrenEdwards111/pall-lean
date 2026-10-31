import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeSwap

/-!
# Block-DT model, foundation 17: the parity lower bound (the contradiction target) (branch only)

The endpoint of the AC⁰ depth-reduction pipeline: the shallow object it produces cannot compute
**parity**.  This is the target contradiction of step (6).

> A decision tree computing `n`-bit parity has depth `≥ n`; equivalently, a tree of depth `< n` cannot
> compute parity.

Proof (full variable sensitivity).  Along any input's computation path a depth-`d` tree queries at most
`d` variables (`pathVars_card_le_depth`).  Flipping an *unqueried* variable does not change the leaf
reached (`eval_invariant_off_path`), so the output is unchanged — but parity flips under any single-bit
flip (`parity_flip`).  If `d < n` some variable is unqueried on the path, giving the contradiction.

* `parity` — `n`-bit parity (oddness of the number of `true` coordinates).
* `parity_flip` — flipping any one bit flips parity (full sensitivity).
* `pathVars` / `pathVars_card_le_depth` — the variables queried on an input's path, `≤ depth` of them.
* `eval_invariant_off_path` — flipping an unqueried variable leaves the output unchanged.
* `parity_needs_full_depth` — a tree computing parity has depth `≥ n`.
* `shallow_dtree_not_parity` — a tree of depth `< n` does **not** compute parity.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

namespace DTree

variable {n : ℕ}

/-! ### Parity and its full sensitivity -/

/-- The number of `true` coordinates. -/
def trueCount (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

/-- `n`-bit parity: oddness of the number of `true` coordinates. -/
def parity (x : Fin n → Bool) : Bool := decide (Odd (trueCount x))

/-- `decide ∘ Odd` toggles under `+1`. -/
theorem decide_odd_succ (m : ℕ) : decide (Odd (m + 1)) = !decide (Odd m) := by
  by_cases hm : Odd m
  · have h2 : ¬ Odd (m + 1) := by rw [Nat.odd_iff] at hm ⊢; omega
    simp [hm, h2]
  · have h2 : Odd (m + 1) := by rw [Nat.odd_iff] at hm ⊢; omega
    simp [hm, h2]

/-- `decide ∘ Odd` toggles under `-1` (for `m ≥ 1`). -/
theorem decide_odd_pred (m : ℕ) (hm1 : 1 ≤ m) : decide (Odd (m - 1)) = !decide (Odd m) := by
  by_cases hm : Odd m
  · have h2 : ¬ Odd (m - 1) := by rw [Nat.odd_iff] at hm ⊢; omega
    simp [hm, h2]
  · have h2 : Odd (m - 1) := by rw [Nat.odd_iff] at hm ⊢; omega
    simp [hm, h2]

/-- Flipping coordinate `j` changes the true-count by erasing/inserting `j`. -/
theorem trueCount_update (x : Fin n → Bool) (j : Fin n) :
    trueCount (Function.update x j (!x j))
      = if x j = true then trueCount x - 1 else trueCount x + 1 := by
  classical
  unfold trueCount
  by_cases hxj : x j = true
  · rw [if_pos hxj]
    have hset : Finset.univ.filter (fun i => Function.update x j (!x j) i = true)
        = (Finset.univ.filter (fun i => x i = true)).erase j := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hij : i = j
      · subst hij; simp [Function.update_self, hxj]
      · rw [Function.update_of_ne hij]; tauto
    rw [hset, Finset.card_erase_of_mem]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hxj
  · rw [if_neg hxj]
    have hxjf : x j = false := by cases h : x j <;> simp_all
    have hset : Finset.univ.filter (fun i => Function.update x j (!x j) i = true)
        = insert j (Finset.univ.filter (fun i => x i = true)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hij : i = j
      · subst hij; simp [Function.update_self, hxjf]
      · rw [Function.update_of_ne hij]; tauto
    rw [hset, Finset.card_insert_of_notMem]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hxj

/-- **Full sensitivity.**  Flipping any one bit flips parity. -/
theorem parity_flip (x : Fin n → Bool) (j : Fin n) :
    parity (Function.update x j (!x j)) = !parity x := by
  unfold parity
  rw [trueCount_update]
  by_cases hxj : x j = true
  · rw [if_pos hxj]
    have hpos : 1 ≤ trueCount x := by
      rw [trueCount, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
      intro he
      have hjmem : j ∈ Finset.univ.filter (fun i => x i = true) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hxj
      rw [he] at hjmem; exact Finset.notMem_empty j hjmem
    exact decide_odd_pred (trueCount x) hpos
  · rw [if_neg hxj]
    exact decide_odd_succ (trueCount x)

/-! ### Path variables and invariance -/

/-- The variables queried along the computation path of `x`. -/
def pathVars : DTree n → (Fin n → Bool) → Finset (Fin n)
  | leaf _, _ => ∅
  | node v lo hi, x => insert v (if x v then pathVars hi x else pathVars lo x)

/-- A depth-`d` tree queries at most `d` variables on any input's path. -/
theorem pathVars_card_le_depth (t : DTree n) (x : Fin n → Bool) :
    (pathVars t x).card ≤ t.depth := by
  induction t with
  | leaf c => simp [pathVars, depth]
  | node v lo hi ihlo ihhi =>
    rw [pathVars, depth]
    refine le_trans (Finset.card_insert_le _ _) ?_
    by_cases hv : x v = true
    · rw [if_pos hv]
      have hm : hi.depth ≤ max lo.depth hi.depth := le_max_right _ _
      omega
    · rw [if_neg hv]
      have hm : lo.depth ≤ max lo.depth hi.depth := le_max_left _ _
      omega

/-- **Off-path invariance.**  Flipping a variable not queried on `x`'s path leaves the output fixed. -/
theorem eval_invariant_off_path (t : DTree n) (x : Fin n → Bool) (j : Fin n) (b : Bool)
    (hj : j ∉ pathVars t x) : t.eval (Function.update x j b) = t.eval x := by
  induction t with
  | leaf c => rfl
  | node v lo hi ihlo ihhi =>
    rw [pathVars, Finset.mem_insert, not_or] at hj
    obtain ⟨hjv, hjS⟩ := hj
    have hxv : (Function.update x j b) v = x v := Function.update_of_ne (Ne.symm hjv) b x
    show (if (Function.update x j b) v then hi.eval (Function.update x j b)
            else lo.eval (Function.update x j b))
          = (if x v then hi.eval x else lo.eval x)
    rw [hxv]
    by_cases hv : x v = true
    · rw [if_pos hv, if_pos hv]; rw [if_pos hv] at hjS; exact ihhi hjS
    · rw [if_neg hv, if_neg hv]; rw [if_neg hv] at hjS; exact ihlo hjS

/-! ### The parity lower bound -/

/-- **Parity needs full depth.**  A decision tree computing parity has depth `≥ n`. -/
theorem parity_needs_full_depth (t : DTree n) (h : ∀ x, t.eval x = parity x) :
    n ≤ t.depth := by
  classical
  by_contra hlt
  push_neg at hlt
  set x : Fin n → Bool := fun _ => false with hx
  have hpv : (pathVars t x).card ≤ t.depth := pathVars_card_le_depth t x
  have hne : pathVars t x ≠ Finset.univ := by
    intro he; rw [he, Finset.card_univ, Fintype.card_fin] at hpv; omega
  have hex : ∃ j, j ∉ pathVars t x := by
    by_contra hall; push_neg at hall; exact hne (Finset.eq_univ_of_forall hall)
  obtain ⟨j, hj⟩ := hex
  have hinv : t.eval (Function.update x j (!x j)) = t.eval x :=
    eval_invariant_off_path t x j (!x j) hj
  have e1 := h (Function.update x j (!x j))
  rw [parity_flip, hinv, h x] at e1
  simp at e1

/-- **A shallow tree is not parity.**  A decision tree of depth `< n` does not compute parity. -/
theorem shallow_dtree_not_parity (t : DTree n) (hd : t.depth < n) :
    ∃ x, t.eval x ≠ parity x := by
  by_contra hall
  push_neg at hall
  exact absurd (parity_needs_full_depth t hall) (by omega)

end DTree

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.parity_flip
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.parity_needs_full_depth
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.shallow_dtree_not_parity
