import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATSubfunctions

/-!
# N-Frame: the cost interface — bounded volume realises boundedly many subfunctions per block

The wall between the counting substrate and a volume bound: **a boundary transducer of volume `V` realises at most
`2·16^V` distinct subfunctions on any block** — and, sharper, at most `2·16^ℓ` where `ℓ` counts only the transducer's
*leaves reading that block*.  This is the Nečiporuk counting lemma, native to the `Trans` model (every transducer is
a tree, so it holds at every width — in particular at the proven-necessary dimension 3).

**The unary-closure induction.**  The naive per-node count blows up on `bin` nodes whose other side is
context-constant.  The fix is classical: bound the *unary-closed* family `{h ∘ g_y : h : Bool → Bool}` — constant
sides are then absorbed into the post-composition (`subCap` recurrence `4·C(a)·C(b) ≤ C(a+b)`, exact at every step).

  `subFunsU_card_le` — **PROVED, the counting lemma**: `|{h ∘ g_y}| ≤ subCap ℓ` (`= 4^(2ℓ−1)`, `2` at `ℓ = 0`).
  `subFuns_card_le` / `cost_interface_volume` — **PROVED, the interface**: `≤ 2·16^ℓ ≤ 2·16^V` subfunctions per block.
  `sum_leavesOn_le_volume` — **PROVED**: disjoint blocks' leaf counts sum below the volume.
  `sat3_block_leaves` — **PROVED**: computing `sat3Family` needs `≥ (m−2)/4` leaves in *every* clause block
        (from the `2^(m−1)` per-block subfunction count).
  `sat3_neciporuk_volume` / `sat3_neciporuk_budget` — **PROVED, the closed loop**:
        `sat3M N · (sat3M N − 2) ≤ 4 · budget (sat3Family N)` — a genuine Nečiporuk-style volume lower bound for the
        definite SAT target in the boundary model, with **no hypotheses beyond the layout being non-degenerate**.

## Honest scope — calibration

The bound is `m(m−2)/4 ≈ N/36`: **sublinear** in the input length `N`.  On this layout Nečiporuk cannot beat `~N`
(`m ≈ √N/3` blocks × `m−1` bits each), so the number is modest; the *value* is the closed interface — count ⇒ volume —
through which any stronger per-block count (the conceivable ceiling is `2^(N−D)` contexts) converts directly.
Superpolynomial `sat3Target` remains **open**; Nečiporuk-shape arguments alone cannot reach it.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Merge, block leaves, and subfunction families -/

/-- Merge: read block bits (`P i = true`) from `u`, context bits from `y`. -/
def mergeP {n : ℕ} (P : Fin n → Bool) (y u : Fin n → Bool) : Fin n → Bool :=
  fun i => if P i then u i else y i

theorem mergeP_self {n : ℕ} (P : Fin n → Bool) (y : Fin n → Bool) : mergeP P y y = y := by
  funext i
  show (if P i then y i else y i) = y i
  by_cases h : P i
  · rw [if_pos h]
  · rw [if_neg h]

/-- The number of `var` leaves of the transducer reading the block `P`. -/
def leavesOn {n : ℕ} (P : Fin n → Bool) : Trans n → ℕ
  | .var i => if P i then 1 else 0
  | .cst _ => 0
  | .un _ s => leavesOn P s
  | .bin _ s₁ s₂ => leavesOn P s₁ + leavesOn P s₂

/-- A subtree with no block leaves is context-constant: its value ignores the block input. -/
theorem eval_mergeP_indep {n : ℕ} (P : Fin n → Bool) (s : Trans n)
    (h : leavesOn P s = 0) (y u : Fin n → Bool) :
    eval s (mergeP P y u) = eval s y := by
  induction s with
  | var i =>
    have hP : ¬ (P i = true) := by
      intro hc
      have : leavesOn P (Trans.var i) = 1 := by
        show (if P i then 1 else 0) = 1
        rw [if_pos hc]
      omega
    show (if P i then u i else y i) = y i
    rw [if_neg hP]
  | cst b => rfl
  | un op s ih =>
    show op (eval s (mergeP P y u)) = op (eval s y)
    rw [ih h]
  | bin op s₁ s₂ ih₁ ih₂ =>
    have h12 : leavesOn P s₁ = 0 ∧ leavesOn P s₂ = 0 := by
      have : leavesOn P s₁ + leavesOn P s₂ = 0 := h
      omega
    show op (eval s₁ (mergeP P y u)) (eval s₂ (mergeP P y u)) = op (eval s₁ y) (eval s₂ y)
    rw [ih₁ h12.1, ih₂ h12.2]

/-- The subfunctions of `eval t` on block `P` as the outside context varies. -/
def subFuns {n : ℕ} (P : Fin n → Bool) (t : Trans n) : Finset ((Fin n → Bool) → Bool) :=
  Finset.image (fun y : Fin n → Bool => fun u => eval t (mergeP P y u)) Finset.univ

/-- The unary closure of the subfunction family — the induction-friendly object. -/
def subFunsU {n : ℕ} (P : Fin n → Bool) (t : Trans n) : Finset ((Fin n → Bool) → Bool) :=
  Finset.image (fun p : (Bool → Bool) × (Fin n → Bool) =>
    fun u => p.1 (eval t (mergeP P p.2 u))) Finset.univ

/-- The capacity: `2` at zero block leaves, `4^(2ℓ−1)` at `ℓ ≥ 1`. -/
def subCap (ℓ : ℕ) : ℕ := if ℓ = 0 then 2 else 4 ^ (2 * ℓ - 1)

/-! ### The counting lemma -/

theorem subFunsU_card_le {n : ℕ} (P : Fin n → Bool) (t : Trans n) :
    (subFunsU P t).card ≤ subCap (leavesOn P t) := by
  induction t with
  | var i =>
    by_cases hP : P i = true
    · have hsub : subFunsU P (Trans.var i) ⊆
          Finset.image (fun h : Bool → Bool => (fun u : Fin n → Bool => h (u i)))
            Finset.univ := by
        intro g hg
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hg
        refine Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, ?_⟩
        funext u
        have hev : eval (Trans.var i) (mergeP P p.2 u) = u i := by
          show (if P i then u i else p.2 i) = u i
          rw [if_pos hP]
        rw [hev]
      have h4 : (Finset.univ : Finset (Bool → Bool)).card = 4 := by decide
      have hcap : subCap (leavesOn P (Trans.var i)) = 4 := by
        show subCap (if P i then 1 else 0) = 4
        rw [if_pos hP]
        show (if (1 : ℕ) = 0 then 2 else 4 ^ (2 * 1 - 1)) = 4
        norm_num
      rw [hcap]
      calc (subFunsU P (Trans.var i)).card
          ≤ _ := Finset.card_le_card hsub
        _ ≤ (Finset.univ : Finset (Bool → Bool)).card := Finset.card_image_le
        _ = 4 := h4
    · have hsub : subFunsU P (Trans.var i) ⊆
          Finset.image (fun b : Bool => (fun _ : Fin n → Bool => b)) Finset.univ := by
        intro g hg
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hg
        refine Finset.mem_image.mpr ⟨p.1 (p.2 i), Finset.mem_univ _, ?_⟩
        funext u
        have hev : eval (Trans.var i) (mergeP P p.2 u) = p.2 i := by
          show (if P i then u i else p.2 i) = p.2 i
          rw [if_neg hP]
        rw [hev]
      have h2 : (Finset.univ : Finset Bool).card = 2 := by decide
      have hcap : subCap (leavesOn P (Trans.var i)) = 2 := by
        show subCap (if P i then 1 else 0) = 2
        rw [if_neg hP]
        rfl
      rw [hcap]
      calc (subFunsU P (Trans.var i)).card
          ≤ _ := Finset.card_le_card hsub
        _ ≤ (Finset.univ : Finset Bool).card := Finset.card_image_le
        _ = 2 := h2
  | cst b =>
    have hsub : subFunsU P (Trans.cst b) ⊆
        Finset.image (fun bb : Bool => (fun _ : Fin n → Bool => bb)) Finset.univ := by
      intro g hg
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hg
      exact Finset.mem_image.mpr ⟨p.1 b, Finset.mem_univ _, rfl⟩
    have h2 : (Finset.univ : Finset Bool).card = 2 := by decide
    calc (subFunsU P (Trans.cst b)).card
        ≤ _ := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset Bool).card := Finset.card_image_le
      _ = 2 := h2
  | un op s ih =>
    have hsub : subFunsU P (Trans.un op s) ⊆ subFunsU P s := by
      intro g hg
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hg
      exact Finset.mem_image.mpr ⟨(fun bb => p.1 (op bb), p.2), Finset.mem_univ _, rfl⟩
    exact le_trans (Finset.card_le_card hsub) ih
  | bin op s₁ s₂ ih₁ ih₂ =>
    rcases Nat.eq_zero_or_pos (leavesOn P s₂) with h2 | h2
    · -- right side context-constant: absorbed into the unary closure
      have hsub : subFunsU P (Trans.bin op s₁ s₂) ⊆ subFunsU P s₁ := by
        intro g hg
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hg
        refine Finset.mem_image.mpr
          ⟨(fun bb => p.1 (op bb (eval s₂ p.2)), p.2), Finset.mem_univ _, ?_⟩
        funext u
        show p.1 (op (eval s₁ (mergeP P p.2 u)) (eval s₂ p.2))
            = p.1 (op (eval s₁ (mergeP P p.2 u)) (eval s₂ (mergeP P p.2 u)))
        rw [eval_mergeP_indep P s₂ h2 p.2 u]
      have hℓ : leavesOn P (Trans.bin op s₁ s₂) = leavesOn P s₁ := by
        show leavesOn P s₁ + leavesOn P s₂ = leavesOn P s₁
        omega
      rw [hℓ]
      exact le_trans (Finset.card_le_card hsub) ih₁
    · rcases Nat.eq_zero_or_pos (leavesOn P s₁) with h1 | h1
      · -- left side context-constant
        have hsub : subFunsU P (Trans.bin op s₁ s₂) ⊆ subFunsU P s₂ := by
          intro g hg
          obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hg
          refine Finset.mem_image.mpr
            ⟨(fun bb => p.1 (op (eval s₁ p.2) bb), p.2), Finset.mem_univ _, ?_⟩
          funext u
          show p.1 (op (eval s₁ p.2) (eval s₂ (mergeP P p.2 u)))
              = p.1 (op (eval s₁ (mergeP P p.2 u)) (eval s₂ (mergeP P p.2 u)))
          rw [eval_mergeP_indep P s₁ h1 p.2 u]
        have hℓ : leavesOn P (Trans.bin op s₁ s₂) = leavesOn P s₂ := by
          show leavesOn P s₁ + leavesOn P s₂ = leavesOn P s₂
          omega
        rw [hℓ]
        exact le_trans (Finset.card_le_card hsub) ih₂
      · -- both sides live: pair counting
        have hsub : subFunsU P (Trans.bin op s₁ s₂) ⊆ Finset.image
            (fun q : (Bool → Bool) ×
                (((Fin n → Bool) → Bool) × ((Fin n → Bool) → Bool)) =>
              fun u => q.1 (op (q.2.1 u) (q.2.2 u)))
            (Finset.univ ×ˢ (subFunsU P s₁ ×ˢ subFunsU P s₂)) := by
          intro g hg
          obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hg
          refine Finset.mem_image.mpr
            ⟨(p.1, (fun u => eval s₁ (mergeP P p.2 u), fun u => eval s₂ (mergeP P p.2 u))),
              ?_, rfl⟩
          refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
          · exact Finset.mem_image.mpr ⟨(id, p.2), Finset.mem_univ _, rfl⟩
          · exact Finset.mem_image.mpr ⟨(id, p.2), Finset.mem_univ _, rfl⟩
        have hBB : (Finset.univ : Finset (Bool → Bool)).card = 4 := by decide
        have hprod : ((Finset.univ : Finset (Bool → Bool)) ×ˢ
              (subFunsU P s₁ ×ˢ subFunsU P s₂)).card
            = 4 * ((subFunsU P s₁).card * (subFunsU P s₂).card) := by
          rw [Finset.card_product, Finset.card_product, hBB]
        have hchain := le_trans (Finset.card_le_card hsub) Finset.card_image_le
        rw [hprod] at hchain
        refine le_trans hchain ?_
        have hmul : 4 * ((subFunsU P s₁).card * (subFunsU P s₂).card)
            ≤ 4 * (subCap (leavesOn P s₁) * subCap (leavesOn P s₂)) :=
          Nat.mul_le_mul_left 4 (Nat.mul_le_mul ih₁ ih₂)
        refine le_trans hmul ?_
        -- the exact recurrence: 4 · 4^(2a−1) · 4^(2b−1) = 4^(2(a+b)−1)
        have hbin : leavesOn P (Trans.bin op s₁ s₂) = leavesOn P s₁ + leavesOn P s₂ := rfl
        rw [hbin]
        unfold subCap
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        have hE : 4 * (4 ^ (2 * leavesOn P s₁ - 1) * 4 ^ (2 * leavesOn P s₂ - 1))
            = 4 ^ (1 + (2 * leavesOn P s₁ - 1) + (2 * leavesOn P s₂ - 1)) := by
          rw [pow_add, pow_add, pow_one]
          ring
        rw [hE]
        have hexp : 1 + (2 * leavesOn P s₁ - 1) + (2 * leavesOn P s₂ - 1)
            = 2 * (leavesOn P s₁ + leavesOn P s₂) - 1 := by omega
        rw [hexp]

theorem subCap_le (ℓ : ℕ) : subCap ℓ ≤ 2 * 16 ^ ℓ := by
  unfold subCap
  by_cases h : ℓ = 0
  · rw [if_pos h, h]
    norm_num
  · rw [if_neg h]
    have hle : (4 : ℕ) ^ (2 * ℓ - 1) ≤ 4 ^ (2 * ℓ) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (4 : ℕ) ^ (2 * ℓ) = 16 ^ ℓ := by
      rw [show (16 : ℕ) = 4 ^ 2 from by norm_num, ← pow_mul]
    omega

/-- **The counting lemma at the subfunction level (proved)**: a transducer with `ℓ` leaves on block `P` realises at
most `2·16^ℓ` distinct subfunctions on `P`. -/
theorem subFuns_card_le {n : ℕ} (P : Fin n → Bool) (t : Trans n) :
    (subFuns P t).card ≤ 2 * 16 ^ leavesOn P t := by
  have hsub : subFuns P t ⊆ subFunsU P t := by
    intro g hg
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_image.mpr ⟨(id, y), Finset.mem_univ _, rfl⟩
  exact le_trans (Finset.card_le_card hsub)
    (le_trans (subFunsU_card_le P t) (subCap_le _))

/-! ### Leaf accounting -/

theorem leavesOn_le_volume {n : ℕ} (P : Fin n → Bool) (t : Trans n) :
    leavesOn P t ≤ volume t := by
  induction t with
  | var i =>
    show (if P i then 1 else 0) ≤ 1
    by_cases h : P i
    · rw [if_pos h]
    · rw [if_neg h]
      omega
  | cst b => exact Nat.zero_le _
  | un op s ih =>
    show leavesOn P s ≤ volume s + 1
    omega
  | bin op s₁ s₂ ih₁ ih₂ =>
    show leavesOn P s₁ + leavesOn P s₂ ≤ volume s₁ + volume s₂ + 1
    omega

/-- **The interface, volume form (proved)**: a transducer of volume `V` realises at most `2·16^V` distinct
subfunctions on any block — at every width, in particular at dimension 3. -/
theorem cost_interface_volume {n : ℕ} (P : Fin n → Bool) (t : Trans n) :
    (subFuns P t).card ≤ 2 * 16 ^ volume t :=
  le_trans (subFuns_card_le P t)
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (leavesOn_le_volume P t)))

/-- Disjoint blocks' leaf counts sum below the volume. -/
theorem sum_leavesOn_le_volume {n m : ℕ} (Ps : Fin m → Fin n → Bool)
    (hdisj : ∀ (i : Fin n) (c c' : Fin m), Ps c i = true → Ps c' i = true → c = c')
    (t : Trans n) :
    (∑ c, leavesOn (Ps c) t) ≤ volume t := by
  induction t with
  | var i =>
    have hcard : (Finset.univ.filter (fun c : Fin m => Ps c i = true)).card ≤ 1 :=
      Finset.card_le_one.mpr (fun a ha b hb =>
        hdisj i a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)
    have hsum : (∑ c, leavesOn (Ps c) (Trans.var i))
        = (Finset.univ.filter (fun c : Fin m => Ps c i = true)).card := by
      rw [Finset.card_filter]
      exact Finset.sum_congr rfl (fun c _ => rfl)
    rw [hsum]
    exact hcard
  | cst b =>
    have h0 : (∑ c, leavesOn (Ps c) (Trans.cst b)) = 0 :=
      Finset.sum_eq_zero (fun c _ => rfl)
    rw [h0]
    exact Nat.zero_le _
  | un op s ih =>
    show (∑ c, leavesOn (Ps c) s) ≤ volume s + 1
    omega
  | bin op s₁ s₂ ih₁ ih₂ =>
    show (∑ c, (leavesOn (Ps c) s₁ + leavesOn (Ps c) s₂)) ≤ volume s₁ + volume s₂ + 1
    rw [Finset.sum_add_distrib]
    omega

/-! ### The sat3 Nečiporuk volume bound -/

/-- The clause-block predicate. -/
def sat3BlockP (N : ℕ) (c : Fin (sat3M N)) : Fin N → Bool :=
  fun b => decide (b.val / sat3D N = c.val)

theorem sat3BlockP_disjoint (N : ℕ) :
    ∀ (i : Fin N) (c c' : Fin (sat3M N)),
      sat3BlockP N c i = true → sat3BlockP N c' i = true → c = c' := by
  intro i c c' h h'
  apply Fin.ext
  have h1 := of_decide_eq_true h
  have h2 := of_decide_eq_true h'
  omega

theorem sat3Patch_eq_mergeP (N : ℕ) (c : Fin (sat3M N)) (y u : Fin N → Bool) :
    sat3Patch N c y u = mergeP (sat3BlockP N c) y u := by
  funext b
  show (if b.val / sat3D N = c.val then u b else y b)
      = (if sat3BlockP N c b then u b else y b)
  by_cases h : b.val / sat3D N = c.val
  · rw [if_pos h, if_pos (show sat3BlockP N c b = true from decide_eq_true h)]
  · rw [if_neg h, if_neg (show ¬ sat3BlockP N c b = true from by
      simp only [sat3BlockP, decide_eq_true_eq]
      exact h)]

/-- **Per-block leaf lower bound (proved)**: computing `sat3Family` requires `≥ (m−2)/4` leaves inside every clause
block — the `2^(m−1)` subfunction count meets the `2·16^ℓ` capacity. -/
theorem sat3_block_leaves (N : ℕ) (hv : 1 ≤ sat3V N) (hm1 : 1 ≤ sat3M N)
    (t : Trans N) (heval : eval t = sat3Family N) (c : Fin (sat3M N)) :
    sat3M N - 2 ≤ 4 * leavesOn (sat3BlockP N c) t := by
  obtain ⟨Y, hY⟩ := sat3_block_subfunction_count_pred N hv hm1 c
  have hsub : (Finset.univ.image (fun bvec : Fin (sat3M N - 1) → Bool =>
      (fun uu : Fin N → Bool => sat3Family N (sat3Patch N c (Y bvec) uu))))
      ⊆ subFuns (sat3BlockP N c) t := by
    intro g hg
    obtain ⟨bvec, -, rfl⟩ := Finset.mem_image.mp hg
    refine Finset.mem_image.mpr ⟨Y bvec, Finset.mem_univ _, ?_⟩
    funext uu
    rw [heval, sat3Patch_eq_mergeP N c (Y bvec) uu]
  have hcard : 2 ^ (sat3M N - 1) ≤ (subFuns (sat3BlockP N c) t).card := by
    rw [← hY]
    exact Finset.card_le_card hsub
  have hbound := subFuns_card_le (sat3BlockP N c) t
  have h16 : 2 * 16 ^ leavesOn (sat3BlockP N c) t
      = 2 ^ (4 * leavesOn (sat3BlockP N c) t + 1) := by
    rw [show (16 : ℕ) = 2 ^ 4 from by norm_num, ← pow_mul, pow_succ]
    ring
  have hfinal : 2 ^ (sat3M N - 1) ≤ 2 ^ (4 * leavesOn (sat3BlockP N c) t + 1) := by
    rw [← h16]
    exact le_trans hcard hbound
  have hexp : sat3M N - 1 ≤ 4 * leavesOn (sat3BlockP N c) t + 1 :=
    (Nat.pow_le_pow_iff_right (by omega)).mp hfinal
  omega

/-- **The Nečiporuk volume bound for SAT (proved)**: any transducer computing `sat3Family` has
`4·volume ≥ m·(m−2)` — the counting substrate crosses the cost interface. -/
theorem sat3_neciporuk_volume (N : ℕ) (hv : 1 ≤ sat3V N) (hm1 : 1 ≤ sat3M N)
    (t : Trans N) (heval : eval t = sat3Family N) :
    sat3M N * (sat3M N - 2) ≤ 4 * volume t := by
  have hsum := sum_leavesOn_le_volume (sat3BlockP N) (sat3BlockP_disjoint N) t
  have hsum2 : (∑ _c : Fin (sat3M N), (sat3M N - 2))
      ≤ ∑ c, 4 * leavesOn (sat3BlockP N c) t :=
    Finset.sum_le_sum (fun c _ => sat3_block_leaves N hv hm1 t heval c)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    ← Finset.mul_sum] at hsum2
  have h4 := Nat.mul_le_mul_left 4 hsum
  omega

/-- **The budget form (proved)**: `sat3M N · (sat3M N − 2) ≤ 4 · budget (sat3Family N)` — the first volume lower
bound on the definite SAT target in the boundary model. -/
theorem sat3_neciporuk_budget (N : ℕ) (hv : 1 ≤ sat3V N) (hm1 : 1 ≤ sat3M N) :
    sat3M N * (sat3M N - 2) ≤ 4 * budget (sat3Family N) := by
  have hne : {v | ∃ t : Trans N, eval t = sat3Family N ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor (sat3Family N)), dnfFor (sat3Family N), eval_dnfFor _, rfl⟩
  obtain ⟨t, ht, hvol⟩ := Nat.sInf_mem hne
  show sat3M N * (sat3M N - 2)
      ≤ 4 * sInf {v | ∃ t : Trans N, eval t = sat3Family N ∧ volume t = v}
  rw [← hvol]
  exact sat3_neciporuk_volume N hv hm1 t ht

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.subFuns_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cost_interface_volume
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_neciporuk_budget
