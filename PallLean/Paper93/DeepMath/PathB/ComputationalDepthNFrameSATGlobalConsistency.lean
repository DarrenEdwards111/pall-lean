import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameNeciporukCostInterface

/-!
# N-Frame: global witness consistency — the cross-block coupling invariant, calibrated

Nečiporuk counts blocks independently and saturates polynomially.  This file formalizes the candidate next
invariant — **cross-block witness coupling** — and runs the calibration battery *before* claiming anything.

**The invariant.**  For a function `f` and block `P`, `funSubs f P` is the set of subfunctions of `f` on `P` as the
outside context varies.  For a *pair* of blocks, the joint set uses `orP P Q`.  Coupling is measured by comparing the
joint diversity against the marginal diversities over a common context family.

**The calibration ladder (all proved).**
  * `funSubs_and_card_le` — full-AND: at most **2** subfunctions on any block (trivial).
  * `funSubs_parity_card_le` — parity: at most **2** — the invariant does *not* falsely explode on parity.
  * `funSubs_maj_card_le` — majority: at most **n+1** — structured, polynomial pressure.
  * `sat3` per block: exactly `2^(m−2)` (from the subfunction-count file) — exponential pressure.

**The coupling theorem (proved).**  `sat3_witness_coupling_collapse`: over the pin family on blocks
`(c, last)`, the **joint** subfunction count equals the **marginal** count on `c` alone — both exactly `2^(m−2)` —
although the last block *in isolation* carries the same `2^(m−2)` diversity (`sat3_lastblock_isolated`).  Adding the
second observation window contributes **zero** joint diversity: both blocks consult the *same* witness.  This is
"global witness consistency" as a theorem: local block choices are many, but the satisfying assignment couples them.

**Capacity side (proved).**  `joint_capacity`: the transducer capacity for a block *pair* is still governed by the
leaf **sum** `2·16^(ℓ_P+ℓ_Q)` — the model's joint capacity is additive, matching the collapsed (not multiplied)
demand.

## Honest scope

The collapse **explains** why block-counting saturates at Nečiporuk scale: block diversities do not multiply, because
the witness is shared — summed per-block information is all an independent-blocks method can extract.  Converting
coupling into a *volume* lower bound needs a mechanism sensitive to joint structure (communication-depth /
Karchmer–Wigderson-flavored), which is **open** and *not* claimed.  `sat3Target` (superpolynomial `cbudget`) is
untouched.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The function-level subfunction invariant -/

/-- The subfunctions of `f` on block `P` as the outside context varies. -/
def funSubs {n : ℕ} (f : (Fin n → Bool) → Bool) (P : Fin n → Bool) :
    Finset ((Fin n → Bool) → Bool) :=
  Finset.image (fun y : Fin n → Bool => fun u => f (mergeP P y u)) Finset.univ

theorem funSubs_eval {n : ℕ} (t : Trans n) (P : Fin n → Bool) :
    funSubs (eval t) P = subFuns P t := rfl

/-- The union of two blocks. -/
def orP {n : ℕ} (P Q : Fin n → Bool) : Fin n → Bool := fun i => P i || Q i

/-! ### Calibration: full-AND has at most two subfunctions on any block -/

theorem and4_shuffle (p q A B : Bool) : ((p && q) && (A && B)) = ((p && A) && (q && B)) := by
  cases p <;> cases q <;> cases A <;> cases B <;> rfl

theorem foldr_and_pointwise {n : ℕ} (l : List (Fin n)) (x a b : Fin n → Bool)
    (hx : ∀ i, x i = (a i && b i)) :
    l.foldr (fun i acc => x i && acc) true
      = (l.foldr (fun i acc => a i && acc) true && l.foldr (fun i acc => b i && acc) true) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    show (x hd && tl.foldr _ true) = _
    rw [ih, hx hd]
    exact and4_shuffle (a hd) (b hd) _ _

theorem mergeP_eq_and_masks {n : ℕ} (P y u : Fin n → Bool) (i : Fin n) :
    mergeP P y u i = ((if P i then u i else true) && (if P i then true else y i)) := by
  show (if P i then u i else y i) = _
  by_cases h : P i = true
  · rw [if_pos h, if_pos h, if_pos h]
    cases u i <;> rfl
  · rw [if_neg h, if_neg h, if_neg h]
    cases y i <;> rfl

/-- **Calibration: AND (proved)** — at most two subfunctions on any block. -/
theorem funSubs_and_card_le (n : ℕ) (P : Fin n → Bool) :
    (funSubs (fullAndFn n) P).card ≤ 2 := by
  have hsub : funSubs (fullAndFn n) P ⊆
      {(fun u : Fin n → Bool => fullAndFn n (fun i => if P i then u i else true)),
       (fun _ : Fin n → Bool => false)} := by
    intro g hg
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg
    have hsplit : ∀ u, fullAndFn n (mergeP P y u)
        = (fullAndFn n (fun i => if P i then u i else true)
            && fullAndFn n (fun i => if P i then true else y i)) := by
      intro u
      exact foldr_and_pointwise _ _ _ _ (fun i => mergeP_eq_and_masks P y u i)
    cases hoff : fullAndFn n (fun i => if P i then true else y i)
    · apply Finset.mem_insert.mpr
      right
      apply Finset.mem_singleton.mpr
      funext u
      rw [hsplit u, hoff]
      cases fullAndFn n (fun i => if P i then u i else true) <;> rfl
    · apply Finset.mem_insert.mpr
      left
      funext u
      rw [hsplit u, hoff]
      cases fullAndFn n (fun i => if P i then u i else true) <;> rfl
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  rw [Finset.card_singleton]

/-! ### Calibration: parity has at most two subfunctions on any block -/

theorem xor4_shuffle (p q A B : Bool) : (xor (xor p q) (xor A B)) = (xor (xor p A) (xor q B)) := by
  cases p <;> cases q <;> cases A <;> cases B <;> rfl

theorem foldr_xor_pointwise {n : ℕ} (l : List (Fin n)) (x a b : Fin n → Bool)
    (hx : ∀ i, x i = xor (a i) (b i)) :
    l.foldr (fun i acc => xor (x i) acc) false
      = xor (l.foldr (fun i acc => xor (a i) acc) false)
            (l.foldr (fun i acc => xor (b i) acc) false) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    show xor (x hd) (tl.foldr _ false) = _
    rw [ih, hx hd]
    exact xor4_shuffle (a hd) (b hd) _ _

theorem mergeP_eq_xor_masks {n : ℕ} (P y u : Fin n → Bool) (i : Fin n) :
    mergeP P y u i = xor (if P i then u i else false) (if P i then false else y i) := by
  show (if P i then u i else y i) = _
  by_cases h : P i = true
  · rw [if_pos h, if_pos h, if_pos h]
    cases u i <;> rfl
  · rw [if_neg h, if_neg h, if_neg h]
    cases y i <;> rfl

/-- **Calibration: parity (proved)** — at most two subfunctions on any block: the invariant does not falsely
explode on parity. -/
theorem funSubs_parity_card_le (n : ℕ) (P : Fin n → Bool) :
    (funSubs (parityFn n) P).card ≤ 2 := by
  have hsub : funSubs (parityFn n) P ⊆
      {(fun u : Fin n → Bool => parityFn n (fun i => if P i then u i else false)),
       (fun u : Fin n → Bool => !(parityFn n (fun i => if P i then u i else false)))} := by
    intro g hg
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg
    have hsplit : ∀ u, parityFn n (mergeP P y u)
        = xor (parityFn n (fun i => if P i then u i else false))
              (parityFn n (fun i => if P i then false else y i)) := by
      intro u
      exact foldr_xor_pointwise _ _ _ _ (fun i => mergeP_eq_xor_masks P y u i)
    cases hoff : parityFn n (fun i => if P i then false else y i)
    · apply Finset.mem_insert.mpr
      left
      funext u
      rw [hsplit u, hoff]
      cases parityFn n (fun i => if P i then u i else false) <;> rfl
    · apply Finset.mem_insert.mpr
      right
      apply Finset.mem_singleton.mpr
      funext u
      rw [hsplit u, hoff]
      cases parityFn n (fun i => if P i then u i else false) <;> rfl
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  rw [Finset.card_singleton]

/-! ### Calibration: majority has at most `n+1` subfunctions on any block -/

/-- **Calibration: majority (proved)** — at most `n+1` subfunctions: structured, polynomial pressure, between the
trivial functions and SAT's exponential count. -/
theorem funSubs_maj_card_le (n : ℕ) (P : Fin n → Bool) :
    (funSubs (majFn n) P).card ≤ n + 1 := by
  have hsub : funSubs (majFn n) P ⊆ Finset.image
      (fun k : ℕ => fun u : Fin n → Bool =>
        decide ((n + 1) / 2 ≤
          (Finset.univ.filter (fun i => P i = true ∧ u i = true)).card + k))
      (Finset.range (n + 1)) := by
    intro g hg
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg
    refine Finset.mem_image.mpr
      ⟨(Finset.univ.filter (fun i => ¬(P i = true) ∧ y i = true)).card, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      have hle := Finset.card_filter_le Finset.univ
        (fun i : Fin n => ¬(P i = true) ∧ y i = true)
      rw [Finset.card_univ, Fintype.card_fin] at hle
      omega
    · funext u
      rw [majFn_eq_decide]
      have hset : onesOf (mergeP P y u)
          = Finset.univ.filter (fun i => P i = true ∧ u i = true)
            ∪ Finset.univ.filter (fun i => ¬(P i = true) ∧ y i = true) := by
        ext i
        simp only [onesOf, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
        show (if P i then u i else y i) = true ↔ _
        by_cases h : P i = true
        · rw [if_pos h]
          simp [h]
        · rw [if_neg h]
          simp [h]
      have hdis : Disjoint (Finset.univ.filter (fun i : Fin n => P i = true ∧ u i = true))
          (Finset.univ.filter (fun i : Fin n => ¬(P i = true) ∧ y i = true)) := by
        rw [Finset.disjoint_left]
        rintro i hi1 hi2
        exact (Finset.mem_filter.mp hi2).2.1 (Finset.mem_filter.mp hi1).2.1
      rw [hset, Finset.card_union_of_disjoint hdis]
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_range]

/-! ### Capacity for block pairs is additive -/

theorem leavesOn_orP_le {n : ℕ} (P Q : Fin n → Bool) (t : Trans n) :
    leavesOn (orP P Q) t ≤ leavesOn P t + leavesOn Q t := by
  induction t with
  | var i =>
    show (if (P i || Q i) then 1 else 0) ≤ (if P i then 1 else 0) + (if Q i then 1 else 0)
    by_cases hp : P i = true
    · rw [if_pos hp, hp, Bool.true_or, if_pos rfl]
      omega
    · have hp' : P i = false := by
        cases hpp : P i
        · rfl
        · exact absurd hpp hp
      rw [if_neg hp, hp', Bool.false_or]
      omega
  | cst b => exact Nat.zero_le _
  | un op s ih => exact ih
  | bin op s₁ s₂ ih₁ ih₂ =>
    show leavesOn (orP P Q) s₁ + leavesOn (orP P Q) s₂ ≤ _
    have h1 := ih₁
    have h2 := ih₂
    show _ ≤ (leavesOn P s₁ + leavesOn P s₂) + (leavesOn Q s₁ + leavesOn Q s₂)
    omega

/-- **Joint capacity (proved)**: the transducer capacity for a block *pair* is governed by the leaf sum — additive,
matching the collapsed (not multiplied) demand of witness-coupled functions. -/
theorem joint_capacity {n : ℕ} (P Q : Fin n → Bool) (t : Trans n) :
    (funSubs (eval t) (orP P Q)).card ≤ 2 * 16 ^ (leavesOn P t + leavesOn Q t) := by
  rw [funSubs_eval]
  exact le_trans (subFuns_card_le _ t)
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (leavesOn_orP_le P Q t)))

/-! ### The sat3 witness-coupling collapse -/

/-- Merging on a block pair decomposes as two nested patches. -/
theorem mergeP_orP_patch (N : ℕ) (c c' : Fin (sat3M N)) (y uu : Fin N → Bool) :
    mergeP (orP (sat3BlockP N c) (sat3BlockP N c')) y uu
      = sat3Patch N c (sat3Patch N c' y uu) uu := by
  funext b
  show (if (sat3BlockP N c b || sat3BlockP N c' b) then uu b else y b)
      = (if b.val / sat3D N = c.val then uu b
         else if b.val / sat3D N = c'.val then uu b else y b)
  by_cases h1 : b.val / sat3D N = c.val
  · rw [if_pos h1, show sat3BlockP N c b = true from decide_eq_true h1, Bool.true_or,
      if_pos rfl]
  · have hb1 : sat3BlockP N c b = false := by
      show decide _ = false
      rw [decide_eq_false_iff_not]
      exact h1
    rw [if_neg h1, hb1, Bool.false_or]
    by_cases h2 : b.val / sat3D N = c'.val
    · rw [show sat3BlockP N c' b = true from decide_eq_true h2, if_pos rfl, if_pos h2]
    · have hb2 : sat3BlockP N c' b = false := by
        show decide _ = false
        rw [decide_eq_false_iff_not]
        exact h2
      rw [hb2, if_neg h2, if_neg Bool.false_ne_true]

/-- Patching is insensitive to the probe's values off the block. -/
theorem sat3Patch_congr_u (N : ℕ) (c : Fin (sat3M N)) (y u u' : Fin N → Bool)
    (h : ∀ b : Fin N, b.val / sat3D N = c.val → u b = u' b) :
    sat3Patch N c y u = sat3Patch N c y u' := by
  funext b
  show (if b.val / sat3D N = c.val then u b else y b)
      = (if b.val / sat3D N = c.val then u' b else y b)
  by_cases hb : b.val / sat3D N = c.val
  · rw [if_pos hb, if_pos hb]
    exact h b hb
  · rw [if_neg hb, if_neg hb]

/-- The pin context is `bvec`-independent away from the pin clauses. -/
theorem sat3Context_offpin (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (bvec bvec' : Fin k → Bool) (b : Fin N)
    (hb : ∀ j : Fin k, b.val / sat3D N ≠ (sat3PinClause N c hk j).val) :
    sat3Context N c hk bvec b = sat3Context N c hk bvec' b := by
  show decide _ = decide _
  rw [decide_eq_decide]
  constructor
  · rintro (⟨j, hdiv, -⟩ | hrest)
    · exact absurd hdiv (hb j)
    · exact Or.inr hrest
  · rintro (⟨j, hdiv, -⟩ | hrest)
    · exact absurd hdiv (hb j)
    · exact Or.inr hrest

/-- **The witness-coupling collapse (proved)**: over the pin family, the joint subfunction count on the block pair
`(c, last)` equals the marginal count on `c` alone — both exactly `2^(m−2)`.  The second block contributes zero
joint diversity: both blocks consult the same witness. -/
theorem sat3_witness_coupling_collapse (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N)
    (c : Fin (sat3M N)) (hc : c.val < sat3M N - 1) :
    ∃ Y : (Fin (sat3M N - 2) → Bool) → (Fin N → Bool),
      (Finset.univ.image (fun bvec : Fin (sat3M N - 2) → Bool =>
        (fun uu : Fin N → Bool => sat3Family N
          (mergeP (orP (sat3BlockP N c)
              (sat3BlockP N ⟨sat3M N - 1, by omega⟩)) (Y bvec) uu)))).card
        = 2 ^ (sat3M N - 2) ∧
      (Finset.univ.image (fun bvec : Fin (sat3M N - 2) → Bool =>
        (fun uu : Fin N → Bool => sat3Family N
          (mergeP (sat3BlockP N c) (Y bvec) uu)))).card = 2 ^ (sat3M N - 2) := by
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  refine ⟨fun bvec => sat3Context N c hk bvec, ?_, ?_⟩
  · -- (i) the joint count
    have hσlast : ∀ j : Fin (sat3M N - 2),
        (sat3PinClause N c hk j).val ≠ sat3M N - 1 := by
      intro j
      rw [sat3PinClause_val]
      have := j.isLt
      by_cases h : j.val < c.val
      · rw [if_pos h]
        omega
      · rw [if_neg h]
        omega
    have hinj : Function.Injective (fun bvec : Fin (sat3M N - 2) → Bool =>
        (fun uu : Fin N → Bool => sat3Family N
          (mergeP (orP (sat3BlockP N c)
              (sat3BlockP N ⟨sat3M N - 1, by omega⟩)) (sat3Context N c hk bvec) uu))) := by
      intro b b' heq
      by_contra hne
      have hex : ∃ j₀ : Fin (sat3M N - 2), b j₀ ≠ b' j₀ := by
        by_contra hcon
        push_neg at hcon
        exact hne (funext hcon)
      obtain ⟨j₀, hj₀⟩ := hex
      set vj : Fin (sat3V N) := ⟨j₀.val, by have := j₀.isLt; omega⟩ with hvj
      set uu : Fin N → Bool := fun bit =>
        if bit.val / sat3D N = sat3M N - 1 then sat3Context N c hk (fun _ => false) bit
        else sat3Probe N vj (!(b j₀)) bit with huu
      -- the joint value at the crafted probe reduces to the single-block workhorse
      have hval : ∀ bvec : Fin (sat3M N - 2) → Bool,
          sat3Family N (mergeP (orP (sat3BlockP N c)
              (sat3BlockP N ⟨sat3M N - 1, by omega⟩)) (sat3Context N c hk bvec) uu)
            = xor (bvec j₀) (!(b j₀)) := by
        intro bvec
        rw [mergeP_orP_patch N c ⟨sat3M N - 1, by omega⟩ (sat3Context N c hk bvec) uu]
        have hA : sat3Patch N ⟨sat3M N - 1, by omega⟩ (sat3Context N c hk bvec) uu
            = sat3Context N c hk bvec := by
          funext bb
          show (if bb.val / sat3D N = (⟨sat3M N - 1, by omega⟩ : Fin (sat3M N)).val
              then uu bb else sat3Context N c hk bvec bb) = sat3Context N c hk bvec bb
          by_cases hbb : bb.val / sat3D N = sat3M N - 1
          · rw [if_pos hbb]
            show (if bb.val / sat3D N = sat3M N - 1
                then sat3Context N c hk (fun _ => false) bb
                else sat3Probe N vj (!(b j₀)) bb) = _
            rw [if_pos hbb]
            exact sat3Context_offpin N c hk (fun _ => false) bvec bb
              (fun j hj => hσlast j (hj.symm.trans hbb))
          · rw [if_neg hbb]
        rw [hA]
        have hagree : ∀ bb : Fin N, bb.val / sat3D N = c.val →
            uu bb = sat3Probe N vj (!(b j₀)) bb := by
          intro bb hbb
          show (if bb.val / sat3D N = sat3M N - 1 then _ else _) = _
          rw [if_neg (by
            rw [hbb]
            omega)]
        rw [sat3Patch_congr_u N c (sat3Context N c hk bvec) uu
          (sat3Probe N vj (!(b j₀))) hagree]
        exact sat3Context_probe_eval N hv hk hkv c bvec j₀ vj rfl (!(b j₀))
      have h0 : sat3Family N (mergeP (orP (sat3BlockP N c)
            (sat3BlockP N ⟨sat3M N - 1, by omega⟩)) (sat3Context N c hk b) uu)
          = sat3Family N (mergeP (orP (sat3BlockP N c)
            (sat3BlockP N ⟨sat3M N - 1, by omega⟩)) (sat3Context N c hk b') uu) :=
        congrFun heq uu
      rw [hval b, hval b'] at h0
      cases hb : b j₀ <;> cases hb' : b' j₀
      · rw [hb, hb'] at hj₀
        exact hj₀ rfl
      · rw [hb, hb'] at h0
        exact absurd h0 (by decide)
      · rw [hb, hb'] at h0
        exact absurd h0 (by decide)
      · rw [hb, hb'] at hj₀
        exact hj₀ rfl
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  · -- (ii) the marginal count on c alone
    have hconv : (fun bvec : Fin (sat3M N - 2) → Bool =>
        (fun uu : Fin N → Bool => sat3Family N
          (mergeP (sat3BlockP N c) (sat3Context N c hk bvec) uu)))
        = (fun bvec : Fin (sat3M N - 2) → Bool =>
          (fun uu : Fin N → Bool => sat3Family N
            (sat3Patch N c (sat3Context N c hk bvec) uu))) := by
      funext bvec uu
      rw [sat3Patch_eq_mergeP]
    rw [hconv]
    exact sat3_block_subfunction_count N hv hk hkv c

/-- **The comparison point (proved)**: the last block *in isolation* — with its own pin contexts — carries the same
`2^(m−2)` diversity that it fails to add jointly.  The coupling is in the sharing, not in the block. -/
theorem sat3_lastblock_isolated (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N) :
    ∃ Y' : (Fin (sat3M N - 2) → Bool) → (Fin N → Bool),
      (Finset.univ.image (fun bvec : Fin (sat3M N - 2) → Bool =>
        (fun uu : Fin N → Bool => sat3Family N
          (mergeP (sat3BlockP N ⟨sat3M N - 1, by omega⟩) (Y' bvec) uu)))).card
        = 2 ^ (sat3M N - 2) := by
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  refine ⟨fun bvec => sat3Context N ⟨sat3M N - 1, by omega⟩ hk bvec, ?_⟩
  have hconv : (fun bvec : Fin (sat3M N - 2) → Bool =>
      (fun uu : Fin N → Bool => sat3Family N
        (mergeP (sat3BlockP N ⟨sat3M N - 1, by omega⟩)
          (sat3Context N ⟨sat3M N - 1, by omega⟩ hk bvec) uu)))
      = (fun bvec : Fin (sat3M N - 2) → Bool =>
        (fun uu : Fin N → Bool => sat3Family N
          (sat3Patch N ⟨sat3M N - 1, by omega⟩
            (sat3Context N ⟨sat3M N - 1, by omega⟩ hk bvec) uu))) := by
    funext bvec uu
    rw [sat3Patch_eq_mergeP]
  rw [hconv]
  exact sat3_block_subfunction_count N hv hk hkv _

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.funSubs_and_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.funSubs_parity_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.funSubs_maj_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.joint_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_witness_coupling_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_lastblock_isolated
