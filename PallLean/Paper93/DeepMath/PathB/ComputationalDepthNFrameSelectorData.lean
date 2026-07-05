import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMinFormBound

/-!
# N-Frame: selector-data families — the last workhorse, and column concentration

The all-signs-out refuge closes.  The role reversal: when pin signs lie **outside** `S`, they are
probe-side — so the row family carries **selector patterns** `T` as data, and each pair is read
apart by choosing which pinned variable to force true.  No new gadgets: the clause over selector
set `T` with pins `bvec` evaluates to "some selected pin is set true".

  `sat3Lit_false_of_unsat` — a slot with no satisfied selected literal is false.
  `sat3ContextG_multi_probe_eval` — **PROVED, the workhorse**: for covered `T`,
        `f (patch (ctxG α bvec, T-indicator)) = decide (∃ j, α j ∈ T ∧ bvec j = true)`.
  `exists_injection_mapping_strict` — the matching extension with both directions: `P` into `V`
        **and** the complement off `V`.
  `sat3_selector_data_drag` — **PROVED, the drag**: data selectors in `S`, covering pin signs off
        `S` ⇒ the data capacity is at most the trace width: `|V₀| ≤ j`.
  `sat3_selector_column_concentration` — **PROVED, the fusion**: over any cut factorization with
        `2j + 4 ≤ m`, **every block's slot-0 selector column is `≤ j`-concentrated on one side of
        `S`** — at most `j` selectors inside, or at most `j` outside.

## Honest scope

Every refuge of the balanced-cut adversary is now priced: all-selectors-in dies on size,
signs-in/selectors-out dies on the min form, all-signs-out dies on this file.  What remains is the
final balance case-count assembling the concentration into `coneExcess ≥ Ω(m)` and
`cbudget ≥ 2N + Ω(m)` — arithmetic over the block census at a chosen threshold, the closing rung.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- A slot with no satisfied selected literal is false. -/
theorem sat3Lit_false_of_unsat (N : ℕ) (x : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (c : Fin (sat3M N)) (t : Fin 3)
    (hsel : ∀ i : Fin (sat3V N),
      x (sat3Bit N c t i.val (by have := i.isLt; omega)) = true →
      xor (a i) (x (sat3Bit N c t (sat3V N) (by omega))) = false) :
    sat3Lit N x a c t = false := by
  unfold sat3Lit
  apply List.any_eq_false.mpr
  intro i _
  by_cases hs : x (sat3Bit N c t i.val (by have := i.isLt; omega)) = true
  · rw [hs, hsel i hs]
    simp
  · rw [Bool.not_eq_true] at hs
    rw [hs]
    simp

set_option maxHeartbeats 1600000 in
/-- **THE MULTI-SELECTOR EVAL (proved)**: the designated clause over selector set `T` with
generalized pins evaluates to "some covered pin in `T` is set true". -/
theorem sat3ContextG_multi_probe_eval (N : ℕ) (hv : 1 ≤ sat3V N) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (hkv : k ≤ sat3V N) (c : Fin (sat3M N))
    (α : Fin k → Fin (sat3V N)) (hα : Function.Injective α)
    (bvec : Fin k → Bool) (T : Finset (Fin (sat3V N)))
    (hcov : ∀ w ∈ T, ∃ j : Fin k, α j = w) :
    sat3Family N (sat3Patch N c (sat3ContextG N c hk α bvec)
      (fun bit => decide (∃ w ∈ T, bit.val % sat3D N = w.val)))
      = decide (∃ j : Fin k, α j ∈ T ∧ bvec j = true) := by
  classical
  have hDpos : 0 < sat3D N := sat3D_pos N
  set y : Fin N → Bool := sat3ContextG N c hk α bvec with hy
  set u : Fin N → Bool :=
    fun bit => decide (∃ w ∈ T, bit.val % sat3D N = w.val) with hu
  have hσne : ∀ j : Fin k, sat3PinClause N c hk j ≠ c :=
    fun j h => sat3PinClause_ne N c hk j (congrArg Fin.val h)
  -- pin-clause reads (verbatim from the single-probe workhorse)
  have hpin_sel : ∀ j : Fin k,
      sat3Patch N c y u (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (α j).val
        (by have := (α j).isLt; omega)) = true := by
    intro j
    rw [sat3Patch_out N c y u _ (hσne j)]
    show decide _ = true
    rw [decide_eq_true_eq]
    left
    refine ⟨j, sat3Bit_clause N (sat3PinClause N c hk j) ⟨0, by omega⟩ (α j).val
      (by have := (α j).isLt; omega), Or.inl ?_⟩
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + (α j).val = (α j).val
    omega
  have hpin_miss : ∀ (j : Fin k) (i : Fin (sat3V N)), i ≠ α j →
      sat3Patch N c y u (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ i.val
        (by have := i.isLt; omega)) = false := by
    intro j i hij
    rw [sat3Patch_out N c y u _ (hσne j)]
    have hd := sat3Bit_clause N (sat3PinClause N c hk j) ⟨0, by omega⟩ i.val
      (by have := i.isLt; omega)
    have hr : (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ i.val
        (by have := i.isLt; omega)).val % sat3D N = i.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + i.val = i.val
      omega
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
    · rw [hd] at hdiv
      have hjj' := sat3PinClause_val_inj N c hk hdiv
      subst hjj'
      rcases hrem with h | ⟨h, -⟩
      · rw [hr] at h
        exact hij (Fin.ext h)
      · rw [hr] at h
        have := i.isLt
        omega
    · exact hnot j hd
  have hpin_sign : ∀ j : Fin k,
      sat3Patch N c y u (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega)) = decide (bvec j = false) := by
    intro j
    rw [sat3Patch_out N c y u _ (hσne j)]
    exact sat3ContextG_pin_sign N c hk hkv α bvec j
  have hpin_dead : ∀ (j : Fin k) (t : Fin 3), 1 ≤ t.val → ∀ i : Fin (sat3V N),
      sat3Patch N c y u (sat3Bit N (sat3PinClause N c hk j) t i.val
        (by have := i.isLt; omega)) = false := by
    intro j t ht i
    rw [sat3Patch_out N c y u _ (hσne j)]
    have hd := sat3Bit_clause N (sat3PinClause N c hk j) t i.val (by have := i.isLt; omega)
    have hr := sat3Bit_rem N (sat3PinClause N c hk j) t i.val (by have := i.isLt; omega)
    have hbound : sat3V N + 1 ≤ t.val * (sat3V N + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
    · have hj' := (α j').isLt
      rcases hrem with h | ⟨h, -⟩ <;> rw [hr] at h <;> omega
    · exact hnot j hd
  -- tautology-clause reads (verbatim)
  have htaut_sel0 : ∀ cl : Fin (sat3M N), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      sat3Patch N c y u (sat3Bit N cl ⟨0, by omega⟩ 0 (by omega)) = true := by
    intro cl hclc hnp
    rw [sat3Patch_out N c y u cl hclc]
    have hd := sat3Bit_clause N cl ⟨0, by omega⟩ 0 (by omega)
    have hr : (sat3Bit N cl ⟨0, by omega⟩ 0 (by omega)).val % sat3D N = 0 := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + 0 = 0
      omega
    show decide _ = true
    rw [decide_eq_true_eq]
    right
    refine ⟨?_, ?_, ?_, Or.inl hr⟩
    · rw [hd]
      exact cl.isLt
    · rw [hd]
      exact fun hh => hclc (Fin.ext hh)
    · intro j'
      rw [hd]
      exact hnp j'
  have htaut_miss0 : ∀ cl : Fin (sat3M N), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      ∀ i : Fin (sat3V N), i ≠ (⟨0, hv⟩ : Fin (sat3V N)) →
      sat3Patch N c y u (sat3Bit N cl ⟨0, by omega⟩ i.val (by have := i.isLt; omega))
        = false := by
    intro cl hclc hnp i hij
    rw [sat3Patch_out N c y u cl hclc]
    have hd := sat3Bit_clause N cl ⟨0, by omega⟩ i.val (by have := i.isLt; omega)
    have hr : (sat3Bit N cl ⟨0, by omega⟩ i.val (by have := i.isLt; omega)).val % sat3D N
        = i.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + i.val = i.val
      omega
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j', hdiv, -⟩ | ⟨-, -, -, hpat⟩)
    · rw [hd] at hdiv
      exact hnp j' hdiv
    · rw [hr] at hpat
      have hilt := i.isLt
      rcases hpat with h | h | h
      · exact hij (Fin.ext h)
      · omega
      · omega
  have htaut_sign0 : ∀ cl : Fin (sat3M N), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      sat3Patch N c y u (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
    intro cl hclc hnp
    rw [sat3Patch_out N c y u cl hclc]
    have hd := sat3Bit_clause N cl ⟨0, by omega⟩ (sat3V N) (by omega)
    have hr : (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N
        = sat3V N := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
      omega
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j', hdiv, -⟩ | ⟨-, -, -, hpat⟩)
    · rw [hd] at hdiv
      exact hnp j' hdiv
    · rw [hr] at hpat
      rcases hpat with h | h | h <;> omega
  have htaut_sel1 : ∀ cl : Fin (sat3M N), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      sat3Patch N c y u (sat3Bit N cl ⟨1, by omega⟩ 0 (by omega)) = true := by
    intro cl hclc hnp
    rw [sat3Patch_out N c y u cl hclc]
    have hd := sat3Bit_clause N cl ⟨1, by omega⟩ 0 (by omega)
    have hr : (sat3Bit N cl ⟨1, by omega⟩ 0 (by omega)).val % sat3D N = sat3V N + 1 := by
      rw [sat3Bit_rem]
      show (1 : ℕ) * (sat3V N + 1) + 0 = sat3V N + 1
      omega
    show decide _ = true
    rw [decide_eq_true_eq]
    right
    refine ⟨?_, ?_, ?_, Or.inr (Or.inl hr)⟩
    · rw [hd]
      exact cl.isLt
    · rw [hd]
      exact fun hh => hclc (Fin.ext hh)
    · intro j'
      rw [hd]
      exact hnp j'
  have htaut_miss1 : ∀ cl : Fin (sat3M N), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      ∀ i : Fin (sat3V N), i ≠ (⟨0, hv⟩ : Fin (sat3V N)) →
      sat3Patch N c y u (sat3Bit N cl ⟨1, by omega⟩ i.val (by have := i.isLt; omega))
        = false := by
    intro cl hclc hnp i hij
    rw [sat3Patch_out N c y u cl hclc]
    have hd := sat3Bit_clause N cl ⟨1, by omega⟩ i.val (by have := i.isLt; omega)
    have hr : (sat3Bit N cl ⟨1, by omega⟩ i.val (by have := i.isLt; omega)).val % sat3D N
        = sat3V N + 1 + i.val := by
      rw [sat3Bit_rem]
      show (1 : ℕ) * (sat3V N + 1) + i.val = sat3V N + 1 + i.val
      omega
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j', hdiv, -⟩ | ⟨-, -, -, hpat⟩)
    · rw [hd] at hdiv
      exact hnp j' hdiv
    · rw [hr] at hpat
      have hilt := i.isLt
      rcases hpat with h | h | h
      · omega
      · have h0 : i.val = 0 := by omega
        exact hij (Fin.ext h0)
      · omega
  have htaut_sign1 : ∀ cl : Fin (sat3M N), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      sat3Patch N c y u (sat3Bit N cl ⟨1, by omega⟩ (sat3V N) (by omega)) = true := by
    intro cl hclc hnp
    rw [sat3Patch_out N c y u cl hclc]
    have hd := sat3Bit_clause N cl ⟨1, by omega⟩ (sat3V N) (by omega)
    have hr : (sat3Bit N cl ⟨1, by omega⟩ (sat3V N) (by omega)).val % sat3D N
        = sat3V N + 1 + sat3V N := by
      rw [sat3Bit_rem]
      show (1 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N + 1 + sat3V N
      omega
    show decide _ = true
    rw [decide_eq_true_eq]
    right
    refine ⟨?_, ?_, ?_, Or.inr (Or.inr hr)⟩
    · rw [hd]
      exact cl.isLt
    · rw [hd]
      exact fun hh => hclc (Fin.ext hh)
    · intro j'
      rw [hd]
      exact hnp j'
  -- designated-block reads: the T-indicator
  have hprobe_sel : ∀ w : Fin (sat3V N), w ∈ T →
      sat3Patch N c y u (sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega)) = true := by
    intro w hw
    rw [sat3Patch_own N c y u]
    show decide _ = true
    rw [decide_eq_true_eq]
    refine ⟨w, hw, ?_⟩
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + w.val = w.val
    omega
  have hprobe_miss : ∀ i : Fin (sat3V N), i ∉ T →
      sat3Patch N c y u (sat3Bit N c ⟨0, by omega⟩ i.val
        (by have := i.isLt; omega)) = false := by
    intro i hi
    rw [sat3Patch_own N c y u]
    have hr : (sat3Bit N c ⟨0, by omega⟩ i.val (by have := i.isLt; omega)).val % sat3D N
        = i.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + i.val = i.val
      omega
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro ⟨w', hw', hrem⟩
    rw [hr] at hrem
    exact hi (by rw [show i = w' from Fin.ext hrem]; exact hw')
  have hprobe_sign :
      sat3Patch N c y u (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
    rw [sat3Patch_own N c y u]
    have hr : (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N
        = sat3V N := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
      omega
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro ⟨w', hw', hrem⟩
    rw [hr] at hrem
    have := w'.isLt
    omega
  have hprobe_dead : ∀ (t : Fin 3), 1 ≤ t.val → ∀ i : Fin (sat3V N),
      sat3Patch N c y u (sat3Bit N c t i.val (by have := i.isLt; omega)) = false := by
    intro t ht i
    rw [sat3Patch_own N c y u]
    have hr := sat3Bit_rem N c t i.val (by have := i.isLt; omega)
    have hbound : sat3V N + 1 ≤ t.val * (sat3V N + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hilt := i.isLt
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro ⟨w', hw', hrem⟩
    rw [hr] at hrem
    have := w'.isLt
    omega
  -- clause-level analysis
  have hLit_pin : ∀ (a : Fin (sat3V N) → Bool) (j : Fin k),
      (∃ t, sat3Lit N (sat3Patch N c y u) a (sat3PinClause N c hk j) t = true) ↔
        xor (a (α j)) (decide (bvec j = false)) = true := by
    intro a j
    have hiff := sat3Clause_single_iff N (sat3Patch N c y u) a (sat3PinClause N c hk j)
      (α j) (hpin_sel j) (hpin_miss j)
      (hpin_dead j ⟨1, by omega⟩ (by show (1 : ℕ) ≤ 1; omega))
      (hpin_dead j ⟨2, by omega⟩ (by show (1 : ℕ) ≤ 2; omega))
    rw [hpin_sign j] at hiff
    exact hiff
  have hLit_taut : ∀ (a : Fin (sat3V N) → Bool) (cl : Fin (sat3M N)), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      ∃ t, sat3Lit N (sat3Patch N c y u) a cl t = true := by
    intro a cl hclc hnp
    cases ha : a ⟨0, hv⟩
    · refine ⟨⟨1, by omega⟩, ?_⟩
      rw [sat3Lit_single N (sat3Patch N c y u) a cl ⟨1, by omega⟩ ⟨0, hv⟩
        (htaut_sel1 cl hclc hnp) (htaut_miss1 cl hclc hnp),
        htaut_sign1 cl hclc hnp, Bool.xor_true, ha]
      rfl
    · refine ⟨⟨0, by omega⟩, ?_⟩
      rw [sat3Lit_single N (sat3Patch N c y u) a cl ⟨0, by omega⟩ ⟨0, hv⟩
        (htaut_sel0 cl hclc hnp) (htaut_miss0 cl hclc hnp),
        htaut_sign0 cl hclc hnp, Bool.xor_false, ha]
  have hLit_c : ∀ a : Fin (sat3V N) → Bool,
      (∃ t, sat3Lit N (sat3Patch N c y u) a c t = true) ↔
        ∃ w ∈ T, a w = true := by
    intro a
    constructor
    · rintro ⟨t, ht⟩
      rcases t with ⟨tv, htv⟩
      interval_cases tv
      · unfold sat3Lit at ht
        obtain ⟨i, -, hi⟩ := List.any_eq_true.mp ht
        rw [Bool.and_eq_true] at hi
        obtain ⟨hisel, hilit⟩ := hi
        have hiT : i ∈ T := by
          by_contra hniT
          rw [hprobe_miss i hniT] at hisel
          exact Bool.noConfusion hisel
        rw [hprobe_sign] at hilit
        refine ⟨i, hiT, ?_⟩
        cases hai : a i
        · rw [hai] at hilit
          exact Bool.noConfusion hilit
        · rfl
      · exfalso
        rw [sat3Lit_false_of_empty N (sat3Patch N c y u) a c ⟨1, htv⟩
          (fun i => hprobe_dead ⟨1, htv⟩ (by show (1 : ℕ) ≤ 1; omega) i)] at ht
        exact Bool.noConfusion ht
      · exfalso
        rw [sat3Lit_false_of_empty N (sat3Patch N c y u) a c ⟨2, htv⟩
          (fun i => hprobe_dead ⟨2, htv⟩ (by show (1 : ℕ) ≤ 2; omega) i)] at ht
        exact Bool.noConfusion ht
    · rintro ⟨w, hwT, haw⟩
      refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N (sat3Patch N c y u) a c
        ⟨0, by omega⟩ w (hprobe_sel w hwT) ?_⟩
      rw [hprobe_sign, haw]
      rfl
  -- final assembly
  by_cases hsat : ∃ j : Fin k, α j ∈ T ∧ bvec j = true
  · rw [decide_eq_true hsat]
    obtain ⟨j₁, hj₁T, hj₁b⟩ := hsat
    set awit : Fin (sat3V N) → Bool :=
      fun i => if h : ∃ j : Fin k, α j = i then bvec (Classical.choose h) else true
      with hawit
    have hawit_at : ∀ j : Fin k, awit (α j) = bvec j := by
      intro j
      show (if h : ∃ j' : Fin k, α j' = α j then bvec (Classical.choose h) else true)
        = bvec j
      have hex : ∃ j' : Fin k, α j' = α j := ⟨j, rfl⟩
      rw [dif_pos hex]
      exact congrArg bvec (hα (Classical.choose_spec hex))
    rw [sat3Family_iff]
    refine ⟨awit, sat3Eval_true_of_all N _ awit ?_⟩
    intro cl
    by_cases hclc : cl = c
    · rw [hclc]
      refine (hLit_c awit).mpr ⟨α j₁, hj₁T, ?_⟩
      rw [hawit_at j₁]
      exact hj₁b
    · by_cases hpin : ∃ j : Fin k, sat3PinClause N c hk j = cl
      · obtain ⟨j, rfl⟩ := hpin
        refine (hLit_pin awit j).mpr ?_
        rw [hawit_at j]
        cases bvec j <;> rfl
      · exact hLit_taut awit cl hclc (fun j h => hpin ⟨j, Fin.ext h.symm⟩)
  · rw [decide_eq_false hsat]
    apply decide_eq_false
    rintro ⟨A, hA⟩
    have hforce : ∀ j : Fin k, A (α j) = bvec j := by
      intro j
      have hpin := (hLit_pin A j).mp
        (sat3Eval_clause_true N _ A hA (sat3PinClause N c hk j))
      exact xor_decide_eq _ _ hpin
    obtain ⟨w, hwT, haw⟩ := (hLit_c A).mp (sat3Eval_clause_true N _ A hA c)
    obtain ⟨j, hj⟩ := hcov w hwT
    apply hsat
    refine ⟨j, by rw [hj]; exact hwT, ?_⟩
    rw [← hforce j, hj]
    exact haw

/-- The matching extension, strict form: `P` into `V` and the complement off `V`. -/
theorem exists_injection_mapping_strict {k v : ℕ} (hkv : k ≤ v)
    (P : Finset (Fin k)) (V : Finset (Fin v)) (hcard : P.card = V.card) :
    ∃ α : Fin k → Fin v, Function.Injective α ∧ (∀ p ∈ P, α p ∈ V) ∧
      (∀ p, p ∉ P → α p ∉ V) := by
  classical
  have hPle : P.card ≤ k := by
    have := Finset.card_le_card (Finset.subset_univ P)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hVle : V.card ≤ v := by
    have := Finset.card_le_card (Finset.subset_univ V)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hle : (Pᶜ : Finset (Fin k)).card ≤ (Vᶜ : Finset (Fin v)).card := by
    rw [Finset.card_compl, Finset.card_compl, Fintype.card_fin, Fintype.card_fin]
    omega
  set β : ↥P ≃ ↥V := P.equivFin.trans ((finCongr hcard).trans V.equivFin.symm)
    with hβ
  set γ : ↥(Pᶜ : Finset (Fin k)) → ↥(Vᶜ : Finset (Fin v)) :=
    fun x => (Vᶜ : Finset (Fin v)).equivFin.symm
      (Fin.castLE hle ((Pᶜ : Finset (Fin k)).equivFin x)) with hγ
  have hγinj : Function.Injective γ := by
    intro x y hxy
    have h1 := (Vᶜ : Finset (Fin v)).equivFin.symm.injective hxy
    have h2 := Fin.castLE_injective hle h1
    exact (Pᶜ : Finset (Fin k)).equivFin.injective h2
  refine ⟨fun p => if hp : p ∈ P then (β ⟨p, hp⟩).val
    else (γ ⟨p, Finset.mem_compl.mpr hp⟩).val, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : (if hp : a ∈ P then (β ⟨a, hp⟩).val
        else (γ ⟨a, Finset.mem_compl.mpr hp⟩).val)
      = (if hp : b ∈ P then (β ⟨b, hp⟩).val
        else (γ ⟨b, Finset.mem_compl.mpr hp⟩).val) := hab
    by_cases ha : a ∈ P <;> by_cases hb : b ∈ P
    · rw [dif_pos ha, dif_pos hb] at hab'
      exact congrArg Subtype.val (β.injective (Subtype.ext hab'))
    · exfalso
      rw [dif_pos ha, dif_neg hb] at hab'
      have h1 : (β ⟨a, ha⟩).val ∈ V := (β ⟨a, ha⟩).2
      have h2 : (γ ⟨b, Finset.mem_compl.mpr hb⟩).val ∈ (Vᶜ : Finset (Fin v)) :=
        (γ ⟨b, Finset.mem_compl.mpr hb⟩).2
      rw [hab'] at h1
      exact (Finset.mem_compl.mp h2) h1
    · exfalso
      rw [dif_neg ha, dif_pos hb] at hab'
      have h1 : (β ⟨b, hb⟩).val ∈ V := (β ⟨b, hb⟩).2
      have h2 : (γ ⟨a, Finset.mem_compl.mpr ha⟩).val ∈ (Vᶜ : Finset (Fin v)) :=
        (γ ⟨a, Finset.mem_compl.mpr ha⟩).2
      rw [← hab'] at h1
      exact (Finset.mem_compl.mp h2) h1
    · rw [dif_neg ha, dif_neg hb] at hab'
      exact congrArg Subtype.val (hγinj (Subtype.ext hab'))
  · intro p hp
    show (if hp' : p ∈ P then (β ⟨p, hp'⟩).val
      else (γ ⟨p, Finset.mem_compl.mpr hp'⟩).val) ∈ V
    rw [dif_pos hp]
    exact (β ⟨p, hp⟩).2
  · intro p hp
    show (if hp' : p ∈ P then (β ⟨p, hp'⟩).val
      else (γ ⟨p, Finset.mem_compl.mpr hp'⟩).val) ∉ V
    rw [dif_neg hp]
    exact Finset.mem_compl.mp (γ ⟨p, Finset.mem_compl.mpr hp⟩).2

set_option maxHeartbeats 1600000 in
/-- **THE SELECTOR-DATA DRAG (proved)**: data selectors inside `S` with covering pin signs outside
`S` cannot outnumber the trace: `|V₀| ≤ j`. -/
theorem sat3_selector_data_drag (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (c : Fin (sat3M N)) (α : Fin (sat3M N - 2) → Fin (sat3V N))
    (hα : Function.Injective α) (V₀ : Finset (Fin (sat3V N)))
    (hdata : ∀ w ∈ V₀, sat3Bit N c ⟨0, by omega⟩ w.val
      (by have := w.isLt; omega) ∈ S)
    (hcov : ∀ w ∈ V₀, ∃ p : Fin (sat3M N - 2), α p = w)
    (hkit : ∀ p : Fin (sat3M N - 2), α p ∈ V₀ →
      sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ S) :
    V₀.card ≤ j := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set bv0 : Fin (sat3M N - 2) → Bool := fun _ => false with hbv0
  set Pt : Finset (Fin (sat3V N)) → (Fin N → Bool) :=
    fun T => sat3Patch N c (sat3ContextG N c hk α bv0)
      (fun bit => decide (∃ w ∈ T, bit.val % sat3D N = w.val)) with hPt
  -- point reads at data selectors identify T
  have hPtread : ∀ (T : Finset (Fin (sat3V N))) (w : Fin (sat3V N)),
      Pt T (sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega))
        = decide (w ∈ T) := by
    intro T w
    have hr : (sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega)).val % sat3D N = w.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + w.val = w.val
      omega
    rw [hPt]
    show sat3Patch N c _ _ _ = _
    rw [sat3Patch_own]
    show decide _ = decide (w ∈ T)
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨w', hw', hrem⟩
      rw [hr] at hrem
      rw [show w = w' from Fin.ext hrem]
      exact hw'
    · intro hw
      exact ⟨w, hw, hr⟩
  set Y : Finset (Fin N → Bool) := V₀.powerset.image Pt with hY
  have hYcard : Y.card = 2 ^ V₀.card := by
    rw [hY, Finset.card_image_of_injOn, Finset.card_powerset]
    intro T hT T' hT' heq
    have hTsub := Finset.mem_powerset.mp (Finset.mem_coe.mp hT)
    have hT'sub := Finset.mem_powerset.mp (Finset.mem_coe.mp hT')
    ext w
    by_cases hwV : w ∈ V₀
    · have h := congrFun heq
        (sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega))
      rw [hPtread T w, hPtread T' w] at h
      constructor
      · intro hw
        exact of_decide_eq_true (by rw [← h]; exact decide_eq_true hw)
      · intro hw
        exact of_decide_eq_true (by rw [h]; exact decide_eq_true hw)
    · constructor
      · intro hw
        exact absurd (hTsub hw) hwV
      · intro hw
        exact absurd (hT'sub hw) hwV
  have hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, sat3Family N (mixOn Sᶜ x y) ≠ sat3Family N (mixOn Sᶜ x y') := by
    intro y hy y' hy' hne
    rw [hY] at hy hy'
    obtain ⟨T, hTmem, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨T', hT'mem, rfl⟩ := Finset.mem_image.mp hy'
    have hTsub := Finset.mem_powerset.mp hTmem
    have hT'sub := Finset.mem_powerset.mp hT'mem
    have hTne : T ≠ T' := fun hcon => hne (by rw [hcon])
    -- a symmetric-difference witness
    have hex : ∃ w, w ∈ V₀ ∧ ¬(w ∈ T ↔ w ∈ T') := by
      by_contra hcon
      push_neg at hcon
      apply hTne
      ext w
      by_cases hwV : w ∈ V₀
      · exact hcon w hwV
      · constructor
        · intro hw
          exact absurd (hTsub hw) hwV
        · intro hw
          exact absurd (hT'sub hw) hwV
    obtain ⟨w₀, hw₀V, hw₀d⟩ := hex
    set bvs : Fin (sat3M N - 2) → Bool := fun p => decide (α p = w₀) with hbvs
    -- the S-part transfer: bv0 and bvs differ only at kit pins, which lie off S
    have hctxag : ∀ (b b' : Fin (sat3M N - 2) → Bool),
        (∀ p, b p ≠ b' p → α p ∈ V₀) →
        ∀ i : Fin N, i ∈ S →
        sat3ContextG N c hk α b i = sat3ContextG N c hk α b' i := by
      intro b b' hbb i hi
      apply sat3ContextG_agree
      intro p hp1 hp2
      by_contra hbne
      have hpV := hbb p hbne
      apply hkit p hpV
      have hiπ : sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
          (by omega) = i := by
        apply Fin.ext
        show (sat3PinClause N c hk p).val * sat3D N + 0 * (sat3V N + 1)
          + sat3V N = i.val
        have hdm := Nat.div_add_mod i.val (sat3D N)
        rw [hp1, hp2] at hdm
        have hcm : sat3D N * (sat3PinClause N c hk p).val
            = (sat3PinClause N c hk p).val * sat3D N := Nat.mul_comm _ _
        omega
      rw [hiπ]
      exact hi
    -- the pair probe: pins set true exactly where α hits w₀
    set x0 : Fin N → Bool := sat3Patch N c (sat3ContextG N c hk α bvs)
      (fun bit => decide (∃ w ∈ T, bit.val % sat3D N = w.val)) with hx0
    have hmixgen : ∀ T'' : Finset (Fin (sat3V N)), T'' ⊆ V₀ →
        mixOn Sᶜ x0 (Pt T'')
          = sat3Patch N c (sat3ContextG N c hk α bvs)
            (fun bit => decide (∃ w ∈ T'', bit.val % sat3D N = w.val)) := by
      intro T'' hT''sub
      funext i
      show (if i ∈ Sᶜ then x0 i else Pt T'' i) = _
      by_cases hi : i ∈ Sᶜ
      · rw [if_pos hi]
        have hiNS : i ∉ S := Finset.mem_compl.mp hi
        rw [hx0]
        show (if i.val / sat3D N = c.val
            then decide (∃ w ∈ T, i.val % sat3D N = w.val)
            else sat3ContextG N c hk α bvs i)
          = (if i.val / sat3D N = c.val
            then decide (∃ w ∈ T'', i.val % sat3D N = w.val)
            else sat3ContextG N c hk α bvs i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, if_pos hdiv]
          -- both indicators agree off S: a differing field would be a data selector in S
          apply decide_eq_decide.mpr
          constructor
          · rintro ⟨w, hw, hrem⟩
            by_contra hno
            push_neg at hno
            -- i is the data-selector bit of w ∈ T ⊆ ... but T ⊆ ?  need w ∈ V₀:
            have hwV : w ∈ V₀ := hTsub hw
            apply hiNS
            have hiw : sat3Bit N c ⟨0, by omega⟩ w.val
                (by have := w.isLt; omega) = i := by
              apply Fin.ext
              show c.val * sat3D N + 0 * (sat3V N + 1) + w.val = i.val
              have hdm := Nat.div_add_mod i.val (sat3D N)
              rw [hdiv, hrem] at hdm
              have hcm : sat3D N * c.val = c.val * sat3D N := Nat.mul_comm _ _
              omega
            rw [← hiw]
            exact hdata w hwV
          · rintro ⟨w, hw, hrem⟩
            by_contra hno
            push_neg at hno
            have hwV : w ∈ V₀ := hT''sub hw
            apply hiNS
            have hiw : sat3Bit N c ⟨0, by omega⟩ w.val
                (by have := w.isLt; omega) = i := by
              apply Fin.ext
              show c.val * sat3D N + 0 * (sat3V N + 1) + w.val = i.val
              have hdm := Nat.div_add_mod i.val (sat3D N)
              rw [hdiv, hrem] at hdm
              have hcm : sat3D N * c.val = c.val * sat3D N := Nat.mul_comm _ _
              omega
            rw [← hiw]
            exact hdata w hwV
        · rw [if_neg hdiv, if_neg hdiv]
      · rw [if_neg hi]
        have hiS : i ∈ S := by
          by_contra hiS
          exact hi (Finset.mem_compl.mpr hiS)
        rw [hPt]
        show (if i.val / sat3D N = c.val
            then decide (∃ w ∈ T'', i.val % sat3D N = w.val)
            else sat3ContextG N c hk α bv0 i)
          = (if i.val / sat3D N = c.val
            then decide (∃ w ∈ T'', i.val % sat3D N = w.val)
            else sat3ContextG N c hk α bvs i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, if_pos hdiv]
        · rw [if_neg hdiv, if_neg hdiv]
          apply hctxag
          · intro p hp
            rw [hbv0, hbvs] at hp
            by_cases hαp : α p = w₀
            · rw [hαp]
              exact hw₀V
            · exfalso
              apply hp
              show false = decide (α p = w₀)
              rw [decide_eq_false hαp]
          · exact hiS
      -- end funext
    have hval : ∀ T'' : Finset (Fin (sat3V N)), T'' ⊆ V₀ →
        sat3Family N (sat3Patch N c (sat3ContextG N c hk α bvs)
          (fun bit => decide (∃ w ∈ T'', bit.val % sat3D N = w.val)))
          = decide (w₀ ∈ T'') := by
      intro T'' hT''sub
      rw [sat3ContextG_multi_probe_eval N hv hk hkv c α hα bvs T''
        (fun w hw => hcov w (hT''sub hw))]
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨p, hpT, hpb⟩
        rw [hbvs] at hpb
        have := of_decide_eq_true hpb
        rw [← this]
        exact hpT
      · intro hw
        obtain ⟨p, hp⟩ := hcov w₀ hw₀V
        refine ⟨p, by rw [hp]; exact hw, ?_⟩
        rw [hbvs]
        exact decide_eq_true hp
    refine ⟨x0, ?_⟩
    rw [hmixgen T hTsub, hmixgen T' hT'sub, hval T hTsub, hval T' hT'sub]
    intro heq
    apply hw₀d
    constructor
    · intro hw
      exact of_decide_eq_true (by rw [← heq]; exact decide_eq_true hw)
    · intro hw
      exact of_decide_eq_true (by rw [heq]; exact decide_eq_true hw)
  have hcap := cut_row_capacity (sat3Family N) S j hcut Y hdist
  rw [hYcard] at hcap
  by_contra hcon
  push_neg at hcon
  have hlt : (2 : ℕ) ^ j < 2 ^ V₀.card :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- **THE COLUMN CONCENTRATION (proved)**: over any cut factorization with `2j + 4 ≤ m`, every
block's slot-0 selector column is `≤ j`-concentrated on one side of `S`. -/
theorem sat3_selector_column_concentration (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (c : Fin (sat3M N)) (hm : 2 * j + 4 ≤ sat3M N) :
    ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card ≤ j
    ∨ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)).card ≤ j := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨hin, hout⟩ := hcon
  rcases sat3_pin_selector_min_bound N hv hk hcut c with hπ | hsel
  · -- few pin signs inside S: build the selector-data family
    -- the offside pin pool
    have hcover : (Finset.univ : Finset (Fin (sat3M N - 2)))
        ⊆ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
            sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
              (by omega) ∈ S))
          ∪ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
            sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
              (by omega) ∉ S)) := by
      intro p _
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases hp : sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
          (by omega) ∈ S
      · exact Or.inl ⟨Finset.mem_univ p, hp⟩
      · exact Or.inr ⟨Finset.mem_univ p, hp⟩
    have hcnt : sat3M N - 2
        ≤ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
            sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
              (by omega) ∈ S)).card
          + ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
            sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
              (by omega) ∉ S)).card := by
      calc sat3M N - 2 = (Finset.univ : Finset (Fin (sat3M N - 2))).card := by
            rw [Finset.card_univ, Fintype.card_fin]
        _ ≤ _ := Finset.card_le_card hcover
        _ ≤ _ := Finset.card_union_le _ _
    have hoffpins : j + 1
        ≤ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
            sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
              (by omega) ∉ S)).card := by
      omega
    obtain ⟨P', hP'sub, hP'card⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
        sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
          (by omega) ∉ S)) (n := j + 1) hoffpins
    obtain ⟨V', hV'sub, hV'card⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
      (n := j + 1) (by omega)
    obtain ⟨α, hαinj, hαmap, hαstrict⟩ := exists_injection_mapping_strict hkv P' V'
      (by rw [hP'card, hV'card])
    -- surjectivity of α from P' onto V'
    have himg : P'.image α = V' := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
        exact hαmap p hp
      · rw [Finset.card_image_of_injective _ hαinj, hP'card, hV'card]
    have hdrag := sat3_selector_data_drag N hv hk hcut c α hαinj V'
      (fun w hw => (Finset.mem_filter.mp (hV'sub hw)).2)
      (fun w hw => by
        have : w ∈ P'.image α := by rw [himg]; exact hw
        obtain ⟨p, -, hp⟩ := Finset.mem_image.mp this
        exact ⟨p, hp⟩)
      (fun p hp => by
        have hpP' : p ∈ P' := by
          by_contra hnp
          exact hαstrict p hnp hp
        exact (Finset.mem_filter.mp (hP'sub hpP')).2)
    omega
  · omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3ContextG_multi_probe_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_data_drag
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_column_concentration
