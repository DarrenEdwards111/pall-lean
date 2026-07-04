import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameXorSquareAllPins

/-!
# N-Frame: odd squares for all pins — the two-literal workhorse, re-parameterized

The residual-shrink step, odd half.  The two-literal probe now targets any pinned variable `j₀`: slot 0
selects `j₀` with the free sign, slot 1 selects `j₀` with sign `0`, so the designated clause is
`(A_{j₀} ⊕ sign) ∨ A_{j₀} = A_{j₀} ∨ sign`, and the pin clause for `j₀` forces `A_{j₀}` in the unsat
corner.

  `sat3Probe2V` / `sat3_two_probe_evalV` — **PROVED**: `f = bvec j₀ || sign` at every pin context, for
        every pinned variable.
  `sat3_outside_probe_satisfied` — the outside-clause lemma, generalized to an arbitrary block override.
  `sat3_odd_square_all_pins` — **PROVED**: engine-format odd parity for every pair (pin-sign of `j₀`,
        designated sign), at every pin context.

With `sat3_xor_square_all_pins`, both squares now exist for all `(m−2)·m` sign pairs; the coverage
widening (kill any cut separating **any** of them; residual = all pairs aligned) is the named next
assembly.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The two-literal probe on variable `vj`: slot-0 and slot-1 selectors on `vj`, all signs `0`. -/
def sat3Probe2V (N : ℕ) (vj : Fin (sat3V N)) : Fin N → Bool :=
  fun bit => decide (bit.val % sat3D N = vj.val
    ∨ bit.val % sat3D N = sat3V N + 1 + vj.val)

/-- Outside clauses are satisfied by the standard witness under **any** block override. -/
theorem sat3_outside_probe_satisfied (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (cIdx : Fin (sat3M N)) (bvec : Fin (sat3M N - 2) → Bool) (u : Fin N → Bool)
    (cl : Fin (sat3M N)) (hclv : cl.val ≠ cIdx.val) (X : Fin N → Bool)
    (houtside : ∀ (cl' : Fin (sat3M N)) (hcl : cl'.val ≠ cIdx.val) (t : Fin 3)
      (fI : ℕ) (hfI : fI < sat3V N + 1),
      X (sat3Bit N cl' t fI hfI)
        = sat3Patch N cIdx (sat3Context N cIdx hk bvec) u (sat3Bit N cl' t fI hfI)) :
    ∃ t, sat3Lit N X (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩
      else true) cl t = true := by
  classical
  by_cases hpin : ∃ j' : Fin (sat3M N - 2), sat3PinClause N cIdx hk j' = cl
  · obtain ⟨j', rfl⟩ := hpin
    have hjlt : j'.val < sat3V N := by have := j'.isLt; omega
    refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N X _ _ ⟨0, by omega⟩
      ⟨j'.val, hjlt⟩ ?_ ?_⟩
    · rw [houtside _ (sat3PinClause_ne N cIdx hk j') _ _ _]
      exact pin_read_sel N cIdx hk hkv bvec u j'
    · rw [houtside _ (sat3PinClause_ne N cIdx hk j') _ _ _,
        pin_read_sign N cIdx hk hkv bvec u j']
      show xor (if h : j'.val < sat3M N - 2 then bvec ⟨j'.val, h⟩ else true)
          (decide (bvec j' = false)) = true
      rw [dif_pos j'.isLt]
      have hbeq : bvec ⟨j'.val, j'.isLt⟩ = bvec j' := by congr 1
      rw [hbeq]
      cases bvec j' <;> rfl
  · push_neg at hpin
    have hnp : ∀ j' : Fin (sat3M N - 2), cl.val ≠ (sat3PinClause N cIdx hk j').val :=
      fun j' h => hpin j' (Fin.ext h.symm)
    have hread : ∀ (t : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1),
        X (sat3Bit N cl t fI hfI)
          = sat3Context N cIdx hk bvec (sat3Bit N cl t fI hfI) := by
      intro t fI hfI
      rw [houtside cl hclv t fI hfI]
      exact sat3Patch_out N cIdx _ _ cl (fun h => hclv (congrArg Fin.val h)) t fI hfI
    by_cases ha0 : (if h : (0 : ℕ) < sat3M N - 2 then bvec ⟨0, h⟩ else true) = true
    · refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N X _ cl ⟨0, by omega⟩
        ⟨0, hv⟩ ?_ ?_⟩
      · rw [hread ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)]
        show decide _ = true
        rw [decide_eq_true_eq]
        refine Or.inr ⟨?_, ?_, ?_, Or.inl ?_⟩
        · rw [sat3Bit_clause]
          exact cl.isLt
        · rw [sat3Bit_clause]
          exact hclv
        · intro j'
          rw [sat3Bit_clause]
          exact hnp j'
        · rw [sat3Bit_rem]
          show (0 : ℕ) * (sat3V N + 1) + 0 = 0
          omega
      · rw [hread ⟨0, by omega⟩ (sat3V N) (by omega)]
        have hsg : sat3Context N cIdx hk bvec
            (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
          show decide _ = false
          rw [decide_eq_false_iff_not]
          rintro (⟨j', hdiv, hrem⟩ | ⟨-, -, -, hrem⟩)
          · rw [sat3Bit_clause] at hdiv
            exact hnp j' hdiv
          · rcases hrem with h | h | h <;> rw [sat3Bit_rem] at h
            · have h' : (0 : ℕ) * (sat3V N + 1) + sat3V N = 0 := h
              omega
            · have h' : (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N + 1 := h
              omega
            · have h' : (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N + 1 + sat3V N := h
              omega
        rw [hsg, ha0]
        rfl
    · have ha0' : (if h : (0 : ℕ) < sat3M N - 2 then bvec ⟨0, h⟩ else true) = false :=
        Bool.eq_false_iff.mpr ha0
      refine ⟨⟨1, by omega⟩, sat3Lit_true_of_selected N X _ cl ⟨1, by omega⟩
        ⟨0, hv⟩ ?_ ?_⟩
      · rw [hread ⟨1, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)]
        show decide _ = true
        rw [decide_eq_true_eq]
        refine Or.inr ⟨?_, ?_, ?_, Or.inr (Or.inl ?_)⟩
        · rw [sat3Bit_clause]
          exact cl.isLt
        · rw [sat3Bit_clause]
          exact hclv
        · intro j'
          rw [sat3Bit_clause]
          exact hnp j'
        · rw [sat3Bit_rem]
          show (1 : ℕ) * (sat3V N + 1) + 0 = sat3V N + 1
          omega
      · rw [hread ⟨1, by omega⟩ (sat3V N) (by omega)]
        have hsg : sat3Context N cIdx hk bvec
            (sat3Bit N cl ⟨1, by omega⟩ (sat3V N) (by omega)) = true := by
          show decide _ = true
          rw [decide_eq_true_eq]
          refine Or.inr ⟨?_, ?_, ?_, Or.inr (Or.inr ?_)⟩
          · rw [sat3Bit_clause]
            exact cl.isLt
          · rw [sat3Bit_clause]
            exact hclv
          · intro j'
            rw [sat3Bit_clause]
            exact hnp j'
          · rw [sat3Bit_rem]
            show (1 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N + 1 + sat3V N
            omega
        rw [hsg, ha0']
        rfl

/-- **THE TWO-LITERAL WORKHORSE, ALL PINS (proved)**: `f = bvec j₀ || sign` at every pin context. -/
theorem sat3_two_probe_evalV (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2))
    (hjv : j₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (a : Bool) :
    sat3Family N (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
      (sat3Probe2V N ⟨j₀.val, hjv⟩)) (sat3SignBit N cIdx) a)
    = (bvec j₀ || a) := by
  classical
  set X : Fin N → Bool := Function.update (sat3Patch N cIdx
    (sat3Context N cIdx hk bvec) (sat3Probe2V N ⟨j₀.val, hjv⟩))
    (sat3SignBit N cIdx) a with hX
  have hownbit : ∀ (t : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1),
      ¬(t.val = 0 ∧ fI = sat3V N) →
      X (sat3Bit N cIdx t fI hfI)
        = decide (t.val * (sat3V N + 1) + fI = j₀.val
            ∨ t.val * (sat3V N + 1) + fI = sat3V N + 1 + j₀.val) := by
    intro t fI hfI hnot
    have hne : sat3Bit N cIdx t fI hfI ≠ sat3SignBit N cIdx := by
      intro hcon
      have hval := congrArg Fin.val hcon
      have h1 : (sat3Bit N cIdx t fI hfI).val
          = cIdx.val * sat3D N + t.val * (sat3V N + 1) + fI := rfl
      have h2 : (sat3SignBit N cIdx).val
          = cIdx.val * sat3D N + 0 * (sat3V N + 1) + sat3V N := rfl
      rw [h1, h2] at hval
      rcases t with ⟨tv, htv⟩
      interval_cases tv
      · refine hnot ⟨rfl, ?_⟩
        have hval' : cIdx.val * sat3D N + 0 * (sat3V N + 1) + fI
            = cIdx.val * sat3D N + 0 * (sat3V N + 1) + sat3V N := hval
        omega
      · have hval' : cIdx.val * sat3D N + 1 * (sat3V N + 1) + fI
            = cIdx.val * sat3D N + 0 * (sat3V N + 1) + sat3V N := hval
        omega
      · have hval' : cIdx.val * sat3D N + 2 * (sat3V N + 1) + fI
            = cIdx.val * sat3D N + 0 * (sat3V N + 1) + sat3V N := hval
        omega
    rw [hX, Function.update_of_ne hne, sat3Patch_own N cIdx _ _ t fI hfI]
    unfold sat3Probe2V
    rw [sat3Bit_rem]
  have hsign : X (sat3Bit N cIdx ⟨0, by omega⟩ (sat3V N) (by omega)) = a := by
    rw [hX]
    exact Function.update_self _ _ _
  have hr00 : X (sat3Bit N cIdx ⟨0, by omega⟩ j₀.val (by omega)) = true := by
    rw [hownbit ⟨0, by omega⟩ j₀.val (by omega) (by rintro ⟨-, h⟩; omega)]
    show decide ((0 : ℕ) * (sat3V N + 1) + j₀.val = j₀.val
        ∨ (0 : ℕ) * (sat3V N + 1) + j₀.val = sat3V N + 1 + j₀.val) = true
    rw [decide_eq_true_eq]
    left
    omega
  have hr0i : ∀ i : Fin (sat3V N), i ≠ ⟨j₀.val, hjv⟩ →
      X (sat3Bit N cIdx ⟨0, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
    intro i hi
    have hiv : i.val ≠ j₀.val := fun h => hi (Fin.ext h)
    rw [hownbit ⟨0, by omega⟩ i.val (by have := i.isLt; omega)
      (by rintro ⟨-, h⟩; have := i.isLt; omega)]
    show decide ((0 : ℕ) * (sat3V N + 1) + i.val = j₀.val
        ∨ (0 : ℕ) * (sat3V N + 1) + i.val = sat3V N + 1 + j₀.val) = false
    rw [decide_eq_false_iff_not]
    rintro (h | h)
    · exact hiv (by omega)
    · have := i.isLt
      omega
  have hr10 : X (sat3Bit N cIdx ⟨1, by omega⟩ j₀.val (by omega)) = true := by
    rw [hownbit ⟨1, by omega⟩ j₀.val (by omega)
      (by rintro ⟨h, -⟩; have h' : (1 : ℕ) = 0 := h; omega)]
    show decide ((1 : ℕ) * (sat3V N + 1) + j₀.val = j₀.val
        ∨ (1 : ℕ) * (sat3V N + 1) + j₀.val = sat3V N + 1 + j₀.val) = true
    rw [decide_eq_true_eq]
    right
    omega
  have hr1i : ∀ i : Fin (sat3V N), i ≠ ⟨j₀.val, hjv⟩ →
      X (sat3Bit N cIdx ⟨1, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
    intro i hi
    have hiv : i.val ≠ j₀.val := fun h => hi (Fin.ext h)
    rw [hownbit ⟨1, by omega⟩ i.val (by have := i.isLt; omega)
      (by rintro ⟨h, -⟩; have h' : (1 : ℕ) = 0 := h; omega)]
    show decide ((1 : ℕ) * (sat3V N + 1) + i.val = j₀.val
        ∨ (1 : ℕ) * (sat3V N + 1) + i.val = sat3V N + 1 + j₀.val) = false
    rw [decide_eq_false_iff_not]
    rintro (h | h)
    · omega
    · exact hiv (by omega)
  have hr1v : X (sat3Bit N cIdx ⟨1, by omega⟩ (sat3V N) (by omega)) = false := by
    rw [hownbit ⟨1, by omega⟩ (sat3V N) (by omega)
      (by rintro ⟨h, -⟩; have h' : (1 : ℕ) = 0 := h; omega)]
    show decide ((1 : ℕ) * (sat3V N + 1) + sat3V N = j₀.val
        ∨ (1 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N + 1 + j₀.val) = false
    rw [decide_eq_false_iff_not]
    rintro (h | h) <;> omega
  have hr2 : ∀ i : Fin (sat3V N),
      X (sat3Bit N cIdx ⟨2, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
    intro i
    rw [hownbit ⟨2, by omega⟩ i.val (by have := i.isLt; omega)
      (by rintro ⟨h, -⟩; have h' : (2 : ℕ) = 0 := h; omega)]
    show decide ((2 : ℕ) * (sat3V N + 1) + i.val = j₀.val
        ∨ (2 : ℕ) * (sat3V N + 1) + i.val = sat3V N + 1 + j₀.val) = false
    rw [decide_eq_false_iff_not]
    have := i.isLt
    rintro (h | h) <;> omega
  have houtside : ∀ (cl : Fin (sat3M N)) (hcl : cl.val ≠ cIdx.val) (t : Fin 3)
      (fI : ℕ) (hfI : fI < sat3V N + 1),
      X (sat3Bit N cl t fI hfI)
        = sat3Patch N cIdx (sat3Context N cIdx hk bvec)
            (sat3Probe2V N ⟨j₀.val, hjv⟩) (sat3Bit N cl t fI hfI) := by
    intro cl hcl t fI hfI
    rw [hX, Function.update_of_ne (show sat3Bit N cl t fI hfI ≠ sat3SignBit N cIdx
      from sat3Bit_ne_of_clause N _ _ _ _ hcl)]
  cases hb : bvec j₀ with
  | true =>
    show sat3Family N X = (true || a)
    rw [Bool.true_or]
    apply sat3Family_of_witness N X
      (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩ else true)
    apply sat3Eval_true_of_all
    intro cl
    by_cases hcl : cl = cIdx
    · subst hcl
      refine ⟨⟨1, by omega⟩, sat3Lit_true_of_selected N X _ cl ⟨1, by omega⟩
        ⟨j₀.val, hjv⟩ hr10 ?_⟩
      rw [hr1v]
      show xor (if h : j₀.val < sat3M N - 2 then bvec ⟨j₀.val, h⟩ else true)
          false = true
      rw [dif_pos j₀.isLt]
      have hb' : bvec ⟨j₀.val, j₀.isLt⟩ = true := hb
      rw [hb']
      rfl
    · exact sat3_outside_probe_satisfied N hv hk hkv cIdx bvec
        (sat3Probe2V N ⟨j₀.val, hjv⟩) cl (fun h => hcl (Fin.ext h)) X houtside
  | false =>
    cases ha : a with
    | true =>
      show sat3Family N X = (false || true)
      rw [Bool.false_or]
      apply sat3Family_of_witness N X
        (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩ else true)
      apply sat3Eval_true_of_all
      intro cl
      by_cases hcl : cl = cIdx
      · subst hcl
        refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N X _ cl ⟨0, by omega⟩
          ⟨j₀.val, hjv⟩ hr00 ?_⟩
        rw [show X (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = true from
          ha ▸ hsign]
        show xor (if h : j₀.val < sat3M N - 2 then bvec ⟨j₀.val, h⟩ else true)
            true = true
        rw [dif_pos j₀.isLt]
        have hb' : bvec ⟨j₀.val, j₀.isLt⟩ = false := hb
        rw [hb']
        rfl
      · exact sat3_outside_probe_satisfied N hv hk hkv cIdx bvec
          (sat3Probe2V N ⟨j₀.val, hjv⟩) cl (fun h => hcl (Fin.ext h)) X houtside
    | false =>
      show sat3Family N X = (false || false)
      apply decide_eq_false
      rintro ⟨A, hA⟩
      have hpin := sat3Eval_clause_true N X A hA (sat3PinClause N cIdx hk j₀)
      have hforce : A ⟨j₀.val, hjv⟩ = bvec j₀ := by
        have hiff := sat3Clause_single_iff N X A
          (sat3PinClause N cIdx hk j₀) ⟨j₀.val, hjv⟩
          (by
            rw [houtside _ (sat3PinClause_ne N cIdx hk j₀) _ _ _]
            exact pin_read_sel N cIdx hk hkv bvec (sat3Probe2V N ⟨j₀.val, hjv⟩) j₀)
          (by
            intro i hi
            rw [houtside _ (sat3PinClause_ne N cIdx hk j₀) _ _ _]
            exact pin_read_miss N cIdx hk hkv bvec (sat3Probe2V N ⟨j₀.val, hjv⟩) j₀ i
              (by
                intro hcon
                apply hi
                rw [hcon]))
          (by
            intro i
            rw [houtside _ (sat3PinClause_ne N cIdx hk j₀) _ _ _]
            exact pin_read_dead N cIdx hk hkv bvec (sat3Probe2V N ⟨j₀.val, hjv⟩) j₀
              ⟨1, by omega⟩ (by show (1 : ℕ) ≤ 1; omega) i)
          (by
            intro i
            rw [houtside _ (sat3PinClause_ne N cIdx hk j₀) _ _ _]
            exact pin_read_dead N cIdx hk hkv bvec (sat3Probe2V N ⟨j₀.val, hjv⟩) j₀
              ⟨2, by omega⟩ (by show (1 : ℕ) ≤ 2; omega) i)
        have hx := hiff.mp hpin
        rw [houtside _ (sat3PinClause_ne N cIdx hk j₀) _ _ _,
          pin_read_sign N cIdx hk hkv bvec (sat3Probe2V N ⟨j₀.val, hjv⟩) j₀] at hx
        exact xor_decide_eq _ _ hx
      obtain ⟨t, ht⟩ := sat3Eval_clause_true N X A hA cIdx
      rcases t with ⟨tv, htv⟩
      interval_cases tv
      · rw [sat3Lit_single N X A cIdx _ ⟨j₀.val, hjv⟩ hr00 hr0i] at ht
        rw [show X (sat3Bit N cIdx ⟨0, by omega⟩ (sat3V N) (by omega)) = false from
          ha ▸ hsign] at ht
        rw [hforce, hb] at ht
        cases ht
      · rw [sat3Lit_single N X A cIdx _ ⟨j₀.val, hjv⟩ hr10 hr1i] at ht
        rw [hr1v, hforce, hb] at ht
        cases ht
      · rw [sat3Lit_false_of_empty N X A cIdx _ hr2] at ht
        cases ht

/-- **ODD SQUARES FOR ALL PINS (proved)**: engine-format parity `true` for every pair
(pin-sign of `j₀`, designated sign), at every pin context. -/
theorem sat3_odd_square_all_pins (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2))
    (bvec : Fin (sat3M N - 2) → Bool) :
    ∃ w : Fin N → Bool,
      xor (xor (sat3Family N w)
          (sat3Family N (Function.update w
            (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
              (by omega))
            (!(w (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
              (sat3V N) (by omega)))))))
        (xor (sat3Family N (Function.update w (sat3SignBit N cIdx)
            (!(w (sat3SignBit N cIdx)))))
          (sat3Family N (Function.update (Function.update w
            (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
              (by omega))
            (!(w (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
              (sat3V N) (by omega))))) (sat3SignBit N cIdx)
            (!(w (sat3SignBit N cIdx)))))) = true := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  have hjv : j₀.val < sat3V N := by
    have := j₀.isLt
    omega
  have hne_ps : (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
      (sat3V N) (by omega) : Fin N) ≠ sat3SignBit N cIdx :=
    sat3Bit_ne_of_clause N _ _ _ _
      (fun h => sat3PinClause_ne N cIdx hk j₀ h)
  refine ⟨Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
    (sat3Probe2V N ⟨j₀.val, hjv⟩)) (sat3SignBit N cIdx) false, ?_⟩
  rw [sat3_two_probe_evalV N hv hk hkv hm3 cIdx j₀ hjv bvec false]
  rw [Function.update_of_ne hne_ps,
    pin_read_sign N cIdx hk hkv bvec (sat3Probe2V N ⟨j₀.val, hjv⟩) j₀]
  rw [show Function.update (Function.update (sat3Patch N cIdx
      (sat3Context N cIdx hk bvec) (sat3Probe2V N ⟨j₀.val, hjv⟩))
      (sat3SignBit N cIdx) false)
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
        (by omega)) (!(decide (bvec j₀ = false)))
    = Function.update (Function.update (sat3Patch N cIdx
      (sat3Context N cIdx hk bvec) (sat3Probe2V N ⟨j₀.val, hjv⟩))
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
        (by omega)) (!(decide (bvec j₀ = false))))
      (sat3SignBit N cIdx) false from
    Function.update_comm hne_ps.symm _ _ _]
  rw [sat3Context_update_pin_sign N cIdx hk hkv bvec j₀
    (sat3Probe2V N ⟨j₀.val, hjv⟩) (!(decide (bvec j₀ = false)))]
  rw [sat3_two_probe_evalV N hv hk hkv hm3 cIdx j₀ hjv _ false]
  rw [show (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
      (sat3Probe2V N ⟨j₀.val, hjv⟩)) (sat3SignBit N cIdx) false)
      (sat3SignBit N cIdx) = false from Function.update_self _ _ _]
  rw [Function.update_idem, sat3_two_probe_evalV N hv hk hkv hm3 cIdx j₀ hjv bvec (!false)]
  rw [Function.update_idem, sat3_two_probe_evalV N hv hk hkv hm3 cIdx j₀ hjv _ (!false)]
  rw [Function.update_self]
  cases hbv : bvec j₀ <;> rfl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_two_probe_evalV
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_odd_square_all_pins
