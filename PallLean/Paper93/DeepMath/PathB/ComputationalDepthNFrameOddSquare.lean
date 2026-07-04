import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameXorSquareAssembly

/-!
# N-Frame: the odd square — the two-literal workhorse, and the second square of the discharge

Track A, rung 2.  The designated block carries **two** literals on the pinned variable `0`: slot 0 with the
free sign (the designated sign bit), slot 1 with sign fixed `0`.  The clause evaluates to
`(A₀ ⊕ sign) ∨ A₀`, i.e. `A₀ ∨ sign` — an OR in the (pin-sign, designated-sign) axes.

  `sat3Probe2` / `sat3_two_probe_eval` — **PROVED, the two-literal workhorse**: at every pin context,
        `f = bvec j₀ || sign`.  The satisfiable corners go through the witness assignment (slot 1 carries
        the pinned-true case, slot 0 the sign-true case); the unsatisfiable corner is a genuine forcing
        argument — the pin clause forces `A₀ = bvec j₀ = false` through `sat3Clause_single_iff`, and then
        both live literals of the designated clause are false.
  `sat3_odd_square_pinSign_designatedSign` — **PROVED, the odd square**: the engine-format parity of the
        four corners is `true` at every pin context — `α ⊕ ¬α ⊕ 1 ⊕ 1 = 1`.

With the XOR-square of the previous file, `two_squares_kill_split` now closes every proper cut that
separates the pair (pin-sign of `j₀ = 0`, designated sign).  Remaining for the discharge of
`Sat3NoBipartiteSplitProper`: cuts that do **not** separate a producible pair — the coverage argument
(more pin-sign pairs by varying `j₀` and `cIdx`, and the rectangle-closure route for selector-heavy
cuts).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The two-literal probe: slot-0 and slot-1 selectors on variable `0`, all signs `0`. -/
def sat3Probe2 (N : ℕ) : Fin N → Bool :=
  fun bit => decide (bit.val % sat3D N = 0 ∨ bit.val % sat3D N = sat3V N + 1)

/-- Every non-designated clause is satisfied by the standard witness under any block override. -/
theorem sat3_outside_clause_satisfied (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (cIdx : Fin (sat3M N)) (bvec : Fin (sat3M N - 2) → Bool) (cl : Fin (sat3M N))
    (hclv : cl.val ≠ cIdx.val) (X : Fin N → Bool)
    (houtside : ∀ (cl' : Fin (sat3M N)) (hcl : cl'.val ≠ cIdx.val) (t : Fin 3)
      (fI : ℕ) (hfI : fI < sat3V N + 1),
      X (sat3Bit N cl' t fI hfI)
        = sat3Patch N cIdx (sat3Context N cIdx hk bvec) (sat3Probe2 N)
            (sat3Bit N cl' t fI hfI)) :
    ∃ t, sat3Lit N X (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩
      else true) cl t = true := by
  classical
  by_cases hpin : ∃ j' : Fin (sat3M N - 2), sat3PinClause N cIdx hk j' = cl
  · obtain ⟨j', rfl⟩ := hpin
    have hjlt : j'.val < sat3V N := by have := j'.isLt; omega
    refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N X _ _ ⟨0, by omega⟩
      ⟨j'.val, hjlt⟩ ?_ ?_⟩
    · rw [houtside _ (sat3PinClause_ne N cIdx hk j') _ _ _]
      exact pin_read_sel N cIdx hk hkv bvec (sat3Probe2 N) j'
    · rw [houtside _ (sat3PinClause_ne N cIdx hk j') _ _ _,
        pin_read_sign N cIdx hk hkv bvec (sat3Probe2 N) j']
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

/-- **THE TWO-LITERAL WORKHORSE (proved)**: `f = bvec j₀ || sign` at every pin context. -/
theorem sat3_two_probe_eval (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (bvec : Fin (sat3M N - 2) → Bool) (a : Bool) :
    sat3Family N (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
      (sat3Probe2 N)) (sat3SignBit N cIdx) a)
    = (bvec ⟨0, by omega⟩ || a) := by
  classical
  set X : Fin N → Bool := Function.update (sat3Patch N cIdx
    (sat3Context N cIdx hk bvec) (sat3Probe2 N)) (sat3SignBit N cIdx) a with hX
  -- designated-block reads off the sign bit
  have hownbit : ∀ (t : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1),
      ¬(t.val = 0 ∧ fI = sat3V N) →
      X (sat3Bit N cIdx t fI hfI)
        = decide (t.val * (sat3V N + 1) + fI = 0
            ∨ t.val * (sat3V N + 1) + fI = sat3V N + 1) := by
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
    unfold sat3Probe2
    rw [sat3Bit_rem]
  have hsign : X (sat3Bit N cIdx ⟨0, by omega⟩ (sat3V N) (by omega)) = a := by
    rw [hX]
    exact Function.update_self _ _ _
  -- the six designated reads
  have hr00 : X (sat3Bit N cIdx ⟨0, by omega⟩ (0 : ℕ) (by omega)) = true := by
    rw [hownbit ⟨0, by omega⟩ 0 (by omega) (by intro h; omega)]
    show decide ((0 : ℕ) * (sat3V N + 1) + 0 = 0
        ∨ (0 : ℕ) * (sat3V N + 1) + 0 = sat3V N + 1) = true
    rw [decide_eq_true_eq]
    left
    omega
  have hr0i : ∀ i : Fin (sat3V N), i ≠ ⟨0, hv⟩ →
      X (sat3Bit N cIdx ⟨0, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
    intro i hi
    have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
    rw [hownbit ⟨0, by omega⟩ i.val (by have := i.isLt; omega)
      (by rintro ⟨-, h⟩; have := i.isLt; omega)]
    show decide ((0 : ℕ) * (sat3V N + 1) + i.val = 0
        ∨ (0 : ℕ) * (sat3V N + 1) + i.val = sat3V N + 1) = false
    rw [decide_eq_false_iff_not]
    rintro (h | h)
    · exact hiv (by omega)
    · have := i.isLt
      omega
  have hr10 : X (sat3Bit N cIdx ⟨1, by omega⟩ (0 : ℕ) (by omega)) = true := by
    rw [hownbit ⟨1, by omega⟩ 0 (by omega)
      (by rintro ⟨h, -⟩; have h' : (1 : ℕ) = 0 := h; omega)]
    show decide ((1 : ℕ) * (sat3V N + 1) + 0 = 0
        ∨ (1 : ℕ) * (sat3V N + 1) + 0 = sat3V N + 1) = true
    rw [decide_eq_true_eq]
    right
    omega
  have hr1i : ∀ i : Fin (sat3V N), i ≠ ⟨0, hv⟩ →
      X (sat3Bit N cIdx ⟨1, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
    intro i hi
    have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
    rw [hownbit ⟨1, by omega⟩ i.val (by have := i.isLt; omega)
      (by rintro ⟨h, -⟩; have h' : (1 : ℕ) = 0 := h; omega)]
    show decide ((1 : ℕ) * (sat3V N + 1) + i.val = 0
        ∨ (1 : ℕ) * (sat3V N + 1) + i.val = sat3V N + 1) = false
    rw [decide_eq_false_iff_not]
    rintro (h | h)
    · omega
    · exact hiv (by omega)
  have hr1v : X (sat3Bit N cIdx ⟨1, by omega⟩ (sat3V N) (by omega)) = false := by
    rw [hownbit ⟨1, by omega⟩ (sat3V N) (by omega)
      (by rintro ⟨h, -⟩; have h' : (1 : ℕ) = 0 := h; omega)]
    show decide ((1 : ℕ) * (sat3V N + 1) + sat3V N = 0
        ∨ (1 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N + 1) = false
    rw [decide_eq_false_iff_not]
    rintro (h | h) <;> omega
  have hr2 : ∀ i : Fin (sat3V N),
      X (sat3Bit N cIdx ⟨2, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
    intro i
    rw [hownbit ⟨2, by omega⟩ i.val (by have := i.isLt; omega)
      (by rintro ⟨h, -⟩; have h' : (2 : ℕ) = 0 := h; omega)]
    show decide ((2 : ℕ) * (sat3V N + 1) + i.val = 0
        ∨ (2 : ℕ) * (sat3V N + 1) + i.val = sat3V N + 1) = false
    rw [decide_eq_false_iff_not]
    have := i.isLt
    rintro (h | h) <;> omega
  -- pin-block and tautology reads: the update at the sign bit never touches them
  have houtside : ∀ (cl : Fin (sat3M N)) (hcl : cl.val ≠ cIdx.val) (t : Fin 3)
      (fI : ℕ) (hfI : fI < sat3V N + 1),
      X (sat3Bit N cl t fI hfI)
        = sat3Patch N cIdx (sat3Context N cIdx hk bvec) (sat3Probe2 N)
            (sat3Bit N cl t fI hfI) := by
    intro cl hcl t fI hfI
    rw [hX, Function.update_of_ne (show sat3Bit N cl t fI hfI ≠ sat3SignBit N cIdx
      from sat3Bit_ne_of_clause N _ _ _ _ hcl)]
  cases hb : bvec ⟨0, by omega⟩ with
  | true =>
    -- satisfied via slot 1 of the designated block
    show sat3Family N X = (true || a)
    rw [Bool.true_or]
    apply sat3Family_of_witness N X
      (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩ else true)
    apply sat3Eval_true_of_all
    intro cl
    by_cases hcl : cl = cIdx
    · subst hcl
      refine ⟨⟨1, by omega⟩, sat3Lit_true_of_selected N X _ cl ⟨1, by omega⟩
        ⟨0, hv⟩ hr10 ?_⟩
      rw [hr1v]
      show xor (if h : (0 : ℕ) < sat3M N - 2 then bvec ⟨0, h⟩ else true) false = true
      have hbv : ∀ p : (0 : ℕ) < sat3M N - 2, bvec ⟨0, p⟩ = true := fun _ => hb
      rw [dif_pos (by omega : (0 : ℕ) < sat3M N - 2), hbv]
      rfl
    · exact sat3_outside_clause_satisfied N hv hk hkv cIdx bvec cl
        (fun h => hcl (Fin.ext h)) X houtside
  | false =>
    cases ha : a with
    | true =>
      -- satisfied via slot 0 with the sign
      show sat3Family N X = (false || true)
      rw [Bool.false_or]
      apply sat3Family_of_witness N X
        (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩ else true)
      apply sat3Eval_true_of_all
      intro cl
      by_cases hcl : cl = cIdx
      · subst hcl
        refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N X _ cl ⟨0, by omega⟩
          ⟨0, hv⟩ hr00 ?_⟩
        rw [show X (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = true from
          ha ▸ hsign]
        show xor (if h : (0 : ℕ) < sat3M N - 2 then bvec ⟨0, h⟩ else true) true = true
        have hbv : ∀ p : (0 : ℕ) < sat3M N - 2, bvec ⟨0, p⟩ = false := fun _ => hb
        rw [dif_pos (by omega : (0 : ℕ) < sat3M N - 2), hbv]
        rfl
      · exact sat3_outside_clause_satisfied N hv hk hkv cIdx bvec cl
          (fun h => hcl (Fin.ext h)) X houtside
    | false =>
      -- the forcing corner: pin forces A₀ = false, both designated literals die
      show sat3Family N X = (false || false)
      apply decide_eq_false
      rintro ⟨A, hA⟩
      -- the pin clause for j₀ = 0 forces A ⟨0⟩ = bvec ⟨0⟩ = false
      have hpin := sat3Eval_clause_true N X A hA
        (sat3PinClause N cIdx hk ⟨0, by omega⟩)
      have hforce : A ⟨0, hv⟩ = bvec ⟨0, by omega⟩ := by
        have hiff := sat3Clause_single_iff N X A
          (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, hv⟩
          (by
            rw [houtside _ (sat3PinClause_ne N cIdx hk ⟨0, by omega⟩) _ _ _]
            exact pin_read_sel N cIdx hk hkv bvec (sat3Probe2 N) ⟨0, by omega⟩)
          (by
            intro i hi
            rw [houtside _ (sat3PinClause_ne N cIdx hk ⟨0, by omega⟩) _ _ _]
            exact pin_read_miss N cIdx hk hkv bvec (sat3Probe2 N) ⟨0, by omega⟩ i
              (by
                intro hcon
                apply hi
                rw [hcon]))
          (by
            intro i
            rw [houtside _ (sat3PinClause_ne N cIdx hk ⟨0, by omega⟩) _ _ _]
            exact pin_read_dead N cIdx hk hkv bvec (sat3Probe2 N) ⟨0, by omega⟩
              ⟨1, by omega⟩ (by show (1:ℕ) ≤ 1; omega) i)
          (by
            intro i
            rw [houtside _ (sat3PinClause_ne N cIdx hk ⟨0, by omega⟩) _ _ _]
            exact pin_read_dead N cIdx hk hkv bvec (sat3Probe2 N) ⟨0, by omega⟩
              ⟨2, by omega⟩ (by show (1:ℕ) ≤ 2; omega) i)
        have hx := hiff.mp hpin
        rw [houtside _ (sat3PinClause_ne N cIdx hk ⟨0, by omega⟩) _ _ _,
          pin_read_sign N cIdx hk hkv bvec (sat3Probe2 N) ⟨0, by omega⟩] at hx
        exact xor_decide_eq _ _ hx
      -- now the designated clause fails
      obtain ⟨t, ht⟩ := sat3Eval_clause_true N X A hA cIdx
      rcases t with ⟨tv, htv⟩
      interval_cases tv
      · rw [sat3Lit_single N X A cIdx _ ⟨0, hv⟩ hr00 hr0i] at ht
        rw [show X (sat3Bit N cIdx ⟨0, by omega⟩ (sat3V N) (by omega)) = false from
          ha ▸ hsign] at ht
        have hbv : ∀ p : (0 : ℕ) < sat3M N - 2, bvec ⟨0, p⟩ = false := fun _ => hb
        rw [hforce, hbv] at ht
        cases ht
      · rw [sat3Lit_single N X A cIdx _ ⟨0, hv⟩ hr10 hr1i] at ht
        have hbv : ∀ p : (0 : ℕ) < sat3M N - 2, bvec ⟨0, p⟩ = false := fun _ => hb
        rw [hr1v, hforce, hbv] at ht
        cases ht
      · rw [sat3Lit_false_of_empty N X A cIdx _ hr2] at ht
        cases ht

/-- **THE ODD SQUARE (proved)**: engine-format parity `true` at every pin context, for the pair
(pin-sign of `j₀ = 0`, designated sign). -/
theorem sat3_odd_square_pinSign_designatedSign (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (bvec : Fin (sat3M N - 2) → Bool) :
    ∃ w : Fin N → Bool,
      xor (xor (sat3Family N w)
          (sat3Family N (Function.update w
            (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
              (by omega))
            (!(w (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩
              (sat3V N) (by omega)))))))
        (xor (sat3Family N (Function.update w (sat3SignBit N cIdx)
            (!(w (sat3SignBit N cIdx)))))
          (sat3Family N (Function.update (Function.update w
            (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
              (by omega))
            (!(w (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩
              (sat3V N) (by omega))))) (sat3SignBit N cIdx)
            (!(w (sat3SignBit N cIdx)))))) = true := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  have hne_ps : (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩
      (sat3V N) (by omega) : Fin N) ≠ sat3SignBit N cIdx :=
    sat3Bit_ne_of_clause N _ _ _ _
      (fun h => sat3PinClause_ne N cIdx hk ⟨0, by omega⟩ h)
  refine ⟨Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
    (sat3Probe2 N)) (sat3SignBit N cIdx) false, ?_⟩
  rw [sat3_two_probe_eval N hv hk hkv hm3 cIdx bvec false]
  -- pin-sign flip corner
  rw [Function.update_of_ne hne_ps,
    pin_read_sign N cIdx hk hkv bvec (sat3Probe2 N) ⟨0, by omega⟩]
  rw [show Function.update (Function.update (sat3Patch N cIdx
      (sat3Context N cIdx hk bvec) (sat3Probe2 N)) (sat3SignBit N cIdx) false)
      (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
        (by omega)) (!(decide (bvec ⟨0, by omega⟩ = false)))
    = Function.update (Function.update (sat3Patch N cIdx
      (sat3Context N cIdx hk bvec) (sat3Probe2 N))
      (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
        (by omega)) (!(decide (bvec ⟨0, by omega⟩ = false))))
      (sat3SignBit N cIdx) false from
    Function.update_comm hne_ps.symm _ _ _]
  rw [sat3Context_update_pin_sign N cIdx hk hkv bvec ⟨0, by omega⟩
    (sat3Probe2 N) (!(decide (bvec ⟨0, by omega⟩ = false)))]
  rw [sat3_two_probe_eval N hv hk hkv hm3 cIdx _ false]
  -- designated-sign flip corner
  rw [show (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
      (sat3Probe2 N)) (sat3SignBit N cIdx) false) (sat3SignBit N cIdx) = false from
    Function.update_self _ _ _]
  rw [Function.update_idem, sat3_two_probe_eval N hv hk hkv hm3 cIdx bvec (!false)]
  -- both-flip corner
  rw [Function.update_idem, sat3_two_probe_eval N hv hk hkv hm3 cIdx _ (!false)]
  rw [Function.update_self]
  cases hbv : bvec ⟨0, by omega⟩ <;> rfl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_two_probe_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_odd_square_pinSign_designatedSign
