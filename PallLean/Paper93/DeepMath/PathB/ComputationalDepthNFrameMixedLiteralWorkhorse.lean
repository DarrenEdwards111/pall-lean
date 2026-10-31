import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSplitCoverageFinal

/-!
# N-Frame: the mixed-literal workhorse — sign↔selector edges

The decisive production rung from the coverage audit.  The designated block carries the slot-0 probe
literal on pinned `w₀` (its sign free — the designated sign bit) **and** a slot-2 selector on pinned `j₀`
(the selector free): the clause is `xor(A_{w₀}, sign) ∨ (sel ∧ A_{j₀})`, and the pins force both values,
so at every pin context

  `f = xor (bvec w₀) sign || (sel && bvec j₀)`.

  `sat3_mixed_literal_eval` — **PROVED**: the two-coordinate evaluation, all four corners, with the unsat
        corner a double forcing argument (both pins fire).
  `sat3_sign_selector_odd` / `sat3_sign_selector_V1_selDown` / `sat3_sign_selector_V1_signDown` —
        **PROVED**: at `bvec = (· = j₀)` the table is `sign ∨ sel` — engine-format odd square and V1
        triples in both orientations, for the pair (designated sign, slot-2 selector on `j₀`).

## Honest scope

With the sign layer monolithic in the residual, these edges connect the sign mass to every block's slot-2
selectors — the assembly that kills whole-block cuts is the named next rung, then slot-0/1 selectors and
slot-1/2 signs.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE MIXED-LITERAL WORKHORSE (proved)**: `f = xor (bvec w₀) a || (b && bvec j₀)`. -/
theorem sat3_mixed_literal_eval (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (w₀ j₀ : Fin (sat3M N - 2))
    (hwv : w₀.val < sat3V N) (hjv : j₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (a b : Bool) :
    sat3Family N (Function.update (Function.update
      (sat3Patch N cIdx (sat3Context N cIdx hk bvec) (sat3Probe N ⟨w₀.val, hwv⟩ false))
      (sat3SignBit N cIdx) a) (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩) b)
    = (xor (bvec w₀) a || (b && bvec j₀)) := by
  classical
  set X : Fin N → Bool := Function.update (Function.update
    (sat3Patch N cIdx (sat3Context N cIdx hk bvec) (sat3Probe N ⟨w₀.val, hwv⟩ false))
    (sat3SignBit N cIdx) a) (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩) b with hX
  have hne_ss : sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ≠ sat3SignBit N cIdx :=
    sat3S2Sel_ne_signBit N cIdx ⟨j₀.val, hjv⟩ cIdx
  -- designated reads away from the two live coordinates
  have hownbit : ∀ (t : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1),
      ¬(t.val = 0 ∧ fI = sat3V N) → ¬(t.val = 2 ∧ fI = j₀.val) →
      X (sat3Bit N cIdx t fI hfI)
        = decide (t.val * (sat3V N + 1) + fI = w₀.val
            ∨ (t.val * (sat3V N + 1) + fI = sat3V N ∧ false = true)) := by
    intro t fI hfI hnot0 hnot2
    have hne2 : sat3Bit N cIdx t fI hfI ≠ sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ := by
      intro hcon
      have hr := sat3S2Sel_rem N cIdx ⟨j₀.val, hjv⟩
      rw [← hcon, sat3Bit_rem] at hr
      rcases t with ⟨tv, htv⟩
      interval_cases tv
      · have hr' : 0 * (sat3V N + 1) + fI = 2 * (sat3V N + 1) + j₀.val := hr
        omega
      · have hr' : 1 * (sat3V N + 1) + fI = 2 * (sat3V N + 1) + j₀.val := hr
        omega
      · have hr' : 2 * (sat3V N + 1) + fI = 2 * (sat3V N + 1) + j₀.val := hr
        exact hnot2 ⟨rfl, by omega⟩
    have hne0 : sat3Bit N cIdx t fI hfI ≠ sat3SignBit N cIdx := by
      intro hcon
      have hval := congrArg Fin.val hcon
      have h1 : (sat3Bit N cIdx t fI hfI).val
          = cIdx.val * sat3D N + t.val * (sat3V N + 1) + fI := rfl
      have h2 : (sat3SignBit N cIdx).val
          = cIdx.val * sat3D N + 0 * (sat3V N + 1) + sat3V N := rfl
      rw [h1, h2] at hval
      rcases t with ⟨tv, htv⟩
      interval_cases tv
      · refine hnot0 ⟨rfl, ?_⟩
        have hval' : cIdx.val * sat3D N + 0 * (sat3V N + 1) + fI
            = cIdx.val * sat3D N + 0 * (sat3V N + 1) + sat3V N := hval
        omega
      · have hval' : cIdx.val * sat3D N + 1 * (sat3V N + 1) + fI
            = cIdx.val * sat3D N + 0 * (sat3V N + 1) + sat3V N := hval
        omega
      · have hval' : cIdx.val * sat3D N + 2 * (sat3V N + 1) + fI
            = cIdx.val * sat3D N + 0 * (sat3V N + 1) + sat3V N := hval
        omega
    rw [hX, Function.update_of_ne hne2, Function.update_of_ne hne0,
      sat3Patch_own N cIdx _ _ t fI hfI]
    unfold sat3Probe
    rw [sat3Bit_rem]
  have hsign0 : X (sat3Bit N cIdx ⟨0, by omega⟩ (sat3V N) (by omega)) = a := by
    rw [hX]
    rw [Function.update_of_ne (show sat3Bit N cIdx ⟨0, by omega⟩ (sat3V N) (by omega)
        ≠ sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ from hne_ss.symm)]
    exact Function.update_self _ _ _
  have hs2j : X (sat3Bit N cIdx ⟨2, by omega⟩ j₀.val (by omega)) = b := by
    rw [hX]
    exact Function.update_self _ _ _
  have hs0w : X (sat3Bit N cIdx ⟨0, by omega⟩ w₀.val (by omega)) = true := by
    rw [hownbit ⟨0, by omega⟩ w₀.val (by omega) (by rintro ⟨-, h⟩; omega)
      (by rintro ⟨h, -⟩; have h' : (0 : ℕ) = 2 := h; omega)]
    show decide ((0 : ℕ) * (sat3V N + 1) + w₀.val = w₀.val
        ∨ ((0 : ℕ) * (sat3V N + 1) + w₀.val = sat3V N ∧ false = true)) = true
    rw [decide_eq_true_eq]
    left
    omega
  have hs0i : ∀ i : Fin (sat3V N), i ≠ ⟨w₀.val, hwv⟩ →
      X (sat3Bit N cIdx ⟨0, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
    intro i hi
    have hiv : i.val ≠ w₀.val := fun h => hi (Fin.ext h)
    rw [hownbit ⟨0, by omega⟩ i.val (by have := i.isLt; omega)
      (by rintro ⟨-, h⟩; have := i.isLt; omega)
      (by rintro ⟨h, -⟩; have h' : (0 : ℕ) = 2 := h; omega)]
    show decide ((0 : ℕ) * (sat3V N + 1) + i.val = w₀.val
        ∨ ((0 : ℕ) * (sat3V N + 1) + i.val = sat3V N ∧ false = true)) = false
    rw [decide_eq_false_iff_not]
    rintro (h | ⟨-, h⟩)
    · exact hiv (by omega)
    · cases h
  have hs1 : ∀ i : Fin (sat3V N),
      X (sat3Bit N cIdx ⟨1, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
    intro i
    rw [hownbit ⟨1, by omega⟩ i.val (by have := i.isLt; omega)
      (by rintro ⟨h, -⟩; have h' : (1 : ℕ) = 0 := h; omega)
      (by rintro ⟨h, -⟩; have h' : (1 : ℕ) = 2 := h; omega)]
    show decide ((1 : ℕ) * (sat3V N + 1) + i.val = w₀.val
        ∨ ((1 : ℕ) * (sat3V N + 1) + i.val = sat3V N ∧ false = true)) = false
    rw [decide_eq_false_iff_not]
    rintro (h | ⟨-, h⟩)
    · omega
    · cases h
  have hs2i : ∀ i : Fin (sat3V N), i ≠ ⟨j₀.val, hjv⟩ →
      X (sat3Bit N cIdx ⟨2, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
    intro i hi
    rw [hownbit ⟨2, by omega⟩ i.val (by have := i.isLt; omega)
      (by rintro ⟨h, -⟩; have h' : (2 : ℕ) = 0 := h; omega)
      (by rintro ⟨-, h⟩; exact hi (Fin.ext h))]
    show decide ((2 : ℕ) * (sat3V N + 1) + i.val = w₀.val
        ∨ ((2 : ℕ) * (sat3V N + 1) + i.val = sat3V N ∧ false = true)) = false
    rw [decide_eq_false_iff_not]
    rintro (h | ⟨-, h⟩)
    · omega
    · cases h
  have hsign2 : X (sat3Bit N cIdx ⟨2, by omega⟩ (sat3V N) (by omega)) = false := by
    rw [hownbit ⟨2, by omega⟩ (sat3V N) (by omega)
      (by rintro ⟨h, -⟩; have h' : (2 : ℕ) = 0 := h; omega)
      (by rintro ⟨-, h⟩; omega)]
    show decide ((2 : ℕ) * (sat3V N + 1) + sat3V N = w₀.val
        ∨ ((2 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N ∧ false = true)) = false
    rw [decide_eq_false_iff_not]
    rintro (h | ⟨-, h⟩)
    · omega
    · cases h
  have houtside : ∀ (cl : Fin (sat3M N)) (hcl : cl.val ≠ cIdx.val) (t : Fin 3)
      (fI : ℕ) (hfI : fI < sat3V N + 1),
      X (sat3Bit N cl t fI hfI)
        = sat3Patch N cIdx (sat3Context N cIdx hk bvec)
            (sat3Probe N ⟨w₀.val, hwv⟩ false) (sat3Bit N cl t fI hfI) := by
    intro cl hcl t fI hfI
    rw [hX,
      Function.update_of_ne (sat3Bit_ne_s2sel_of_clause N cl cIdx hcl _ _ _ _),
      Function.update_of_ne (show sat3Bit N cl t fI hfI ≠ sat3SignBit N cIdx
        from sat3Bit_ne_of_clause N _ _ _ _ hcl)]
  -- the four-value case analysis
  cases hcase : xor (bvec w₀) a with
  | true =>
    show sat3Family N X = (true || (b && bvec j₀))
    rw [Bool.true_or]
    apply sat3Family_of_witness N X
      (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩ else true)
    apply sat3Eval_true_of_all
    intro cl
    by_cases hcl : cl = cIdx
    · subst hcl
      refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N X _ cl ⟨0, by omega⟩
        ⟨w₀.val, hwv⟩ hs0w ?_⟩
      rw [hsign0]
      show xor (if h : w₀.val < sat3M N - 2 then bvec ⟨w₀.val, h⟩ else true) a = true
      rw [dif_pos w₀.isLt]
      have hb' : bvec ⟨w₀.val, w₀.isLt⟩ = bvec w₀ := rfl
      rw [hb', hcase]
    · exact sat3_outside_probe_satisfied N hv hk hkv cIdx bvec
        (sat3Probe N ⟨w₀.val, hwv⟩ false) cl (fun h => hcl (Fin.ext h)) X houtside
  | false =>
    cases hbj : (b && bvec j₀) with
    | true =>
      show sat3Family N X = (false || true)
      rw [Bool.false_or]
      have hb : b = true := by
        cases b
        · cases hbj
        · rfl
      have hj : bvec j₀ = true := by
        rw [hb, Bool.true_and] at hbj
        exact hbj
      apply sat3Family_of_witness N X
        (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩ else true)
      apply sat3Eval_true_of_all
      intro cl
      by_cases hcl : cl = cIdx
      · subst hcl
        refine ⟨⟨2, by omega⟩, sat3Lit_true_of_selected N X _ cl ⟨2, by omega⟩
          ⟨j₀.val, hjv⟩ (by rw [hs2j, hb]) ?_⟩
        rw [hsign2]
        show xor (if h : j₀.val < sat3M N - 2 then bvec ⟨j₀.val, h⟩ else true)
            false = true
        rw [dif_pos j₀.isLt]
        have hb' : bvec ⟨j₀.val, j₀.isLt⟩ = bvec j₀ := rfl
        rw [hb', hj]
        rfl
      · exact sat3_outside_probe_satisfied N hv hk hkv cIdx bvec
          (sat3Probe N ⟨w₀.val, hwv⟩ false) cl (fun h => hcl (Fin.ext h)) X houtside
    | false =>
      show sat3Family N X = (false || false)
      apply decide_eq_false
      rintro ⟨A, hA⟩
      -- both pins force
      have hforceW : A ⟨w₀.val, hwv⟩ = bvec w₀ := by
        have hiff := sat3Clause_single_iff N X A
          (sat3PinClause N cIdx hk w₀) ⟨w₀.val, hwv⟩
          (by
            rw [houtside _ (sat3PinClause_ne N cIdx hk w₀) _ _ _]
            exact pin_read_sel N cIdx hk hkv bvec _ w₀)
          (by
            intro i hi
            rw [houtside _ (sat3PinClause_ne N cIdx hk w₀) _ _ _]
            exact pin_read_miss N cIdx hk hkv bvec _ w₀ i
              (by intro hcon; apply hi; rw [hcon]))
          (by
            intro i
            rw [houtside _ (sat3PinClause_ne N cIdx hk w₀) _ _ _]
            exact pin_read_dead N cIdx hk hkv bvec _ w₀ ⟨1, by omega⟩
              (by show (1 : ℕ) ≤ 1; omega) i)
          (by
            intro i
            rw [houtside _ (sat3PinClause_ne N cIdx hk w₀) _ _ _]
            exact pin_read_dead N cIdx hk hkv bvec _ w₀ ⟨2, by omega⟩
              (by show (1 : ℕ) ≤ 2; omega) i)
        have hx := hiff.mp (sat3Eval_clause_true N X A hA _)
        rw [houtside _ (sat3PinClause_ne N cIdx hk w₀) _ _ _,
          pin_read_sign N cIdx hk hkv bvec _ w₀] at hx
        exact xor_decide_eq _ _ hx
      have hforceJ : A ⟨j₀.val, hjv⟩ = bvec j₀ := by
        have hiff := sat3Clause_single_iff N X A
          (sat3PinClause N cIdx hk j₀) ⟨j₀.val, hjv⟩
          (by
            rw [houtside _ (sat3PinClause_ne N cIdx hk j₀) _ _ _]
            exact pin_read_sel N cIdx hk hkv bvec _ j₀)
          (by
            intro i hi
            rw [houtside _ (sat3PinClause_ne N cIdx hk j₀) _ _ _]
            exact pin_read_miss N cIdx hk hkv bvec _ j₀ i
              (by intro hcon; apply hi; rw [hcon]))
          (by
            intro i
            rw [houtside _ (sat3PinClause_ne N cIdx hk j₀) _ _ _]
            exact pin_read_dead N cIdx hk hkv bvec _ j₀ ⟨1, by omega⟩
              (by show (1 : ℕ) ≤ 1; omega) i)
          (by
            intro i
            rw [houtside _ (sat3PinClause_ne N cIdx hk j₀) _ _ _]
            exact pin_read_dead N cIdx hk hkv bvec _ j₀ ⟨2, by omega⟩
              (by show (1 : ℕ) ≤ 2; omega) i)
        have hx := hiff.mp (sat3Eval_clause_true N X A hA _)
        rw [houtside _ (sat3PinClause_ne N cIdx hk j₀) _ _ _,
          pin_read_sign N cIdx hk hkv bvec _ j₀] at hx
        exact xor_decide_eq _ _ hx
      obtain ⟨t, ht⟩ := sat3Eval_clause_true N X A hA cIdx
      rcases t with ⟨tv, htv⟩
      interval_cases tv
      · rw [sat3Lit_single N X A cIdx _ ⟨w₀.val, hwv⟩ hs0w hs0i, hsign0,
          hforceW, hcase] at ht
        cases ht
      · rw [sat3Lit_false_of_empty N X A cIdx _ hs1] at ht
        cases ht
      · cases hb : b with
        | false =>
          rw [sat3Lit_false_of_empty N X A cIdx _ (by
            intro i
            by_cases hij : i = ⟨j₀.val, hjv⟩
            · rw [hij]
              rw [show X (sat3Bit N cIdx ⟨2, by omega⟩
                  (⟨j₀.val, hjv⟩ : Fin (sat3V N)).val (by omega)) = b from hs2j, hb]
            · exact hs2i i hij)] at ht
          cases ht
        | true =>
          rw [sat3Lit_single N X A cIdx _ ⟨j₀.val, hjv⟩ (by rw [hs2j, hb]) hs2i,
            hsign2, hforceJ] at ht
          rw [hb, Bool.true_and] at hbj
          rw [hbj] at ht
          cases ht

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_mixed_literal_eval
