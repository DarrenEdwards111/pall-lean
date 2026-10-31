import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameOneBitPropagation

/-!
# N-Frame: the free-variable anchor menu — sign escape forces an `Ω(m)`-wide menu offside

The cross-slot machinery generalized from the single unpinned variable `m − 2` to **every** unpinned
variable `jF` (`m − 2 ≤ jF < v`, and the layout gives `v ≥ 3m − 1`, so the menu has `≥ 2m` entries
per slot pair).  An escaped slot-`t` sign now forces an entire `Ω(m)`-sized anchor menu off the
aligned side — the adversary can no longer block sign capture by interning two coordinates.

  `sat3_cross_slot_or_eval_free` — **PROVED**: the OR workhorse at an arbitrary unpinned variable.
  `crossSlotPtF` + helpers, `sat3_cross_slot_odd_free/odd'_free`,
  `sat3_cross_slot_V1_signDown_free/selDown_free` — the packaged producers, `jF`-parametric.
  `sat3_cross_slot_sign_capture_free_left/right` — **PROVED**: capture with anchors at any unpinned
        variable.
  `sat3_sign_escape_forces_menu_left` — **PROVED, the menu law**: in the aligned-left branch, an
        escaped slot-`t` sign forces **all** free-variable anchors `(t', jF)` off `A \ B`, or **all**
        pinned slot-`t` anchors off `A \ B` — either way an `Ω(m)`-sized family is interned-or-right,
        and interned costs interface while right feeds the selector escape bounds.

## Honest scope

Remaining `GlobalPACInterfaceBound` gaps: slot-1/2 one-bit propagation, and the final case-count over
escapee classes.  Then the wire-frontier → coordinate-interface extraction.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE FREE-VARIABLE OR EVAL (proved)**: the cross-slot workhorse at any unpinned `jF`. -/
theorem sat3_cross_slot_or_eval_free (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (jF : Fin (sat3V N)) (hjF : sat3M N - 2 ≤ jF.val)
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    sat3Family N (Function.update (Function.update
      (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
        (fun bit => decide (bit = sat3Bit N cIdx t w₀.val (by omega))))
      (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega)) b)
      (sat3Bit N cIdx t (sat3V N) (by omega)) a)
    = (b || xor (bvec w₀) a) := by
  classical
  set u₀ : Fin N → Bool :=
    fun bit => decide (bit = sat3Bit N cIdx t w₀.val (by omega)) with hu₀
  set X : Fin N → Bool := Function.update (Function.update
    (sat3Patch N cIdx (sat3Context N cIdx hk bvec) u₀)
    (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega)) b)
    (sat3Bit N cIdx t (sat3V N) (by omega)) a with hX
  have hne_ba : sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega)
      ≠ sat3Bit N cIdx t (sat3V N) (by omega) :=
    sat3Bit_ne_same_block N cIdx t' t jF.val (sat3V N) (by have := jF.isLt; omega)
      (by omega) (by rintro ⟨h, -⟩; exact htt (Fin.ext h))
  have hON : X (sat3Bit N cIdx t w₀.val (by omega)) = true := by
    rw [hX,
      Function.update_of_ne (sat3Bit_ne_same_block N cIdx t t w₀.val (sat3V N)
        (by omega) (by omega) (by rintro ⟨-, h⟩; omega)),
      Function.update_of_ne (sat3Bit_ne_same_block N cIdx t t' w₀.val
        jF.val (by omega) (by have := jF.isLt; omega)
        (by rintro ⟨h, -⟩; exact htt (Fin.ext h.symm))),
      sat3Patch_own N cIdx _ _ t w₀.val (by omega)]
    exact decide_eq_true rfl
  have hbax : X (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega)) = b := by
    rw [hX, Function.update_of_ne hne_ba]
    exact Function.update_self _ _ _
  have hsign : X (sat3Bit N cIdx t (sat3V N) (by omega)) = a := by
    rw [hX]
    exact Function.update_self _ _ _
  have hown0 : ∀ (t'' : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1),
      ¬(t''.val = t.val ∧ fI = w₀.val) →
      ¬(t''.val = t'.val ∧ fI = jF.val) →
      ¬(t''.val = t.val ∧ fI = sat3V N) →
      X (sat3Bit N cIdx t'' fI hfI) = false := by
    intro t'' fI hfI hn1 hn2 hn3
    rw [hX,
      Function.update_of_ne (sat3Bit_ne_same_block N cIdx t'' t fI (sat3V N)
        hfI (by omega) hn3),
      Function.update_of_ne (sat3Bit_ne_same_block N cIdx t'' t' fI
        jF.val hfI (by have := jF.isLt; omega) hn2),
      sat3Patch_own N cIdx _ _ t'' fI hfI]
    exact decide_eq_false (sat3Bit_ne_same_block N cIdx t'' t fI w₀.val hfI
      (by omega) hn1)
  have houtside : ∀ (cl : Fin (sat3M N)) (hcl : cl.val ≠ cIdx.val) (t'' : Fin 3)
      (fI : ℕ) (hfI : fI < sat3V N + 1),
      X (sat3Bit N cl t'' fI hfI)
        = sat3Patch N cIdx (sat3Context N cIdx hk bvec) u₀
            (sat3Bit N cl t'' fI hfI) := by
    intro cl hcl t'' fI hfI
    rw [hX, Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _ hcl),
      Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _ hcl)]
  cases hb : b with
  | true =>
    show sat3Family N X = (true || xor (bvec w₀) a)
    apply sat3Family_of_witness N X
      (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩ else true)
    apply sat3Eval_true_of_all
    intro cl
    by_cases hcl : cl = cIdx
    · subst hcl
      refine ⟨t', sat3Lit_true_of_selected N X _ cl t' jF
        (by rw [show sat3Bit N cl t' jF.val (by omega)
            = sat3Bit N cl t' jF.val (by have := jF.isLt; omega) from rfl,
          hbax, hb]) ?_⟩
      rw [show X (sat3Bit N cl t' (sat3V N) (by omega)) = false from
        hown0 t' (sat3V N) (by omega)
          (by rintro ⟨h, -⟩; exact htt (Fin.ext h))
          (by rintro ⟨-, h⟩; have := jF.isLt; omega)
          (by rintro ⟨h, -⟩; exact htt (Fin.ext h))]
      show xor (if h : jF.val < sat3M N - 2
        then bvec ⟨jF.val, h⟩ else true) false = true
      rw [dif_neg (Nat.not_lt.mpr hjF)]
      rfl
    · exact sat3_outside_probe_satisfied N hv hk hkv cIdx bvec u₀ cl
        (fun h' => hcl (Fin.ext h')) X houtside
  | false =>
    cases hxa : xor (bvec w₀) a with
    | true =>
      show sat3Family N X = (false || true)
      apply sat3Family_of_witness N X
        (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩ else true)
      apply sat3Eval_true_of_all
      intro cl
      by_cases hcl : cl = cIdx
      · subst hcl
        refine ⟨t, sat3Lit_true_of_selected N X _ cl t ⟨w₀.val, hwv⟩
          (by rw [show sat3Bit N cl t (⟨w₀.val, hwv⟩ : Fin (sat3V N)).val
              (by omega) = sat3Bit N cl t w₀.val (by omega) from rfl]
              exact hON) ?_⟩
        rw [hsign]
        show xor (if h : w₀.val < sat3M N - 2 then bvec ⟨w₀.val, h⟩ else true)
          a = true
        rw [dif_pos w₀.isLt]
        have hb' : bvec ⟨w₀.val, w₀.isLt⟩ = bvec w₀ := rfl
        rw [hb', hxa]
      · exact sat3_outside_probe_satisfied N hv hk hkv cIdx bvec u₀ cl
          (fun h' => hcl (Fin.ext h')) X houtside
    | false =>
      show sat3Family N X = (false || false)
      apply decide_eq_false
      rintro ⟨A, hA⟩
      have hforce : A ⟨w₀.val, hwv⟩ = bvec w₀ := by
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
      obtain ⟨t'', ht''⟩ := sat3Eval_clause_true N X A hA cIdx
      by_cases htt2 : t'' = t
      · subst htt2
        rw [sat3Lit_single N X A cIdx _ ⟨w₀.val, hwv⟩
          (by rw [show sat3Bit N cIdx t'' (⟨w₀.val, hwv⟩ : Fin (sat3V N)).val
              (by omega) = sat3Bit N cIdx t'' w₀.val (by omega) from rfl]
              exact hON)
          (fun i hi => hown0 t'' i.val (by have := i.isLt; omega)
            (by rintro ⟨-, h⟩; exact hi (Fin.ext h))
            (by rintro ⟨h, -⟩; exact htt (Fin.ext h.symm))
            (by rintro ⟨-, h⟩; have := i.isLt; omega))] at ht''
        rw [hsign, hforce, hxa] at ht''
        cases ht''
      · by_cases htt3 : t'' = t'
        · subst htt3
          rw [sat3Lit_false_of_empty N X A cIdx _ (fun i => by
            by_cases hij : i.val = jF.val
            · have hbit : sat3Bit N cIdx t'' i.val (by have := i.isLt; omega)
                  = sat3Bit N cIdx t'' jF.val (by have := jF.isLt; omega) := by
                apply Fin.ext
                show cIdx.val * sat3D N + t''.val * (sat3V N + 1) + i.val
                  = cIdx.val * sat3D N + t''.val * (sat3V N + 1) + jF.val
                omega
              rw [hbit, hbax]
              exact hb
            · exact hown0 t'' i.val (by have := i.isLt; omega)
                (by rintro ⟨h, -⟩; exact htt (Fin.ext h))
                (by rintro ⟨-, h⟩; exact hij h)
                (by rintro ⟨h, -⟩; exact htt (Fin.ext h)))] at ht''
          cases ht''
        · rw [sat3Lit_false_of_empty N X A cIdx _ (fun i =>
            hown0 t'' i.val (by have := i.isLt; omega)
              (by rintro ⟨h, -⟩; exact htt2 (Fin.ext h))
              (by rintro ⟨h, -⟩; exact htt3 (Fin.ext h))
              (by rintro ⟨h, -⟩; exact htt2 (Fin.ext h)))] at ht''
          cases ht''

/-- The free-variable cross-slot corner point. -/
def crossSlotPtF (N : ℕ) (cIdx : Fin (sat3M N)) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (t t' : Fin 3) (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (jF : Fin (sat3V N)) (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    Fin N → Bool :=
  Function.update (Function.update
    (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
      (fun bit => decide (bit = sat3Bit N cIdx t w₀.val (by omega))))
    (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega)) b)
    (sat3Bit N cIdx t (sat3V N) (by omega)) a

theorem crossSlotPtF_eval (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (jF : Fin (sat3V N)) (hjF : sat3M N - 2 ≤ jF.val)
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    sat3Family N (crossSlotPtF N cIdx hk t t' w₀ hwv jF bvec b a)
      = (b || xor (bvec w₀) a) := by
  unfold crossSlotPtF
  exact sat3_cross_slot_or_eval_free N hv hk hkv hm3 cIdx t t' htt w₀ hwv
    jF hjF bvec b a

theorem crossSlotPtF_val_sel' (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) (jF : Fin (sat3V N))
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    crossSlotPtF N cIdx hk t t' w₀ hwv jF bvec b a
      (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega)) = b := by
  unfold crossSlotPtF
  rw [Function.update_of_ne (sat3Bit_ne_same_block N cIdx t' t jF.val
    (sat3V N) (by have := jF.isLt; omega) (by omega)
    (by rintro ⟨h, -⟩; exact htt (Fin.ext h)))]
  exact Function.update_self _ _ _

theorem crossSlotPtF_val_sign (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (t t' : Fin 3)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) (jF : Fin (sat3V N))
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    crossSlotPtF N cIdx hk t t' w₀ hwv jF bvec b a
      (sat3Bit N cIdx t (sat3V N) (by omega)) = a := by
  unfold crossSlotPtF
  exact Function.update_self _ _ _

theorem crossSlotPtF_flip_sign (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (t t' : Fin 3)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) (jF : Fin (sat3V N))
    (bvec : Fin (sat3M N - 2) → Bool) (b a v : Bool) :
    Function.update (crossSlotPtF N cIdx hk t t' w₀ hwv jF bvec b a)
      (sat3Bit N cIdx t (sat3V N) (by omega)) v
    = crossSlotPtF N cIdx hk t t' w₀ hwv jF bvec b v := by
  unfold crossSlotPtF
  exact Function.update_idem _ _ _

theorem crossSlotPtF_flip_sel' (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) (jF : Fin (sat3V N))
    (bvec : Fin (sat3M N - 2) → Bool) (b a v : Bool) :
    Function.update (crossSlotPtF N cIdx hk t t' w₀ hwv jF bvec b a)
      (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega)) v
    = crossSlotPtF N cIdx hk t t' w₀ hwv jF bvec v a := by
  unfold crossSlotPtF
  rw [Function.update_comm (show sat3Bit N cIdx t (sat3V N) (by omega)
      ≠ sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega) from
    sat3Bit_ne_same_block N cIdx t t' (sat3V N) jF.val (by omega)
      (by have := jF.isLt; omega)
      (by rintro ⟨h, -⟩; exact htt (Fin.ext h.symm)))]
  rw [Function.update_idem]

/-- **ODD SQUARE, free variable, (sel', sign) orientation (proved)**. -/
theorem sat3_cross_slot_odd_free (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (jF : Fin (sat3V N)) (hjF : sat3M N - 2 ≤ jF.val) :
    xor (xor (sat3Family N (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false))
        (sat3Family N (Function.update
          (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false)
          (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))
          (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false
            (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega)))))))
      (xor (sat3Family N (Function.update
          (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false)
          (sat3Bit N cIdx t (sat3V N) (by omega))
          (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false
            (sat3Bit N cIdx t (sat3V N) (by omega))))))
        (sat3Family N (Function.update (Function.update
          (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false)
          (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))
          (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false
            (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega)))))
          (sat3Bit N cIdx t (sat3V N) (by omega))
          (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false
            (sat3Bit N cIdx t (sat3V N) (by omega))))))) = true := by
  rw [crossSlotPtF_val_sel' N cIdx hk t t' htt w₀ hwv jF,
    crossSlotPtF_val_sign N cIdx hk t t' w₀ hwv jF]
  rw [crossSlotPtF_flip_sel' N cIdx hk t t' htt w₀ hwv jF]
  rw [crossSlotPtF_flip_sign N cIdx hk t t' w₀ hwv jF,
    crossSlotPtF_flip_sign N cIdx hk t t' w₀ hwv jF]
  rw [crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF,
    crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF,
    crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF,
    crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF]
  rfl

/-- **ODD SQUARE, free variable, (sign, sel') orientation (proved)**. -/
theorem sat3_cross_slot_odd'_free (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (jF : Fin (sat3V N)) (hjF : sat3M N - 2 ≤ jF.val) :
    xor (xor (sat3Family N (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false))
        (sat3Family N (Function.update
          (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false)
          (sat3Bit N cIdx t (sat3V N) (by omega))
          (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false
            (sat3Bit N cIdx t (sat3V N) (by omega)))))))
      (xor (sat3Family N (Function.update
          (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false)
          (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))
          (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false
            (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))))))
        (sat3Family N (Function.update (Function.update
          (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false)
          (sat3Bit N cIdx t (sat3V N) (by omega))
          (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false
            (sat3Bit N cIdx t (sat3V N) (by omega)))))
          (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))
          (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false
            (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))))))) = true := by
  rw [crossSlotPtF_val_sel' N cIdx hk t t' htt w₀ hwv jF,
    crossSlotPtF_val_sign N cIdx hk t t' w₀ hwv jF]
  rw [crossSlotPtF_flip_sign N cIdx hk t t' w₀ hwv jF]
  rw [crossSlotPtF_flip_sel' N cIdx hk t t' htt w₀ hwv jF,
    crossSlotPtF_flip_sel' N cIdx hk t t' htt w₀ hwv jF]
  rw [crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF,
    crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF,
    crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF,
    crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF]
  rfl

/-- **V1, sign down, free variable (proved)**: `(s₂, t₂) = (sel', sign)`, base `(0, 1)`. -/
theorem sat3_cross_slot_V1_signDown_free (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (jF : Fin (sat3V N)) (hjF : sat3M N - 2 ≤ jF.val) :
    sat3Family N (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false true) = true ∧
    sat3Family N (Function.update (Function.update
        (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false true)
        (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))
        (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false true
          (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega)))))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false true
        (sat3Bit N cIdx t (sat3V N) (by omega))))) = true ∧
    sat3Family N (Function.update
        (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false true)
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false true
        (sat3Bit N cIdx t (sat3V N) (by omega))))) = false := by
  rw [crossSlotPtF_val_sel' N cIdx hk t t' htt w₀ hwv jF,
    crossSlotPtF_val_sign N cIdx hk t t' w₀ hwv jF]
  rw [crossSlotPtF_flip_sel' N cIdx hk t t' htt w₀ hwv jF]
  rw [crossSlotPtF_flip_sign N cIdx hk t t' w₀ hwv jF,
    crossSlotPtF_flip_sign N cIdx hk t t' w₀ hwv jF]
  rw [crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF,
    crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF,
    crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF]
  exact ⟨rfl, rfl, rfl⟩

/-- **V1, selector down, free variable (proved)**: `(s₂, t₂) = (sign, sel')`, base `(1, 0)`. -/
theorem sat3_cross_slot_V1_selDown_free (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (jF : Fin (sat3V N)) (hjF : sat3M N - 2 ≤ jF.val) :
    sat3Family N (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) true false) = true ∧
    sat3Family N (Function.update (Function.update
        (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) true false)
        (sat3Bit N cIdx t (sat3V N) (by omega))
        (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) true false
          (sat3Bit N cIdx t (sat3V N) (by omega)))))
      (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))
      (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) true false
        (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))))) = true ∧
    sat3Family N (Function.update
        (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) true false)
      (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))
      (!(crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) true false
        (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))))) = false := by
  rw [crossSlotPtF_val_sel' N cIdx hk t t' htt w₀ hwv jF,
    crossSlotPtF_val_sign N cIdx hk t t' w₀ hwv jF]
  rw [crossSlotPtF_flip_sign N cIdx hk t t' w₀ hwv jF]
  rw [crossSlotPtF_flip_sel' N cIdx hk t t' htt w₀ hwv jF,
    crossSlotPtF_flip_sel' N cIdx hk t t' htt w₀ hwv jF]
  rw [crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF,
    crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF,
    crossSlotPtF_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF]
  exact ⟨rfl, rfl, rfl⟩

/-- **SLOT-SIGN CAPTURE AT ANY FREE VARIABLE, LEFT (proved)**. -/
theorem sat3_cross_slot_sign_capture_free_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (jF : Fin (sat3V N)) (hjF : sat3M N - 2 ≤ jF.val)
    (hanch1 : sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega) ∈ A \ B)
    (hanch2 : sat3Bit N cIdx t w₀.val (by omega) ∈ A \ B)
    (hI : sat3Bit N cIdx t (sat3V N) (by omega) ∉ A ∩ B) :
    sat3Bit N cIdx t (sat3V N) (by omega) ∈ A \ B := by
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  have hu := sat3_slotT_sign_mem_union N hv hk hkv hm3 op g h A B hg hh hf
    cIdx t t' htt w₀ hwv
  rw [Finset.mem_union] at hu
  rw [Finset.mem_inter] at hI
  push_neg at hI
  rw [Finset.mem_sdiff] at hanch1 hanch2
  rw [Finset.mem_sdiff]
  by_cases hsA : sat3Bit N cIdx t (sat3V N) (by omega) ∈ A
  · exact ⟨hsA, hI hsA⟩
  · exfalso
    obtain ⟨v1a, v1b, v1c⟩ :=
      sat3_cross_slot_V1_signDown_free N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF
    obtain ⟨z0a, z0b, z0c⟩ :=
      sat3_slot_sign_V0_selDown N hv hk hkv hm3 cIdx t w₀ hwv
    exact crossing_triples_kill_interfaced (sat3Family N) A B op g h hg hh hf
      (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (sat3Bit N cIdx t w₀.val (by omega))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      hanch1.2 hsA
      (sat3Bit_ne_same_block N cIdx t' t jF.val (sat3V N)
        (by have := jF.isLt; omega) (by omega)
        (by rintro ⟨h', -⟩; exact htt (Fin.ext h')))
      hanch1.2 hsA
      (sat3Bit_ne_same_block N cIdx t' t jF.val (sat3V N)
        (by have := jF.isLt; omega) (by omega)
        (by rintro ⟨h', -⟩; exact htt (Fin.ext h')))
      hanch2.2 hsA
      (sat3Bit_ne_same_block N cIdx t t w₀.val (sat3V N) (by omega) (by omega)
        (by rintro ⟨-, h'⟩; omega))
      (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false)
      (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false true)
      (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) true false)
      (sat3_cross_slot_odd_free N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF)
      v1a v1b v1c z0a z0b z0c

/-- **SLOT-SIGN CAPTURE AT ANY FREE VARIABLE, RIGHT (proved)**: the mirror. -/
theorem sat3_cross_slot_sign_capture_free_right (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (jF : Fin (sat3V N)) (hjF : sat3M N - 2 ≤ jF.val)
    (hanch1 : sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega) ∈ B \ A)
    (hanch2 : sat3Bit N cIdx t w₀.val (by omega) ∈ B \ A)
    (hI : sat3Bit N cIdx t (sat3V N) (by omega) ∉ A ∩ B) :
    sat3Bit N cIdx t (sat3V N) (by omega) ∈ B \ A := by
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  have hu := sat3_slotT_sign_mem_union N hv hk hkv hm3 op g h A B hg hh hf
    cIdx t t' htt w₀ hwv
  rw [Finset.mem_union] at hu
  rw [Finset.mem_inter] at hI
  push_neg at hI
  rw [Finset.mem_sdiff] at hanch1 hanch2
  rw [Finset.mem_sdiff]
  by_cases hsB : sat3Bit N cIdx t (sat3V N) (by omega) ∈ B
  · exact ⟨hsB, fun hsA => hI hsA hsB⟩
  · exfalso
    obtain ⟨v1a, v1b, v1c⟩ :=
      sat3_cross_slot_V1_selDown_free N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF
    obtain ⟨z0a, z0b, z0c⟩ :=
      sat3_slot_sign_V0_signDown N hv hk hkv hm3 cIdx t w₀ hwv
    exact crossing_triples_kill_interfaced (sat3Family N) A B op g h hg hh hf
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (sat3Bit N cIdx t w₀.val (by omega))
      hsB hanch1.2
      (sat3Bit_ne_same_block N cIdx t t' (sat3V N) jF.val (by omega)
        (by have := jF.isLt; omega)
        (by rintro ⟨h', -⟩; exact htt (Fin.ext h'.symm)))
      hsB hanch1.2
      (sat3Bit_ne_same_block N cIdx t t' (sat3V N) jF.val (by omega)
        (by have := jF.isLt; omega)
        (by rintro ⟨h', -⟩; exact htt (Fin.ext h'.symm)))
      hsB hanch2.2
      (sat3Bit_ne_same_block N cIdx t t (sat3V N) w₀.val (by omega) (by omega)
        (by rintro ⟨-, h'⟩; omega))
      (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) false false)
      (crossSlotPtF N cIdx hk t t' w₀ hwv jF (fun _ => false) true false)
      (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false true)
      (sat3_cross_slot_odd'_free N hv hk hkv hm3 cIdx t t' htt w₀ hwv jF hjF)
      v1a v1b v1c z0a z0b z0c

/-- **THE MENU LAW (proved)**: an escaped slot-`t` sign forces the entire free-variable anchor menu
off `A \ B`, or the entire pinned slot-`t` anchor menu off `A \ B`. -/
theorem sat3_sign_escape_forces_menu_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (cIdx : Fin (sat3M N)) (t : Fin 3)
    (hesc : sat3Bit N cIdx t (sat3V N) (by omega) ∈ B \ A) :
    (∀ (t' : Fin 3), t' ≠ t → ∀ jF : Fin (sat3V N), sat3M N - 2 ≤ jF.val →
      sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega) ∉ A \ B) ∨
    (∀ w₀ : Fin (sat3M N - 2), sat3Bit N cIdx t w₀.val
      (by have := sat3M_pred_le_sat3V N; have := w₀.isLt; omega) ∉ A \ B) := by
  classical
  by_cases hfr : ∃ (t' : Fin 3) (_ : t' ≠ t) (jF : Fin (sat3V N))
      (_ : sat3M N - 2 ≤ jF.val),
      sat3Bit N cIdx t' jF.val (by have := jF.isLt; omega) ∈ A \ B
  · right
    intro w₀ hpin
    obtain ⟨t', htt, jF, hjF, hfree⟩ := hfr
    have hI : sat3Bit N cIdx t (sat3V N) (by omega) ∉ A ∩ B :=
      fun hW => (Finset.mem_sdiff.mp hesc).2 (Finset.mem_inter.mp hW).1
    have hcap := sat3_cross_slot_sign_capture_free_left N hv hm3 hk
      op g h A B hg hh hf cIdx t t' htt w₀
      (by have := sat3M_pred_le_sat3V N; have := w₀.isLt; omega)
      jF hjF hfree hpin hI
    exact (Finset.mem_sdiff.mp hesc).2 (Finset.mem_sdiff.mp hcap).1
  · left
    intro t' htt jF hjF hmem
    exact hfr ⟨t', htt, jF, hjF, hmem⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cross_slot_or_eval_free
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cross_slot_sign_capture_free_left
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_escape_forces_menu_left
