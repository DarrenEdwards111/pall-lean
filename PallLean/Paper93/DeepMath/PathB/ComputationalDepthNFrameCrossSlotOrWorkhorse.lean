import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSlotSignCells

/-!
# N-Frame: the cross-slot OR workhorse — `f = b ∨ xor (bvec w₀) a`

The last pattern-production gap.  The designated block carries a **hardwired** slot-`t` selector on
the pinned variable `w₀` (its literal forced to `xor (bvec w₀) a` by the pin, sign free = axis `a`),
and a free slot-`t'` selector axis `b` on the **unpinned** variable `m − 2` (its literal satisfiable
at will).  The clause is then an OR across slots:

    `sat3Family X(b, a) = b ∨ xor (bvec w₀) a`.

Satisfied corners `{(1,0), (1,1), (0, ·)}` support the V1 triple on a pair **containing a slot-`t`
sign bit** — the missing V1 source for slot-1/2 sign capture.

  `sat3_cross_slot_or_eval` — **PROVED, the workhorse**: the two-axis evaluation, any slots
        `t' ≠ t`, any pin `w₀`, with double forcing in the refutation branch.

## Honest scope

This file is the eval only.  The corner-point packaging (`crossSlotPt` + val/flip helpers + the V1
producers in engine format) and the slot-`t` sign-capture assembly are the mechanical next rungs, in
the style of `slotSignPt`'s.  Then: `GlobalPACInterfaceBound`, and the wire-frontier →
coordinate-interface extraction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE CROSS-SLOT OR EVAL (proved)**: hardwired slot-`t` literal on pinned `w₀` (sign axis `a`)
OR free slot-`t'` selector axis `b` on the unpinned variable `m − 2`. -/
theorem sat3_cross_slot_or_eval (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    sat3Family N (Function.update (Function.update
      (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
        (fun bit => decide (bit = sat3Bit N cIdx t w₀.val (by omega))))
      (sat3Bit N cIdx t' (sat3M N - 2)
        (by have := sat3M_pred_le_sat3V N; omega)) b)
      (sat3Bit N cIdx t (sat3V N) (by omega)) a)
    = (b || xor (bvec w₀) a) := by
  classical
  have hfree : sat3M N - 2 < sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set u₀ : Fin N → Bool :=
    fun bit => decide (bit = sat3Bit N cIdx t w₀.val (by omega)) with hu₀
  set X : Fin N → Bool := Function.update (Function.update
    (sat3Patch N cIdx (sat3Context N cIdx hk bvec) u₀)
    (sat3Bit N cIdx t' (sat3M N - 2) (by omega)) b)
    (sat3Bit N cIdx t (sat3V N) (by omega)) a with hX
  have hne_ba : sat3Bit N cIdx t' (sat3M N - 2) (by omega)
      ≠ sat3Bit N cIdx t (sat3V N) (by omega) :=
    sat3Bit_ne_same_block N cIdx t' t (sat3M N - 2) (sat3V N) (by omega) (by omega)
      (by rintro ⟨h, -⟩; exact htt (Fin.ext h))
  -- the hardwired selector reads ON
  have hON : X (sat3Bit N cIdx t w₀.val (by omega)) = true := by
    rw [hX,
      Function.update_of_ne (sat3Bit_ne_same_block N cIdx t t w₀.val (sat3V N)
        (by omega) (by omega) (by rintro ⟨-, h⟩; omega)),
      Function.update_of_ne (sat3Bit_ne_same_block N cIdx t t' w₀.val
        (sat3M N - 2) (by omega) (by omega)
        (by rintro ⟨h, -⟩; exact htt (Fin.ext h.symm))),
      sat3Patch_own N cIdx _ _ t w₀.val (by omega)]
    exact decide_eq_true rfl
  have hbax : X (sat3Bit N cIdx t' (sat3M N - 2) (by omega)) = b := by
    rw [hX, Function.update_of_ne hne_ba]
    exact Function.update_self _ _ _
  have hsign : X (sat3Bit N cIdx t (sat3V N) (by omega)) = a := by
    rw [hX]
    exact Function.update_self _ _ _
  -- everything else in the designated block reads OFF
  have hown0 : ∀ (t'' : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1),
      ¬(t''.val = t.val ∧ fI = w₀.val) →
      ¬(t''.val = t'.val ∧ fI = sat3M N - 2) →
      ¬(t''.val = t.val ∧ fI = sat3V N) →
      X (sat3Bit N cIdx t'' fI hfI) = false := by
    intro t'' fI hfI hn1 hn2 hn3
    rw [hX,
      Function.update_of_ne (sat3Bit_ne_same_block N cIdx t'' t fI (sat3V N)
        hfI (by omega) hn3),
      Function.update_of_ne (sat3Bit_ne_same_block N cIdx t'' t' fI
        (sat3M N - 2) hfI (by omega) hn2),
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
      refine ⟨t', sat3Lit_true_of_selected N X _ cl t' ⟨sat3M N - 2, hfree⟩
        (by rw [show sat3Bit N cl t' (⟨sat3M N - 2, hfree⟩ : Fin (sat3V N)).val
            (by omega) = sat3Bit N cl t' (sat3M N - 2) (by omega) from rfl,
          hbax, hb]) ?_⟩
      rw [show X (sat3Bit N cl t' (sat3V N) (by omega)) = false from
        hown0 t' (sat3V N) (by omega)
          (by rintro ⟨h, -⟩; exact htt (Fin.ext h))
          (by rintro ⟨-, h⟩; omega)
          (by rintro ⟨h, -⟩; exact htt (Fin.ext h))]
      show xor (if h : (⟨sat3M N - 2, hfree⟩ : Fin (sat3V N)).val < sat3M N - 2
        then bvec ⟨(⟨sat3M N - 2, hfree⟩ : Fin (sat3V N)).val, h⟩ else true)
        false = true
      rw [dif_neg (Nat.lt_irrefl _)]
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
      -- double forcing: the pin fixes A at w₀
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
            by_cases hij : i.val = sat3M N - 2
            · have hbit : sat3Bit N cIdx t'' i.val (by have := i.isLt; omega)
                  = sat3Bit N cIdx t'' (sat3M N - 2) (by omega) := by
                apply Fin.ext
                show cIdx.val * sat3D N + t''.val * (sat3V N + 1) + i.val
                  = cIdx.val * sat3D N + t''.val * (sat3V N + 1) + (sat3M N - 2)
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

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cross_slot_or_eval
