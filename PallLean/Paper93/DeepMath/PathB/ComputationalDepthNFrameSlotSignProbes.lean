import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSelectorSweep

/-!
# N-Frame: slot-`t` sign probes — the last coordinate family joins the pattern graph

The final production rung.  The designated block carries a single slot-`t` literal on pinned `w₀`, with
both the selector and that slot's sign free:

  `f = b && xor (bvec w₀) a`

over the axes (slot-`t` selector on `w₀`, slot-`t` sign).  At `bvec w₀ = false` and `b = true` this is
`xor`-shaped in (sign, pin-sign of `w₀`) — V1 and V0 through the identification lemma; with the sign as
the second axis it is AND-shaped in (selector, sign) — the odd squares.

  `sat3Bit_ne_same_block` — the general same-block bit disjointness (9-way literal-slot bash).
  `sat3_slot_sign_eval` — **PROVED**: the two-axis evaluation, forcing corner through pin `w₀`.
  `slotSignPt` + helpers, and the six engine-format packages: odd in both orders for the AND pair
        (selector, sign); V1 and V0 in both orders for the XOR pair (sign, pin-sign).

## Honest scope

Every slot-1/2 sign field now has killable pairs into the united mass.  The single remaining step is the
final reduction: sweep the sign fields, discharge the residual, and fire
`2·m·D ≤ cbudget (sat3Family N)` unconditionally.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Same-block bits with different (slot, field) addresses are distinct. -/
theorem sat3Bit_ne_same_block (N : ℕ) (c : Fin (sat3M N)) (t₁ t₂ : Fin 3)
    (f₁ f₂ : ℕ) (h₁ : f₁ < sat3V N + 1) (h₂ : f₂ < sat3V N + 1)
    (hne : ¬(t₁.val = t₂.val ∧ f₁ = f₂)) :
    sat3Bit N c t₁ f₁ h₁ ≠ sat3Bit N c t₂ f₂ h₂ := by
  intro hcon
  have hval := congrArg Fin.val hcon
  rcases t₁ with ⟨a, ha⟩
  rcases t₂ with ⟨b, hb⟩
  interval_cases a <;> interval_cases b
  · exact hne ⟨rfl, by
      have h' : c.val * sat3D N + 0 * (sat3V N + 1) + f₁
          = c.val * sat3D N + 0 * (sat3V N + 1) + f₂ := hval
      omega⟩
  · exact absurd (show c.val * sat3D N + 0 * (sat3V N + 1) + f₁
        = c.val * sat3D N + 1 * (sat3V N + 1) + f₂ from hval) (by omega)
  · exact absurd (show c.val * sat3D N + 0 * (sat3V N + 1) + f₁
        = c.val * sat3D N + 2 * (sat3V N + 1) + f₂ from hval) (by omega)
  · exact absurd (show c.val * sat3D N + 1 * (sat3V N + 1) + f₁
        = c.val * sat3D N + 0 * (sat3V N + 1) + f₂ from hval) (by omega)
  · exact hne ⟨rfl, by
      have h' : c.val * sat3D N + 1 * (sat3V N + 1) + f₁
          = c.val * sat3D N + 1 * (sat3V N + 1) + f₂ := hval
      omega⟩
  · exact absurd (show c.val * sat3D N + 1 * (sat3V N + 1) + f₁
        = c.val * sat3D N + 2 * (sat3V N + 1) + f₂ from hval) (by omega)
  · exact absurd (show c.val * sat3D N + 2 * (sat3V N + 1) + f₁
        = c.val * sat3D N + 0 * (sat3V N + 1) + f₂ from hval) (by omega)
  · exact absurd (show c.val * sat3D N + 2 * (sat3V N + 1) + f₁
        = c.val * sat3D N + 1 * (sat3V N + 1) + f₂ from hval) (by omega)
  · exact hne ⟨rfl, by
      have h' : c.val * sat3D N + 2 * (sat3V N + 1) + f₁
          = c.val * sat3D N + 2 * (sat3V N + 1) + f₂ := hval
      omega⟩

/-- **THE SLOT-SIGN EVAL (proved)**: single slot-`t` literal on pinned `w₀`, selector and sign free —
`f = b && xor (bvec w₀) a`. -/
theorem sat3_slot_sign_eval (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t : Fin 3)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    sat3Family N (Function.update (Function.update
      (sat3Patch N cIdx (sat3Context N cIdx hk bvec) (fun _ => false))
      (sat3Bit N cIdx t w₀.val (by omega)) b)
      (sat3Bit N cIdx t (sat3V N) (by omega)) a)
    = (b && xor (bvec w₀) a) := by
  classical
  set X : Fin N → Bool := Function.update (Function.update
    (sat3Patch N cIdx (sat3Context N cIdx hk bvec) (fun _ => false))
    (sat3Bit N cIdx t w₀.val (by omega)) b)
    (sat3Bit N cIdx t (sat3V N) (by omega)) a with hX
  have hne_selsign : sat3Bit N cIdx t w₀.val (by omega)
      ≠ sat3Bit N cIdx t (sat3V N) (by omega) :=
    sat3Bit_ne_same_block N cIdx t t w₀.val (sat3V N) (by omega) (by omega)
      (by rintro ⟨-, h⟩; omega)
  have hown0 : ∀ (t' : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1),
      ¬(t'.val = t.val ∧ fI = w₀.val) → ¬(t'.val = t.val ∧ fI = sat3V N) →
      X (sat3Bit N cIdx t' fI hfI) = false := by
    intro t' fI hfI hn1 hn2
    rw [hX, Function.update_of_ne (sat3Bit_ne_same_block N cIdx t' t fI (sat3V N)
        hfI (by omega) hn2),
      Function.update_of_ne (sat3Bit_ne_same_block N cIdx t' t fI w₀.val
        hfI (by omega) hn1),
      sat3Patch_own N cIdx _ _ t' fI hfI]
  have hsel : X (sat3Bit N cIdx t w₀.val (by omega)) = b := by
    rw [hX, Function.update_of_ne hne_selsign]
    exact Function.update_self _ _ _
  have hsign : X (sat3Bit N cIdx t (sat3V N) (by omega)) = a := by
    rw [hX]
    exact Function.update_self _ _ _
  have houtside : ∀ (cl : Fin (sat3M N)) (hcl : cl.val ≠ cIdx.val) (t' : Fin 3)
      (fI : ℕ) (hfI : fI < sat3V N + 1),
      X (sat3Bit N cl t' fI hfI)
        = sat3Patch N cIdx (sat3Context N cIdx hk bvec) (fun _ => false)
            (sat3Bit N cl t' fI hfI) := by
    intro cl hcl t' fI hfI
    rw [hX, Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _ hcl),
      Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _ hcl)]
  cases hb : b with
  | false =>
    show sat3Family N X = (false && xor (bvec w₀) a)
    rw [Bool.false_and]
    apply sat3Family_false_of_empty_clause N X cIdx
    intro t' i
    by_cases hti : t'.val = t.val ∧ i.val = w₀.val
    · rw [show sat3Bit N cIdx t' i.val (by have := i.isLt; omega)
          = sat3Bit N cIdx t w₀.val (by omega) from by
        rcases hti with ⟨ht', hi⟩
        congr 1
        · exact Fin.ext ht']
      rw [hsel, hb]
    · exact hown0 t' i.val (by have := i.isLt; omega) hti
        (by rintro ⟨-, h⟩; have := i.isLt; omega)
  | true =>
    cases hxa : xor (bvec w₀) a with
    | true =>
      show sat3Family N X = (true && true)
      apply sat3Family_of_witness N X
        (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩ else true)
      apply sat3Eval_true_of_all
      intro cl
      by_cases hcl : cl = cIdx
      · subst hcl
        refine ⟨t, sat3Lit_true_of_selected N X _ cl t ⟨w₀.val, hwv⟩
          (by rw [show sat3Bit N cl t (⟨w₀.val, hwv⟩ : Fin (sat3V N)).val
              (by omega) = sat3Bit N cl t w₀.val (by omega) from rfl, hsel, hb]) ?_⟩
        rw [hsign]
        show xor (if h : w₀.val < sat3M N - 2 then bvec ⟨w₀.val, h⟩ else true) a = true
        rw [dif_pos w₀.isLt]
        have hb' : bvec ⟨w₀.val, w₀.isLt⟩ = bvec w₀ := rfl
        rw [hb', hxa]
      · exact sat3_outside_probe_satisfied N hv hk hkv cIdx bvec
          (fun _ => false) cl (fun h => hcl (Fin.ext h)) X houtside
    | false =>
      show sat3Family N X = (true && false)
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
      obtain ⟨t', ht'⟩ := sat3Eval_clause_true N X A hA cIdx
      by_cases htt : t' = t
      · subst htt
        rw [sat3Lit_single N X A cIdx _ ⟨w₀.val, hwv⟩
          (by rw [show sat3Bit N cIdx t' (⟨w₀.val, hwv⟩ : Fin (sat3V N)).val
              (by omega) = sat3Bit N cIdx t' w₀.val (by omega) from rfl, hsel, hb])
          (fun i hi => hown0 t' i.val (by have := i.isLt; omega)
            (by rintro ⟨-, h⟩; exact hi (Fin.ext h))
            (by rintro ⟨-, h⟩; have := i.isLt; omega))] at ht'
        rw [hsign, hforce, hxa] at ht'
        cases ht'
      · rw [sat3Lit_false_of_empty N X A cIdx _ (fun i =>
          hown0 t' i.val (by have := i.isLt; omega)
            (by rintro ⟨h, -⟩; exact htt (Fin.ext h))
            (by rintro ⟨h, -⟩; exact htt (Fin.ext h)))] at ht'
        cases ht'

/-- The slot-sign corner point. -/
def slotSignPt (N : ℕ) (cIdx : Fin (sat3M N)) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (t : Fin 3) (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) : Fin N → Bool :=
  Function.update (Function.update
    (sat3Patch N cIdx (sat3Context N cIdx hk bvec) (fun _ => false))
    (sat3Bit N cIdx t w₀.val (by omega)) b)
    (sat3Bit N cIdx t (sat3V N) (by omega)) a

theorem slotSignPt_eval (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t : Fin 3)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    sat3Family N (slotSignPt N cIdx hk t w₀ hwv bvec b a)
      = (b && xor (bvec w₀) a) := by
  unfold slotSignPt
  exact sat3_slot_sign_eval N hv hk hkv hm3 cIdx t w₀ hwv bvec b a

theorem slotSignPt_val_sel (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (t : Fin 3) (w₀ : Fin (sat3M N - 2))
    (hwv : w₀.val < sat3V N) (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    slotSignPt N cIdx hk t w₀ hwv bvec b a (sat3Bit N cIdx t w₀.val (by omega)) = b := by
  unfold slotSignPt
  rw [Function.update_of_ne (sat3Bit_ne_same_block N cIdx t t w₀.val (sat3V N)
    (by omega) (by omega) (by rintro ⟨-, h⟩; omega))]
  exact Function.update_self _ _ _

theorem slotSignPt_val_sign (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (t : Fin 3) (w₀ : Fin (sat3M N - 2))
    (hwv : w₀.val < sat3V N) (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    slotSignPt N cIdx hk t w₀ hwv bvec b a (sat3Bit N cIdx t (sat3V N) (by omega)) = a := by
  unfold slotSignPt
  exact Function.update_self _ _ _

theorem slotSignPt_val_pin (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N) (t : Fin 3)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    slotSignPt N cIdx hk t w₀ hwv bvec b a
      (sat3Bit N (sat3PinClause N cIdx hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega))
    = decide (bvec w₀ = false) := by
  unfold slotSignPt
  rw [Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _
      (sat3PinClause_ne N cIdx hk w₀)),
    Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _
      (sat3PinClause_ne N cIdx hk w₀))]
  exact pin_read_sign N cIdx hk hkv bvec _ w₀

theorem slotSignPt_flip_sign (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (t : Fin 3) (w₀ : Fin (sat3M N - 2))
    (hwv : w₀.val < sat3V N) (bvec : Fin (sat3M N - 2) → Bool) (b a v : Bool) :
    Function.update (slotSignPt N cIdx hk t w₀ hwv bvec b a)
      (sat3Bit N cIdx t (sat3V N) (by omega)) v
    = slotSignPt N cIdx hk t w₀ hwv bvec b v := by
  unfold slotSignPt
  exact Function.update_idem _ _ _

theorem slotSignPt_flip_sel (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (t : Fin 3) (w₀ : Fin (sat3M N - 2))
    (hwv : w₀.val < sat3V N) (bvec : Fin (sat3M N - 2) → Bool) (b a v : Bool) :
    Function.update (slotSignPt N cIdx hk t w₀ hwv bvec b a)
      (sat3Bit N cIdx t w₀.val (by omega)) v
    = slotSignPt N cIdx hk t w₀ hwv bvec v a := by
  unfold slotSignPt
  rw [Function.update_comm (show sat3Bit N cIdx t (sat3V N) (by omega)
      ≠ sat3Bit N cIdx t w₀.val (by omega) from
    sat3Bit_ne_same_block N cIdx t t (sat3V N) w₀.val (by omega) (by omega)
      (by rintro ⟨-, h⟩; omega))]
  rw [Function.update_idem]

theorem slotSignPt_flip_pin (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N) (t : Fin 3)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b a v : Bool) :
    Function.update (slotSignPt N cIdx hk t w₀ hwv bvec b a)
      (sat3Bit N (sat3PinClause N cIdx hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega)) v
    = slotSignPt N cIdx hk t w₀ hwv (Function.update bvec w₀ (!v)) b a := by
  unfold slotSignPt
  rw [Function.update_comm (show sat3Bit N cIdx t (sat3V N) (by omega)
      ≠ sat3Bit N (sat3PinClause N cIdx hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega) from
    sat3Bit_ne_of_clause N _ _ _ _
      (fun h' => sat3PinClause_ne N cIdx hk w₀ h'.symm))]
  rw [Function.update_comm (show sat3Bit N cIdx t w₀.val (by omega)
      ≠ sat3Bit N (sat3PinClause N cIdx hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega) from
    sat3Bit_ne_of_clause N _ _ _ _
      (fun h' => sat3PinClause_ne N cIdx hk w₀ h'.symm))]
  rw [sat3Context_update_pin_sign N cIdx hk hkv bvec w₀ (fun _ => false) v]

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_slot_sign_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.slotSignPt_flip_pin
