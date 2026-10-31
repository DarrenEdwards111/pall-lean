import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSetFlipEngine

/-!
# N-Frame: pinned-selector patterns — the AND edge for the two-mass cut

The discovery from the set-flip file, produced.  The empty designated block with a single slot-2 selector
on **pinned** `j₀` evaluates to `sel ∧ bvec j₀` — pure AND in the axes (selector, pin-sign of `j₀`),
since the identification lemma turns the pin-sign flip into a `bvec` flip.

  `sat3_pinned_selector_eval` — **PROVED**: `f = b && bvec j₀`; the `b = true, bvec j₀ = false` corner is
        a forcing argument through pin `j₀`.
  `sat3_selector_pinsign_odd` — **PROVED**: engine-format odd square (`0, 0, 1, 0` from base `(1,0)`),
        pair `(s₁, t₁) = (sel, pinSign)`.
  `sat3_selector_pinsign_V0_selDown` / `sat3_selector_pinsign_V0_pinDown` — **PROVED**: engine-format
        unsat/unsat/sat L-triples in both orientations.

## Honest scope

With these, the two-mass cut (slot-2 selectors vs the sign layer) has separated pairs carrying odd + V1
(the sign↔selector OR pair) and V0 (this AND pair) — the mixed engine assembly that discharges the
two-mass branch of `Sat3MonolithicMassNoSplit` is the named next rung; slot-0/1 selectors and slot-1/2
signs remain after that.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE PINNED-SELECTOR EVAL (proved)**: empty designated block, slot-2 selector on pinned `j₀` —
`f = b && bvec j₀`. -/
theorem sat3_pinned_selector_eval (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2))
    (hjv : j₀.val < sat3V N) (bvec : Fin (sat3M N - 2) → Bool) (b : Bool) :
    sat3Family N (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
      (fun _ => false)) (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩) b)
    = (b && bvec j₀) := by
  classical
  set X : Fin N → Bool := Function.update (sat3Patch N cIdx
    (sat3Context N cIdx hk bvec) (fun _ => false))
    (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩) b with hX
  have hown0 : ∀ (t : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1),
      ¬(t.val = 2 ∧ fI = j₀.val) → X (sat3Bit N cIdx t fI hfI) = false := by
    intro t fI hfI hnot
    have hne : sat3Bit N cIdx t fI hfI ≠ sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ := by
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
        exact hnot ⟨rfl, by omega⟩
    rw [hX, Function.update_of_ne hne, sat3Patch_own N cIdx _ _ t fI hfI]
  have hs2j : X (sat3Bit N cIdx ⟨2, by omega⟩ j₀.val (by omega)) = b := by
    rw [hX]
    exact Function.update_self _ _ _
  have houtside : ∀ (cl : Fin (sat3M N)) (hcl : cl.val ≠ cIdx.val) (t : Fin 3)
      (fI : ℕ) (hfI : fI < sat3V N + 1),
      X (sat3Bit N cl t fI hfI)
        = sat3Patch N cIdx (sat3Context N cIdx hk bvec) (fun _ => false)
            (sat3Bit N cl t fI hfI) := by
    intro cl hcl t fI hfI
    rw [hX, Function.update_of_ne (sat3Bit_ne_s2sel_of_clause N cl cIdx hcl _ _ _ _)]
  cases hb : b with
  | false =>
    show sat3Family N X = (false && bvec j₀)
    rw [Bool.false_and]
    apply sat3Family_false_of_empty_clause N X cIdx
    intro t i
    by_cases hti : t.val = 2 ∧ i.val = j₀.val
    · rw [show sat3Bit N cIdx t i.val (by have := i.isLt; omega)
          = sat3Bit N cIdx ⟨2, by omega⟩ j₀.val (by omega) from by
        rcases hti with ⟨ht, hi⟩
        congr 1
        · exact Fin.ext ht]
      rw [hs2j, hb]
    · exact hown0 t i.val (by have := i.isLt; omega)
        (by rintro ⟨h1, h2⟩; exact hti ⟨h1, h2⟩)
  | true =>
    cases hbj : bvec j₀ with
    | true =>
      show sat3Family N X = (true && true)
      apply sat3Family_of_witness N X
        (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩ else true)
      apply sat3Eval_true_of_all
      intro cl
      by_cases hcl : cl = cIdx
      · subst hcl
        refine ⟨⟨2, by omega⟩, sat3Lit_true_of_selected N X _ cl ⟨2, by omega⟩
          ⟨j₀.val, hjv⟩ (by rw [hs2j, hb]) ?_⟩
        rw [hown0 ⟨2, by omega⟩ (sat3V N) (by omega) (by rintro ⟨-, h⟩; omega)]
        show xor (if h : j₀.val < sat3M N - 2 then bvec ⟨j₀.val, h⟩ else true)
            false = true
        rw [dif_pos j₀.isLt]
        have hb' : bvec ⟨j₀.val, j₀.isLt⟩ = true := hbj
        rw [hb']
        rfl
      · exact sat3_outside_probe_satisfied N hv hk hkv cIdx bvec
          (fun _ => false) cl (fun h => hcl (Fin.ext h)) X houtside
    | false =>
      show sat3Family N X = (true && false)
      apply decide_eq_false
      rintro ⟨A, hA⟩
      have hforce : A ⟨j₀.val, hjv⟩ = bvec j₀ := by
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
      · rw [sat3Lit_false_of_empty N X A cIdx _ (fun i =>
          hown0 ⟨0, by omega⟩ i.val (by have := i.isLt; omega)
            (by rintro ⟨h, -⟩; have h' : (0 : ℕ) = 2 := h; omega))] at ht
        cases ht
      · rw [sat3Lit_false_of_empty N X A cIdx _ (fun i =>
          hown0 ⟨1, by omega⟩ i.val (by have := i.isLt; omega)
            (by rintro ⟨h, -⟩; have h' : (1 : ℕ) = 2 := h; omega))] at ht
        cases ht
      · rw [sat3Lit_single N X A cIdx _ ⟨j₀.val, hjv⟩ (by rw [hs2j, hb])
          (fun i hi => hown0 ⟨2, by omega⟩ i.val (by have := i.isLt; omega)
            (by rintro ⟨-, h⟩; exact hi (Fin.ext h)))] at ht
        rw [hown0 ⟨2, by omega⟩ (sat3V N) (by omega) (by rintro ⟨-, h⟩; omega),
          hforce, hbj] at ht
        cases ht

/-- The pinned-selector corner point. -/
def pinnedPt (N : ℕ) (cIdx : Fin (sat3M N)) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b : Bool) : Fin N → Bool :=
  Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec) (fun _ => false))
    (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩) b

theorem pinnedPt_eval (N : ℕ) (hv : 1 ≤ sat3V N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hkv : sat3M N - 2 ≤ sat3V N) (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N))
    (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b : Bool) :
    sat3Family N (pinnedPt N cIdx hk j₀ hjv bvec b) = (b && bvec j₀) := by
  unfold pinnedPt
  exact sat3_pinned_selector_eval N hv hk hkv hm3 cIdx j₀ hjv bvec b

theorem pinnedPt_val_sel (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (j₀ : Fin (sat3M N - 2))
    (hjv : j₀.val < sat3V N) (bvec : Fin (sat3M N - 2) → Bool) (b : Bool) :
    pinnedPt N cIdx hk j₀ hjv bvec b (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩) = b := by
  unfold pinnedPt
  exact Function.update_self _ _ _

theorem pinnedPt_val_pin (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b : Bool) :
    pinnedPt N cIdx hk j₀ hjv bvec b
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
    = decide (bvec j₀ = false) := by
  unfold pinnedPt
  rw [Function.update_of_ne (sat3Bit_ne_s2sel_of_clause N
    (sat3PinClause N cIdx hk j₀) cIdx (sat3PinClause_ne N cIdx hk j₀) _ _ _ _)]
  exact pin_read_sign N cIdx hk hkv bvec _ j₀

theorem pinnedPt_flip_sel (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (j₀ : Fin (sat3M N - 2))
    (hjv : j₀.val < sat3V N) (bvec : Fin (sat3M N - 2) → Bool) (b v : Bool) :
    Function.update (pinnedPt N cIdx hk j₀ hjv bvec b)
      (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩) v = pinnedPt N cIdx hk j₀ hjv bvec v := by
  unfold pinnedPt
  exact Function.update_idem _ _ _

theorem pinnedPt_flip_pin (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b v : Bool) :
    Function.update (pinnedPt N cIdx hk j₀ hjv bvec b)
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega)) v
    = pinnedPt N cIdx hk j₀ hjv (Function.update bvec j₀ (!v)) b := by
  unfold pinnedPt
  rw [Function.update_comm (show sat3S2Sel N cIdx ⟨j₀.val, hjv⟩
      ≠ sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega) from
    (sat3Bit_ne_s2sel_of_clause N (sat3PinClause N cIdx hk j₀) cIdx
      (sat3PinClause_ne N cIdx hk j₀) _ _ _ ⟨j₀.val, hjv⟩).symm)]
  rw [sat3Context_update_pin_sign N cIdx hk hkv bvec j₀ (fun _ => false) v]

/-- **ODD SQUARE (proved)**: pair `(s₁, t₁) = (sel, pinSign)`, corners `0, 0, 1, 0` from base `(1,0)`. -/
theorem sat3_selector_pinsign_odd (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2))
    (hjv : j₀.val < sat3V N) :
    xor (xor (sat3Family N (pinnedPt N cIdx hk j₀ hjv (fun _ => false) true))
        (sat3Family N (Function.update (pinnedPt N cIdx hk j₀ hjv (fun _ => false) true)
          (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
          (!(pinnedPt N cIdx hk j₀ hjv (fun _ => false) true
            (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩))))))
      (xor (sat3Family N (Function.update (pinnedPt N cIdx hk j₀ hjv (fun _ => false) true)
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (!(pinnedPt N cIdx hk j₀ hjv (fun _ => false) true
            (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
              (by omega))))))
        (sat3Family N (Function.update (Function.update
          (pinnedPt N cIdx hk j₀ hjv (fun _ => false) true)
          (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
          (!(pinnedPt N cIdx hk j₀ hjv (fun _ => false) true
            (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩))))
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (!(pinnedPt N cIdx hk j₀ hjv (fun _ => false) true
            (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
              (by omega))))))) = true := by
  rw [pinnedPt_val_sel N cIdx hk j₀ hjv, pinnedPt_val_pin N cIdx hk hkv j₀ hjv]
  rw [pinnedPt_flip_sel N cIdx hk j₀ hjv, pinnedPt_flip_pin N cIdx hk hkv j₀ hjv,
    pinnedPt_flip_pin N cIdx hk hkv j₀ hjv]
  rw [pinnedPt_eval N hv hk hkv hm3 cIdx j₀ hjv,
    pinnedPt_eval N hv hk hkv hm3 cIdx j₀ hjv,
    pinnedPt_eval N hv hk hkv hm3 cIdx j₀ hjv,
    pinnedPt_eval N hv hk hkv hm3 cIdx j₀ hjv]
  rw [Function.update_self]
  rfl

/-- **V0, selector down (proved)**: `(s₃, t₃) = (sel, pinSign)`, base `(1, 0)`. -/
theorem sat3_selector_pinsign_V0_selDown (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2))
    (hjv : j₀.val < sat3V N) :
    sat3Family N (pinnedPt N cIdx hk j₀ hjv (fun _ => false) true) = false ∧
    sat3Family N (Function.update (Function.update
        (pinnedPt N cIdx hk j₀ hjv (fun _ => false) true)
        (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
        (!(pinnedPt N cIdx hk j₀ hjv (fun _ => false) true
          (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩))))
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
      (!(pinnedPt N cIdx hk j₀ hjv (fun _ => false) true
        (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
          (by omega))))) = false ∧
    sat3Family N (Function.update (pinnedPt N cIdx hk j₀ hjv (fun _ => false) true)
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
      (!(pinnedPt N cIdx hk j₀ hjv (fun _ => false) true
        (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
          (by omega))))) = true := by
  rw [pinnedPt_val_sel N cIdx hk j₀ hjv, pinnedPt_val_pin N cIdx hk hkv j₀ hjv]
  rw [pinnedPt_flip_sel N cIdx hk j₀ hjv, pinnedPt_flip_pin N cIdx hk hkv j₀ hjv,
    pinnedPt_flip_pin N cIdx hk hkv j₀ hjv]
  rw [pinnedPt_eval N hv hk hkv hm3 cIdx j₀ hjv,
    pinnedPt_eval N hv hk hkv hm3 cIdx j₀ hjv,
    pinnedPt_eval N hv hk hkv hm3 cIdx j₀ hjv]
  rw [Function.update_self]
  exact ⟨rfl, rfl, rfl⟩

/-- **V0, pin down (proved)**: `(s₃, t₃) = (pinSign, sel)`, base `(0, 1)` at the all-true context. -/
theorem sat3_selector_pinsign_V0_pinDown (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2))
    (hjv : j₀.val < sat3V N) :
    sat3Family N (pinnedPt N cIdx hk j₀ hjv (fun _ => true) false) = false ∧
    sat3Family N (Function.update (Function.update
        (pinnedPt N cIdx hk j₀ hjv (fun _ => true) false)
        (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
        (!(pinnedPt N cIdx hk j₀ hjv (fun _ => true) false
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
            (by omega)))))
      (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
      (!(pinnedPt N cIdx hk j₀ hjv (fun _ => true) false
        (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)))) = false ∧
    sat3Family N (Function.update (pinnedPt N cIdx hk j₀ hjv (fun _ => true) false)
      (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
      (!(pinnedPt N cIdx hk j₀ hjv (fun _ => true) false
        (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)))) = true := by
  rw [pinnedPt_val_sel N cIdx hk j₀ hjv, pinnedPt_val_pin N cIdx hk hkv j₀ hjv]
  rw [pinnedPt_flip_pin N cIdx hk hkv j₀ hjv, pinnedPt_flip_sel N cIdx hk j₀ hjv,
    pinnedPt_flip_sel N cIdx hk j₀ hjv]
  rw [pinnedPt_eval N hv hk hkv hm3 cIdx j₀ hjv,
    pinnedPt_eval N hv hk hkv hm3 cIdx j₀ hjv,
    pinnedPt_eval N hv hk hkv hm3 cIdx j₀ hjv]
  rw [Function.update_self]
  exact ⟨rfl, rfl, rfl⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_pinned_selector_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_pinsign_odd
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_pinsign_V0_selDown
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_pinsign_V0_pinDown
