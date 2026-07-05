import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFreeAnchorMenu

/-!
# N-Frame: slot-`t` one-bit propagation — the per-block escape bound at every slot

`GlobalPACInterfaceBound` gap (2).  The slot-0 one-bit law generalizes to every slot with **no new
probe eval**: `slotSignPt` at `(b, a) = (true, false)` *is* the slot-`t` one-bit probe — the sign
update writes `false` onto an already-false base, so the live set is the single slot-`t` selector
bit, and `slotSignPt_eval` gives the pin-reading closed form `true && xor (bvec w₀) false = bvec w₀`.

  `sat3_slotT_pin_propagation_left/right` — **PROVED, the one-bit law at every slot**: with no
        hypothesis on any sign bit, among pins `j` whose slot-`t` selector `(c, j)` lies in one
        exclusive side, at most `|A ∩ B| + 1` have their pin sign outside that side.
  `sat3_slotT_escape_bound_left/right` — **PROVED**: in the sign-aligned branch, every block —
        corrupted or not — has at most `|A ∩ B| + 1` slot-`t` pinned selectors on the opposite side,
        for **each** slot `t`; so at most `3(|A ∩ B| + 1)` pinned selectors escape per block in
        total.

## Honest scope

Remaining `GlobalPACInterfaceBound` gap: the final case-count over escapee classes — its per-class
inputs are now all at `Ω(m)` strength.  Then the wire-frontier → coordinate-interface extraction.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The tiny Bool core, kept out of the big context. -/
theorem and_xor_false_inj (x y : Bool)
    (h : (true && xor x false) = (true && xor y false)) : x = y := by
  cases x <;> cases y <;> simp_all

set_option maxHeartbeats 1600000 in
/-- **THE SLOT-`t` ONE-BIT PROPAGATION, LEFT (proved)**: no sign hypothesis — among pins whose
slot-`t` selector lies in `A \ B`, at most `|A ∩ B| + 1` have their pin sign outside `A \ B`. -/
theorem sat3_slotT_pin_propagation_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (t : Fin 3) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A \ B ∧
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ A \ B)).card ≤ (A ∩ B).card + 1 := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set Jf := (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
    sat3Bit N c t j.val
      (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A \ B ∧
    sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
      (by omega) ∉ A \ B) with hJf
  set e : (↥Jf → Bool) → (Fin (sat3M N - 2) → Bool) :=
    fun bb j => if hmem : j ∈ Jf then bb ⟨j, hmem⟩ else false with he
  have heval : ∀ (bb : ↥Jf → Bool) (w : ↥Jf), e bb w.val = bb w := by
    intro bb w
    show (if hmem : w.val ∈ Jf then bb ⟨w.val, hmem⟩ else false) = bb w
    rw [dif_pos w.prop, Subtype.coe_eta]
  have heinj : Function.Injective e := by
    intro bb bb' heq
    funext w
    rw [← heval bb w, ← heval bb' w, heq]
  set Y : Finset (Fin N → Bool) :=
    Finset.univ.image (fun bb : ↥Jf → Bool => sat3Context N c hk (e bb)) with hY
  have hYcard : Y.card = 2 ^ Jf.card := by
    rw [hY, Finset.card_image_of_injective _
        (fun bb bb' heq => heinj (sat3Context_injective N hv hk hkv c heq)),
      Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_bool]
  have hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, sat3Family N (mixOn (A \ B) x y)
        ≠ sat3Family N (mixOn (A \ B) x y') := by
    intro y hy y' hy' hne
    rw [hY] at hy hy'
    obtain ⟨bb, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨bb', -, rfl⟩ := Finset.mem_image.mp hy'
    have hbne : e bb ≠ e bb' := fun hh' => hne (by rw [hh'])
    obtain ⟨j₀, hj₀ne⟩ := Function.ne_iff.mp hbne
    have hj₀J : j₀ ∈ Jf := by
      by_contra hmem
      apply hj₀ne
      show (if hm : j₀ ∈ Jf then bb ⟨j₀, hm⟩ else false)
        = (if hm : j₀ ∈ Jf then bb' ⟨j₀, hm⟩ else false)
      rw [dif_neg hmem, dif_neg hmem]
    have hj₀mem := Finset.mem_filter.mp (hJf ▸ hj₀J)
    have hselJ := hj₀mem.2.1
    have hjv : j₀.val < sat3V N := by
      have := j₀.isLt
      omega
    set uu : Fin N → Bool :=
      fun bit => decide (bit = sat3Bit N c t j₀.val (by omega)) with huudef
    -- the indicator patch IS the slot-t one-bit probe point
    have hpteq : ∀ bv : Fin (sat3M N - 2) → Bool,
        sat3Patch N c (sat3Context N c hk bv) uu
          = slotSignPt N c hk t j₀ hjv bv true false := by
      intro bv
      funext i
      rw [huudef]
      unfold slotSignPt
      by_cases hsig : i = sat3Bit N c t (sat3V N) (by omega)
      · rw [hsig, Function.update_self]
        show (if (sat3Bit N c t (sat3V N) (by omega)).val / sat3D N = c.val
          then decide (sat3Bit N c t (sat3V N) (by omega)
            = sat3Bit N c t j₀.val (by omega))
          else sat3Context N c hk bv (sat3Bit N c t (sat3V N) (by omega)))
          = false
        rw [if_pos (sat3Bit_div N c t (sat3V N) (by omega))]
        exact decide_eq_false (sat3Bit_ne_same_block N c t t (sat3V N) j₀.val
          (by omega) (by omega) (by rintro ⟨-, h'⟩; omega))
      · rw [Function.update_of_ne hsig]
        by_cases hsel : i = sat3Bit N c t j₀.val (by omega)
        · rw [hsel, Function.update_self]
          show (if (sat3Bit N c t j₀.val (by omega)).val / sat3D N = c.val
            then decide (sat3Bit N c t j₀.val (by omega)
              = sat3Bit N c t j₀.val (by omega))
            else sat3Context N c hk bv (sat3Bit N c t j₀.val (by omega)))
            = true
          rw [if_pos (sat3Bit_div N c t j₀.val (by omega))]
          exact decide_eq_true rfl
        · rw [Function.update_of_ne hsel]
          show (if i.val / sat3D N = c.val
            then decide (i = sat3Bit N c t j₀.val (by omega))
            else sat3Context N c hk bv i)
            = (if i.val / sat3D N = c.val then (fun _ => false) i
              else sat3Context N c hk bv i)
          by_cases hdiv : i.val / sat3D N = c.val
          · rw [if_pos hdiv, if_pos hdiv]
            exact decide_eq_false hsel
          · rw [if_neg hdiv, if_neg hdiv]
    -- distinctness: the slot-t probe reads the pin apart
    have huu : sat3Family N (sat3Patch N c (sat3Context N c hk (e bb)) uu)
        ≠ sat3Family N (sat3Patch N c (sat3Context N c hk (e bb')) uu) := by
      rw [hpteq (e bb), hpteq (e bb'),
        slotSignPt_eval N hv hk hkv hm3 c t j₀ hjv (e bb) true false,
        slotSignPt_eval N hv hk hkv hm3 c t j₀ hjv (e bb') true false]
      intro heq
      exact hj₀ne (and_xor_false_inj _ _ heq)
    -- the indicator vanishes everywhere in the block except the owned selector
    have hprobe0 : ∀ i : Fin N, i.val / sat3D N = c.val → i ∉ A \ B →
        uu i = false := by
      intro i hdiv hi
      rw [huudef]
      show decide _ = false
      rw [decide_eq_false_iff_not]
      intro hcon
      apply hi
      rw [hcon]
      exact hselJ
    have hagree : ∀ i : Fin N, i ∈ A \ B →
        sat3Context N c hk (e bb) i = sat3Context N c hk (e bb') i := by
      intro i hi
      apply sat3Context_agree
      intro j hj1 hj2
      by_cases hmem : j ∈ Jf
      · exfalso
        have hπ := (Finset.mem_filter.mp (hJf ▸ hmem)).2.2
        apply hπ
        have hiπ : sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
            (by omega) = i := by
          apply Fin.ext
          show (sat3PinClause N c hk j).val * sat3D N + 0 * (sat3V N + 1)
            + sat3V N = i.val
          have hdm := Nat.div_add_mod i.val (sat3D N)
          rw [hj1, hj2] at hdm
          have hcm : sat3D N * (sat3PinClause N c hk j).val
              = (sat3PinClause N c hk j).val * sat3D N := Nat.mul_comm _ _
          omega
        rw [hiπ]
        exact hi
      · show (if hm : j ∈ Jf then bb ⟨j, hm⟩ else false)
          = (if hm : j ∈ Jf then bb' ⟨j, hm⟩ else false)
        rw [dif_neg hmem, dif_neg hmem]
    refine ⟨sat3Patch N c (sat3Context N c hk (e bb)) uu, ?_⟩
    have hmix1 : mixOn (A \ B) (sat3Patch N c (sat3Context N c hk (e bb)) uu)
        (sat3Context N c hk (e bb))
        = sat3Patch N c (sat3Context N c hk (e bb)) uu := by
      funext i
      show (if i ∈ A \ B then sat3Patch N c (sat3Context N c hk (e bb)) uu i
        else sat3Context N c hk (e bb) i)
        = sat3Patch N c (sat3Context N c hk (e bb)) uu i
      by_cases hi : i ∈ A \ B
      · rw [if_pos hi]
      · rw [if_neg hi]
        show sat3Context N c hk (e bb) i
          = (if i.val / sat3D N = c.val then uu i else sat3Context N c hk (e bb) i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, sat3Context_designated N c hk (e bb) i hdiv,
            hprobe0 i hdiv hi]
        · rw [if_neg hdiv]
    have hmix2 : mixOn (A \ B) (sat3Patch N c (sat3Context N c hk (e bb)) uu)
        (sat3Context N c hk (e bb'))
        = sat3Patch N c (sat3Context N c hk (e bb')) uu := by
      funext i
      show (if i ∈ A \ B then sat3Patch N c (sat3Context N c hk (e bb)) uu i
        else sat3Context N c hk (e bb') i)
        = sat3Patch N c (sat3Context N c hk (e bb')) uu i
      by_cases hi : i ∈ A \ B
      · rw [if_pos hi]
        show (if i.val / sat3D N = c.val then uu i else sat3Context N c hk (e bb) i)
          = (if i.val / sat3D N = c.val then uu i else sat3Context N c hk (e bb') i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, if_pos hdiv]
        · rw [if_neg hdiv, if_neg hdiv]
          exact hagree i hi
      · rw [if_neg hi]
        show sat3Context N c hk (e bb') i
          = (if i.val / sat3D N = c.val then uu i else sat3Context N c hk (e bb') i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, sat3Context_designated N c hk (e bb') i hdiv,
            hprobe0 i hdiv hi]
        · rw [if_neg hdiv]
    rw [hmix1, hmix2]
    exact huu
  have hcap := shared_split_row_capacity (sat3Family N) A B op g h hg hh hf Y hdist
  rw [hYcard] at hcap
  by_contra hcon
  push_neg at hcon
  have hlt : (2 : ℕ) ^ ((A ∩ B).card + 1) < 2 ^ Jf.card :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- **THE SLOT-`t` ONE-BIT PROPAGATION, RIGHT (proved)**: the mirror. -/
theorem sat3_slotT_pin_propagation_right (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (t : Fin 3) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ B \ A ∧
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ B \ A)).card ≤ (A ∩ B).card + 1 := by
  have hswap := sat3_slotT_pin_propagation_left N hv hm3 hk (fun x y => op y x)
    h g B A hh hg hf c t
  have hint : (B ∩ A).card = (A ∩ B).card := by
    rw [Finset.inter_comm]
  omega

/-- **THE PER-BLOCK ESCAPE BOUND AT EVERY SLOT, LEFT-ALIGNED (proved)**. -/
theorem sat3_slotT_escape_bound_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (haligned : ∀ c' : Fin (sat3M N), sat3SignBit N c' ∉ A ∩ B →
      sat3SignBit N c' ∈ A \ B)
    (c : Fin (sat3M N)) (t : Fin 3) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ B \ A)).card
      ≤ (A ∩ B).card + 1 := by
  classical
  have hprop := sat3_slotT_pin_propagation_right N hv hm3 hk op g h A B
    hg hh hf c t
  have hsub : (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ B \ A)
      ⊆ (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ B \ A ∧
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ B \ A) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨hj.1, hj.2, ?_⟩
    intro hmem
    have h1 : sat3SignBit N (sat3PinClause N c hk j) ∉ A ∩ B :=
      fun hW => (Finset.mem_sdiff.mp hmem).2 (Finset.mem_inter.mp hW).1
    have h2 := haligned (sat3PinClause N c hk j) h1
    exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_sdiff.mp h2).1
  calc ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ B \ A)).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ (A ∩ B).card + 1 := hprop

/-- **THE PER-BLOCK ESCAPE BOUND AT EVERY SLOT, RIGHT-ALIGNED (proved)**: the mirror. -/
theorem sat3_slotT_escape_bound_right (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (haligned : ∀ c' : Fin (sat3M N), sat3SignBit N c' ∉ A ∩ B →
      sat3SignBit N c' ∈ B \ A)
    (c : Fin (sat3M N)) (t : Fin 3) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A \ B)).card
      ≤ (A ∩ B).card + 1 := by
  classical
  have hprop := sat3_slotT_pin_propagation_left N hv hm3 hk op g h A B
    hg hh hf c t
  have hsub : (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A \ B)
      ⊆ (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A \ B ∧
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ A \ B) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨hj.1, hj.2, ?_⟩
    intro hmem
    have h1 : sat3SignBit N (sat3PinClause N c hk j) ∉ A ∩ B :=
      fun hW => (Finset.mem_sdiff.mp hmem).2 (Finset.mem_inter.mp hW).2
    have h2 := haligned (sat3PinClause N c hk j) h1
    exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_sdiff.mp h2).1
  calc ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c t j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A \ B)).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ (A ∩ B).card + 1 := hprop

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_slotT_pin_propagation_left
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_slotT_escape_bound_left
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_slotT_escape_bound_right
