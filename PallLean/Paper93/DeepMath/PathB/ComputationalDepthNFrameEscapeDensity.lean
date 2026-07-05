import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSelectorEscapeCounting

/-!
# N-Frame: escape density — the opposite side owns no full block

The row-capacity machinery re-enters, at its honest strength.  A first-choice formulation —
"a block inside one exclusive side forces a large interface" — is **false** (`B = ∅`, `h` junk,
`g = f` is a legitimate factorization).  What the row family actually proves is a **propagation**
law: block ownership drags the block's *pin signs* to the same side.

  `sat3Context_agree` — **PROVED, the support lemma**: pin contexts agree at every coordinate except
        the pin-sign bits of differing `bvec` entries (`bvec` enters `sat3Context` only under the
        pin-sign guard).
  `sat3_pin_propagation_left/right` — **PROVED, the row-capacity re-entry**: if block `c` lies
        inside `A \ B`, then at most `|A ∩ B| + 1` of its pins have sign bits outside `A \ B` —
        the pin contexts supported on the offside pins give `2^{#offside}` pairwise-distinct rows
        over `A \ B`, and `shared_split_row_capacity` caps them.
  `sat3_no_opposite_block_left/right` — **PROVED, the fusion with alignment**: in the sign-aligned
        branch, the opposite exclusive side can own **no full block** — ownership would propagate
        `m − 3 − |A ∩ B|` pin signs onto the opposite side, where alignment forbids every one of
        them; so `m ≤ |A ∩ B| + 3`.
  `sat3_opposite_block_scattered` — **PROVED, the assembly**: any interfaced factorization of
        `sat3Family`: signs aligned left and the right side owns no full block, or the mirror, or
        `m ≤ |A ∩ B| + 4`.  **With a small interface, the side opposite the signs is scattered
        below block granularity** — it can hold fragments only.

## Honest scope

Named, not claimed: (1) pushing scatteredness below block granularity — sub-block row families
(the offside-pin bound applies to *partial* ownership too, via the same context machinery) toward
`GlobalPACInterfaceBound`; (2) slot-0/1 selector and slot-probe families; (3) the wire-frontier →
coordinate-interface extraction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE SUPPORT LEMMA (proved)**: `bvec` enters the pin context only at pin-sign bits. -/
theorem sat3Context_agree (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (b b' : Fin k → Bool) (i : Fin N)
    (hag : ∀ j : Fin k, i.val / sat3D N = (sat3PinClause N c hk j).val →
      i.val % sat3D N = sat3V N → b j = b' j) :
    sat3Context N c hk b i = sat3Context N c hk b' i := by
  show decide _ = decide _
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨j, hj1, hj2 | ⟨hj2, hj3⟩⟩ | hother)
    · exact Or.inl ⟨j, hj1, Or.inl hj2⟩
    · exact Or.inl ⟨j, hj1, Or.inr ⟨hj2, by rw [← hag j hj1 hj2]; exact hj3⟩⟩
    · exact Or.inr hother
  · rintro (⟨j, hj1, hj2 | ⟨hj2, hj3⟩⟩ | hother)
    · exact Or.inl ⟨j, hj1, Or.inl hj2⟩
    · exact Or.inl ⟨j, hj1, Or.inr ⟨hj2, by rw [hag j hj1 hj2]; exact hj3⟩⟩
    · exact Or.inr hother

/-- **PIN PROPAGATION, LEFT (proved)**: a block inside `A \ B` has at most `|A ∩ B| + 1` pins with
sign bits outside `A \ B`. -/
theorem sat3_pin_propagation_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (hsub : blockCoords N c ⊆ A \ B) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ A \ B)).card ≤ (A ∩ B).card + 1 := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set Jf := (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
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
    obtain ⟨uu, huu⟩ :=
      sat3_block_subfunctions_distinct N hv hk hkv c (e bb) (e bb') hbne
    -- contexts agree on all of A \ B: differing entries live on offside pins
    have hagree : ∀ i : Fin N, i ∈ A \ B →
        sat3Context N c hk (e bb) i = sat3Context N c hk (e bb') i := by
      intro i hi
      apply sat3Context_agree
      intro j hj1 hj2
      by_cases hmem : j ∈ Jf
      · exfalso
        have hπ : sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
            (by omega) ∉ A \ B := by
          have := Finset.mem_filter.mp (hJf ▸ hmem)
          exact this.2
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
        rw [if_neg (fun hdiv => hi (hsub (show i ∈ blockCoords N c from
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hdiv⟩)))]
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
        rw [if_neg (fun hdiv => hi (hsub (show i ∈ blockCoords N c from
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hdiv⟩)))]
    rw [hmix1, hmix2]
    exact huu
  have hcap := shared_split_row_capacity (sat3Family N) A B op g h hg hh hf Y hdist
  rw [hYcard] at hcap
  by_contra hcon
  push_neg at hcon
  have hlt : (2 : ℕ) ^ ((A ∩ B).card + 1) < 2 ^ Jf.card :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- **PIN PROPAGATION, RIGHT (proved)**: the mirror, by swapping the factor roles. -/
theorem sat3_pin_propagation_right (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (hsub : blockCoords N c ⊆ B \ A) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ B \ A)).card ≤ (A ∩ B).card + 1 := by
  have hswap := sat3_pin_propagation_left N hv hk (fun a b => op b a) h g B A
    hh hg hf c hsub
  have hint : (B ∩ A).card = (A ∩ B).card := by
    rw [Finset.inter_comm]
  omega

/-- **NO OPPOSITE BLOCK, LEFT-ALIGNED (proved)**: signs aligned in `A \ B` ⇒ the right side owns no
full block unless `m ≤ |A ∩ B| + 3` — ownership would propagate `m − 3 − |A ∩ B|` pin signs into
`B \ A`, where alignment forbids each one. -/
theorem sat3_no_opposite_block_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (haligned : ∀ c' : Fin (sat3M N), sat3SignBit N c' ∉ A ∩ B →
      sat3SignBit N c' ∈ A \ B)
    (c : Fin (sat3M N)) (hsub : blockCoords N c ⊆ B \ A) :
    sat3M N ≤ (A ∩ B).card + 3 := by
  classical
  have hprop := sat3_pin_propagation_right N hv hk op g h A B hg hh hf c hsub
  -- alignment forbids every pin sign from lying in B \ A: the offside filter is everything
  have hall : ∀ j : Fin (sat3M N - 2),
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ B \ A := by
    intro j hmem
    have h1 : sat3SignBit N (sat3PinClause N c hk j) ∉ A ∩ B :=
      fun hW => (Finset.mem_sdiff.mp hmem).2 (Finset.mem_inter.mp hW).1
    have h2 := haligned (sat3PinClause N c hk j) h1
    exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_sdiff.mp h2).1
  have hfull : sat3M N - 2
      ≤ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
        sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
          (by omega) ∉ B \ A)).card := by
    calc sat3M N - 2 = (Finset.univ : Finset (Fin (sat3M N - 2))).card := by
          rw [Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card
          (fun j hj => Finset.mem_filter.mpr ⟨hj, hall j⟩)
  omega

/-- **NO OPPOSITE BLOCK, RIGHT-ALIGNED (proved)**: the mirror. -/
theorem sat3_no_opposite_block_right (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (haligned : ∀ c' : Fin (sat3M N), sat3SignBit N c' ∉ A ∩ B →
      sat3SignBit N c' ∈ B \ A)
    (c : Fin (sat3M N)) (hsub : blockCoords N c ⊆ A \ B) :
    sat3M N ≤ (A ∩ B).card + 3 := by
  classical
  have hprop := sat3_pin_propagation_left N hv hk op g h A B hg hh hf c hsub
  have hall : ∀ j : Fin (sat3M N - 2),
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ A \ B := by
    intro j hmem
    have h1 : sat3SignBit N (sat3PinClause N c hk j) ∉ A ∩ B :=
      fun hW => (Finset.mem_sdiff.mp hmem).2 (Finset.mem_inter.mp hW).2
    have h2 := haligned (sat3PinClause N c hk j) h1
    exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_sdiff.mp h2).1
  have hfull : sat3M N - 2
      ≤ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
        sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
          (by omega) ∉ A \ B)).card := by
    calc sat3M N - 2 = (Finset.univ : Finset (Fin (sat3M N - 2))).card := by
          rw [Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card
          (fun j hj => Finset.mem_filter.mpr ⟨hj, hall j⟩)
  omega

/-- **THE SCATTERING ASSEMBLY (proved)**: any interfaced factorization of `sat3Family`: signs
aligned left and the right side owns no full block, or the mirror, or `m ≤ |A ∩ B| + 4`. -/
theorem sat3_opposite_block_scattered (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x)) :
    ((∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B → sat3SignBit N c ∈ A \ B) ∧
      ∀ c : Fin (sat3M N), ¬ (blockCoords N c ⊆ B \ A)) ∨
    ((∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B → sat3SignBit N c ∈ B \ A) ∧
      ∀ c : Fin (sat3M N), ¬ (blockCoords N c ⊆ A \ B)) ∨
    sat3M N ≤ (A ∩ B).card + 4 := by
  classical
  by_cases hbig : sat3M N ≤ (A ∩ B).card + 4
  · exact Or.inr (Or.inr hbig)
  · rcases sat3_sign_alignment_or_interface N hv hm3 hk op g h A B hg hh hf
      with hL | hR | hC
    · refine Or.inl ⟨hL, fun c hsub => ?_⟩
      have := sat3_no_opposite_block_left N hv hk op g h A B hg hh hf hL c hsub
      omega
    · refine Or.inr (Or.inl ⟨hR, fun c hsub => ?_⟩)
      have := sat3_no_opposite_block_right N hv hk op g h A B hg hh hf hR c hsub
      omega
    · exact absurd (by omega : sat3M N ≤ (A ∩ B).card + 4) hbig

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_pin_propagation_left
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_no_opposite_block_left
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_opposite_block_scattered
