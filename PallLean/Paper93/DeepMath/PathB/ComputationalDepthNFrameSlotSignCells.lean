import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameAllSlotSelectorCapture

/-!
# N-Frame: slot-sign cells — odd + V0 producers and the interfaced dodge for slot-`t` signs

The slot-1/2 sign class enters the interfaced-cut regime.  The slot-sign corner point
(`slotSignPt`, eval `f = b && xor (bvec w₀) a`) is an **AND pair** at every slot: over the
(slot-`t` selector `w₀`, slot-`t` sign) axes with `bvec ≡ false` the table is `b && a` — carrying an
odd square and a V0 triple in both orientations, and **no V1** (one satisfied corner).

  `sat3_slot_sign_odd` / `sat3_slot_sign_odd'` — **PROVED**: engine-format odd squares on the
        (selector, sign) pair, both orientations, any slot `t`.
  `sat3_slot_sign_V0_selDown` / `sat3_slot_sign_V0_signDown` — **PROVED**: engine-format V0 triples,
        both orientations.
  `sat3_slot_sign_dodge` — **PROVED, the interfaced constraint**: no interfaced factorization of
        `sat3Family` admits a crossing (slot-`t` selector, slot-`t` sign) pair together with a
        crossing same-block selector pair (the V1 source) — all four orientation combinations, any
        interface.  Slot-1/2 signs are now cell-constrained.

## Honest scope

This is the dodge, not capture.  Sign **capture** in the aligned branch needs a V1 triple carried by
a pair *containing the sign bit itself* — a **cross-slot OR workhorse** (slot-`t'` selector axis
against a slot-`t` pinned literal's sign axis, eval `f = b ∨ xor (w, a)`, whose satisfied corners
support V1) — a genuinely new eval construction in the style of `sat3_mixed_literal_eval`.  Named,
not claimed.  Also still open: `GlobalPACInterfaceBound` assembly and the wire-frontier →
coordinate-interface extraction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **ODD SQUARE, (sel, sign) orientation (proved)**: base `(0,0)`, table `b && a`. -/
theorem sat3_slot_sign_odd (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t : Fin 3)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) :
    xor (xor (sat3Family N (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false))
        (sat3Family N (Function.update
          (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false)
          (sat3Bit N cIdx t w₀.val (by omega))
          (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t w₀.val (by omega)))))))
      (xor (sat3Family N (Function.update
          (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false)
          (sat3Bit N cIdx t (sat3V N) (by omega))
          (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t (sat3V N) (by omega))))))
        (sat3Family N (Function.update (Function.update
          (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false)
          (sat3Bit N cIdx t w₀.val (by omega))
          (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t w₀.val (by omega)))))
          (sat3Bit N cIdx t (sat3V N) (by omega))
          (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t (sat3V N) (by omega))))))) = true := by
  rw [slotSignPt_val_sel N cIdx hk t w₀ hwv, slotSignPt_val_sign N cIdx hk t w₀ hwv]
  rw [slotSignPt_flip_sel N cIdx hk t w₀ hwv]
  rw [slotSignPt_flip_sign N cIdx hk t w₀ hwv, slotSignPt_flip_sign N cIdx hk t w₀ hwv]
  rw [slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv,
    slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv,
    slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv,
    slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv]
  rfl

/-- **ODD SQUARE, (sign, sel) orientation (proved)**: the mirror update order. -/
theorem sat3_slot_sign_odd' (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t : Fin 3)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) :
    xor (xor (sat3Family N (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false))
        (sat3Family N (Function.update
          (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false)
          (sat3Bit N cIdx t (sat3V N) (by omega))
          (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t (sat3V N) (by omega)))))))
      (xor (sat3Family N (Function.update
          (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false)
          (sat3Bit N cIdx t w₀.val (by omega))
          (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t w₀.val (by omega))))))
        (sat3Family N (Function.update (Function.update
          (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false)
          (sat3Bit N cIdx t (sat3V N) (by omega))
          (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t (sat3V N) (by omega)))))
          (sat3Bit N cIdx t w₀.val (by omega))
          (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t w₀.val (by omega))))))) = true := by
  rw [slotSignPt_val_sel N cIdx hk t w₀ hwv, slotSignPt_val_sign N cIdx hk t w₀ hwv]
  rw [slotSignPt_flip_sign N cIdx hk t w₀ hwv]
  rw [slotSignPt_flip_sel N cIdx hk t w₀ hwv, slotSignPt_flip_sel N cIdx hk t w₀ hwv]
  rw [slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv,
    slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv,
    slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv,
    slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv]
  rfl

/-- **V0, selector down (proved)**: `(s₃, t₃) = (sel, sign)`, base `(1, 0)`. -/
theorem sat3_slot_sign_V0_selDown (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t : Fin 3)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) :
    sat3Family N (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) true false) = false ∧
    sat3Family N (Function.update (Function.update
        (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) true false)
        (sat3Bit N cIdx t w₀.val (by omega))
        (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) true false
          (sat3Bit N cIdx t w₀.val (by omega)))))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) true false
        (sat3Bit N cIdx t (sat3V N) (by omega))))) = false ∧
    sat3Family N (Function.update
        (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) true false)
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) true false
        (sat3Bit N cIdx t (sat3V N) (by omega))))) = true := by
  rw [slotSignPt_val_sel N cIdx hk t w₀ hwv, slotSignPt_val_sign N cIdx hk t w₀ hwv]
  rw [slotSignPt_flip_sel N cIdx hk t w₀ hwv]
  rw [slotSignPt_flip_sign N cIdx hk t w₀ hwv, slotSignPt_flip_sign N cIdx hk t w₀ hwv]
  rw [slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv,
    slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv,
    slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv]
  exact ⟨rfl, rfl, rfl⟩

/-- **V0, sign down (proved)**: `(s₃, t₃) = (sign, sel)`, base `(0, 1)`. -/
theorem sat3_slot_sign_V0_signDown (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t : Fin 3)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) :
    sat3Family N (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false true) = false ∧
    sat3Family N (Function.update (Function.update
        (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false true)
        (sat3Bit N cIdx t (sat3V N) (by omega))
        (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false true
          (sat3Bit N cIdx t (sat3V N) (by omega)))))
      (sat3Bit N cIdx t w₀.val (by omega))
      (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false true
        (sat3Bit N cIdx t w₀.val (by omega))))) = false ∧
    sat3Family N (Function.update
        (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false true)
      (sat3Bit N cIdx t w₀.val (by omega))
      (!(slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false true
        (sat3Bit N cIdx t w₀.val (by omega))))) = true := by
  rw [slotSignPt_val_sel N cIdx hk t w₀ hwv, slotSignPt_val_sign N cIdx hk t w₀ hwv]
  rw [slotSignPt_flip_sign N cIdx hk t w₀ hwv]
  rw [slotSignPt_flip_sel N cIdx hk t w₀ hwv, slotSignPt_flip_sel N cIdx hk t w₀ hwv]
  rw [slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv,
    slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv,
    slotSignPt_eval N hv hk hkv hm3 cIdx t w₀ hwv]
  exact ⟨rfl, rfl, rfl⟩

/-- **THE SLOT-SIGN DODGE (proved)**: no interfaced factorization admits a crossing
(slot-`t` selector, slot-`t` sign) pair together with a crossing same-block selector pair — the AND
cell (odd + V0) plus the OR cell (V1) refute `op` at any interface. -/
theorem sat3_slot_sign_dodge (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (cIdx : Fin (sat3M N)) (t : Fin 3) (w₀ : Fin (sat3M N - 2))
    (hwv : w₀.val < sat3V N)
    (c₂ : Fin (sat3M N)) (t₁ t₂ : Fin 3) (j₁ j₂ : Fin (sat3V N))
    (hne : sat3Bit N c₂ t₁ j₁.val (by have := j₁.isLt; omega)
      ≠ sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega)) :
    ¬ (((sat3Bit N cIdx t w₀.val (by omega) ∉ B
          ∧ sat3Bit N cIdx t (sat3V N) (by omega) ∉ A)
        ∨ (sat3Bit N cIdx t (sat3V N) (by omega) ∉ B
          ∧ sat3Bit N cIdx t w₀.val (by omega) ∉ A))
      ∧ ((sat3Bit N c₂ t₁ j₁.val (by have := j₁.isLt; omega) ∉ B
          ∧ sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega) ∉ A)
        ∨ (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega) ∉ B
          ∧ sat3Bit N c₂ t₁ j₁.val (by have := j₁.isLt; omega) ∉ A))) := by
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  have hss : sat3Bit N cIdx t w₀.val (by omega)
      ≠ sat3Bit N cIdx t (sat3V N) (by omega) :=
    sat3Bit_ne_same_block N cIdx t t w₀.val (sat3V N) (by omega) (by omega)
      (by rintro ⟨-, h'⟩; omega)
  rintro ⟨hSS | hSS, hV1 | hV1⟩
  · obtain ⟨v1a, v1b, v1c⟩ := sat3_same_block_V1_t N hv c₂ t₁ t₂ j₁ j₂ hne
    exact crossing_triples_kill_interfaced (sat3Family N) A B op g h hg hh hf
      (sat3Bit N cIdx t w₀.val (by omega)) (sat3Bit N cIdx t (sat3V N) (by omega))
      (sat3Bit N c₂ t₁ j₁.val (by have := j₁.isLt; omega))
      (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega))
      (sat3Bit N cIdx t w₀.val (by omega)) (sat3Bit N cIdx t (sat3V N) (by omega))
      hSS.1 hSS.2 hss hV1.1 hV1.2 hne hSS.1 hSS.2 hss
      (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false)
      (Function.update (sat3ZBase N c₂)
        (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega)) true)
      (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) true false)
      (sat3_slot_sign_odd N hv hk hkv hm3 cIdx t w₀ hwv)
      v1a v1b v1c
      (sat3_slot_sign_V0_selDown N hv hk hkv hm3 cIdx t w₀ hwv).1
      (sat3_slot_sign_V0_selDown N hv hk hkv hm3 cIdx t w₀ hwv).2.1
      (sat3_slot_sign_V0_selDown N hv hk hkv hm3 cIdx t w₀ hwv).2.2
  · obtain ⟨v1a, v1b, v1c⟩ := sat3_same_block_V1_t N hv c₂ t₂ t₁ j₂ j₁
      (fun hcon => hne hcon.symm)
    exact crossing_triples_kill_interfaced (sat3Family N) A B op g h hg hh hf
      (sat3Bit N cIdx t w₀.val (by omega)) (sat3Bit N cIdx t (sat3V N) (by omega))
      (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega))
      (sat3Bit N c₂ t₁ j₁.val (by have := j₁.isLt; omega))
      (sat3Bit N cIdx t w₀.val (by omega)) (sat3Bit N cIdx t (sat3V N) (by omega))
      hSS.1 hSS.2 hss hV1.1 hV1.2 (fun hcon => hne hcon.symm) hSS.1 hSS.2 hss
      (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false)
      (Function.update (sat3ZBase N c₂)
        (sat3Bit N c₂ t₁ j₁.val (by have := j₁.isLt; omega)) true)
      (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) true false)
      (sat3_slot_sign_odd N hv hk hkv hm3 cIdx t w₀ hwv)
      v1a v1b v1c
      (sat3_slot_sign_V0_selDown N hv hk hkv hm3 cIdx t w₀ hwv).1
      (sat3_slot_sign_V0_selDown N hv hk hkv hm3 cIdx t w₀ hwv).2.1
      (sat3_slot_sign_V0_selDown N hv hk hkv hm3 cIdx t w₀ hwv).2.2
  · obtain ⟨v1a, v1b, v1c⟩ := sat3_same_block_V1_t N hv c₂ t₁ t₂ j₁ j₂ hne
    exact crossing_triples_kill_interfaced (sat3Family N) A B op g h hg hh hf
      (sat3Bit N cIdx t (sat3V N) (by omega)) (sat3Bit N cIdx t w₀.val (by omega))
      (sat3Bit N c₂ t₁ j₁.val (by have := j₁.isLt; omega))
      (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega))
      (sat3Bit N cIdx t (sat3V N) (by omega)) (sat3Bit N cIdx t w₀.val (by omega))
      hSS.1 hSS.2 (fun hcon => hss hcon.symm) hV1.1 hV1.2 hne
      hSS.1 hSS.2 (fun hcon => hss hcon.symm)
      (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false)
      (Function.update (sat3ZBase N c₂)
        (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega)) true)
      (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false true)
      (sat3_slot_sign_odd' N hv hk hkv hm3 cIdx t w₀ hwv)
      v1a v1b v1c
      (sat3_slot_sign_V0_signDown N hv hk hkv hm3 cIdx t w₀ hwv).1
      (sat3_slot_sign_V0_signDown N hv hk hkv hm3 cIdx t w₀ hwv).2.1
      (sat3_slot_sign_V0_signDown N hv hk hkv hm3 cIdx t w₀ hwv).2.2
  · obtain ⟨v1a, v1b, v1c⟩ := sat3_same_block_V1_t N hv c₂ t₂ t₁ j₂ j₁
      (fun hcon => hne hcon.symm)
    exact crossing_triples_kill_interfaced (sat3Family N) A B op g h hg hh hf
      (sat3Bit N cIdx t (sat3V N) (by omega)) (sat3Bit N cIdx t w₀.val (by omega))
      (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega))
      (sat3Bit N c₂ t₁ j₁.val (by have := j₁.isLt; omega))
      (sat3Bit N cIdx t (sat3V N) (by omega)) (sat3Bit N cIdx t w₀.val (by omega))
      hSS.1 hSS.2 (fun hcon => hss hcon.symm) hV1.1 hV1.2 (fun hcon => hne hcon.symm)
      hSS.1 hSS.2 (fun hcon => hss hcon.symm)
      (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false false)
      (Function.update (sat3ZBase N c₂)
        (sat3Bit N c₂ t₁ j₁.val (by have := j₁.isLt; omega)) true)
      (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false true)
      (sat3_slot_sign_odd' N hv hk hkv hm3 cIdx t w₀ hwv)
      v1a v1b v1c
      (sat3_slot_sign_V0_signDown N hv hk hkv hm3 cIdx t w₀ hwv).1
      (sat3_slot_sign_V0_signDown N hv hk hkv hm3 cIdx t w₀ hwv).2.1
      (sat3_slot_sign_V0_signDown N hv hk hkv hm3 cIdx t w₀ hwv).2.2

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_slot_sign_odd
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_slot_sign_V0_selDown
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_slot_sign_dodge
