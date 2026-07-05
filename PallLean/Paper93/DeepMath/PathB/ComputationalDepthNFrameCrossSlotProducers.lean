import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCrossSlotOrWorkhorse

/-!
# N-Frame: cross-slot producers — V1 for slot signs, and slot-sign capture

The corner-point packaging of the cross-slot OR workhorse, and the payoff.  With `bvec ≡ false` the
table over the (slot-`t'` free selector, slot-`t` sign) axes is `b ∨ a` — an **OR pair**: odd square
and V1 triple in both orientations, no V0 (one falsified corner) — the exact dual of the slot-sign
AND pair.  Combining the two pairs closes the last capture gap.

  `crossSlotPt` + `_eval/_val_sel'/_val_sign/_flip_sel'/_flip_sign` — the corner point and its
        helpers, `slotSignPt`-style.
  `sat3_cross_slot_odd/odd'` — **PROVED**: engine-format odd squares, both orientations.
  `sat3_cross_slot_V1_signDown/selDown` — **PROVED**: engine-format V1 triples, both orientations —
        **the V1 source on a pair containing a slot-`t` sign bit**.
  `sat3_slotT_sign_mem_union` — **PROVED**: every slot-`t` sign bit is essential.
  `sat3_cross_slot_sign_capture_left/right` — **PROVED, the capture**: two same-block anchors — the
        free slot-`t'` selector and the pinned slot-`t` selector `w₀` — on one exclusive side force
        every non-interned slot-`t` sign onto that side: escape crosses the OR pair (odd + V1) and
        the AND pair (V0 via `sat3_slot_sign_V0_*`), killed at any interface.

**Every coordinate class of the exact layout now has interfaced capture machinery**: slot-0 signs
(sign graph), all-slot selectors (anchored capture), slot-`t` signs (this file).

## Honest scope

Remaining Track C mountains, named: the `GlobalPACInterfaceBound` counting assembly over the
accumulated per-class capture/dodge constraints, and the wire-frontier → coordinate-interface
extraction (`coneExcess ≤ k` ⇒ factorization with bounded `|A ∩ B|`).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The cross-slot OR corner point. -/
def crossSlotPt (N : ℕ) (cIdx : Fin (sat3M N)) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (t t' : Fin 3) (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) : Fin N → Bool :=
  Function.update (Function.update
    (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
      (fun bit => decide (bit = sat3Bit N cIdx t w₀.val (by omega))))
    (sat3Bit N cIdx t' (sat3M N - 2) (by have := sat3M_pred_le_sat3V N; omega)) b)
    (sat3Bit N cIdx t (sat3V N) (by omega)) a

theorem crossSlotPt_eval (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    sat3Family N (crossSlotPt N cIdx hk t t' w₀ hwv bvec b a)
      = (b || xor (bvec w₀) a) := by
  unfold crossSlotPt
  exact sat3_cross_slot_or_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv bvec b a

theorem crossSlotPt_val_sel' (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    crossSlotPt N cIdx hk t t' w₀ hwv bvec b a
      (sat3Bit N cIdx t' (sat3M N - 2)
        (by have := sat3M_pred_le_sat3V N; omega)) = b := by
  unfold crossSlotPt
  rw [Function.update_of_ne (sat3Bit_ne_same_block N cIdx t' t (sat3M N - 2)
    (sat3V N) (by have := sat3M_pred_le_sat3V N; omega) (by omega)
    (by rintro ⟨h, -⟩; exact htt (Fin.ext h)))]
  exact Function.update_self _ _ _

theorem crossSlotPt_val_sign (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (t t' : Fin 3)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b a : Bool) :
    crossSlotPt N cIdx hk t t' w₀ hwv bvec b a
      (sat3Bit N cIdx t (sat3V N) (by omega)) = a := by
  unfold crossSlotPt
  exact Function.update_self _ _ _

theorem crossSlotPt_flip_sign (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (t t' : Fin 3)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b a v : Bool) :
    Function.update (crossSlotPt N cIdx hk t t' w₀ hwv bvec b a)
      (sat3Bit N cIdx t (sat3V N) (by omega)) v
    = crossSlotPt N cIdx hk t t' w₀ hwv bvec b v := by
  unfold crossSlotPt
  exact Function.update_idem _ _ _

theorem crossSlotPt_flip_sel' (N : ℕ) (cIdx : Fin (sat3M N))
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (bvec : Fin (sat3M N - 2) → Bool) (b a v : Bool) :
    Function.update (crossSlotPt N cIdx hk t t' w₀ hwv bvec b a)
      (sat3Bit N cIdx t' (sat3M N - 2)
        (by have := sat3M_pred_le_sat3V N; omega)) v
    = crossSlotPt N cIdx hk t t' w₀ hwv bvec v a := by
  unfold crossSlotPt
  rw [Function.update_comm (show sat3Bit N cIdx t (sat3V N) (by omega)
      ≠ sat3Bit N cIdx t' (sat3M N - 2)
        (by have := sat3M_pred_le_sat3V N; omega) from
    sat3Bit_ne_same_block N cIdx t t' (sat3V N) (sat3M N - 2) (by omega)
      (by have := sat3M_pred_le_sat3V N; omega)
      (by rintro ⟨h, -⟩; exact htt (Fin.ext h.symm)))]
  rw [Function.update_idem]

/-- **ODD SQUARE, (sel', sign) orientation (proved)**: base `(0,0)`, table `b ∨ a`. -/
theorem sat3_cross_slot_odd (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) :
    xor (xor (sat3Family N (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false))
        (sat3Family N (Function.update
          (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false)
          (sat3Bit N cIdx t' (sat3M N - 2)
            (by have := sat3M_pred_le_sat3V N; omega))
          (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t' (sat3M N - 2)
              (by have := sat3M_pred_le_sat3V N; omega)))))))
      (xor (sat3Family N (Function.update
          (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false)
          (sat3Bit N cIdx t (sat3V N) (by omega))
          (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t (sat3V N) (by omega))))))
        (sat3Family N (Function.update (Function.update
          (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false)
          (sat3Bit N cIdx t' (sat3M N - 2)
            (by have := sat3M_pred_le_sat3V N; omega))
          (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t' (sat3M N - 2)
              (by have := sat3M_pred_le_sat3V N; omega)))))
          (sat3Bit N cIdx t (sat3V N) (by omega))
          (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t (sat3V N) (by omega))))))) = true := by
  rw [crossSlotPt_val_sel' N cIdx hk t t' htt w₀ hwv,
    crossSlotPt_val_sign N cIdx hk t t' w₀ hwv]
  rw [crossSlotPt_flip_sel' N cIdx hk t t' htt w₀ hwv]
  rw [crossSlotPt_flip_sign N cIdx hk t t' w₀ hwv,
    crossSlotPt_flip_sign N cIdx hk t t' w₀ hwv]
  rw [crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv,
    crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv,
    crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv,
    crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv]
  rfl

/-- **ODD SQUARE, (sign, sel') orientation (proved)**: the mirror update order. -/
theorem sat3_cross_slot_odd' (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) :
    xor (xor (sat3Family N (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false))
        (sat3Family N (Function.update
          (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false)
          (sat3Bit N cIdx t (sat3V N) (by omega))
          (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t (sat3V N) (by omega)))))))
      (xor (sat3Family N (Function.update
          (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false)
          (sat3Bit N cIdx t' (sat3M N - 2)
            (by have := sat3M_pred_le_sat3V N; omega))
          (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t' (sat3M N - 2)
              (by have := sat3M_pred_le_sat3V N; omega))))))
        (sat3Family N (Function.update (Function.update
          (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false)
          (sat3Bit N cIdx t (sat3V N) (by omega))
          (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t (sat3V N) (by omega)))))
          (sat3Bit N cIdx t' (sat3M N - 2)
            (by have := sat3M_pred_le_sat3V N; omega))
          (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false
            (sat3Bit N cIdx t' (sat3M N - 2)
              (by have := sat3M_pred_le_sat3V N; omega))))))) = true := by
  rw [crossSlotPt_val_sel' N cIdx hk t t' htt w₀ hwv,
    crossSlotPt_val_sign N cIdx hk t t' w₀ hwv]
  rw [crossSlotPt_flip_sign N cIdx hk t t' w₀ hwv]
  rw [crossSlotPt_flip_sel' N cIdx hk t t' htt w₀ hwv,
    crossSlotPt_flip_sel' N cIdx hk t t' htt w₀ hwv]
  rw [crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv,
    crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv,
    crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv,
    crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv]
  rfl

/-- **V1, sign down (proved)**: `(s₂, t₂) = (sel', sign)`, base `(0, 1)` — the V1 source on a pair
containing the slot-`t` sign bit. -/
theorem sat3_cross_slot_V1_signDown (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) :
    sat3Family N (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false true) = true ∧
    sat3Family N (Function.update (Function.update
        (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false true)
        (sat3Bit N cIdx t' (sat3M N - 2)
          (by have := sat3M_pred_le_sat3V N; omega))
        (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false true
          (sat3Bit N cIdx t' (sat3M N - 2)
            (by have := sat3M_pred_le_sat3V N; omega)))))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false true
        (sat3Bit N cIdx t (sat3V N) (by omega))))) = true ∧
    sat3Family N (Function.update
        (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false true)
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false true
        (sat3Bit N cIdx t (sat3V N) (by omega))))) = false := by
  rw [crossSlotPt_val_sel' N cIdx hk t t' htt w₀ hwv,
    crossSlotPt_val_sign N cIdx hk t t' w₀ hwv]
  rw [crossSlotPt_flip_sel' N cIdx hk t t' htt w₀ hwv]
  rw [crossSlotPt_flip_sign N cIdx hk t t' w₀ hwv,
    crossSlotPt_flip_sign N cIdx hk t t' w₀ hwv]
  rw [crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv,
    crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv,
    crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv]
  exact ⟨rfl, rfl, rfl⟩

/-- **V1, selector down (proved)**: `(s₂, t₂) = (sign, sel')`, base `(1, 0)`. -/
theorem sat3_cross_slot_V1_selDown (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) :
    sat3Family N (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) true false) = true ∧
    sat3Family N (Function.update (Function.update
        (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) true false)
        (sat3Bit N cIdx t (sat3V N) (by omega))
        (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) true false
          (sat3Bit N cIdx t (sat3V N) (by omega)))))
      (sat3Bit N cIdx t' (sat3M N - 2)
        (by have := sat3M_pred_le_sat3V N; omega))
      (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) true false
        (sat3Bit N cIdx t' (sat3M N - 2)
          (by have := sat3M_pred_le_sat3V N; omega))))) = true ∧
    sat3Family N (Function.update
        (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) true false)
      (sat3Bit N cIdx t' (sat3M N - 2)
        (by have := sat3M_pred_le_sat3V N; omega))
      (!(crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) true false
        (sat3Bit N cIdx t' (sat3M N - 2)
          (by have := sat3M_pred_le_sat3V N; omega))))) = false := by
  rw [crossSlotPt_val_sel' N cIdx hk t t' htt w₀ hwv,
    crossSlotPt_val_sign N cIdx hk t t' w₀ hwv]
  rw [crossSlotPt_flip_sign N cIdx hk t t' w₀ hwv]
  rw [crossSlotPt_flip_sel' N cIdx hk t t' htt w₀ hwv,
    crossSlotPt_flip_sel' N cIdx hk t t' htt w₀ hwv]
  rw [crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv,
    crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv,
    crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv]
  exact ⟨rfl, rfl, rfl⟩

/-- **Every slot-`t` sign bit is read (proved)**: the cross-slot corners make it essential. -/
theorem sat3_slotT_sign_mem_union (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N) :
    sat3Bit N cIdx t (sat3V N) (by omega) ∈ A ∪ B := by
  by_contra hout
  rw [Finset.mem_union] at hout
  push_neg at hout
  obtain ⟨hA, hB⟩ := hout
  have h1 : sat3Family N (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false)
      false false) = false := by
    rw [crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv]
    rfl
  have h2 : sat3Family N (Function.update
      (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false)
      (sat3Bit N cIdx t (sat3V N) (by omega)) true) = true := by
    rw [crossSlotPt_flip_sign N cIdx hk t t' w₀ hwv,
      crossSlotPt_eval N hv hk hkv hm3 cIdx t t' htt w₀ hwv]
    rfl
  rw [hf] at h1 h2
  have hgu : g (Function.update
      (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false)
      (sat3Bit N cIdx t (sat3V N) (by omega)) true)
      = g (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false) := by
    apply hg
    intro i hi
    exact Function.update_of_ne (fun hc => hA (by rw [← hc]; exact hi)) _ _
  have hhu : h (Function.update
      (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false)
      (sat3Bit N cIdx t (sat3V N) (by omega)) true)
      = h (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false) := by
    apply hh
    intro i hi
    exact Function.update_of_ne (fun hc => hB (by rw [← hc]; exact hi)) _ _
  rw [hgu, hhu, h1] at h2
  exact Bool.noConfusion h2

/-- **SLOT-SIGN CAPTURE, LEFT (proved)**: the free slot-`t'` selector and the pinned slot-`t`
selector anchored in `A \ B` force every non-interned slot-`t` sign into `A \ B` — escape crosses
the OR pair (odd + V1) and the AND pair (V0). -/
theorem sat3_cross_slot_sign_capture_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (hanch1 : sat3Bit N cIdx t' (sat3M N - 2)
      (by have := sat3M_pred_le_sat3V N; omega) ∈ A \ B)
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
      sat3_cross_slot_V1_signDown N hv hk hkv hm3 cIdx t t' htt w₀ hwv
    obtain ⟨z0a, z0b, z0c⟩ :=
      sat3_slot_sign_V0_selDown N hv hk hkv hm3 cIdx t w₀ hwv
    exact crossing_triples_kill_interfaced (sat3Family N) A B op g h hg hh hf
      (sat3Bit N cIdx t' (sat3M N - 2) (by have := sat3M_pred_le_sat3V N; omega))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (sat3Bit N cIdx t' (sat3M N - 2) (by have := sat3M_pred_le_sat3V N; omega))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (sat3Bit N cIdx t w₀.val (by omega))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      hanch1.2 hsA
      (sat3Bit_ne_same_block N cIdx t' t (sat3M N - 2) (sat3V N)
        (by have := sat3M_pred_le_sat3V N; omega) (by omega)
        (by rintro ⟨h', -⟩; exact htt (Fin.ext h')))
      hanch1.2 hsA
      (sat3Bit_ne_same_block N cIdx t' t (sat3M N - 2) (sat3V N)
        (by have := sat3M_pred_le_sat3V N; omega) (by omega)
        (by rintro ⟨h', -⟩; exact htt (Fin.ext h')))
      hanch2.2 hsA
      (sat3Bit_ne_same_block N cIdx t t w₀.val (sat3V N) (by omega) (by omega)
        (by rintro ⟨-, h'⟩; omega))
      (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false)
      (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false true)
      (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) true false)
      (sat3_cross_slot_odd N hv hk hkv hm3 cIdx t t' htt w₀ hwv)
      v1a v1b v1c z0a z0b z0c

/-- **SLOT-SIGN CAPTURE, RIGHT (proved)**: the mirror, via the primed orientations. -/
theorem sat3_cross_slot_sign_capture_right (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (cIdx : Fin (sat3M N)) (t t' : Fin 3) (htt : t' ≠ t)
    (w₀ : Fin (sat3M N - 2)) (hwv : w₀.val < sat3V N)
    (hanch1 : sat3Bit N cIdx t' (sat3M N - 2)
      (by have := sat3M_pred_le_sat3V N; omega) ∈ B \ A)
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
      sat3_cross_slot_V1_selDown N hv hk hkv hm3 cIdx t t' htt w₀ hwv
    obtain ⟨z0a, z0b, z0c⟩ :=
      sat3_slot_sign_V0_signDown N hv hk hkv hm3 cIdx t w₀ hwv
    exact crossing_triples_kill_interfaced (sat3Family N) A B op g h hg hh hf
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (sat3Bit N cIdx t' (sat3M N - 2) (by have := sat3M_pred_le_sat3V N; omega))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (sat3Bit N cIdx t' (sat3M N - 2) (by have := sat3M_pred_le_sat3V N; omega))
      (sat3Bit N cIdx t (sat3V N) (by omega))
      (sat3Bit N cIdx t w₀.val (by omega))
      hsB hanch1.2
      (sat3Bit_ne_same_block N cIdx t t' (sat3V N) (sat3M N - 2) (by omega)
        (by have := sat3M_pred_le_sat3V N; omega)
        (by rintro ⟨h', -⟩; exact htt (Fin.ext h'.symm)))
      hsB hanch1.2
      (sat3Bit_ne_same_block N cIdx t t' (sat3V N) (sat3M N - 2) (by omega)
        (by have := sat3M_pred_le_sat3V N; omega)
        (by rintro ⟨h', -⟩; exact htt (Fin.ext h'.symm)))
      hsB hanch2.2
      (sat3Bit_ne_same_block N cIdx t t (sat3V N) w₀.val (by omega) (by omega)
        (by rintro ⟨-, h'⟩; omega))
      (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) false false)
      (crossSlotPt N cIdx hk t t' w₀ hwv (fun _ => false) true false)
      (slotSignPt N cIdx hk t w₀ hwv (fun _ => false) false true)
      (sat3_cross_slot_odd' N hv hk hkv hm3 cIdx t t' htt w₀ hwv)
      v1a v1b v1c z0a z0b z0c

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cross_slot_V1_signDown
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cross_slot_sign_capture_left
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cross_slot_sign_capture_right
