import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSubBlockScattering

/-!
# N-Frame: all-slot selector capture — the slot-0/1 selector gap closes

The slot-0/1 selector class needed **no new eval workhorse**: the general-slot pattern producers
(`sat3_same_block_{odd,V1}_t`, `sat3_cross_block_{odd,V0}_t`) already run at arbitrary slots, so the
interfaced selector kill applies to every selector coordinate.  What was missing was only the capture
assembly: two left-side selector **anchors** — one in the target's block, one in any other block —
capture every selector of the block.

  `sat3_sel_mem_union` — **PROVED**: every selector bit, any slot, any variable, is essential.
  `sat3_anchored_selector_capture_left/right` — **PROVED, the capture**: a same-block anchor and a
        cross-block anchor on one exclusive side force every non-interned selector of the block onto
        that side — escape would cross both a same-block pair (odd + V1) and a cross-block pair
        (V0), killed at any interface.
  `sat3_two_anchor_united_left` — **PROVED, the assembly**: two anchored blocks have their entire
        non-interned selector layers (all slots, all variables) united on the anchors' side.

## Honest scope

This closes the selector classes: slot-0/1/2, all variables, pin or not.  The remaining uncovered
class is **slot-1/2 signs**: the slot-sign probe machinery (`slotSignPt`) carries odd + V0 on the
(slot-`t` selector, slot-`t` sign) pair but no V1 — sign capture needs a **cross-slot OR workhorse**
(slot-`t'` selector axis against a slot-`t` pinned literal's sign axis, giving `f = b ∨ xor(w, a)`
with V1 corners), a genuinely new eval construction.  Named, not claimed.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **Every selector bit is read (proved)** — any slot, any variable. -/
theorem sat3_sel_mem_union (N : ℕ) (hv : 1 ≤ sat3V N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (t : Fin 3) (jv : Fin (sat3V N)) :
    sat3Bit N c t jv.val (by have := jv.isLt; omega) ∈ A ∪ B := by
  by_contra hout
  rw [Finset.mem_union] at hout
  push_neg at hout
  obtain ⟨hA, hB⟩ := hout
  have h1 : sat3Family N (sat3ZBase N c) = false := sat3ZBase_unsat N c
  have h2 : sat3Family N (Function.update (sat3ZBase N c)
      (sat3Bit N c t jv.val (by have := jv.isLt; omega)) true) = true :=
    sat3_zbase_flip_sat_t N hv c t jv
  rw [hf] at h1 h2
  have hgu : g (Function.update (sat3ZBase N c)
      (sat3Bit N c t jv.val (by have := jv.isLt; omega)) true)
      = g (sat3ZBase N c) := by
    apply hg
    intro i hi
    exact Function.update_of_ne (fun hc => hA (by rw [← hc]; exact hi)) _ _
  have hhu : h (Function.update (sat3ZBase N c)
      (sat3Bit N c t jv.val (by have := jv.isLt; omega)) true)
      = h (sat3ZBase N c) := by
    apply hh
    intro i hi
    exact Function.update_of_ne (fun hc => hB (by rw [← hc]; exact hi)) _ _
  rw [hgu, hhu, h1] at h2
  exact Bool.noConfusion h2

/-- **ANCHORED CAPTURE, LEFT (proved)**: a same-block anchor and a cross-block anchor in `A \ B`
capture every non-interned selector of the block into `A \ B`. -/
theorem sat3_anchored_selector_capture_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (tx : Fin 3) (jx : Fin (sat3V N))
    (ty : Fin 3) (jy : Fin (sat3V N))
    (hyx : sat3Bit N c ty jy.val (by have := jy.isLt; omega)
      ≠ sat3Bit N c tx jx.val (by have := jx.isLt; omega))
    (hy : sat3Bit N c ty jy.val (by have := jy.isLt; omega) ∈ A \ B)
    (c' : Fin (sat3M N)) (hcc : c'.val ≠ c.val) (tz : Fin 3) (jz : Fin (sat3V N))
    (hz : sat3Bit N c' tz jz.val (by have := jz.isLt; omega) ∈ A \ B)
    (hxI : sat3Bit N c tx jx.val (by have := jx.isLt; omega) ∉ A ∩ B) :
    sat3Bit N c tx jx.val (by have := jx.isLt; omega) ∈ A \ B := by
  have hxu := sat3_sel_mem_union N hv op g h A B hg hh hf c tx jx
  rw [Finset.mem_union] at hxu
  rw [Finset.mem_inter] at hxI
  push_neg at hxI
  rw [Finset.mem_sdiff] at hy hz
  rw [Finset.mem_sdiff]
  by_cases hxA : sat3Bit N c tx jx.val (by have := jx.isLt; omega) ∈ A
  · exact ⟨hxA, hxI hxA⟩
  · exfalso
    exact sat3_selector_cells_kill_interfaced N hv op g h A B hg hh hf
      c ty tx jy jx hyx hy.2 hxA c' c hcc tz tx jz jx hz.2 hxA

/-- **ANCHORED CAPTURE, RIGHT (proved)**: the mirror. -/
theorem sat3_anchored_selector_capture_right (N : ℕ) (hv : 1 ≤ sat3V N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (tx : Fin 3) (jx : Fin (sat3V N))
    (ty : Fin 3) (jy : Fin (sat3V N))
    (hyx : sat3Bit N c ty jy.val (by have := jy.isLt; omega)
      ≠ sat3Bit N c tx jx.val (by have := jx.isLt; omega))
    (hy : sat3Bit N c ty jy.val (by have := jy.isLt; omega) ∈ B \ A)
    (c' : Fin (sat3M N)) (hcc : c'.val ≠ c.val) (tz : Fin 3) (jz : Fin (sat3V N))
    (hz : sat3Bit N c' tz jz.val (by have := jz.isLt; omega) ∈ B \ A)
    (hxI : sat3Bit N c tx jx.val (by have := jx.isLt; omega) ∉ A ∩ B) :
    sat3Bit N c tx jx.val (by have := jx.isLt; omega) ∈ B \ A := by
  have hxu := sat3_sel_mem_union N hv op g h A B hg hh hf c tx jx
  rw [Finset.mem_union] at hxu
  rw [Finset.mem_inter] at hxI
  push_neg at hxI
  rw [Finset.mem_sdiff] at hy hz
  rw [Finset.mem_sdiff]
  by_cases hxB : sat3Bit N c tx jx.val (by have := jx.isLt; omega) ∈ B
  · exact ⟨hxB, fun hxA => hxI hxA hxB⟩
  · exfalso
    exact sat3_selector_cells_kill_interfaced N hv op g h A B hg hh hf
      c tx ty jx jy (fun hcon => hyx hcon.symm) hxB hy.2
      c c' (fun hcon => hcc hcon.symm) tx tz jx jz hxB hz.2

/-- **THE TWO-ANCHOR UNITED MASS (proved)**: two anchored blocks have their entire non-interned
selector layers — all slots, all variables — united on the anchors' side. -/
theorem sat3_two_anchor_united_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c c' : Fin (sat3M N)) (hcc : c'.val ≠ c.val)
    (ty : Fin 3) (jy : Fin (sat3V N))
    (hy : sat3Bit N c ty jy.val (by have := jy.isLt; omega) ∈ A \ B)
    (tz : Fin 3) (jz : Fin (sat3V N))
    (hz : sat3Bit N c' tz jz.val (by have := jz.isLt; omega) ∈ A \ B) :
    (∀ (t : Fin 3) (j : Fin (sat3V N)),
      sat3Bit N c t j.val (by have := j.isLt; omega) ∉ A ∩ B →
      sat3Bit N c t j.val (by have := j.isLt; omega) ∈ A \ B) ∧
    (∀ (t : Fin 3) (j : Fin (sat3V N)),
      sat3Bit N c' t j.val (by have := j.isLt; omega) ∉ A ∩ B →
      sat3Bit N c' t j.val (by have := j.isLt; omega) ∈ A \ B) := by
  constructor
  · intro t j hI
    by_cases heq : sat3Bit N c ty jy.val (by have := jy.isLt; omega)
        = sat3Bit N c t j.val (by have := j.isLt; omega)
    · rw [← heq]
      exact hy
    · exact sat3_anchored_selector_capture_left N hv op g h A B hg hh hf
        c t j ty jy heq hy c' hcc tz jz hz hI
  · intro t j hI
    by_cases heq : sat3Bit N c' tz jz.val (by have := jz.isLt; omega)
        = sat3Bit N c' t j.val (by have := j.isLt; omega)
    · rw [← heq]
      exact hz
    · exact sat3_anchored_selector_capture_left N hv op g h A B hg hh hf
        c' t j tz jz heq hz c (fun hcon => hcc hcon.symm) ty jy hy hI

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sel_mem_union
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_anchored_selector_capture_left
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_two_anchor_united_left
