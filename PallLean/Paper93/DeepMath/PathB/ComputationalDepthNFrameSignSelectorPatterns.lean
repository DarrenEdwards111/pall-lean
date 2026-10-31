import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMixedLiteralWorkhorse

/-!
# N-Frame: sign↔selector patterns — the edge package from the mixed-literal workhorse

At `w₀ := j₀` and the all-true pin context, the mixed-literal table is `f = !sign ∨ sel` — corners
`X(0,0)=1, X(1,0)=0, X(0,1)=1, X(1,1)=1`.  Engine-format packages for the pair
(designated sign, slot-2 selector on a pinned variable):

  `sat3_sign_selector_odd` — **PROVED**: odd square, base at the zero corner.
  `sat3_sign_selector_V1_signDown` — **PROVED**: V1 with the sign as the down-flip (`s₂ = sel`,
        `t₂ = sign`), base `X(0,0)`.
  `sat3_sign_selector_V1_selDown` — **PROVED**: V1 with the selector as the down-flip (`s₂ = sign`,
        `t₂ = sel`), base `X(1,1)`.

## Honest scope — the V0 finding

Recorded before assembly: sign↔selector tables always contain the full `sign`-row of ones
(`xor(β, sign)` fires for one sign value regardless of the selector), so these pairs carry odd and V1 but
**never V0**.  The whole-block assembly therefore needs its V0 from a separated cross-block selector pair
— available unless the cut puts all slot-2 selectors on one side.  For those cuts the single-coordinate
engine cannot finish: the V0 must come from **set-flips** (a block of selectors flipped inside `S`, a sign
package flipped inside `Sᶜ` — the four points `p, p⊕A, p⊕B, p⊕A⊕B` are constructible whenever `A ⊆ S`
and `B ⊆ Sᶜ` are known-side coordinate sets, and blindness gives the same 2×2 op-submatrix).  The
set-flip generalization of `triples_kill_split_mixed` (via the existing `pinAll` machinery) is the named
next engine.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The mixed-literal corner point: probe on `j₀` with free sign `a`, slot-2 selector on `j₀` at `b`,
all-true pin context. -/
def mixedPt (N : ℕ) (cIdx : Fin (sat3M N)) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N) (a b : Bool) : Fin N → Bool :=
  Function.update (Function.update
    (sat3Patch N cIdx (sat3Context N cIdx hk (fun _ => true))
      (sat3Probe N ⟨j₀.val, hjv⟩ false))
    (sat3SignBit N cIdx) a) (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩) b

variable {N : ℕ}

theorem mixedPt_eval (N : ℕ) (hv : 1 ≤ sat3V N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hkv : sat3M N - 2 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (a b : Bool) :
    sat3Family N (mixedPt N cIdx hk j₀ hjv a b) = (!a || b) := by
  unfold mixedPt
  rw [sat3_mixed_literal_eval N hv hk hkv hm3 cIdx j₀ j₀ hjv hjv (fun _ => true) a b]
  cases a <;> cases b <;> rfl

theorem mixedPt_val_sign (N : ℕ) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (a b : Bool) :
    mixedPt N cIdx hk j₀ hjv a b (sat3SignBit N cIdx) = a := by
  unfold mixedPt
  rw [Function.update_of_ne (sat3S2Sel_ne_signBit N cIdx ⟨j₀.val, hjv⟩ cIdx).symm]
  exact Function.update_self _ _ _

theorem mixedPt_val_sel (N : ℕ) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (a b : Bool) :
    mixedPt N cIdx hk j₀ hjv a b (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩) = b := by
  unfold mixedPt
  exact Function.update_self _ _ _

theorem mixedPt_flip_sel (N : ℕ) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (a b v : Bool) :
    Function.update (mixedPt N cIdx hk j₀ hjv a b)
      (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩) v = mixedPt N cIdx hk j₀ hjv a v := by
  unfold mixedPt
  exact Function.update_idem _ _ _

theorem mixedPt_flip_sign (N : ℕ) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (a b v : Bool) :
    Function.update (mixedPt N cIdx hk j₀ hjv a b)
      (sat3SignBit N cIdx) v = mixedPt N cIdx hk j₀ hjv v b := by
  unfold mixedPt
  rw [Function.update_comm (sat3S2Sel_ne_signBit N cIdx ⟨j₀.val, hjv⟩ cIdx)]
  rw [Function.update_idem]

/-- **ODD SQUARE (proved)**: engine format at pair `(s₁, t₁) = (signBit, sel j₀)`, base `X(1,0)`. -/
theorem sat3_sign_selector_odd (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2))
    (hjv : j₀.val < sat3V N) :
    xor (xor (sat3Family N (mixedPt N cIdx hk j₀ hjv true false))
        (sat3Family N (Function.update (mixedPt N cIdx hk j₀ hjv true false)
          (sat3SignBit N cIdx)
          (!(mixedPt N cIdx hk j₀ hjv true false (sat3SignBit N cIdx))))))
      (xor (sat3Family N (Function.update (mixedPt N cIdx hk j₀ hjv true false)
          (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
          (!(mixedPt N cIdx hk j₀ hjv true false (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)))))
        (sat3Family N (Function.update (Function.update
          (mixedPt N cIdx hk j₀ hjv true false) (sat3SignBit N cIdx)
          (!(mixedPt N cIdx hk j₀ hjv true false (sat3SignBit N cIdx))))
          (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
          (!(mixedPt N cIdx hk j₀ hjv true false
            (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)))))) = true := by
  rw [mixedPt_val_sign N hk cIdx j₀ hjv, mixedPt_val_sel N hk cIdx j₀ hjv]
  rw [mixedPt_flip_sign N hk cIdx j₀ hjv, mixedPt_flip_sel N hk cIdx j₀ hjv]
  rw [mixedPt_flip_sel N hk cIdx j₀ hjv]
  rw [mixedPt_eval N hv hk hkv hm3 cIdx j₀ hjv, mixedPt_eval N hv hk hkv hm3 cIdx j₀ hjv,
    mixedPt_eval N hv hk hkv hm3 cIdx j₀ hjv, mixedPt_eval N hv hk hkv hm3 cIdx j₀ hjv]
  rfl

/-- **V1, sign down (proved)**: `(s₂, t₂) = (sel j₀, signBit)`, base `X(0,0)`. -/
theorem sat3_sign_selector_V1_signDown (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2))
    (hjv : j₀.val < sat3V N) :
    sat3Family N (mixedPt N cIdx hk j₀ hjv false false) = true ∧
    sat3Family N (Function.update (Function.update
        (mixedPt N cIdx hk j₀ hjv false false) (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
        (!(mixedPt N cIdx hk j₀ hjv false false (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩))))
      (sat3SignBit N cIdx)
      (!(mixedPt N cIdx hk j₀ hjv false false (sat3SignBit N cIdx)))) = true ∧
    sat3Family N (Function.update (mixedPt N cIdx hk j₀ hjv false false)
      (sat3SignBit N cIdx)
      (!(mixedPt N cIdx hk j₀ hjv false false (sat3SignBit N cIdx)))) = false := by
  rw [mixedPt_val_sign N hk cIdx j₀ hjv, mixedPt_val_sel N hk cIdx j₀ hjv]
  rw [mixedPt_flip_sel N hk cIdx j₀ hjv, mixedPt_flip_sign N hk cIdx j₀ hjv,
    mixedPt_flip_sign N hk cIdx j₀ hjv]
  rw [mixedPt_eval N hv hk hkv hm3 cIdx j₀ hjv, mixedPt_eval N hv hk hkv hm3 cIdx j₀ hjv,
    mixedPt_eval N hv hk hkv hm3 cIdx j₀ hjv]
  exact ⟨rfl, rfl, rfl⟩

/-- **V1, selector down (proved)**: `(s₂, t₂) = (signBit, sel j₀)`, base `X(1,1)`. -/
theorem sat3_sign_selector_V1_selDown (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2))
    (hjv : j₀.val < sat3V N) :
    sat3Family N (mixedPt N cIdx hk j₀ hjv true true) = true ∧
    sat3Family N (Function.update (Function.update
        (mixedPt N cIdx hk j₀ hjv true true) (sat3SignBit N cIdx)
        (!(mixedPt N cIdx hk j₀ hjv true true (sat3SignBit N cIdx))))
      (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
      (!(mixedPt N cIdx hk j₀ hjv true true (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)))) = true ∧
    sat3Family N (Function.update (mixedPt N cIdx hk j₀ hjv true true)
      (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
      (!(mixedPt N cIdx hk j₀ hjv true true (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)))) = false := by
  rw [mixedPt_val_sign N hk cIdx j₀ hjv, mixedPt_val_sel N hk cIdx j₀ hjv]
  rw [mixedPt_flip_sign N hk cIdx j₀ hjv, mixedPt_flip_sel N hk cIdx j₀ hjv,
    mixedPt_flip_sel N hk cIdx j₀ hjv]
  rw [mixedPt_eval N hv hk hkv hm3 cIdx j₀ hjv, mixedPt_eval N hv hk hkv hm3 cIdx j₀ hjv,
    mixedPt_eval N hv hk hkv hm3 cIdx j₀ hjv]
  exact ⟨rfl, rfl, rfl⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_selector_odd
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_selector_V1_signDown
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_selector_V1_selDown
