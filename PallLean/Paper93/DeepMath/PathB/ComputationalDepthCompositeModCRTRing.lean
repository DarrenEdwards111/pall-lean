import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompositeModRing

/-!
# Composite `MOD_m`: the ring CRT isomorphism `ZMod m ≃ ∏ ZMod pᵢ`

Rung 2 (`…CompositeModRing`) showed `ZMod m` is *not a field* for composite `m` (it has zero divisors), so the RS Fermat
gadget dies there.  This file records the ring-structure resolution: for coprime factors, `ZMod (a·b)` is **isomorphic as
a ring** to `ZMod a × ZMod b` (Chinese Remainder), so for squarefree `m = ∏ pᵢ`, `ZMod m ≅ ∏ F_{pᵢ}` — a *product of
fields*.  This is the mechanism Toda's construction uses to sidestep the non-field `ZMod m`: work in each field component,
where RS's Fermat gadget *does* apply.

  `zmodCRT` — the ring isomorphism `ZMod (a·b) ≃+* ZMod a × ZMod b` for coprime `a, b` (Chinese Remainder).
  `zmod_zero_iff_components` — **PROVED**: the `MOD_{a·b}` zero-test factors — `(k : ZMod (a·b)) = 0 ↔ (k : ZMod a) = 0 ∧
        (k : ZMod b) = 0`.
  `modZero_iff_components` — **PROVED**: the same for the gate value `modZero (a·b) k`.
  `zmod6CRT` — the canonical `ZMod 6 ≃+* ZMod 2 × ZMod 3 = F_2 × F_3`.

## Honest scope — the representation mechanism, not a lower bound

The ring iso is the *upper-bound / representation* mechanism: over `ZMod m ≅ ∏ F_{pᵢ}`, each field component `F_{pᵢ}` is
where RS's `fermatInd` is valid, so a `MOD_m` gate is handled component-wise — this is exactly how Toda / Beigel–Tarui
represent `ACC⁰[m]` circuits without a single field.  It does **not** give a lower bound: an `ACC⁰` *lower* bound is
Williams' algorithmic method (fast `ACC⁰`-SAT ⇒ `NEXP ⊄ ACC⁰`), not the RS degree argument, which cannot see a function
simultaneously hard over every `F_{pᵢ}`.  This file supplies the ring-decomposition mechanism and is careful about its
direction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CompositeMod

/-- **The ring CRT isomorphism**: `ZMod (a·b) ≃+* ZMod a × ZMod b` for coprime `a, b`. -/
noncomputable def zmodCRT {a b : ℕ} (h : Nat.Coprime a b) : ZMod (a * b) ≃+* ZMod a × ZMod b :=
  ZMod.chineseRemainder h

/-- **The `MOD_{a·b}` zero-test factors (proved)**: `(k : ZMod (a·b)) = 0 ↔ (k : ZMod a) = 0 ∧ (k : ZMod b) = 0`. -/
theorem zmod_zero_iff_components {a b : ℕ} (h : Nat.Coprime a b) (k : ℕ) :
    (k : ZMod (a * b)) = 0 ↔ (k : ZMod a) = 0 ∧ (k : ZMod b) = 0 := by
  rw [CharP.cast_eq_zero_iff (ZMod (a * b)) (a * b) k, CharP.cast_eq_zero_iff (ZMod a) a k,
    CharP.cast_eq_zero_iff (ZMod b) b k]
  exact ⟨fun hd => ⟨dvd_trans (dvd_mul_right a b) hd, dvd_trans (dvd_mul_left b a) hd⟩,
    fun ⟨ha, hb⟩ => Nat.Coprime.mul_dvd_of_dvd_of_dvd h ha hb⟩

/-- **The gate value factors through the components (proved)**: `modZero (a·b) k` holds iff the count is `0` in both field
components. -/
theorem modZero_iff_components {a b : ℕ} (h : Nat.Coprime a b) (k : ℕ) :
    modZero (a * b) k = true ↔ (k : ZMod a) = 0 ∧ (k : ZMod b) = 0 := by
  rw [modZero_eq_zmod, decide_eq_true_eq, zmod_zero_iff_components h]

/-- **The canonical `ZMod 6 ≃+* ZMod 2 × ZMod 3 = F_2 × F_3` (proved)**: the composite `MOD_6` ring decomposes into two
prime fields. -/
noncomputable def zmod6CRT : ZMod 6 ≃+* ZMod 2 × ZMod 3 :=
  ZMod.chineseRemainder (show Nat.Coprime 2 3 by decide)

end PallLean.Paper93.DeepMath.PathB.CompositeMod

#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.zmod_zero_iff_components
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.modZero_iff_components
