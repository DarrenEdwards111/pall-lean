import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompositeModCRT

/-!
# Composite `MOD_m`: the ring-level two-fields barrier

Rung 1 (`…CompositeModCRT`) gave the CRT decomposition `MOD_m = ⋀ᵢ MOD_{pᵢ^{eᵢ}}`.  This file recasts a `MOD_m` gate as a
**zero-test in the ring `ZMod m`** and pins down, concretely, *why* the Razborov–Smolensky polynomial gadget cannot cross
the composite-modulus wall: for composite `m`, `ZMod m` has **zero divisors**, so it is not a field, and Fermat's
`a^{m-1} = 1` (the exact nonzero-indicator the whole RS method is built on, valid only over a field) **fails**.

  `modZero_eq_zmod` — **PROVED**: the `MOD_m` gate is the zero-test `decide ((k : ZMod m) = 0)` — the gate lives in the
        ring `ZMod m`, which is the field `F_p` exactly when `m` is prime.
  `zmod_zero_divisor_of_mul` — **PROVED, the barrier**: for `m = a·b` with `a, b ≥ 2`, the images of `a` and `b` are
        nonzero in `ZMod m` yet multiply to `0` — genuine zero divisors, so `ZMod m` is not an integral domain.
  `zmod6_zero_divisor` / `zmod6_fermat_fails` — **PROVED, the canonical `ZMod 6` witness**: `2·3 = 0` (both nonzero), and
        `2^{5} = 2 ≠ 1`, so the degree-`(m-1)` Fermat nonzero-indicator gadget is wrong at `m = 6`.

## Honest scope — the obstruction, made explicit

The RS method's engine is Fermat's little theorem: over `F_p`, `(subset-sum)^{p-1}` is the exact `{0,1}` nonzero-indicator
(the repo's `fermatInd`), which is what makes `MOD_p` a single degree-`(p-1)` polynomial.  This file shows that engine has
**no analogue** over `ZMod m` for composite `m`: `ZMod m` is not a field (`zmod_zero_divisor_of_mul`), and the `(m-1)`-power
is not the indicator (`zmod6_fermat_fails`).  So each prime-power factor `MOD_{pᵢ^{eᵢ}}` from the CRT decomposition is
low-degree only over its *own* characteristic-`pᵢ` field, and no single field serves all factors — the two-fields
barrier, now stated at the ring level.  Crossing it (Toda's symmetric representation over `ℤ`) is the `NEXP`-strength
frontier of Williams' method, **not** established here.  This file makes the obstruction concrete; it is not a proof that
`MOD_m ∉ ACC⁰` or anything of `NEXP ⊄ ACC⁰` / `P ≠ NP` strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.CompositeMod

/-- **The `MOD_m` gate is a `ZMod m` zero-test (proved)**: `modZero m k = decide ((k : ZMod m) = 0)` — the gate lives in
the ring `ZMod m`. -/
theorem modZero_eq_zmod (m k : ℕ) : modZero m k = decide ((k : ZMod m) = 0) := by
  rw [modZero, decide_eq_decide]
  exact (CharP.cast_eq_zero_iff (ZMod m) m k).symm

/-- **The ring-level two-fields barrier (proved)**: for `m = a·b` with `a, b ≥ 2`, `ZMod m` has nonzero zero divisors
(the images of `a` and `b`), so it is not an integral domain — the Fermat nonzero-indicator gadget has no analogue. -/
theorem zmod_zero_divisor_of_mul {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (a : ZMod (a * b)) ≠ 0 ∧ (b : ZMod (a * b)) ≠ 0 ∧
      (a : ZMod (a * b)) * (b : ZMod (a * b)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Ne, CharP.cast_eq_zero_iff (ZMod (a * b)) (a * b) a]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    nlinarith
  · rw [Ne, CharP.cast_eq_zero_iff (ZMod (a * b)) (a * b) b]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    nlinarith
  · rw [← Nat.cast_mul]
    exact (CharP.cast_eq_zero_iff (ZMod (a * b)) (a * b) (a * b)).mpr (dvd_refl _)

/-- **The canonical `ZMod 6` zero divisors (proved)**: `2, 3 ≠ 0` yet `2·3 = 0`. -/
theorem zmod6_zero_divisor : (2 : ZMod 6) ≠ 0 ∧ (3 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) * 3 = 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The Fermat indicator fails at `m = 6` (proved)**: `2^{6-1} = 2 ≠ 1`, so `(·)^{m-1}` is not the nonzero-indicator
over `ZMod 6` (contrast `fermatInd` over a prime field). -/
theorem zmod6_fermat_fails : (2 : ZMod 6) ^ 5 ≠ 1 := by decide

end PallLean.Paper93.DeepMath.PathB.CompositeMod

#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.modZero_eq_zmod
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.zmod_zero_divisor_of_mul
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.zmod6_fermat_fails
