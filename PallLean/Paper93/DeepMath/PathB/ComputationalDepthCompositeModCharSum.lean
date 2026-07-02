import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompositeModRing

/-!
# Composite `MOD_m`: the character-sum (roots-of-unity) representation — Toda's escape from the barrier

Rung 2 pinned the obstruction: `ZMod m` has zero divisors for composite `m`, so the Fermat gadget `(·)^{m-1}` (the RS
nonzero-indicator, valid only over a field) has no analogue.  Toda's device to get *past* this is to leave `ZMod m`
entirely and work over a ring that **does** have a primitive `m`-th root of unity — e.g. `ℂ` (or `ℤ[ω]`), which has one
for **every** `m`, composite included.  There the `MOD_m` indicator has a clean low-order representation:

  `charSum_eq` — **PROVED**: for a primitive `m`-th root `ζ` in any field, `∑_{j<m} ζ^{j·k} = m·[m ∣ k]` — a character
        sum that is `m` when `m ∣ k` and `0` otherwise (geometric-sum / roots-of-unity cancellation).
  `charSum_indicator` — **PROVED, the representation**: `m⁻¹ · ∑_{j<m} ζ^{j·k} = [m ∣ k]` — the `MOD_m` zero-indicator as
        a normalised character sum, **valid for composite `m`** where the `ZMod m` Fermat gadget fails.
  `charSum_eq_complex` / `charSum_indicator_complex` — **PROVED**: the concrete instance over `ℂ` with `ζ = e^{2πi/m}`,
        available for every `m ≥ 1` (so, in particular, for composite `m` like `6`).

## Honest scope — the escape device, not the full lifting

This is exactly the ingredient the `ZMod m` barrier (rung 2) forces: representing `MOD_m` over a field with roots of unity
rather than `ZMod m`.  The character sum works uniformly for prime and composite `m` — that is Toda's escape.  What this
does **not** do is the hard part: this representation has order `m-1` in `ζ`, and `ζ^k = ζ^{∑ xᵢ} = ∏ᵢ ζ^{xᵢ}` is a
degree-`n` multilinear polynomial in the bits — so composing character-sum representations through a depth-`d` `ACC⁰[m]`
circuit while keeping the total ℤ-degree quasipolynomial (the actual Beigel–Tarui / Williams construction) is the
`NEXP`-strength step, **not** established here.  This file supplies the roots-of-unity representation of a single `MOD_m`
gate — the device that crosses the ring barrier — and states honestly that the circuit-level lifting remains open.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CompositeMod

open Finset

/-- **The character sum (proved)**: for a primitive `m`-th root of unity `ζ` in a field, `∑_{j<m} ζ^{j·k}` is `m` if
`m ∣ k` and `0` otherwise — the roots-of-unity cancellation underlying the Toda representation. -/
theorem charSum_eq {K : Type*} [Field K] {m : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ m) (k : ℕ) :
    ∑ j ∈ Finset.range m, ζ ^ (j * k) = if m ∣ k then (m : K) else 0 := by
  have hrw : ∀ j, ζ ^ (j * k) = (ζ ^ k) ^ j := fun j => by rw [mul_comm, pow_mul]
  simp only [hrw]
  by_cases hk : m ∣ k
  · rw [if_pos hk, (hζ.pow_eq_one_iff_dvd k).mpr hk]
    simp
  · rw [if_neg hk]
    have hz1 : ζ ^ k ≠ 1 := fun h => hk ((hζ.pow_eq_one_iff_dvd k).mp h)
    rw [geom_sum_eq hz1]
    have hpm : (ζ ^ k) ^ m = 1 := by rw [← pow_mul, mul_comm k m, pow_mul, hζ.pow_eq_one, one_pow]
    rw [hpm]; simp

/-- **The `MOD_m` indicator as a normalised character sum (proved)**: `m⁻¹ · ∑_{j<m} ζ^{j·k} = [m ∣ k]` — valid for
composite `m`, where the `ZMod m` Fermat gadget fails. -/
theorem charSum_indicator {K : Type*} [Field K] {m : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    (hm : (m : K) ≠ 0) (k : ℕ) :
    (m : K)⁻¹ * ∑ j ∈ Finset.range m, ζ ^ (j * k) = if m ∣ k then 1 else 0 := by
  rw [charSum_eq hζ]
  by_cases hk : m ∣ k
  · rw [if_pos hk, if_pos hk, inv_mul_cancel₀ hm]
  · rw [if_neg hk, if_neg hk, mul_zero]

/-- **The concrete `ℂ` character sum (proved)**: with `ζ = e^{2πi/m}`, available for every `m ≥ 1` — in particular for
composite `m`. -/
theorem charSum_eq_complex {m : ℕ} (hm : m ≠ 0) (k : ℕ) :
    ∑ j ∈ Finset.range m, (Complex.exp (2 * Real.pi * Complex.I / m)) ^ (j * k)
      = if m ∣ k then (m : ℂ) else 0 :=
  charSum_eq (Complex.isPrimitiveRoot_exp m hm) k

/-- **The concrete `ℂ` `MOD_m` indicator (proved)**: valid for every `m ≥ 1`, composite included (e.g. `m = 6`). -/
theorem charSum_indicator_complex {m : ℕ} (hm : m ≠ 0) (k : ℕ) :
    (m : ℂ)⁻¹ * ∑ j ∈ Finset.range m, (Complex.exp (2 * Real.pi * Complex.I / m)) ^ (j * k)
      = if m ∣ k then 1 else 0 :=
  charSum_indicator (Complex.isPrimitiveRoot_exp m hm) (by exact_mod_cast hm) k

end PallLean.Paper93.DeepMath.PathB.CompositeMod

#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.charSum_eq
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.charSum_indicator
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.charSum_indicator_complex
