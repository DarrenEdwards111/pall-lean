import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CharWitness
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ParityBarrier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqWitness

/-!
# Brick (MOD_q Fourier) — the character decomposition of the Boolean `MOD_q` indicator (proved)

The structural heart of the Boolean `MOD_q` indicator: for `ζ` a primitive `q`-th root of unity in `F_p` (which exists when
`q ∣ p−1`), the discrete Fourier / geometric-sum identity gives

  `bv(MOD_q x) = q⁻¹ · ∑_{j<q} charWt_{ζʲ}(x)`,

expressing `[q ∣ weight]` as the average of the `q` characters `charWt_{ζʲ} = (ζʲ)^{weight}` (Brick char witness).  This is
exactly the decomposition underlying `MOD_q`'s degree: applying the sign-functional `Dsign` (which detects each character via
`Dsign(charWt_ζ) = (1−ζ)ⁿ`) yields `Dsign(MOD_q) = q⁻¹ · ∑_{j<q} (1−ζʲ)ⁿ` — the top coefficient whose nonvanishing drives the
conditional separation (Brick MOD_q indicator).

## What is proved (clean axioms, no `sorry`)

* **`charWt_eq_pow`** (PROVED) — `charWt ζ x = ζ^{weight(x)}`.
* **`modq_fourier`** (PROVED) — `(bv(modqFn q x) : F_p) = q⁻¹ · ∑_{j<q} charWt (ζ^j) x` (for `orderOf ζ = q`, `q` invertible).
* **`Dsign_modq`** (PROVED) — `∑ₓ signWt x · bv(modqFn q x) = q⁻¹ · ∑_{j<q} (1−ζ^j)^n`.

## Honest scope

The exact character decomposition of the Boolean `MOD_q` indicator (the structural identity).  It takes `ζ` (a primitive
`q`-th root, `orderOf ζ = q`) and `q` invertible as hypotheses (both hold when `q ∣ p−1`), and does **not** prove the
top-coefficient nonvanishing for all large `n` (the RS rank bound) nor the Williams cash-out.  General YBT and `NEXP ⊄ ACC⁰`
remain open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModqFourier

open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityWitness (signWt)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier (wt)
open PallLean.Paper93.DeepMath.PathB.ACC0CharWitness (charWt Dsign_charWt)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqWitness (modqFn)

variable {n p : ℕ} [Fact p.Prime]

/-- **`charWt ζ x = ζ^{weight(x)}` (PROVED).** -/
theorem charWt_eq_pow (ζ : ZMod p) (x : Fin n → Bool) : charWt ζ x = ζ ^ (wt x) := by
  unfold charWt wt
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]

/-- **The discrete-Fourier identity for the `MOD_q` indicator (PROVED).** -/
theorem modq_fourier (q : ℕ) (hq : (q : ZMod p) ≠ 0) (ζ : ZMod p) (hord : orderOf ζ = q)
    (x : Fin n → Bool) :
    (bv (modqFn q x) : ZMod p) = (q : ZMod p)⁻¹ * ∑ j ∈ Finset.range q, charWt (ζ ^ j) x := by
  have hsum : (∑ j ∈ Finset.range q, charWt (ζ ^ j) x) = if q ∣ wt x then (q : ZMod p) else 0 := by
    have hpow : ∀ j, charWt (ζ ^ j) x = (ζ ^ wt x) ^ j := by
      intro j; rw [charWt_eq_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [Finset.sum_congr rfl (fun j _ => hpow j)]
    by_cases hd : q ∣ wt x
    · have hz : ζ ^ wt x = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hord]; exact hd)
      rw [hz, if_pos hd]; simp
    · have hne : ζ ^ wt x ≠ 1 := fun h => hd (hord ▸ orderOf_dvd_iff_pow_eq_one.mpr h)
      rw [geom_sum_eq hne q, if_neg hd, show (ζ ^ wt x) ^ q = 1 by
        rw [← pow_mul, Nat.mul_comm, pow_mul, ← hord, pow_orderOf_eq_one, one_pow], sub_self, zero_div]
  rw [hsum]
  by_cases hd : q ∣ wt x
  · rw [if_pos hd, inv_mul_cancel₀ hq]; simp [bv, modqFn, hd]
  · rw [if_neg hd, mul_zero]; simp [bv, modqFn, hd]

/-- **`Dsign(MOD_q) = q⁻¹ · ∑_{j<q} (1−ζ^j)^n` (PROVED).** -/
theorem Dsign_modq (q : ℕ) (hq : (q : ZMod p) ≠ 0) (ζ : ZMod p) (hord : orderOf ζ = q) :
    (∑ x : Fin n → Bool, signWt p x * (bv (modqFn q x) : ZMod p))
      = (q : ZMod p)⁻¹ * ∑ j ∈ Finset.range q, (1 - ζ ^ j) ^ n := by
  rw [Finset.sum_congr rfl (fun x _ => by rw [modq_fourier q hq ζ hord x])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Dsign_charWt (ζ ^ j), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => by ring)

/-!
**The `MOD_q` Fourier decomposition, proved.**  `[q ∣ weight] = q⁻¹ ∑_{j<q} charWt_{ζʲ}`, so `Dsign(MOD_q) = q⁻¹ ∑_{j<q}
(1−ζʲ)ⁿ` — the exact top coefficient, whose nonvanishing (Brick MOD_q indicator) gives `MOD_q ∉` constant-depth `AC⁰[p]`.
Remaining (open, not faked): nonvanishing for all large `n` (RS rank bound), Williams cash-out.  Not `NEXP ⊄ ACC⁰`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModqFourier

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModqFourier.modq_fourier
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModqFourier.Dsign_modq
