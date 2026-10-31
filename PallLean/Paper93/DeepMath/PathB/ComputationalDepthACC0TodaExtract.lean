import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaModGate

/-!
# Exact extraction over a common modulus — the across-depth reconciliation seed (PROVED)

The Toda amplification rungs deliver `≡ b (mod p^{2^k})`; to *compose across depth* the reps must become
**exact `{0,1}` values over one modulus**.  The reconciliation: pick a **uniform** `k` for the whole
circuit (against the max count = circuit size `s`, so `p^{2^k} > s`), giving a common modulus
`M = p^{2^k}`; then over `ZMod M` each rep is its exact `{0,1}` output, and the per-gate moduli no longer
diverge.

  `toda_extract` — divisibility `M ∣ (V − b)` ⇒ exact equality `(V : ZMod M) = (b : ZMod M)`.
  `todaMod_extract` — the `MOD_p` gate: `(A^{[k]}(1 − y^{p−1}) : ZMod (p^{2^k})) = [p ∣ y]` — the exact
  `{0,1}` value over the common modulus, with no residual error.

So over the common `ZMod (p^{2^k})`, the Toda representation of a `MOD_p` gate **is** its Boolean output
exactly — the composable form needed to stack `MOD` layers across depth.

## What is proved (clean axioms, no `sorry`)

* `toda_extract` — divisibility ⇒ exact `ZMod` equality (the extraction bridge).
* `todaMod_extract` — the `MOD_p` gate's exact `{0,1}` value over `ZMod (p^{2^k})`.

## Honest scope

This is the *extraction* that turns the `mod p^{2^k}` amplification into an exact `ZMod (p^{2^k})` value,
and the *uniform-`k`* observation that makes one modulus serve every gate.  The full across-depth
assembly still needs: the reps produced as polynomials, the count of one layer fed as the next layer's
`y` over the same `ZMod M`, the degree stacked (`(3^k(p−1))^d`), and the `AND`/`OR` layers.  That is the
Beigel–Tarui integer construction body, not built here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaExtract

open PallLean.Paper93.DeepMath.PathB.ACC0TodaModGate (todaMod_amplifies)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaIterate (todaAmpIter)

/-- **Exact extraction (proved): `M ∣ (V − b) ⇒ (V : ZMod M) = (b : ZMod M)`.**  Turns an amplified
congruence into an exact value over `ZMod M`. -/
theorem toda_extract {M : ℕ} {V b : ℤ} (h : (M : ℤ) ∣ (V - b)) :
    (V : ZMod M) = (b : ZMod M) := by
  have h0 : ((V : ZMod M) - (b : ZMod M)) = 0 := by
    rw [← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
  exact sub_eq_zero.mp h0

/-- **The `MOD_p` gate's exact `{0,1}` value over the common modulus (proved).**  Over `ZMod (p^{2^k})`,
the Toda representation `A^{[k]}(1 − y^{p−1})` equals the gate's Boolean output `[p ∣ y]` exactly. -/
theorem todaMod_extract (p : ℕ) [Fact p.Prime] (y : ℤ) (k : ℕ) :
    ((todaAmpIter k (1 - y ^ (p - 1)) : ℤ) : ZMod (p ^ (2 ^ k)))
      = (((if (p : ℤ) ∣ y then (1 : ℤ) else 0) : ℤ) : ZMod (p ^ (2 ^ k))) := by
  refine toda_extract ?_
  have h := todaMod_amplifies p y k
  push_cast
  push_cast at h
  convert h using 2

/-!
**Exact extraction proved.**  Over the common modulus `ZMod (p^{2^k})` (uniform `k`, `p^{2^k} >` the
circuit-wide max count), the Toda representation of a `MOD_p` gate is exactly its Boolean output — the
composable form for stacking `MOD` layers across depth.  The full polynomial across-depth assembly (count
flow + degree stacking + `AND`/`OR`) is the remaining Beigel–Tarui integer-construction wall.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TodaExtract

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TodaExtract.todaMod_extract
