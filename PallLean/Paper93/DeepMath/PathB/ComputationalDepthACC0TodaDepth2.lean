import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaModCompose

/-!
# Stacking two `MOD_p` layers via Toda — the depth-2 `MOD∘MOD` representation (PROVED)

The across-depth assembly's stacking rung.  `ACC0TodaModCompose` represented a `MOD_p` gate over a layer
of *generic* representations `g i ≡ b i (mod p)`.  Here the inner layer is itself `MOD_p` gates: each
inner gate is `g i = A^{[k]}(1 − y_i^{p−1})` with `A^{[k]}` representing it `≡ b i = [p ∣ y_i] (mod
p^{2^k})`.  Since `p ∣ p^{2^k}`, this gives `g i ≡ b i (mod p)` — exactly the hypothesis the outer
`todaMod_compose` needs.  So the outer `MOD_p` over the inner `MOD_p` gates is again Toda-represented:

  `toda_depth2` — `p^{2^{k'}} ∣ (A^{[k']}(1 − (∑ A^{[k]}(1 − y_i^{p−1}))^{p−1}) − [p ∣ ∑ [p ∣ y_i]])`:
  the depth-2 `MOD_p∘MOD_p` circuit's value is `[p ∣ ∑ (inner outputs)]`, Toda-represented mod
  `p^{2^{k'}}`.

The amplification composes: the inner reps' `mod p^{2^k}` weakens to `mod p`, feeds the outer count, and
the outer `A^{[k']}` re-amplifies.  This is the depth-2 case of the all-`MOD` tower — the integer route
stacking across depth.

## What is proved (clean axioms, no `sorry`)

* `toda_depth2` — the depth-2 `MOD_p∘MOD_p` Toda representation (value-level).

## Honest scope

This is the depth-2 `MOD∘MOD` stack, value-level.  Iterating to depth `d` (a recursive tower type), the
polynomial/degree form (`(3^k(p−1))^d`), the common-modulus extraction at each level, and the `AND`/`OR`
layers remain — the Beigel–Tarui integer construction body, not built here.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaDepth2

open PallLean.Paper93.DeepMath.PathB.ACC0TodaModCompose (todaMod_compose)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaModGate (todaMod_amplifies)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaIterate (todaAmpIter)

variable {ι : Type*}

/-- **Depth-2 `MOD_p∘MOD_p` via Toda (proved).**  The outer `MOD_p` over inner `MOD_p` gates
`g i = A^{[k]}(1 − y_i^{p−1})` is Toda-represented mod `p^{2^{k'}}`, with value the depth-2 circuit's
output `[p ∣ ∑ [p ∣ y_i]]`.  Each inner rep is `≡ [p ∣ y_i] (mod p^{2^k})`, hence `(mod p)`, feeding the
outer composition. -/
theorem toda_depth2 (p : ℕ) [Fact p.Prime] (k k' : ℕ) (y : ι → ℤ) (s : Finset ι) :
    (p : ℤ) ^ (2 ^ k') ∣
      (todaAmpIter k' (1 - (∑ i ∈ s, todaAmpIter k (1 - (y i) ^ (p - 1))) ^ (p - 1))
        - (if (p : ℤ) ∣ (∑ i ∈ s, (if (p : ℤ) ∣ y i then (1 : ℤ) else 0)) then (1 : ℤ) else 0)) := by
  refine todaMod_compose p k' (fun i => todaAmpIter k (1 - (y i) ^ (p - 1)))
    (fun i => if (p : ℤ) ∣ y i then (1 : ℤ) else 0) s ?_
  intro i
  exact dvd_trans (dvd_pow_self (p : ℤ) (by positivity : (2 : ℕ) ^ k ≠ 0))
    (todaMod_amplifies p (y i) k)

/-!
**Depth-2 `MOD∘MOD` Toda stack proved.**  The integer route composes across one extra `MOD` layer: inner
`mod p^{2^k}` reps weaken to `mod p`, feed the outer count, and `A^{[k']}` re-amplifies — value the true
depth-2 output.  Iterating to depth `d`, the polynomial-degree form, and the `AND`/`OR` layers are the
remaining Beigel–Tarui integer-construction wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TodaDepth2

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TodaDepth2.toda_depth2
