import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaModGate

/-!
# `MOD_p` over a layer of representations — the count composes (PROVED)

The across-depth assembly's composition rung.  `ACC0TodaModGate` represented a single `MOD_p` gate on an
*integer count* `y`.  Here the count is itself the sum of **subcircuit representations**: given
subcircuit values `g i` that represent `{0,1}` outputs `b i` modulo `p` (`p ∣ g i − b i`), the count
`Y = ∑ g i` satisfies `Y ≡ ∑ b i (mod p)`, so `p ∣ Y ↔ p ∣ ∑ b i` — the `MOD_p` decision **transfers
from the representations to the true accepting-count**.

  `todaMod_compose` — `p^{2^k} ∣ (A^{[k]}(1 − (∑ g i)^{p−1}) − [p ∣ ∑ b i])`: the `MOD_p` gate over the
  representation layer is represented (mod `p^{2^k}`) by the Toda iterate of the count's Fermat indicator,
  and its value is the gate's true output `[p ∣ ∑ b i]`.

So a `MOD_p` gate stacked over a layer whose subcircuits are each Toda-represented mod `p` is itself
Toda-represented mod `p^{2^k}` — the count flows through the layer.  This is one depth step of the
integer-route across-depth assembly.

## What is proved (clean axioms, no `sorry`)

* `todaMod_compose` — the `MOD_p`-over-representation-layer composition (value-level, divisibility transfer
  + Toda amplification).

## Honest scope

This is the *value-level* count composition for **one** `MOD_p` layer: the count's divisibility transfers
from the reps to the true outputs, then `A^{[k]}` amplifies.  The full across-depth assembly still needs:
the reps `g i` produced as polynomials with a consistent modulus across depth (each subcircuit's own
`p^{2^k_i}` reconciled), the degree bookkeeping stacked, and `AND`/`OR` layers handled.  That is the
Beigel–Tarui integer construction body, not built here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaModCompose

open PallLean.Paper93.DeepMath.PathB.ACC0TodaModGate (todaMod_amplifies)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaIterate (todaAmpIter)

variable {ι : Type*}

/-- **`MOD_p` over a representation layer (proved).**  If each `g i ≡ b i (mod p)` (the subcircuit
representations), then `A^{[k]}(1 − (∑ g i)^{p−1})` represents the `MOD_p` gate's true output
`[p ∣ ∑ b i]` modulo `p^{2^k}`.  The count's `MOD_p` decision transfers from the reps to the accepting
count (`p ∣ ∑ g i ↔ p ∣ ∑ b i`), then `A^{[k]}` amplifies the Fermat indicator. -/
theorem todaMod_compose (p : ℕ) [Fact p.Prime] (k : ℕ) (g b : ι → ℤ) (s : Finset ι)
    (hgb : ∀ i, (p : ℤ) ∣ (g i - b i)) :
    (p : ℤ) ^ (2 ^ k) ∣
      (todaAmpIter k (1 - (∑ i ∈ s, g i) ^ (p - 1))
        - (if (p : ℤ) ∣ (∑ i ∈ s, b i) then (1 : ℤ) else 0)) := by
  have hY : (p : ℤ) ∣ ((∑ i ∈ s, g i) - (∑ i ∈ s, b i)) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.dvd_sum (fun i _ => hgb i)
  have hdvd_iff : ((p : ℤ) ∣ ∑ i ∈ s, g i) ↔ ((p : ℤ) ∣ ∑ i ∈ s, b i) := by
    constructor
    · intro h
      have h2 := dvd_sub h hY
      rwa [show (∑ i ∈ s, g i) - ((∑ i ∈ s, g i) - (∑ i ∈ s, b i)) = ∑ i ∈ s, b i from by ring] at h2
    · intro h
      have h2 := dvd_add h hY
      rwa [show (∑ i ∈ s, b i) + ((∑ i ∈ s, g i) - (∑ i ∈ s, b i)) = ∑ i ∈ s, g i from by ring] at h2
  have htoda := todaMod_amplifies p (∑ i ∈ s, g i) k
  have heq : (if (p : ℤ) ∣ (∑ i ∈ s, g i) then (1 : ℤ) else 0)
      = (if (p : ℤ) ∣ (∑ i ∈ s, b i) then 1 else 0) := by
    by_cases h : (p : ℤ) ∣ (∑ i ∈ s, b i)
    · rw [if_pos (hdvd_iff.mpr h), if_pos h]
    · rw [if_neg (fun hg => h (hdvd_iff.mp hg)), if_neg h]
  rwa [heq] at htoda

/-!
**`MOD_p`-over-layer composition proved.**  The accepting count flows through one `MOD_p` layer: reps
`≡ b i (mod p)` give `p ∣ ∑ g i ↔ p ∣ ∑ b i`, and `A^{[k]}` lifts the count's Fermat indicator to
modulus `p^{2^k}`.  Stacking this across depth with consistent moduli/degrees and the `AND`/`OR` layers
is the remaining Beigel–Tarui integer-construction wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TodaModCompose

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TodaModCompose.todaMod_compose
