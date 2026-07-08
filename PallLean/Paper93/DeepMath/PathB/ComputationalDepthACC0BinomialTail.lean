import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SmolenskyPrime

/-!
# The binomial tail — discharging the last mechanical residual of the prime Smolensky route

The prime-modulus Razborov–Smolensky lower bound (`ACC0SmolenskyPrime.no_small_approximator`) was closed
*modulo* one honest numeric hypothesis, the **binomial tail**
`htail : lowDegreeDim n D' < 2ⁿ − E` (with `lowDegreeDim n D' = ∑_{i≤D'} C(n,i)`), kept as a socket because
it "looked like" a Chernoff/normal-tail estimate on the partial binomial sum. This file **proves it**, and
plugs it in.

The observation that removes the estimate: the tail is bounded below by its own *largest omitted term*.
Since `∑_{i=0}^{n} C(n,i) = 2ⁿ`, the degree-`≤ D'` sum satisfies

  `lowDegreeDim n D' + C(n, D'+1) = lowDegreeDim n (D'+1) < 2ⁿ`   (for `D'+1 < n`),

directly from the already-proved weak dimension bound `ACC0NonNativeDegree.lowDegreeDim_lt_two_pow` plus
`Finset.sum_range_succ`. Hence `lowDegreeDim n D' < 2ⁿ − E` for **any** `E ≤ C(n, D'+1)`. At the Smolensky
parameter regime `D' = n/2 + D` with `D = O(√n)`, the slack `C(n, n/2+D+1)` is the central-binomial scale
`≈ 2ⁿ/√n` — so this dominates the small `E` the argument actually uses. No Chernoff bound, no anti-
concentration; the estimate was a corollary of the dimension count all along.

## What is proved (clean axioms, no `sorry`)

* `lowDegreeDim_add_choose_succ_lt` — `K+1 < n ⇒ lowDegreeDim n K + C(n,K+1) < 2ⁿ`.
* `binomial_tail_lt` — `D'+1 < n`, `E ≤ C(n,D'+1) ⇒ lowDegreeDim n D' < 2ⁿ − E`  (the socketed `htail`).
* `lowDegreeDim_midpoint_tail_lt` — the same at the Smolensky window `D' = n/2 + D`, exhibiting the explicit
  central-binomial slack `E ≤ C(n, n/2+D+1)`.
* `no_small_approximator_of_tail_bound` — `ACC0SmolenskyPrime.no_small_approximator` with `htail`
  **discharged**: the prime lower bound now needs only degree-halving + a large good set + `E ≤ C(n,D'+1)`.

## Honest scope

This closes the last *mechanical* residual of the **prime** (`p` odd prime) Smolensky route; the prime-case
`PARITY / MOD_q ∉ AC⁰[p]` engine is the genuine classical circuit lower bound it feeds. It does **not**
touch the composite-modulus `CarryRefinementCrossing` wall (the real open frontier), the Williams
`NEXP ⊄ ACC⁰` sockets (`beigelTarui_faithful`, `williams_decider_in_NEXP`), or the `Circ` recursion.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BinomialTail

open PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree (lowDegreeDim lowDegreeDim_lt_two_pow)
open PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPigeonhole (SmolenskyDegreeHalving)
open PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyPrime (no_small_approximator)

/-- **The omitted top term is a tail lower bound (PROVED).**  Adding the next binomial coefficient to the
degree-`≤ K` dimension gives the degree-`≤ K+1` dimension, still strictly below `2ⁿ` when `K+1 < n`:
`lowDegreeDim n K + C(n, K+1) = lowDegreeDim n (K+1) < 2ⁿ`.  Reuses the proved weak bound
`lowDegreeDim_lt_two_pow`. -/
theorem lowDegreeDim_add_choose_succ_lt {n K : ℕ} (h : K + 1 < n) :
    lowDegreeDim n K + n.choose (K + 1) < 2 ^ n := by
  have e : lowDegreeDim n (K + 1) = lowDegreeDim n K + n.choose (K + 1) := by
    simp only [lowDegreeDim]
    rw [Finset.sum_range_succ]
  rw [← e]
  exact lowDegreeDim_lt_two_pow h

/-- **The binomial tail (PROVED) — the socketed `htail`.**  For any error slack `E` no larger than the
central omitted term `C(n, D'+1)`, the degree-`≤ D'` dimension is below `2ⁿ − E`.  This is exactly the
hypothesis `ACC0SmolenskyPrime.no_small_approximator` took on faith. -/
theorem binomial_tail_lt {n D' E : ℕ} (hn : D' + 1 < n) (hE : E ≤ n.choose (D' + 1)) :
    lowDegreeDim n D' < 2 ^ n - E := by
  have h := lowDegreeDim_add_choose_succ_lt (n := n) (K := D') hn
  omega

/-- **The tail at the Smolensky window (PROVED).**  At `D' = n/2 + D` (the degree-halving output, `D = O(√n)`),
the explicit slack is the central-binomial coefficient `C(n, n/2+D+1) ≈ 2ⁿ/√n`. -/
theorem lowDegreeDim_midpoint_tail_lt {n D E : ℕ} (hn : n / 2 + D + 1 < n)
    (hE : E ≤ n.choose (n / 2 + D + 1)) :
    lowDegreeDim n (n / 2 + D) < 2 ^ n - E :=
  binomial_tail_lt hn hE

/-- **The prime lower bound with the tail discharged (PROVED).**  `ACC0SmolenskyPrime.no_small_approximator`
with its `htail` hypothesis removed and replaced by the proved binomial tail: under degree-halving and a
large good set (`2ⁿ − E ≤ |G|`), there is no degree-`D'`, `≤ E`-error approximator of the symmetric target,
provided the error slack fits the central omitted term (`E ≤ C(n, D'+1)`, `D'+1 < n`).  No numeric socket. -/
theorem no_small_approximator_of_tail_bound {F : Type} [Field F] {n D' E : ℕ}
    (G : Finset (Fin n → Bool))
    (hhalving : SmolenskyDegreeHalving (F := F) (D' := D') G)
    (hGsize : 2 ^ n - E ≤ G.card)
    (hn : D' + 1 < n) (hE : E ≤ n.choose (D' + 1)) : False :=
  no_small_approximator G hhalving hGsize (binomial_tail_lt hn hE)

end PallLean.Paper93.DeepMath.PathB.ACC0BinomialTail

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BinomialTail.lowDegreeDim_add_choose_succ_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BinomialTail.binomial_tail_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BinomialTail.lowDegreeDim_midpoint_tail_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BinomialTail.no_small_approximator_of_tail_bound
