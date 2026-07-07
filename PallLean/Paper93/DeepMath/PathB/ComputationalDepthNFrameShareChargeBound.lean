import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConeAmplify

/-!
# N-Frame: the per-share RATIO bound does not close the cross-branch — the ABSOLUTE bound does

The proposed finishing target `ramanujan_share_gate_double_charge` (every cross-cone share adds `≥ 2`
cone-excess, i.e. `savings ≤ coneExcess/2`) was pressure-tested against the dichotomy arithmetic.
Outcome: a constant per-share RATIO bound provably does NOT close the middle regime — it only shifts
the low edge by that constant.  The bound that DOES close it is ABSOLUTE: `savings ≤ cN`.

## The refutation of the ratio target

`half_charge_does_not_close` — **PROVED**: there exist `(length, cbudgetFk, coneExcess, ess, savings,
cN)` satisfying all three dichotomy inputs — disjoint-deficit `2·cbudgetFk + cN ≤ length + savings`,
ledger `2·ess + coneExcess ≤ length + 1`, AND the per-share `≥ 2` bound `2·savings ≤ coneExcess` — yet
`length + 1 < 2·cbudgetFk` (the `2×` bound FAILS).  Witness `(150, 100, 102, 0, 51, 1)`.  So even with
`savings ≤ coneExcess/2` the direct sum can fail: `ramanujan_share_gate_double_charge` is NOT a
finishing lemma.

Why: `savings ≤ coneExcess/c` extends the low (disjoint) regime only to `coneExcess ≤ c·cN`; the
band `c·cN < coneExcess < 2·cbudgetFk − 2·ess` survives for every constant `c` once `cbudgetFk` is
large — which it is (it grows with `k`).

## The correct target — the absolute bound

`absolute_savings_bound_closes` — **PROVED**: if cross-cone sharing saves at most the mixer's fresh
capacity, `savings ≤ cN`, then the disjoint-deficit alone gives `2·cbudgetFk ≤ length` — the full
`2×`, with no case split and no ledger needed.

So the live finishing statement is not a per-share ratio; it is the ABSOLUTE

    total cross-cone sharing saving  ≤  cN

i.e. the sharing between the two sibling computations cannot save more length than the mixer's fresh
`cN` coupling.  Intuition: the only structure `F_k(x_L)` and `F_k(x_R)` share (disjoint inputs) is the
function `F_k` itself, and the sibling reuse must route through the mixer's `cN`-dimensional coupling
— so the saving is capped by `cN`, not by the incidental cone-excess.

## Honest scope — target corrected, not closed

This is a genuine correction: the per-share ratio bound the plan named would not finish the proof
(refuted here), and the finishing target is the absolute `savings ≤ cN`.  That absolute bound IS the
cross-branch direct sum in its sharpest form — it is the KRW-hard content, and it is NOT proved here.
What is proved: the ratio bound is insufficient, the absolute bound suffices, so the search should aim
at `savings ≤ cN` (a routing-capacity statement about the mixer) rather than at per-gate fan-out.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameShareChargeBound

/-- **THE RATIO BOUND DOES NOT CLOSE IT (proved)**: a witness satisfying disjoint-deficit, ledger, and
the per-share `≥ 2` bound `2·savings ≤ coneExcess`, yet with the `2×` bound `length + 1 < 2·cbudgetFk`
failing.  So `savings ≤ coneExcess/2` is insufficient to close the cross-branch. -/
theorem half_charge_does_not_close :
    ∃ (length cbudgetFk coneExcess ess savings cN : ℕ),
      2 * cbudgetFk + cN ≤ length + savings ∧
      2 * ess + coneExcess ≤ length + 1 ∧
      2 * savings ≤ coneExcess ∧
      length + 1 < 2 * cbudgetFk :=
  ⟨150, 100, 102, 0, 51, 1, by omega, by omega, by omega, by omega⟩

/-- **THE ABSOLUTE BOUND CLOSES IT (proved)**: if cross-cone sharing saves at most the mixer's fresh
capacity `savings ≤ cN`, then the disjoint-deficit `2·cbudgetFk + cN ≤ length + savings` alone yields
`2·cbudgetFk ≤ length` — the full `2×` direct-sum bound. -/
theorem absolute_savings_bound_closes (length cbudgetFk savings cN : ℕ)
    (hdisjoint : 2 * cbudgetFk + cN ≤ length + savings)
    (habs : savings ≤ cN) :
    2 * cbudgetFk ≤ length := by
  omega

/-- **THE RATIO BAND, GENERALLY (proved)**: for any per-share ratio `c ≥ 1`, the low regime the ratio
closes reaches only `coneExcess ≤ c · cN`; the surviving band starts at `c · cN`.  Formally: a witness
with `c · savings ≤ coneExcess`, disjoint-deficit, ledger, and failing `2×` exists whenever
`cbudgetFk` exceeds `c · cN` (here shown by scaling the base witness). -/
theorem ratio_band_survives (c : ℕ) (hc : 1 ≤ c) :
    ∃ (length cbudgetFk coneExcess ess savings cN : ℕ),
      2 * cbudgetFk + cN ≤ length + savings ∧
      2 * ess + coneExcess ≤ length + 1 ∧
      c * savings ≤ coneExcess ∧
      length + 1 < 2 * cbudgetFk :=
  ⟨4 * c, 2 * c + 1, 3 * c, 0, 3, 1, by omega, by omega, by omega, by omega⟩

end PallLean.Paper93.DeepMath.PathB.NFrameShareChargeBound

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameShareChargeBound.half_charge_does_not_close
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameShareChargeBound.absolute_savings_bound_closes
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameShareChargeBound.ratio_band_survives
