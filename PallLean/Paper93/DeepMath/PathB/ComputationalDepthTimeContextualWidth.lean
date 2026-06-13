import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameBook1Audit

/-!
# A time-sensitive contextual invariant — and an honest attempt at Book-1 axiom A1

The audit (`…NFrameBook1Audit`) located the live wall as **A1**: every poly-time SAT decider has small
contextual width.  It showed the *naive* (time-only) form is refuted by `action_unbounded_by_time` — the raw
action `∑_τ 2^{Bτ}` is unbounded by the step count, because a single step's *capacity* `2^{Bτ}` is arbitrary.
The recommendation was: define a **time-sensitive contextual invariant** finer than raw boundary/action, and try
A1.  This file does exactly that, and reports the outcome without varnish.

## The invariant: cumulative contextual log-width

The fix to the `action_unbounded_by_time` obstruction is to measure **realized distinguishable contexts**, not
raw capacity.  At time `τ` an observer presents a view `views τ : X → Fin W`; the number of contexts it actually
realizes is `contextWidth (views τ) = |image (views τ)|` — bounded by the *input count*, not by `2^{Bτ}`.  The
time-sensitive invariant integrates the log-width over the actual `T` steps:

`tcw views = ∑_{τ < T} log₂ (contextWidth (views τ))`.

Unlike `action`, this is **tied to the realized image** at each step, so it cannot be inflated by a single
high-capacity step against a fixed finite input domain.

## What is proved

* `contextWidth_le_width`, `tcw_le_mul` — `tcw ≤ T · log₂ W`.
* `tcw_le_steps_mul_bits` — over the Boolean cube `Fin n → Bool` with `W ≤ 2^n`: **`tcw ≤ T · n`**.
* **A1 holds for `tcw` (proved):** `tcw_A1_bounded_for_polyTime` — for `T ≤ n^k` the invariant is
  `≤ n^{k+1}`, i.e. *polynomially bounded for every poly-time observer*.  The time-sensitive invariant **does**
  dodge `action_unbounded_by_time`: it is bounded for all of P, which the raw action was not.

## The outcome: A1 succeeds, but the dual wall appears (proved)

* `additive_tcw_below_superpoly_threshold` — **precisely because `tcw` is additive (a sum of log-widths) it is
  capped at `T · n`, which is polynomial; so it can never reach the super-polynomial Book-1 hard-rank threshold
  `n^{log₂ n / 4}`.**  At infinitely many lengths, *every* poly-time observer — including any correct SAT decider
  — has `tcw` strictly below the threshold.  So the Book-1 **A3** lower bound is *false* for `tcw`.

This is the honest result.  Making the contextual invariant **time-sensitive** fixes the obstruction that killed
the raw boundary (A1 becomes a theorem — bounded contextual width for all P).  But the fix is fatal to the *other*
half: an additive/log-width invariant that is bounded for P is bounded for *everything realizable in poly time*,
so it cannot separate the hard family (A3 fails).  The two requirements — **bounded for P (A1)** and
**super-poly on the hard family (A3)** — are in tension for any additive contextual width.

To have both, the invariant must be **super-additive** across the time cut — a *product*/*rank* quantity (the
SPDP / contextual-entanglement-rank route), where the hard family's directions multiply rather than add.  That is
exactly the route whose A1 (poly rank for all of P) is the barriered, assumed-not-derived step
(`…NFrameHypercubeConstraint`, the corpus SPDP audit).  So: a time-sensitive *additive* invariant relocates the
wall from A1 to A3 and proves A3 unmeetable; a *multiplicative* invariant relocates it back to A1.  Either way the
separation is not reached here — and this file proves the additive horn of that dichotomy rather than asserting it.
-/

namespace PallLean.Paper93.DeepMath.PathB.TimeContextualWidth

/-- The number of **distinct contexts** an observer view realizes: the cardinality of its image.  Tied to the
realized outputs (`≤ |X|`), not to raw boundary capacity — this is what dodges `action_unbounded_by_time`. -/
def contextWidth {X : Type*} [Fintype X] {W : ℕ} (view : X → Fin W) : ℕ :=
  (Finset.univ.image view).card

/-- The realized context count is at most the available width `W`. -/
theorem contextWidth_le_width {X : Type*} [Fintype X] {W : ℕ} (view : X → Fin W) :
    contextWidth view ≤ W := by
  unfold contextWidth
  calc (Finset.univ.image view).card
      ≤ (Finset.univ : Finset (Fin W)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = W := by rw [Finset.card_univ, Fintype.card_fin]

/-- **The time-sensitive contextual invariant.**  Cumulative log-width: the sum, over the actual `T` time steps,
of the log of the number of distinct contexts realized at each step. -/
def tcw {X : Type*} [Fintype X] {T W : ℕ} (views : Fin T → X → Fin W) : ℕ :=
  ∑ τ : Fin T, Nat.log 2 (contextWidth (views τ))

/-- **`tcw ≤ T · log₂ W` (proved).**  Each step contributes at most `log₂ W`; there are `T` steps. -/
theorem tcw_le_mul {X : Type*} [Fintype X] {T W : ℕ} (views : Fin T → X → Fin W) :
    tcw views ≤ T * Nat.log 2 W := by
  unfold tcw
  calc ∑ τ : Fin T, Nat.log 2 (contextWidth (views τ))
      ≤ ∑ _τ : Fin T, Nat.log 2 W :=
        Finset.sum_le_sum (fun τ _ => Nat.log_mono_right (contextWidth_le_width (views τ)))
    _ = T * Nat.log 2 W := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- `log₂ W ≤ n` when `W ≤ 2^n`. -/
theorem log_width_le_bits {W n : ℕ} (hW : W ≤ 2 ^ n) : Nat.log 2 W ≤ n := by
  calc Nat.log 2 W ≤ Nat.log 2 (2 ^ n) := Nat.log_mono_right hW
    _ = n := Nat.log_pow (show (1 : ℕ) < 2 by decide) n

/-- **`tcw ≤ T · n` on the Boolean cube (proved).**  With input domain `Fin n → Bool` and width `W ≤ 2^n`, the
cumulative contextual log-width is bounded by `(number of steps) · (input bits)`. -/
theorem tcw_le_steps_mul_bits {n T W : ℕ} (views : Fin T → (Fin n → Bool) → Fin W) (hW : W ≤ 2 ^ n) :
    tcw views ≤ T * n :=
  le_trans (tcw_le_mul views) (Nat.mul_le_mul (le_refl T) (log_width_le_bits hW))

/-- **A1 holds for `tcw` (proved): the time-sensitive invariant is polynomially bounded for every poly-time
observer.**  For a poly-time observer (`T ≤ n^k` steps) on `n` input bits with width `W ≤ 2^n`, the cumulative
contextual width is `≤ n^{k+1}`.  This is the half that the raw action `∑ 2^{Bτ}` *failed*
(`action_unbounded_by_time`): measuring realized contexts instead of capacity makes contextual width bounded for
all of P. -/
theorem tcw_A1_bounded_for_polyTime {n k W : ℕ} (views : Fin (n ^ k) → (Fin n → Bool) → Fin W)
    (hW : W ≤ 2 ^ n) :
    tcw views ≤ n ^ (k + 1) := by
  calc tcw views ≤ n ^ k * n := tcw_le_steps_mul_bits views hW
    _ = n ^ (k + 1) := (pow_succ n k).symm

/-- A local copy of the Book-1 super-polynomial gap: every fixed polynomial degree `d` is eventually beaten by
the calibrated Ramanujan/Tseitin hard-rank exponent `log₂ n / 4`. -/
theorem superpoly_gap (d : ℕ) : ∃ n : ℕ, n ^ d < n ^ (Nat.log 2 n / 4) := by
  refine ⟨2 ^ (4 * (d + 1)), ?_⟩
  rw [Nat.log_pow (by decide : 1 < 2)]
  have hbase : 1 < 2 ^ (4 * (d + 1)) := Nat.one_lt_pow (by omega) (by decide)
  have hexp : d < 4 * (d + 1) / 4 := by omega
  exact Nat.pow_lt_pow_right hbase hexp

/-- **The dual wall (proved): an additive contextual invariant cannot witness the hard lower bound.**  Because
`tcw` is bounded by `T · n` (polynomial for poly-time `T ≤ n^k`), at infinitely many input lengths **every**
poly-time observer — including any correct SAT decider of any width `W ≤ 2^n` — has `tcw` strictly below the
super-polynomial Book-1 threshold `n^{log₂ n / 4}`.  Hence the Book-1 **A3** super-polynomial lower bound is
*false* for `tcw`: making A1 provable (by going time-sensitive and additive) makes A3 unmeetable.  Separation
would require a super-additive (product/rank) invariant, where A1 is the barriered step instead. -/
theorem additive_tcw_below_superpoly_threshold (k : ℕ) :
    ∃ n : ℕ, ∀ (W : ℕ) (views : Fin (n ^ k) → (Fin n → Bool) → Fin W),
      W ≤ 2 ^ n → tcw views < n ^ (Nat.log 2 n / 4) := by
  obtain ⟨n, hgap⟩ := superpoly_gap (k + 1)
  refine ⟨n, fun W views hW => ?_⟩
  exact lt_of_le_of_lt (tcw_A1_bounded_for_polyTime views hW) hgap

end PallLean.Paper93.DeepMath.PathB.TimeContextualWidth

#print axioms PallLean.Paper93.DeepMath.PathB.TimeContextualWidth.tcw_le_steps_mul_bits
#print axioms PallLean.Paper93.DeepMath.PathB.TimeContextualWidth.tcw_A1_bounded_for_polyTime
#print axioms PallLean.Paper93.DeepMath.PathB.TimeContextualWidth.additive_tcw_below_superpoly_threshold
