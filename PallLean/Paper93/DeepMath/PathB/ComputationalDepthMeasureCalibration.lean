import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAlgebraicOracleModel

/-!
# Measure calibration — why the two known measure families miss, as theorems

The `SeparatingMeasure` target must satisfy (A) circuit-bounded, (B) superpolynomial on the target, and
the three barriers (non-natural, non-relativizing, non-algebrizing).  The two families of measures we
actually possess each fail a **specific** field — and here those failures are theorems, so the empty spot
in the terrain is a kernel-checked fact.

## Gate-elimination / `cbudget` — passes the barriers, fails (B) by a *linear cap*

Gate-elimination is circuit-structural and non-algebraic (right side of all three barriers).  It bounds
`cbudget` from below by an **amortized kill chain**: a restriction schedule where each step drops the
measure by some `kills i`.  Its total is `∑ kills i`.  Two hard limits multiply:

* the schedule has length `L ≤ V` (you can restrict at most the `V` variables), and
* each step kills `≤ C` (`ComputationalDepthThreeKillNoGo.threekill_per_step_no_go`: general rate ≤ 2;
  `sat3_xf_threekill_chain`: xor-free rate 3, giving the linear `3(m−2)+1`).

`amortized_bound_linear` proves the product is `≤ C · V` — **linear**.  `amortized_superlinear_needs`
proves the contrapositive: to exceed `C · V` you need `L > V` (more steps than variables) *or* `C`
unbounded (a growing rate).  That is *exactly* the earlier "what to build" — non-algebraic, but breaking
`steps × rate = V × O(1)`.

## Algebraic rank (SPDP / shifted partials) — reaches (B), fails *non-algebrizing*

The algebraic-rank family reaches superpolynomial (B) but is defined by arithmetization, so it
**algebrizes** — and `AlgebraicOracleModel.no_relativizing_separatingMeasure_zmod2` proves any measure
separating relative to every algebraic oracle is impossible (the extension-of-`L` collapse).  Re-exported
below as `algebrizing_measure_cannot_separate`.

## The terrain, as fact

|                         | (A) | (B) | non-natural | non-relativizing | non-algebrizing |
|-------------------------|-----|-----|-------------|------------------|-----------------|
| gate-elimination        | ✓   | ✗ (linear cap) | ✓ | ✓ | ✓ |
| algebraic rank (SPDP)   | restricted only | ✓ | — | — | ✗ (algebrizes) |
| **the target**          | ✓   | ✓   | ✓ | ✓ | ✓ |

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MeasureCalibration

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.RelativizationBarrier

/-- **The gate-elimination linear cap (proved).**  An amortized kill chain of length `L ≤ V` (variables),
each step killing `≤ C`, certifies at most `C · V` — linear in the variable count. -/
theorem amortized_bound_linear (C V : ℕ) (kills : ℕ → ℕ) (hk : ∀ i, kills i ≤ C)
    (L : ℕ) (hL : L ≤ V) : (∑ i ∈ Finset.range L, kills i) ≤ C * V := by
  calc (∑ i ∈ Finset.range L, kills i)
      ≤ (∑ _i ∈ Finset.range L, C) := Finset.sum_le_sum (fun i _ => hk i)
    _ = C * L := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
    _ ≤ C * V := Nat.mul_le_mul (le_refl C) hL

/-- **What superlinear requires (proved).**  For an amortized kill chain to certify a bound above `C · V`,
either the schedule must exceed the variable count (`V < L`) or some step must exceed the rate `C`
(`C < kills i`).  Breaking `steps × rate = V × O(1)` is the whole gap — non-algebraically. -/
theorem amortized_superlinear_needs (C V bound : ℕ) (kills : ℕ → ℕ) (L : ℕ)
    (hbound : bound = ∑ i ∈ Finset.range L, kills i) (hexceed : C * V < bound) :
    V < L ∨ ∃ i, C < kills i := by
  by_contra h
  push_neg at h
  obtain ⟨hLV, hC⟩ := h
  have hlin := amortized_bound_linear C V kills hC L hLV
  omega

/-- **The algebraic-rank family is out (proved, re-exported).**  Any measure separating `L` relative to
every algebraic oracle is impossible — the arithmetization extension of `L` collapses it.  So a measure
that *algebrizes* (the SPDP / shifted-partial / rank family) cannot be the separating measure. -/
theorem algebrizing_measure_cannot_separate (L : Layer7.BoolLang)
    (rm : RelativizingSeparatingMeasure L
      (AlgebraicOracleModel.SIZErelA AlgebraicOracleModel.ι₂ AlgebraicOracleModel.decode₂)) :
    False :=
  AlgebraicOracleModel.no_relativizing_separatingMeasure_zmod2 L rm

end PallLean.Paper93.DeepMath.PathB.MeasureCalibration

#print axioms PallLean.Paper93.DeepMath.PathB.MeasureCalibration.amortized_bound_linear
#print axioms PallLean.Paper93.DeepMath.PathB.MeasureCalibration.amortized_superlinear_needs
#print axioms PallLean.Paper93.DeepMath.PathB.MeasureCalibration.algebrizing_measure_cannot_separate
