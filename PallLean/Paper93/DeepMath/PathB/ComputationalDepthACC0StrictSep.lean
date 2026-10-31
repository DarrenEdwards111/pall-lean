import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ParityAC0

/-!
# Bridge (AC⁰ ⊊ AC⁰[2]) — the constant-depth hierarchy is strict at this level (proved)

The classes `AC⁰` and `AC⁰[2]` are genuinely different: `MOD` gates add power.  `PARITY` is computed by a single `MOD_2`
gate (`parity_mem_acc02`) — so it lies in `AC⁰[2]` at depth `1` — yet `PARITY ∉ AC⁰` (`parity_not_ac0`).  Hence
`AC⁰ ⊊ AC⁰[2]` (`ac0_strict_subset_acc02`).

## What is proved (clean axioms, no `sorry`)

* **`mod2_cast_eq_one`** (PROVED) — `(n : ZMod 2) = 1 ↔ Odd n`.
* **`eval_mod2_univ`** (PROVED) — the single gate `MOD_2` over all inputs computes `PARITY`.
* **`parity_mem_acc02`** (PROVED) — `PARITY` is computed by a depth-`1` `AC⁰[2]` circuit.
* **`ac0_strict_subset_acc02`** (PROVED) — `PARITY ∈ AC⁰[2] \ AC⁰` (for `n > 2^{d+1}`), witnessing `AC⁰ ⊊ AC⁰[2]`.

## Honest scope

This is the strict separation `AC⁰ ⊊ AC⁰[2]` — the `MOD`-gate hierarchy is strict here — a clean consequence of
`PARITY ∈ AC⁰[2]` and `PARITY ∉ AC⁰`.  The **Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different, P≠NP-strength theorem and
remains **open** / not faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0StrictSep

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit depth)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier (parityFn wt)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityAC0 (ModFree parity_not_ac0)
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (weightOn modQStatOn)

/-- **`(n : ZMod 2) = 1 ↔ Odd n` (PROVED).** -/
theorem mod2_cast_eq_one (n : ℕ) : ((n : ZMod 2) = 1) ↔ Odd n := by
  rw [← Nat.cast_one (R := ZMod 2), ZMod.natCast_eq_natCast_iff, Nat.odd_iff]
  unfold Nat.ModEq
  omega

/-- **A single `MOD_2` gate over all inputs computes `PARITY` (PROVED).** -/
theorem eval_mod2_univ {n : ℕ} :
    ACC0CircuitModel.eval (.mod 2 (Finset.univ : Finset (Fin n)) 1) = parityFn := by
  funext x
  have hwt : weightOn (Finset.univ : Finset (Fin n)) x = wt x := by
    rw [weightOn, wt, Finset.card_filter]
  simp only [ACC0CircuitModel.eval, modQStatOn, parityFn]
  apply decide_eq_decide.mpr
  rw [hwt]
  exact mod2_cast_eq_one (wt x)

/-- **`PARITY ∈ AC⁰[2]` at depth `1` (PROVED).** -/
theorem parity_mem_acc02 {n : ℕ} :
    ∃ C : ACC0Circuit n, ModpOnly 2 C ∧ depth C ≤ 1 ∧ ACC0CircuitModel.eval C = parityFn :=
  ⟨.mod 2 Finset.univ 1, rfl, le_refl 1, eval_mod2_univ⟩

/-- **`AC⁰ ⊊ AC⁰[2]` (PROVED).**  `PARITY` lies in `AC⁰[2]` (depth-`1`) but not in `AC⁰` (for `n > 2^{d+1}`) — so `MOD`
gates strictly increase the power of constant-depth circuits. -/
theorem ac0_strict_subset_acc02 {n d : ℕ} (hd : 2 * 2 ^ d < n) :
    (∃ C : ACC0Circuit n, ModpOnly 2 C ∧ depth C ≤ 1 ∧ ACC0CircuitModel.eval C = parityFn) ∧
      ¬ ∃ C : ACC0Circuit n, ModFree C ∧ depth C ≤ d ∧ ACC0CircuitModel.eval C = parityFn :=
  ⟨parity_mem_acc02, parity_not_ac0 hd⟩

/-!
**`AC⁰ ⊊ AC⁰[2]`, proved.**  `PARITY` separates the two classes — a single `MOD_2` gate computes it, but no `AC⁰` circuit
does.  Remaining (open, not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0StrictSep

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0StrictSep.ac0_strict_subset_acc02
