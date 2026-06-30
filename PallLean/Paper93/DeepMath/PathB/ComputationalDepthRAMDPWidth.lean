import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMDP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMWidth
import Mathlib.Tactic

/-!
# RAM memo DP — toward discharging the width invariant (the cost lemma's hypothesis)

`dpLoop_runCost_le` takes `∀ k < 13N+3, WidthBounded dpLoop (run … k) W` as a hypothesis (the program-specific
obligation).  This file isolates exactly the hard part of discharging it.

`WidthBounded` is three conjuncts: `bitlen acc ≤ W`, `∀x bitlen (mem x) ≤ W`, `∀i∈prog, instrWidth i ≤ W`.  The
first two follow from a *value* bound (`acc ≤ V`, `∀x mem x ≤ V`) with `bitlen V ≤ W` via `bitlen` monotonicity —
that is `widthBounded_of_value_le` here.  The third is constant for `dpLoop` (its operands are `0,1,2,3,13`, so
`≤ 4`) — that is `dpLoop_instrWidth` here.

So the *whole* width invariant reduces to a single **value bound**: `∀ k < 13N+3, (run … k).acc ≤ V ∧ ∀x …mem x ≤ V`
for some `V` with `bitlen V ≤ W`.

**Honest note on why that value bound is hard (not the easy lemma it looks like).**  One might hope each step
raises every value by `≤ 1`, giving `value ≤ V₀ + k`.  It does *not* hold in general: `addI a` computes
`acc := acc + mem a` (the value *at address* `a`, not the literal), so a single `addI` can roughly *double* a value.
For `dpLoop` the adds are `addI 1`, and `mem 1 = 1` throughout — but `mem 1 = 1` is only preserved because the
indirect store `storeIndI 2` (which writes `mem[mem 2]`) never targets address `1`, i.e. `mem 2 ≠ 1`; and `mem 2`
stays `≥ 4` only because at `storeI 2` the accumulator equals `pointer+1 ≥ 5`.  Establishing those relationships is
exactly the pc-indexed exact-state tracking that `dpLoop_correct` performs — so the value bound is a
`dpLoop_correct`-strength obligation, not a one-line induction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.BitCost (bitlen bitlen_mono)

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- **Value bound ⇒ width bound.**  If accumulator and every memory cell are `≤ V` and `bitlen V ≤ W` (and the
program's operands fit in `W`), the state is `W`-width-bounded — by `bitlen` monotonicity.  This is the reusable
interface: any value bound `≤ V` with `bitlen V ≤ W` discharges the two value-dependent `WidthBounded` conjuncts. -/
theorem widthBounded_of_value_le (prog : List Instr) (s : State) (V W : ℕ)
    (hacc : s.acc ≤ V) (hmem : ∀ x, s.mem x ≤ V) (hV : bitlen V ≤ W)
    (hprog : ∀ i ∈ prog, instrWidth i ≤ W) : WidthBounded prog s W :=
  ⟨le_trans (bitlen_mono hacc) hV, fun x => le_trans (bitlen_mono (hmem x)) hV, hprog⟩

/-- **`dpLoop`'s operands fit in 4 bits.**  Every instruction operand of `dpLoop` is one of `0,1,2,3,13`, so its
`instrWidth` (`= bitlen`) is `≤ 4` (`bitlen 13 = 4`).  This discharges the third `WidthBounded` conjuct for `dpLoop`
at any width `W ≥ 4`. -/
theorem dpLoop_instrWidth : ∀ i ∈ dpLoop, instrWidth i ≤ 4 := by decide

/-- **The width invariant, reduced to the value bound.**  Given a value bound `V` holding at step `k` (with
`bitlen V ≤ W`, `4 ≤ W`), the state is `W`-width-bounded.  So discharging `dpLoop_runCost_le`'s hypothesis is
*exactly* establishing the value bound `∀ k < 13N+3, (run … k).acc ≤ V ∧ ∀x …mem x ≤ V` — the remaining
(`dpLoop_correct`-strength) obligation. -/
theorem dpLoop_widthBounded_of_value_le (s : State) (V W : ℕ)
    (hacc : s.acc ≤ V) (hmem : ∀ x, s.mem x ≤ V) (hV : bitlen V ≤ W) (hW : 4 ≤ W) :
    WidthBounded dpLoop s W :=
  widthBounded_of_value_le dpLoop s V W hacc hmem hV
    (fun i hi => le_trans (dpLoop_instrWidth i hi) hW)

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.widthBounded_of_value_le
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.dpLoop_instrWidth
