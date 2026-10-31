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

set_option maxHeartbeats 4000000 in
/-- **Within one active iteration, every value stays `≤ V`.**  From a start state with a live counter
(`m 0 ≠ 0`), `m 1 = 1`, pointer `m 2 ≥ 4`, and bounds `m 2 + 1 ≤ V`, `m 3 + 1 ≤ V`, `acc ≤ V`, `∀x m x ≤ V`, each
of the `13` micro-steps keeps the accumulator and every memory cell `≤ V`.  Proved by evaluating each of the 14
reachable states explicitly (`acc` and `mem` handled separately to avoid blowing up the run-unfolding under `∀x`). -/
theorem dpLoop_iter_values_le (m : Mem) (acc V : ℕ)
    (h0 : m 0 ≠ 0) (h1 : m 1 = 1) (hb : 4 ≤ m 2)
    (hmem : ∀ x, m x ≤ V) (hacc : acc ≤ V) (hp : m 2 + 1 ≤ V) (hv : m 3 + 1 ≤ V) :
    ∀ k, k ≤ 13 → (run dpLoop ⟨m, acc, 0, false⟩ k).acc ≤ V
        ∧ ∀ x, (run dpLoop ⟨m, acc, 0, false⟩ k).mem x ≤ V := by
  have hm0 := hmem 0
  have hm2 := hmem 2
  have hm3 := hmem 3
  have e0 : (0 : ℕ) ≠ m 2 := by omega
  have e1 : (1 : ℕ) ≠ m 2 := by omega
  have e2 : (2 : ℕ) ≠ m 2 := by omega
  have e3 : (3 : ℕ) ≠ m 2 := by omega
  intro k hk
  interval_cases k <;> refine ⟨?_, ?_⟩ <;>
    first
      | (intro x
         simp [run, step, dpLoop, h0, h1, Mem.set,
           e0, e1, e2]
         split_ifs <;> first | exact hmem _ | omega)
      | (simp [run, step, dpLoop, h0, h1, Mem.set,
           e0, e1, e2]
         omega)

set_option maxHeartbeats 4000000 in
/-- **The `dpLoop` value bound.**  From counter `N`, with `m 1 = 1`, pointer `≥ 4`, and `V` dominating the grown
values (`m 2 + N ≤ V`, `m 3 + N ≤ V`) and the initial cells (`acc ≤ V`, `∀x m x ≤ V`), *every* reached state in the
exact `13·N+3`-step run keeps the accumulator and every memory cell `≤ V`.  Induction on `N`: each iteration uses
`dpLoop_iter_values_le` for its `13` micro-steps, then `dpLoop_one` advances to the next iteration's start
(`dpNext`), whose cells are again `≤ V`. -/
theorem dpLoop_values_le (V : ℕ) : ∀ (N : ℕ) (m : Mem) (acc : ℕ),
    m 0 = N → m 1 = 1 → 4 ≤ m 2 → m 2 + N ≤ V → m 3 + N ≤ V → acc ≤ V → (∀ x, m x ≤ V) →
    ∀ k, k ≤ 13 * N + 3 → (run dpLoop ⟨m, acc, 0, false⟩ k).acc ≤ V
        ∧ ∀ x, (run dpLoop ⟨m, acc, 0, false⟩ k).mem x ≤ V := by
  intro N
  induction N with
  | zero =>
    intro m acc h0 h1 _ _ _ hacc hmem k hk
    interval_cases k <;> refine ⟨?_, ?_⟩ <;>
      first
        | (intro x
           simp [run, step, dpLoop, h0]
           exact hmem x)
        | (simp [run, step, dpLoop, h0] <;> omega)
  | succ N ih =>
    intro m acc h0 h1 hb hp hv hacc hmem k hk
    rcases Nat.lt_or_ge k 14 with hk13 | hk13
    · exact dpLoop_iter_values_le m acc V (by omega) h1 hb hmem hacc (by omega) (by omega) k
        (by omega)
    · obtain ⟨k', rfl⟩ : ∃ k', k = 13 + k' := ⟨k - 13, by omega⟩
      have hk' : k' ≤ 13 * N + 3 := by omega
      rw [run_add, dpLoop_one m acc N h0 h1 hb]
      have hdp : ∀ x, dpNext m N x ≤ V := by
        intro x
        by_cases hx0 : x = 0
        · subst hx0; rw [dpNext_0]; omega
        · by_cases hx2 : x = 2
          · subst hx2; rw [dpNext_2]; omega
          · by_cases hx3 : x = 3
            · subst hx3; rw [dpNext_3]; omega
            · by_cases hxb : x = m 2
              · subst hxb; rw [dpNext_base m N hb]; omega
              · rw [dpNext_other m N x hx0 hx2 hx3 hxb]; exact hmem x
      exact ih (dpNext m N) N (dpNext_0 m N) (by rw [dpNext_1 m N hb]; exact h1)
        (by rw [dpNext_2 m N]; omega) (by rw [dpNext_2 m N]; omega) (by rw [dpNext_3 m N]; omega)
        (by omega) hdp k' hk'

/-- **The `dpLoop` width invariant — DISCHARGED.**  With `V` dominating the grown values and `bitlen V ≤ W`
(`4 ≤ W`), every reached state of the `13·N+3`-step run is `W`-width-bounded.  This is exactly the hypothesis
`dpLoop_runCost_le` assumed. -/
theorem dpLoop_maintains_width (m : Mem) (acc V W N : ℕ)
    (h0 : m 0 = N) (h1 : m 1 = 1) (hb : 4 ≤ m 2)
    (hp : m 2 + N ≤ V) (hv : m 3 + N ≤ V) (hacc : acc ≤ V) (hmem : ∀ x, m x ≤ V)
    (hVW : bitlen V ≤ W) (hW : 4 ≤ W) :
    ∀ k, k < 13 * N + 3 → WidthBounded dpLoop (run dpLoop ⟨m, acc, 0, false⟩ k) W := by
  intro k hk
  obtain ⟨hkacc, hkmem⟩ := dpLoop_values_le V N m acc h0 h1 hb hp hv hacc hmem k (by omega)
  exact dpLoop_widthBounded_of_value_le _ V W hkacc hkmem hVW hW

/-- **Unconditional poly bit-cost of the memo DP.**  Discharging the width invariant, the exact `13·N+3`-step run
costs `≤ (13·N+3)·(3W+1)` bits with **no** width hypothesis — only that `W` accommodates the values
(`bitlen V ≤ W`, `V` dominating `m 2 + N`, `m 3 + N`, and the initial cells).  The `dpLoop_runCost_le` socket is
now closed. -/
theorem dpLoop_runCost_unconditional (m : Mem) (acc V W N : ℕ)
    (h0 : m 0 = N) (h1 : m 1 = 1) (hb : 4 ≤ m 2)
    (hp : m 2 + N ≤ V) (hv : m 3 + N ≤ V) (hacc : acc ≤ V) (hmem : ∀ x, m x ≤ V)
    (hVW : bitlen V ≤ W) (hW : 4 ≤ W) :
    runCost dpLoop ⟨m, acc, 0, false⟩ (13 * N + 3) ≤ (13 * N + 3) * (3 * W + 1) :=
  dpLoop_runCost_le m acc N W (dpLoop_maintains_width m acc V W N h0 h1 hb hp hv hacc hmem hVW hW)

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.dpLoop_iter_values_le
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.dpLoop_values_le
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.dpLoop_runCost_unconditional
