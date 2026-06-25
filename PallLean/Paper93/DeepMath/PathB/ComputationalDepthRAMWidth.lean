import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMCost
import Mathlib.Tactic
import Mathlib.Data.List.GetD

/-!
# RAM machine model — the per-step width bound (PROVED)

A `W`-width-bounded state has accumulator, every memory cell, and every instruction operand of bit-length
`≤ W`.  Then each step costs `≤ 3W + 1` (`stepCost_le`) — every instruction touches at most three values, each
`≤ W` bits.  Maintained over an `n`-step run, the total bit-cost is `≤ n·(3W+1)` (`runCost_width_le`),
**polynomial** in the step count and the width.

This is the machine-level statement that the RAM runs in poly bit-cost as long as the bit-width stays
bounded — exactly the regime of the bit-bounded class (`ComputationalDepthBitCostBounded`).  Maintaining the
width invariant for a *specific* program (the memo DP) is the program-specific obligation, supplied as the
hypothesis here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.BitCost (bitlen)

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- Bit-length of an instruction's literal operand. -/
def instrWidth : Instr → ℕ
  | .constI v => bitlen v
  | .loadI a => bitlen a
  | .storeI a => bitlen a
  | .loadIndI a => bitlen a
  | .storeIndI a => bitlen a
  | .addI a => bitlen a
  | .subI a => bitlen a
  | .jzI t => bitlen t
  | .jmpI t => bitlen t
  | .haltI => 0

/-- A state/program is `W`-width-bounded: accumulator, every memory cell, and every instruction operand have
bit-length `≤ W`. -/
def WidthBounded (prog : List Instr) (s : State) (W : ℕ) : Prop :=
  bitlen s.acc ≤ W ∧ (∀ x, bitlen (s.mem x) ≤ W) ∧ (∀ i ∈ prog, instrWidth i ≤ W)

/-- The current instruction's operand width is `≤ W`. -/
theorem current_instr_width (prog : List Instr) (pc W : ℕ) (h : ∀ i ∈ prog, instrWidth i ≤ W) :
    instrWidth (prog.getD pc Instr.haltI) ≤ W := by
  by_cases hpc : pc < prog.length
  · rw [List.getD_eq_getElem prog Instr.haltI hpc]
    exact h _ (List.getElem_mem hpc)
  · rw [List.getD_eq_default prog Instr.haltI (by omega)]
    simp [instrWidth]

/-- **Per-step bit-cost under a width bound: `stepCost ≤ 3W + 1`.**  Every instruction touches `≤ 3` values,
each of bit-length `≤ W`. -/
theorem stepCost_le (prog : List Instr) (s : State) (W : ℕ) (h : WidthBounded prog s W) :
    stepCost prog s ≤ 3 * W + 1 := by
  obtain ⟨hacc, hmem, hops⟩ := h
  have hop := current_instr_width prog s.pc W hops
  unfold stepCost
  by_cases hh : s.halted = true
  · rw [if_pos hh]; omega
  · rw [if_neg hh]
    split <;> rename_i heq <;> rw [heq] at hop <;> simp only [instrWidth] at hop
    · omega
    · have := hmem ‹ℕ›; omega
    · omega
    · have := hmem ‹ℕ›; have := hmem (s.mem ‹ℕ›); omega
    · have := hmem ‹ℕ›; omega
    · have := hmem ‹ℕ›; omega
    · have := hmem ‹ℕ›; omega
    · omega
    · omega
    · omega

/-- **Run-level bit-cost under a maintained width bound: `runCost ≤ n · (3W+1)`** — polynomial in steps and
width.  The hypothesis is that every reached state stays `W`-width-bounded (a program-specific invariant). -/
theorem runCost_width_le (prog : List Instr) (s : State) (n W : ℕ)
    (h : ∀ k, k < n → WidthBounded prog (run prog s k) W) :
    runCost prog s n ≤ n * (3 * W + 1) :=
  runCost_le prog s n (3 * W + 1) (fun k hk => stepCost_le prog (run prog s k) W (h k hk))

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.runCost_width_le
