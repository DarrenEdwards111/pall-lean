import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMModel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostModel
import Mathlib.Tactic

/-!
# RAM machine model — bit-cost (PROVED)

Each RAM step is charged by the **bit-lengths** of the addresses/values it touches (not their magnitude), so a
memory read/write is `O(bit-width)` — the property `Code.evaln` fuel lacks.  `stepCost` gives the per-step
bit-cost; `runCost` sums it over a run; `runCost_le` bounds an `n`-step run by `n · C` when every step costs
`≤ C` — **polynomial** in the step count and the per-step bit-width.

This is the RAM analogue of the abstract flat-DP cost (`buildReadCost`/`buildArithCost`); here it is realised
by an actual machine with addressable memory, so the memo table genuinely lives in memory rather than in one
blowing-up `Nat`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.BitCost (bitlen)

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- **Bit-cost of one step**: charged by the bit-lengths of the addresses/values touched (memory access is
cheap in bits — magnitude is irrelevant). -/
def stepCost (prog : List Instr) (s : State) : ℕ :=
  if s.halted then 0 else
  match prog.getD s.pc Instr.haltI with
  | .constI v    => bitlen v + 1
  | .loadI a     => bitlen a + bitlen (s.mem a) + 1
  | .storeI a    => bitlen a + bitlen s.acc + 1
  | .loadIndI a  => bitlen a + bitlen (s.mem a) + bitlen (s.mem (s.mem a)) + 1
  | .storeIndI a => bitlen a + bitlen (s.mem a) + bitlen s.acc + 1
  | .addI a      => bitlen s.acc + bitlen (s.mem a) + 1
  | .subI a      => bitlen s.acc + bitlen (s.mem a) + 1
  | .jzI t       => bitlen t + bitlen s.acc + 1
  | .jmpI t      => bitlen t + 1
  | .haltI       => 1

/-- Total bit-cost of running `n` steps. -/
def runCost (prog : List Instr) (s : State) : ℕ → ℕ
  | 0 => 0
  | k + 1 => stepCost prog s + runCost prog (step prog s) k

/-- **The RAM bit-cost over `n` steps is `≤ n · C`** when every step costs `≤ C` — polynomial in the number of
steps and the per-step bit-width. -/
theorem runCost_le (prog : List Instr) (s : State) (n C : ℕ)
    (h : ∀ k, k < n → stepCost prog (run prog s k) ≤ C) :
    runCost prog s n ≤ n * C := by
  induction n generalizing s with
  | zero => simp [runCost]
  | succ n ih =>
    have hhead : stepCost prog s ≤ C := by
      have := h 0 (by omega); simpa [run] using this
    have htail : runCost prog (step prog s) n ≤ n * C := by
      apply ih
      intro k hk
      have := h (k + 1) (by omega)
      simpa [run_succ] using this
    calc runCost prog s (n + 1) = stepCost prog s + runCost prog (step prog s) n := rfl
      _ ≤ C + n * C := by omega
      _ = (n + 1) * C := by ring

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.runCost_le
