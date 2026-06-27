import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMSimDecider
import Mathlib.Tactic

/-!
# RAM bit-cost — discharging the width invariant via value bounds (PROVED) — step 3

The cost bound `runCost_width_le` charges every step `≤ 3W + 1` bits *given* that the reached states stay
`W`-bit-width-bounded.  Left as an abstract hypothesis, that bit-width bound is the one place a hidden
unit-cost assumption could sneak in.  This file discharges it down to the **physical** quantity it really is:
the magnitudes of the values the machine holds.  A state is `W`-bit-width-bounded as soon as every value
(accumulator + memory cells) is `≤ V` with `bitlen V ≤ W` and the program's operands fit in `W` bits.  So the
bit-cost is genuinely `poly` exactly when the stored values stay `poly`-bounded — no unit-cost cheating.

Provided here, all reusable:

* `ValueBounded` and `widthBounded_of_valueBounded` — a value bound `V` with `bitlen V ≤ W` (and operands `≤ W`)
  gives bit-width-boundedness.
* `runCost_value_le` — hence the run cost is `≤ n·(3W + 1)` once every reached state is value-bounded by `V`.
* `step_mem_le` — **unconditional**: one step never writes any value to memory other than the current
  accumulator, so a value bound on `(acc, mem)` is preserved by memory on the next step.
* `step_acc_le` — the next accumulator is bounded by `V` under explicit, *local* side conditions on the current
  instruction (a `constI` literal `≤ V`; an `addI`'s `acc + operand ≤ V`; a `loadIndI`'s target `≤ V`).  These
  are the only ways a step can grow a value, made explicit.
* `step_valueBounded` — combining the two: `ValueBounded` is preserved by one step under those side conditions.
* `simDecider_instrWidth_le` — the concrete operand-width fact for the integrated decider (`≤ 6` bits).

This is the honest reduction: the remaining obligation for any concrete program is a *value* bound on its
reachable states (a poly magnitude bound), not an abstract width hypothesis.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.BitCost (bitlen bitlen_mono)

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- A state is value-bounded by `V`: accumulator and every memory cell have magnitude `≤ V`. -/
def ValueBounded (s : State) (V : ℕ) : Prop := s.acc ≤ V ∧ ∀ x, s.mem x ≤ V

/-- A value bound `V` with `bitlen V ≤ W`, plus operands `≤ W` bits, gives bit-width-boundedness. -/
theorem widthBounded_of_valueBounded (prog : List Instr) (s : State) (W V : ℕ)
    (hV : bitlen V ≤ W) (hops : ∀ i ∈ prog, instrWidth i ≤ W) (h : ValueBounded s V) :
    WidthBounded prog s W :=
  ⟨le_trans (bitlen_mono h.1) hV, fun x => le_trans (bitlen_mono (h.2 x)) hV, hops⟩

/-- **Bit-cost from a value bound.**  If every reached state is value-bounded by `V`, `bitlen V ≤ W`, and the
operands fit in `W` bits, then the `n`-step run costs `≤ n·(3W + 1)` bits.  The width hypothesis of
`runCost_width_le` is thereby reduced to a concrete magnitude bound on the reachable values. -/
theorem runCost_value_le (prog : List Instr) (s : State) (n W V : ℕ)
    (hV : bitlen V ≤ W) (hops : ∀ i ∈ prog, instrWidth i ≤ W)
    (h : ∀ k, k < n → ValueBounded (run prog s k) V) :
    runCost prog s n ≤ n * (3 * W + 1) :=
  runCost_width_le prog s n W (fun k hk =>
    widthBounded_of_valueBounded prog (run prog s k) W V hV hops (h k hk))

/-- **Memory never grows past the accumulator.**  A single step writes to memory only the current accumulator
(via `storeI`/`storeIndI`); every other instruction leaves memory unchanged.  So if `acc ≤ V` and all cells
are `≤ V`, all cells of the next state are `≤ V` — unconditionally. -/
theorem step_mem_le (prog : List Instr) (s : State) (V : ℕ)
    (hacc : s.acc ≤ V) (hmem : ∀ x, s.mem x ≤ V) (x : ℕ) :
    (step prog s).mem x ≤ V := by
  unfold step
  split
  · exact hmem x
  · split <;>
      first
      | exact hmem x
      | · simp only [Mem.set]
          split
          · exact hacc
          · exact hmem x

/-- **The next accumulator is bounded by `V`** under the only side conditions that can let a step grow it: a
`constI` literal `≤ V`, an `addI`'s `acc + operand ≤ V`, a `loadIndI`'s target value `≤ V`.  Every other
instruction copies an already-bounded value or shrinks (`subI`). -/
theorem step_acc_le (prog : List Instr) (s : State) (V : ℕ)
    (hacc : s.acc ≤ V) (hmem : ∀ x, s.mem x ≤ V)
    (hconst : ∀ v, prog.getD s.pc Instr.haltI = Instr.constI v → v ≤ V)
    (hadd : ∀ a, prog.getD s.pc Instr.haltI = Instr.addI a → s.acc + s.mem a ≤ V)
    (hind : ∀ a, prog.getD s.pc Instr.haltI = Instr.loadIndI a → s.mem (s.mem a) ≤ V) :
    (step prog s).acc ≤ V := by
  unfold step
  split
  · exact hacc
  · rename_i heq
    split <;> rename_i hi
    · exact hconst _ hi
    · exact hmem _
    · exact hacc
    · exact hind _ hi
    · exact hacc
    · exact hadd _ hi
    · exact le_trans (Nat.sub_le _ _) hacc
    · exact hacc
    · exact hacc
    · exact hacc

/-- **`ValueBounded` is preserved by one step** under the (local) growth side conditions. -/
theorem step_valueBounded (prog : List Instr) (s : State) (V : ℕ)
    (h : ValueBounded s V)
    (hconst : ∀ v, prog.getD s.pc Instr.haltI = Instr.constI v → v ≤ V)
    (hadd : ∀ a, prog.getD s.pc Instr.haltI = Instr.addI a → s.acc + s.mem a ≤ V)
    (hind : ∀ a, prog.getD s.pc Instr.haltI = Instr.loadIndI a → s.mem (s.mem a) ≤ V) :
    ValueBounded (step prog s) V :=
  ⟨step_acc_le prog s V h.1 h.2 hconst hadd hind, step_mem_le prog s V h.1 h.2⟩

/-- **Operand widths of the integrated decider are `≤ 6` bits** (its largest operand is the jump target `34`,
and `34 < 2^6`).  This discharges the operand hypothesis of `runCost_value_le` for `simDecider` at any
`W ≥ 6`. -/
theorem simDecider_instrWidth_le : ∀ i ∈ simDecider, instrWidth i ≤ 6 := by
  intro i hi
  have hb : ∀ n : ℕ, n < 64 → bitlen n ≤ 6 := by
    intro n hn; rw [bitlen, Nat.size_le]; simpa using hn
  fin_cases hi <;> simp only [instrWidth] <;> first | omega | (apply hb; norm_num)

/-- **Bit-cost of the integrated decider from a value bound.**  For any `W ≥ 6` with `bitlen V ≤ W`, if every
state reached in the first `n` steps of `simDecider` keeps all values `≤ V`, then those `n` steps cost
`≤ n·(3W + 1)` bits.  The operand-width hypothesis is discharged (`≤ 6`); the only remaining obligation is the
concrete value bound `V` on the reachable magnitudes — exactly the physical quantity, no hidden unit cost.

For the **complement** branch this is unconditional given a bounded input: those `14` steps execute no `addI`
and no `loadIndI` and write only the constants `0,1` and the shrunk value `1 - inp`, so `step_valueBounded`'s
side conditions hold and the value bound is the input bound.  For the **copy** branch the value bound is
`V = code-base + bound + 1` (pointer, clock, and `sim_acc` never exceed it), the remaining program-specific
magnitude obligation. -/
theorem simDecider_runCost_le (m : Mem) (acc n W V : ℕ)
    (hV : bitlen V ≤ W) (hW : 6 ≤ W)
    (hbound : ∀ k, k < n → ValueBounded (run simDecider ⟨m, acc, 0, false⟩ k) V) :
    runCost simDecider ⟨m, acc, 0, false⟩ n ≤ n * (3 * W + 1) :=
  runCost_value_le simDecider ⟨m, acc, 0, false⟩ n W V hV
    (fun i hi => le_trans (simDecider_instrWidth_le i hi) hW) hbound

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.runCost_value_le
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.step_mem_le
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.step_acc_le
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.step_valueBounded
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_instrWidth_le
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_runCost_le
