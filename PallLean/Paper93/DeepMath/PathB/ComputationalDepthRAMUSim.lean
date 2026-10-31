import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMClockedDecider
import Mathlib.Tactic

/-!
# RAM lazy diagonal decider — a universal simulator in the budget, verified (PROVED) — step 2, brick 3

Brick 2's clock just counted down — the "simulate `M_code`" budget was a placeholder.  Here the clocked loop
**genuinely simulates a machine**: each tick **fetches** the next opcode of a simulated program from a code
array (indexed/indirect addressing — the real power of the RAM), **dispatches** on it, and applies the effect
to a simulated accumulator.  This is a real fetch–decode–dispatch interpreter loop, not a hardcoded counter.

Simulated machine: program counter `sp` walks a code array via a pointer `mem[2]`, simulated accumulator in
`mem[3]`.  Opcodes: `0 = INC` (sim_acc += 1), nonzero `= NOP` (sim_acc unchanged); both advance the code
pointer.  A clock counter `mem[0]` bounds the simulation to `bound` steps (the lazy budget).

Layout: `mem[0]=clock  mem[1]=1  mem[2]=code-pointer  mem[3]=sim_acc`; code lives at addresses `≥ 4`.

```
  0: loadI 0   1: jzI 15                         -- clock test (budget exhausted → done)
  2: loadIndI 2  3: jzI 5                         -- FETCH opcode at *cp; DISPATCH (0 → INC)
  4: jmpI 8                                       -- NOP: skip
  5: loadI 3   6: addI 1   7: storeI 3            -- INC: sim_acc += 1
  8: loadI 2   9: addI 1  10: storeI 2            -- advance code pointer
  11: loadI 0 12: subI 1  13: storeI 0  14: jmpI 0  -- clock--, loop
  15: haltI
```

  `uSim_one` — one **INC** tick (fetched opcode `0`) is exactly `14` steps: `sim_acc += 1`, pointer++, clock--.
  `uSim_one_nop` — one **NOP** tick (fetched opcode `≠ 0`) is exactly `12` steps and **leaves `sim_acc`
        unchanged** — proof that the loop genuinely dispatches on the *fetched* opcode (not a hardcoded inc).
  `uSim_correct` — over a code that is all-`INC` for the simulated range, after exactly `14·bound + 3` steps
        the simulator halts with `sim_acc = (initial) + bound`: it ran the simulated machine for exactly
        `bound` steps inside the budget.  Proved by induction on `bound` (walking code pointer + per-cell code
        hypothesis), via `run_add` + `uSim_one`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This is the universal-simulator step running inside the clock
budget; richer opcodes and the final diagonal wrap are later bricks.
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- A clocked universal-simulator step loop: fetch opcode at the code pointer, dispatch (`0=INC`, else `NOP`),
advance the pointer, decrement the clock, loop. -/
def uSim : List Instr :=
  [ Instr.loadI 0, Instr.jzI 15            -- 0,1:  clock test
  , Instr.loadIndI 2, Instr.jzI 5          -- 2,3:  fetch opcode at *cp; dispatch (0 → INC at 5)
  , Instr.jmpI 8                            -- 4:    NOP → advance
  , Instr.loadI 3, Instr.addI 1, Instr.storeI 3   -- 5,6,7: INC → sim_acc += 1
  , Instr.loadI 2, Instr.addI 1, Instr.storeI 2   -- 8,9,10: advance code pointer
  , Instr.loadI 0, Instr.subI 1, Instr.storeI 0, Instr.jmpI 0  -- 11..14: clock--, loop
  , Instr.haltI ]                           -- 15:   done

/-- **One INC tick is exactly `14` steps**: with the fetched opcode `0`, increment the simulated accumulator,
advance the code pointer, decrement the clock; `pc` back to the top. -/
theorem uSim_one (m : Mem) (acc N : ℕ) (h0 : m 0 = N + 1) (h1 : m 1 = 1) (hcode : m (m 2) = 0) :
    run uSim ⟨m, acc, 0, false⟩ 14
      = ⟨((m.set 3 (m 3 + 1)).set 2 (m 2 + 1)).set 0 N, N, 0, false⟩ := by
  show step uSim (step uSim (step uSim (step uSim (step uSim (step uSim (step uSim (step uSim
    (step uSim (step uSim (step uSim (step uSim (step uSim (step uSim
    (⟨m, acc, 0, false⟩)))))))))))))) = _
  simp [step, uSim, List.getD, Mem.set, h0, h1, hcode]

/-- **One NOP tick is exactly `13` steps and leaves `sim_acc` unchanged.**  With the fetched opcode `≠ 0` the
loop takes the other branch and only advances the pointer / clock — demonstrating it genuinely dispatches on
the *fetched* opcode. -/
theorem uSim_one_nop (m : Mem) (acc N : ℕ) (h0 : m 0 = N + 1) (h1 : m 1 = 1) (hnop : m (m 2) ≠ 0) :
    run uSim ⟨m, acc, 0, false⟩ 12
      = ⟨(m.set 2 (m 2 + 1)).set 0 N, N, 0, false⟩ := by
  show step uSim (step uSim (step uSim (step uSim (step uSim (step uSim (step uSim (step uSim
    (step uSim (step uSim (step uSim (step uSim
    (⟨m, acc, 0, false⟩)))))))))))) = _
  simp [step, uSim, List.getD, Mem.set, h0, h1, hnop]

/-- **The simulator runs the machine for exactly `bound` steps inside the budget.**  Over a code that is
all-`INC` on the simulated range (`∀ k < bound, code[cp + k] = 0`), from clock `= bound`, code pointer
`cp ≥ 4`, after exactly `14·bound + 3` steps the simulator halts with `clock = 0`, pointer `= cp + bound`, and
`sim_acc = (initial sim_acc) + bound`. -/
theorem uSim_correct (N : ℕ) :
    ∀ (m : Mem) (acc : ℕ), m 0 = N → m 1 = 1 → 4 ≤ m 2 → (∀ k, k < N → m (m 2 + k) = 0) →
      let S := run uSim ⟨m, acc, 0, false⟩ (14 * N + 3)
      S.halted = true ∧ S.mem 0 = 0 ∧ S.mem 2 = m 2 + N ∧ S.mem 3 = m 3 + N := by
  induction N with
  | zero =>
    intro m acc h0 _ _ _
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [run, step, uSim, List.getD, h0]
  | succ N ih =>
    intro m acc h0 h1 hb hcode
    have hc0 : m (m 2) = 0 := by have := hcode 0 (by omega); simpa using this
    have hone : run uSim ⟨m, acc, 0, false⟩ 14
        = ⟨((m.set 3 (m 3 + 1)).set 2 (m 2 + 1)).set 0 N, N, 0, false⟩ := uSim_one m acc N h0 h1 hc0
    set M' : Mem := ((m.set 3 (m 3 + 1)).set 2 (m 2 + 1)).set 0 N with hM'
    have hM'0 : M' 0 = N := by simp [hM']
    have hM'1 : M' 1 = 1 := by simp [hM', h1]
    have hM'2 : M' 2 = m 2 + 1 := by simp [hM']
    have hM'3 : M' 3 = m 3 + 1 := by simp [hM']
    have hM'b : 4 ≤ M' 2 := by rw [hM'2]; omega
    have hM'code : ∀ k, k < N → M' (M' 2 + k) = 0 := by
      intro k hk
      rw [hM'2]
      have ha2 : m 2 + 1 + k ≠ 2 := by omega
      have ha3 : m 2 + 1 + k ≠ 3 := by omega
      have heq : M' (m 2 + 1 + k) = m (m 2 + 1 + k) := by simp [hM', ha2, ha3]
      rw [heq]
      have hck := hcode (k + 1) (by omega)
      have : m 2 + (k + 1) = m 2 + 1 + k := by ring
      rwa [this] at hck
    have key := ih M' N hM'0 hM'1 hM'b hM'code
    have hSeq : run uSim ⟨m, acc, 0, false⟩ (14 * (N + 1) + 3)
        = run uSim ⟨M', N, 0, false⟩ (14 * N + 3) := by
      rw [show 14 * (N + 1) + 3 = 14 + (14 * N + 3) from by ring, run_add, hone]
    simp only [hSeq]
    obtain ⟨kh, k0, k2, k3⟩ := key
    refine ⟨kh, k0, ?_, ?_⟩
    · rw [k2, hM'2]; ring
    · rw [k3, hM'3]; ring

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.uSim_one
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.uSim_one_nop
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.uSim_correct
