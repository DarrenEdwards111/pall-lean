import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMUSim
import Mathlib.Tactic

/-!
# RAM lazy diagonal decider — content-dependent simulation, verified (PROVED) — step 2, brick 5

Brick 3's `uSim` proved the simulator runs `bound` steps, but its correctness theorem was for all-`INC` code:
the simulated output didn't yet depend on *which* program was simulated.  Here the simulator's output genuinely
**depends on the simulated program's content**: each tick fetches the opcode, computes an increment `0/1` from
it, and accumulates, so after `bound` steps `sim_acc = (initial) + (number of INC opcodes in the simulated
prefix)`.  The simulated value is now a real function of the simulated machine's code — exactly what the
diagonal wrap needs (`sim x x` must depend on machine `x`).

The design keeps the **step count uniform** (every tick is `17` steps, whatever the opcode): the dispatch sets
an increment cell to `1` (INC) or `0` (NOP) and the body always adds it.  So the total is a clean
`17·bound + 3`, while the *output* reflects the code.

Layout: `mem[0]=clock mem[1]=1 mem[2]=code-pointer mem[3]=sim_acc mem[4]=incr`; code at addresses `≥ 5`.

```
  0: loadI 0  1: jzI 20                          -- clock test
  2: loadIndI 2  3: jzI 7                         -- FETCH opcode; dispatch (0 → INC at 7)
  4: constI 0  5: storeI 4  6: jmpI 10            -- NOP: incr := 0
  7: constI 1  8: storeI 4  9: jmpI 10            -- INC: incr := 1
  10: loadI 3 11: addI 4 12: storeI 3             -- sim_acc += incr
  13: loadI 2 14: addI 1 15: storeI 2             -- advance code pointer
  16: loadI 0 17: subI 1 18: storeI 0 19: jmpI 0  -- clock--, loop
  20: haltI
```

  `incCount` — number of INC opcodes (`= 0`) in `code[c .. c+n)`.
  `uSim2_one` / `uSim2_one_nop` — one INC / one NOP tick, **both exactly `17` steps**; INC adds `1` to `sim_acc`,
        NOP adds `0` — uniform timing, content-dependent effect.
  `uSim2_count` — from clock `= bound`, code pointer `cp ≥ 5`, after exactly `17·bound + 3` steps the simulator
        halts with `sim_acc = (initial) + incCount code cp bound`: the output is the INC-count of the simulated
        prefix.  Proved by induction on `bound` (`by_cases` on each fetched opcode) via `run_add` + the tick
        lemmas + an `incCount` congruence lemma.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This makes the simulated output content-dependent; the diagonal
wrap and the classical sockets are elsewhere.
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- Number of `INC` opcodes (cells equal to `0`) in `code[c .. c+n)`. -/
def incCount (m : Mem) (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if m c = 0 then 1 else 0) + incCount m (c + 1) n

/-- `incCount` depends only on the code cells it reads: agreement on `code[c .. c+n)` gives equal counts. -/
theorem incCount_congr (m m' : Mem) (n : ℕ) :
    ∀ (c : ℕ), (∀ k, k < n → m (c + k) = m' (c + k)) → incCount m c n = incCount m' c n := by
  induction n with
  | zero => intro c _; rfl
  | succ n ih =>
    intro c h
    have h0 : m c = m' c := by have := h 0 (by omega); simpa using this
    have htail : ∀ k, k < n → m (c + 1 + k) = m' (c + 1 + k) := by
      intro k hk
      have hh := h (k + 1) (by omega)
      have e : c + (k + 1) = c + 1 + k := by ring
      rwa [e] at hh
    show (if m c = 0 then 1 else 0) + incCount m (c + 1) n
        = (if m' c = 0 then 1 else 0) + incCount m' (c + 1) n
    rw [h0, ih (c + 1) htail]

/-- A content-dependent universal-simulator step loop: fetch opcode, set increment `0/1`, accumulate, advance,
clock down, loop — every tick the same `17` steps. -/
def uSim2 : List Instr :=
  [ Instr.loadI 0, Instr.jzI 20            -- 0,1:  clock test
  , Instr.loadIndI 2, Instr.jzI 7          -- 2,3:  fetch opcode; dispatch (0 → INC at 7)
  , Instr.constI 0, Instr.storeI 4, Instr.jmpI 10   -- 4,5,6:  NOP → incr := 0
  , Instr.constI 1, Instr.storeI 4, Instr.jmpI 10   -- 7,8,9:  INC → incr := 1
  , Instr.loadI 3, Instr.addI 4, Instr.storeI 3     -- 10,11,12: sim_acc += incr
  , Instr.loadI 2, Instr.addI 1, Instr.storeI 2     -- 13,14,15: advance code pointer
  , Instr.loadI 0, Instr.subI 1, Instr.storeI 0, Instr.jmpI 0  -- 16..19: clock--, loop
  , Instr.haltI ]                           -- 20:   done

/-- **One INC tick is exactly `17` steps and adds `1` to `sim_acc`** (fetched opcode `0`). -/
theorem uSim2_one (m : Mem) (acc N : ℕ) (h0 : m 0 = N + 1) (h1 : m 1 = 1) (hcode : m (m 2) = 0) :
    run uSim2 ⟨m, acc, 0, false⟩ 17
      = ⟨(((m.set 4 1).set 3 (m 3 + 1)).set 2 (m 2 + 1)).set 0 N, N, 0, false⟩ := by
  show step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2
    (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2
    (step uSim2 (⟨m, acc, 0, false⟩))))))))))))))))) = _
  simp [step, uSim2, List.getD, Mem.set, h0, h1, hcode]

/-- **One NOP tick is exactly `17` steps and leaves `sim_acc` unchanged** (fetched opcode `≠ 0`) — uniform
timing with the INC tick, but the content-dependent effect (`+0` instead of `+1`). -/
theorem uSim2_one_nop (m : Mem) (acc N : ℕ) (h0 : m 0 = N + 1) (h1 : m 1 = 1) (hnop : m (m 2) ≠ 0) :
    run uSim2 ⟨m, acc, 0, false⟩ 17
      = ⟨(((m.set 4 0).set 3 (m 3)).set 2 (m 2 + 1)).set 0 N, N, 0, false⟩ := by
  show step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2
    (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2 (step uSim2
    (step uSim2 (⟨m, acc, 0, false⟩))))))))))))))))) = _
  simp [step, uSim2, List.getD, Mem.set, h0, h1, hnop]

/-- **The simulator's output is the INC-count of the simulated prefix.**  From clock `= bound`, code pointer
`cp ≥ 5`, after exactly `17·bound + 3` steps the simulator halts with `clock = 0`, pointer `= cp + bound`, and
`sim_acc = (initial sim_acc) + incCount code cp bound` — a real function of the simulated machine's code. -/
theorem uSim2_count (N : ℕ) :
    ∀ (m : Mem) (acc : ℕ), m 0 = N → m 1 = 1 → 5 ≤ m 2 →
      let S := run uSim2 ⟨m, acc, 0, false⟩ (17 * N + 3)
      S.halted = true ∧ S.mem 0 = 0 ∧ S.mem 2 = m 2 + N ∧ S.mem 3 = m 3 + incCount m (m 2) N := by
  induction N with
  | zero =>
    intro m acc h0 _ _
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [run, step, uSim2, List.getD, h0, incCount]
  | succ N ih =>
    intro m acc h0 h1 hb
    have hexp : incCount m (m 2) (N + 1)
        = (if m (m 2) = 0 then 1 else 0) + incCount m (m 2 + 1) N := rfl
    by_cases hc : m (m 2) = 0
    · -- INC tick
      have hone := uSim2_one m acc N h0 h1 hc
      set M' : Mem := (((m.set 4 1).set 3 (m 3 + 1)).set 2 (m 2 + 1)).set 0 N with hM'
      have hM'0 : M' 0 = N := by simp [hM']
      have hM'1 : M' 1 = 1 := by simp [hM', h1]
      have hM'2 : M' 2 = m 2 + 1 := by simp [hM']
      have hM'3 : M' 3 = m 3 + 1 := by simp [hM']
      have hM'b : 5 ≤ M' 2 := by rw [hM'2]; omega
      have hcong : incCount M' (m 2 + 1) N = incCount m (m 2 + 1) N := by
        apply incCount_congr
        intro k hk
        have ha2 : m 2 + 1 + k ≠ 2 := by omega
        have ha3 : m 2 + 1 + k ≠ 3 := by omega
        have ha4 : m 2 + 1 + k ≠ 4 := by omega
        simp [hM', ha2, ha3, ha4]
      have key := ih M' N hM'0 hM'1 hM'b
      have hSeq : run uSim2 ⟨m, acc, 0, false⟩ (17 * (N + 1) + 3)
          = run uSim2 ⟨M', N, 0, false⟩ (17 * N + 3) := by
        rw [show 17 * (N + 1) + 3 = 17 + (17 * N + 3) from by ring, run_add, hone]
      simp only [hSeq]
      obtain ⟨kh, k0, k2, k3⟩ := key
      refine ⟨kh, k0, ?_, ?_⟩
      · rw [k2, hM'2]; ring
      · rw [k3, hM'3, hM'2, hcong, hexp, if_pos hc]; ring
    · -- NOP tick
      have hone := uSim2_one_nop m acc N h0 h1 hc
      set M' : Mem := (((m.set 4 0).set 3 (m 3)).set 2 (m 2 + 1)).set 0 N with hM'
      have hM'0 : M' 0 = N := by simp [hM']
      have hM'1 : M' 1 = 1 := by simp [hM', h1]
      have hM'2 : M' 2 = m 2 + 1 := by simp [hM']
      have hM'3 : M' 3 = m 3 := by simp [hM']
      have hM'b : 5 ≤ M' 2 := by rw [hM'2]; omega
      have hcong : incCount M' (m 2 + 1) N = incCount m (m 2 + 1) N := by
        apply incCount_congr
        intro k hk
        have ha2 : m 2 + 1 + k ≠ 2 := by omega
        have ha3 : m 2 + 1 + k ≠ 3 := by omega
        have ha4 : m 2 + 1 + k ≠ 4 := by omega
        simp [hM', ha2, ha3, ha4]
      have key := ih M' N hM'0 hM'1 hM'b
      have hSeq : run uSim2 ⟨m, acc, 0, false⟩ (17 * (N + 1) + 3)
          = run uSim2 ⟨M', N, 0, false⟩ (17 * N + 3) := by
        rw [show 17 * (N + 1) + 3 = 17 + (17 * N + 3) from by ring, run_add, hone]
      simp only [hSeq]
      obtain ⟨kh, k0, k2, k3⟩ := key
      refine ⟨kh, k0, ?_, ?_⟩
      · rw [k2, hM'2]; ring
      · rw [k3, hM'3, hM'2, hcong, hexp, if_neg hc]; ring

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.incCount_congr
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.uSim2_one
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.uSim2_one_nop
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.uSim2_count
