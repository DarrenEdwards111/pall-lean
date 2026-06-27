import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMUSim2
import Mathlib.Tactic

/-!
# RAM lazy diagonal decider — the full composition, verified (PROVED) — step 2, brick 6

The previous bricks proved the phases as separate programs.  This brick **composes them into one machine**:
`simDecider` is a single RAM program that decodes the input, dispatches on the mode flag, and either

* (copy, `mode = 0`) runs the **content-dependent simulator** of brick 5 inline — fetch/decode/dispatch each
  opcode and accumulate — leaving `result = incCount(code)`, the simulated machine's output; or
* (complement, `mode ≠ 0`) outputs `result = 1 - inp`, the diagonal flip.

So the simulator is no longer a separate program fed a hand-set input cell: the *same machine* decodes, then
simulates the decoded code, then can complement.  The engineering content is genuine **program composition with
absolute-pc relocation** — `clockedDecider`'s clock loop is replaced by `uSim2`'s fetch-decode loop relocated
to offset `14`, and its invariant is re-derived there (the relocated-loop pattern, as `clockLoop` was a
relocated `countLoop`).  Phases are glued with `run_add`.

Layout: `mem[0]=clock mem[1]=1 mem[2]=code-ptr mem[3]=sim_acc/result mem[4]=incr`;
input `mem[10]=bound mem[11]=mode mem[12]=inp mem[13]=code-base`; code at addresses `≥ 5`.

```
  0..7:  init — clock:=bound, one:=1, sim_acc:=0, code-ptr:=code-base
  8: loadI 11  9: jzI 14                         -- dispatch (mode=0 → simulator at 14)
  10: constI 1 11: subI 12 12: storeI 3 13: haltI -- complement: result := 1 - inp
  14..33: uSim2's fetch-decode-accumulate loop, relocated +14 (jzI 34 / jzI 21 / jmpI 24 / jmpI 14)
  34: haltI                                       -- done: result = sim_acc
```

  `simLoop_one` / `simLoop_one_nop` — one INC / one NOP simulator tick (each `17` steps) at offset `14`.
  `simLoop_correct` — the relocated simulator loop runs `bound` ticks: `sim_acc = init + incCount code cp bound`.
  `simDecider_copy` — `mode = 0`: after exactly `10 + (17·bound + 3)` steps, `result = incCount code-base bound`
        — the *same machine* decoded the input and simulated the decoded program.
  `simDecider_complement` — `mode ≠ 0`: after exactly `14` steps, `result = 1 - inp` (the diagonal flip).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This is the integrated decider; the classical sockets
(`FaithfulOnDiagonal`, decider `∈ NEXP`) of the diagonal skeleton remain the load-bearing, unproved content.
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- The fully integrated decider: decode → dispatch → (copy: content-dependent simulate / complement). -/
def simDecider : List Instr :=
  [ Instr.loadI 10, Instr.storeI 0       -- 0,1:  clock := bound
  , Instr.constI 1, Instr.storeI 1       -- 2,3:  one := 1
  , Instr.constI 0, Instr.storeI 3       -- 4,5:  sim_acc := 0
  , Instr.loadI 13, Instr.storeI 2       -- 6,7:  code-ptr := code-base
  , Instr.loadI 11, Instr.jzI 14         -- 8,9:  dispatch (mode=0 → simulator at 14)
  , Instr.constI 1, Instr.subI 12, Instr.storeI 3, Instr.haltI  -- 10..13: complement → 1 - inp
  , Instr.loadI 0, Instr.jzI 34          -- 14,15: simulator clock test
  , Instr.loadIndI 2, Instr.jzI 21       -- 16,17: fetch opcode; dispatch (0 → INC at 21)
  , Instr.constI 0, Instr.storeI 4, Instr.jmpI 24   -- 18,19,20: NOP → incr := 0
  , Instr.constI 1, Instr.storeI 4, Instr.jmpI 24   -- 21,22,23: INC → incr := 1
  , Instr.loadI 3, Instr.addI 4, Instr.storeI 3     -- 24,25,26: sim_acc += incr
  , Instr.loadI 2, Instr.addI 1, Instr.storeI 2     -- 27,28,29: advance code pointer
  , Instr.loadI 0, Instr.subI 1, Instr.storeI 0, Instr.jmpI 14  -- 30..33: clock--, loop
  , Instr.haltI ]                         -- 34:   done → result = sim_acc

/-- **One INC simulator tick at offset `14` is exactly `17` steps and adds `1` to `sim_acc`.** -/
theorem simLoop_one (m : Mem) (acc N : ℕ) (h0 : m 0 = N + 1) (h1 : m 1 = 1) (hcode : m (m 2) = 0) :
    run simDecider ⟨m, acc, 14, false⟩ 17
      = ⟨(((m.set 4 1).set 3 (m 3 + 1)).set 2 (m 2 + 1)).set 0 N, N, 14, false⟩ := by
  show step simDecider (step simDecider (step simDecider (step simDecider (step simDecider (step simDecider
    (step simDecider (step simDecider (step simDecider (step simDecider (step simDecider (step simDecider
    (step simDecider (step simDecider (step simDecider (step simDecider (step simDecider
    (⟨m, acc, 14, false⟩))))))))))))))))) = _
  simp [step, simDecider, List.getD, Mem.set, h0, h1, hcode]

/-- **One NOP simulator tick at offset `14` is exactly `17` steps and leaves `sim_acc` unchanged.** -/
theorem simLoop_one_nop (m : Mem) (acc N : ℕ) (h0 : m 0 = N + 1) (h1 : m 1 = 1) (hnop : m (m 2) ≠ 0) :
    run simDecider ⟨m, acc, 14, false⟩ 17
      = ⟨(((m.set 4 0).set 3 (m 3)).set 2 (m 2 + 1)).set 0 N, N, 14, false⟩ := by
  show step simDecider (step simDecider (step simDecider (step simDecider (step simDecider (step simDecider
    (step simDecider (step simDecider (step simDecider (step simDecider (step simDecider (step simDecider
    (step simDecider (step simDecider (step simDecider (step simDecider (step simDecider
    (⟨m, acc, 14, false⟩))))))))))))))))) = _
  simp [step, simDecider, List.getD, Mem.set, h0, h1, hnop]

/-- **The relocated simulator loop runs the decoded machine for `bound` steps.**  From the loop top `pc = 14`
with clock `= N`, code pointer `cp ≥ 5`, after exactly `17·N + 3` steps the machine halts (`pc = 34`) with
clock `= 0`, pointer `= cp + N`, and `sim_acc = (initial) + incCount code cp N`. -/
theorem simLoop_correct (N : ℕ) :
    ∀ (m : Mem) (acc : ℕ), m 0 = N → m 1 = 1 → 5 ≤ m 2 →
      let S := run simDecider ⟨m, acc, 14, false⟩ (17 * N + 3)
      S.halted = true ∧ S.mem 0 = 0 ∧ S.mem 2 = m 2 + N ∧ S.mem 3 = m 3 + incCount m (m 2) N := by
  induction N with
  | zero =>
    intro m acc h0 _ _
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [run, step, simDecider, List.getD, h0, incCount]
  | succ N ih =>
    intro m acc h0 h1 hb
    have hexp : incCount m (m 2) (N + 1)
        = (if m (m 2) = 0 then 1 else 0) + incCount m (m 2 + 1) N := rfl
    by_cases hc : m (m 2) = 0
    · have hone := simLoop_one m acc N h0 h1 hc
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
      have hSeq : run simDecider ⟨m, acc, 14, false⟩ (17 * (N + 1) + 3)
          = run simDecider ⟨M', N, 14, false⟩ (17 * N + 3) := by
        rw [show 17 * (N + 1) + 3 = 17 + (17 * N + 3) from by ring, run_add, hone]
      simp only [hSeq]
      obtain ⟨kh, k0, k2, k3⟩ := key
      refine ⟨kh, k0, ?_, ?_⟩
      · rw [k2, hM'2]; ring
      · rw [k3, hM'3, hM'2, hcong, hexp, if_pos hc]; ring
    · have hone := simLoop_one_nop m acc N h0 h1 hc
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
      have hSeq : run simDecider ⟨m, acc, 14, false⟩ (17 * (N + 1) + 3)
          = run simDecider ⟨M', N, 14, false⟩ (17 * N + 3) := by
        rw [show 17 * (N + 1) + 3 = 17 + (17 * N + 3) from by ring, run_add, hone]
      simp only [hSeq]
      obtain ⟨kh, k0, k2, k3⟩ := key
      refine ⟨kh, k0, ?_, ?_⟩
      · rw [k2, hM'2]; ring
      · rw [k3, hM'3, hM'2, hcong, hexp, if_neg hc]; ring

/-- The exact state after the `10`-step init+dispatch on a **copy** input (`mode = 0`): simulator cells set up
(clock `= bound`, code pointer `= code-base`, `sim_acc = 0`), control at the simulator loop top `pc = 14`. -/
theorem simDecider_copy_prefix (m : Mem) (acc : ℕ) (hmode : m 11 = 0) :
    run simDecider ⟨m, acc, 0, false⟩ 10
      = ⟨(((m.set 0 (m 10)).set 1 1).set 3 0).set 2 (m 13), 0, 14, false⟩ := by
  show step simDecider (step simDecider (step simDecider (step simDecider (step simDecider (step simDecider
    (step simDecider (step simDecider (step simDecider (step simDecider
    (⟨m, acc, 0, false⟩)))))))))) = _
  simp [step, simDecider, List.getD, hmode]

/-- **Copy branch — the same machine decodes then simulates the decoded program.**  When `mode = 0`, after
exactly `10 + (17·bound + 3)` steps the decider halts with `result = incCount code-base bound`: the integrated
machine ran the decoded program for `bound` steps and its result is that program's INC-count (its simulated
output).  This is the full composition: decode and content-dependent simulation in one machine. -/
theorem simDecider_copy (m : Mem) (acc : ℕ) (hmode : m 11 = 0) (hbase : 5 ≤ m 13) :
    (run simDecider ⟨m, acc, 0, false⟩ (10 + (17 * m 10 + 3))).mem 3 = incCount m (m 13) (m 10) := by
  have hrw : run simDecider ⟨m, acc, 0, false⟩ (10 + (17 * m 10 + 3))
      = run simDecider ⟨(((m.set 0 (m 10)).set 1 1).set 3 0).set 2 (m 13), 0, 14, false⟩ (17 * m 10 + 3) := by
    rw [run_add, simDecider_copy_prefix m acc hmode]
  rw [hrw]
  set IM : Mem := (((m.set 0 (m 10)).set 1 1).set 3 0).set 2 (m 13) with hIM
  have hi0 : IM 0 = m 10 := by simp [hIM]
  have hi1 : IM 1 = 1 := by simp [hIM]
  have hi2 : IM 2 = m 13 := by simp [hIM]
  have hi3 : IM 3 = 0 := by simp [hIM]
  have hib : 5 ≤ IM 2 := by rw [hi2]; exact hbase
  have hcong : incCount IM (m 13) (m 10) = incCount m (m 13) (m 10) := by
    apply incCount_congr
    intro k hk
    show IM (m 13 + k) = m (m 13 + k)
    rw [hIM, Mem.set_get_ne _ 2 _ _ (by omega), Mem.set_get_ne _ 3 _ _ (by omega),
      Mem.set_get_ne _ 1 _ _ (by omega), Mem.set_get_ne _ 0 _ _ (by omega)]
  have key := simLoop_correct (m 10) IM 0 hi0 hi1 hib
  obtain ⟨_, _, _, k3⟩ := key
  rw [k3, hi3, hi2, hcong]
  simp

/-- **Complement branch.**  When `mode ≠ 0`, after exactly `14` steps the decider halts with `result = 1 - inp`
— the diagonal flip, computed by the same integrated machine. -/
theorem simDecider_complement (m : Mem) (acc : ℕ) (hmode : m 11 ≠ 0) :
    (run simDecider ⟨m, acc, 0, false⟩ 14).halted = true
      ∧ (run simDecider ⟨m, acc, 0, false⟩ 14).mem 3 = 1 - m 12 := by
  have hrw : run simDecider ⟨m, acc, 0, false⟩ 14
      = run simDecider ⟨(((m.set 0 (m 10)).set 1 1).set 3 0).set 2 (m 13), m 11, 10, false⟩ 4 := by
    have hpre : run simDecider ⟨m, acc, 0, false⟩ 10
        = ⟨(((m.set 0 (m 10)).set 1 1).set 3 0).set 2 (m 13), m 11, 10, false⟩ := by
      show step simDecider (step simDecider (step simDecider (step simDecider (step simDecider
        (step simDecider (step simDecider (step simDecider (step simDecider (step simDecider
        (⟨m, acc, 0, false⟩)))))))))) = _
      simp [step, simDecider, List.getD, hmode]
    rw [show (14 : ℕ) = 10 + 4 from rfl, run_add, hpre]
  rw [hrw]
  constructor
  · show (step simDecider (step simDecider (step simDecider (step simDecider
      (⟨(((m.set 0 (m 10)).set 1 1).set 3 0).set 2 (m 13), m 11, 10, false⟩))))).halted = true
    simp [step, simDecider, List.getD]
  · show (step simDecider (step simDecider (step simDecider (step simDecider
      (⟨(((m.set 0 (m 10)).set 1 1).set 3 0).set 2 (m 13), m 11, 10, false⟩))))).mem 3 = 1 - m 12
    simp [step, simDecider, List.getD]

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simLoop_correct
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_copy
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_complement
