import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMSimDecider
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMDPWidth
import Mathlib.Tactic

/-!
# RAM lazy diagonal decider — discharging the width invariant (the cost lemma's hypothesis)

The companion of `ComputationalDepthRAMDPWidth` for `simDecider`.  `simDecider` is the integrated decider (10-step
init+dispatch, then either the 14-step complement branch or the `17·bound+3`-step relocated simulator loop).  This
file discharges the width invariant for its runs, so the decider's bit-cost is unconditional.

Same shape as the `dpLoop` discharge: the value-dependent `WidthBounded` conjuncts follow from a value bound
(`widthBounded_of_value_le`), and `simDecider`'s operands are `≤ 34`, so `instrWidth ≤ 6`.  The hard part is the
value bound through the simulator loop (`addI 1` adds `mem 1 = 1`, the `loadIndI 2` reads an opcode `≤ V`).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.BitCost (bitlen bitlen_mono)

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- **`simDecider`'s operands fit in 6 bits.**  Every operand is `≤ 34` (`bitlen 34 = 6`). -/
theorem simDecider_instrWidth : ∀ i ∈ simDecider, instrWidth i ≤ 6 := by decide

/-- **Value bound ⇒ width bound for `simDecider`** (`W ≥ 6`). -/
theorem simDecider_widthBounded_of_value_le (s : State) (V W : ℕ)
    (hacc : s.acc ≤ V) (hmem : ∀ x, s.mem x ≤ V) (hV : bitlen V ≤ W) (hW : 6 ≤ W) :
    WidthBounded simDecider s W :=
  widthBounded_of_value_le simDecider s V W hacc hmem hV
    (fun i hi => le_trans (simDecider_instrWidth i hi) hW)

set_option maxHeartbeats 8000000 in
/-- **Within one simulator tick, every value stays `≤ V`.**  From the loop top (`pc = 14`) with a live clock
(`m 0 ≠ 0`), `m 1 = 1`, code pointer `m 2 ≥ 5`, and bounds `m 2 + 1 ≤ V`, `m 3 + 1 ≤ V`, `acc ≤ V`, `∀x m x ≤ V`,
each of the `17` micro-steps keeps the accumulator and every memory cell `≤ V`.  Casing on the fetched opcode
`m (m 2)` (`INC` / `NOP`); the opcode itself is `≤ V` (`hmem`), the increments add `mem 1 = 1` / `mem 4 ∈ {0,1}`. -/
theorem simLoop_iter_values_le (m : Mem) (acc V : ℕ)
    (h0 : m 0 ≠ 0) (h1 : m 1 = 1) (_hb : 5 ≤ m 2)
    (hmem : ∀ x, m x ≤ V) (hacc : acc ≤ V) (hp : m 2 + 1 ≤ V) (hv : m 3 + 1 ≤ V) :
    ∀ k, k ≤ 17 → (run simDecider ⟨m, acc, 14, false⟩ k).acc ≤ V
        ∧ ∀ x, (run simDecider ⟨m, acc, 14, false⟩ k).mem x ≤ V := by
  have hm0 := hmem 0
  have hm2 := hmem 2
  have hm3 := hmem 3
  have hmm2 := hmem (m 2)
  intro k hk
  by_cases hc : m (m 2) = 0 <;>
    (interval_cases k <;> refine ⟨?_, ?_⟩ <;>
      first
        | (intro x
           simp [run, step, simDecider, h0, h1, hc, Mem.set]
           first | exact hmem _ | omega | (split_ifs <;> first | exact hmem _ | omega))
        | (simp [run, step, simDecider, h0, h1, hc, Mem.set] <;> omega))

set_option maxHeartbeats 4000000 in
/-- **The simulator-loop value bound.**  From the loop top with clock `N`, `m 1 = 1`, pointer `≥ 5`, and `V`
dominating the grown values (`m 2 + N ≤ V`, `m 3 + N ≤ V`) and the initial cells, every reached state in the exact
`17·N+3`-step loop keeps the accumulator and every memory cell `≤ V`.  Induction on `N`: each tick uses
`simLoop_iter_values_le`, then `simLoop_one`/`simLoop_one_nop` (by the fetched opcode) advances to the next tick's
start, whose cells are again `≤ V`. -/
theorem simLoop_values_le (V : ℕ) : ∀ (N : ℕ) (m : Mem) (acc : ℕ),
    m 0 = N → m 1 = 1 → 5 ≤ m 2 → m 2 + N ≤ V → m 3 + N ≤ V → acc ≤ V → (∀ x, m x ≤ V) →
    ∀ k, k ≤ 17 * N + 3 → (run simDecider ⟨m, acc, 14, false⟩ k).acc ≤ V
        ∧ ∀ x, (run simDecider ⟨m, acc, 14, false⟩ k).mem x ≤ V := by
  intro N
  induction N with
  | zero =>
    intro m acc h0 h1 _ _ _ hacc hmem k hk
    interval_cases k <;> refine ⟨?_, ?_⟩ <;>
      first
        | (intro x
           simp [run, step, simDecider, h0]
           exact hmem x)
        | (simp [run, step, simDecider, h0] <;> omega)
  | succ N ih =>
    intro m acc h0 h1 hb hp hv hacc hmem k hk
    rcases Nat.lt_or_ge k 18 with hk17 | hk17
    · exact simLoop_iter_values_le m acc V (by omega) h1 hb hmem hacc (by omega) (by omega) k (by omega)
    · obtain ⟨k', rfl⟩ : ∃ k', k = 17 + k' := ⟨k - 17, by omega⟩
      have hk' : k' ≤ 17 * N + 3 := by omega
      by_cases hc : m (m 2) = 0
      · rw [run_add, simLoop_one m acc N h0 h1 hc]
        set M' : Mem := (((m.set 4 1).set 3 (m 3 + 1)).set 2 (m 2 + 1)).set 0 N with hM'def
        have hM' : ∀ x, M' x ≤ V := by
          intro x
          simp only [hM'def, Mem.set]
          split_ifs <;> first | omega | exact hmem x
        exact ih M' N (by simp [hM'def]) (by simp [hM'def, h1]) (by simp [hM'def]; omega)
          (by simp [hM'def]; omega) (by simp [hM'def]; omega) (by omega) hM' k' hk'
      · rw [run_add, simLoop_one_nop m acc N h0 h1 hc]
        set M' : Mem := (((m.set 4 0).set 3 (m 3)).set 2 (m 2 + 1)).set 0 N with hM'def
        have hM' : ∀ x, M' x ≤ V := by
          intro x
          simp only [hM'def, Mem.set]
          split_ifs <;> first | omega | exact hmem x
        exact ih M' N (by simp [hM'def]) (by simp [hM'def, h1]) (by simp [hM'def]; omega)
          (by simp [hM'def]; omega) (by simp [hM'def]; omega) (by omega) hM' k' hk'

set_option maxHeartbeats 4000000 in
/-- **The init+dispatch prefix keeps every value `≤ V`** (`mode = 0`).  The 10-step init sets the simulator cells
(clock `= m 10`, one `= 1`, `sim_acc = 0`, code pointer `= m 13`) and dispatches; all the values touched are `≤ V`. -/
theorem simDecider_copy_prefix_values_le (m : Mem) (acc V : ℕ)
    (hmode : m 11 = 0) (hbase : 5 ≤ m 13) (hmem : ∀ x, m x ≤ V) (hacc : acc ≤ V) :
    ∀ k, k ≤ 10 → (run simDecider ⟨m, acc, 0, false⟩ k).acc ≤ V
        ∧ ∀ x, (run simDecider ⟨m, acc, 0, false⟩ k).mem x ≤ V := by
  have hm10 := hmem 10
  have hm11 := hmem 11
  have hm13 := hmem 13
  intro k hk
  interval_cases k <;> refine ⟨?_, ?_⟩ <;>
    first
      | (intro x
         simp [run, step, simDecider, hmode, Mem.set]
         first | exact hmem _ | omega | (split_ifs <;> first | exact hmem _ | omega))
      | (simp [run, step, simDecider, hmode, Mem.set] <;> omega)

/-- **The copy-run value bound.**  When `mode = 0` (`code-base ≥ 5`), with `V` dominating `m 13 + m 10` and the
initial cells, every reached state of the exact `10 + (17·m 10 + 3)`-step copy run keeps the accumulator and every
memory cell `≤ V`.  Prefix (`< 10`) via `simDecider_copy_prefix_values_le`, then the simulator loop via
`simDecider_copy_prefix` + `simLoop_values_le`. -/
theorem simDecider_copy_values_le (m : Mem) (acc V : ℕ)
    (hmode : m 11 = 0) (hbase : 5 ≤ m 13) (hmem : ∀ x, m x ≤ V) (hacc : acc ≤ V)
    (hp : m 13 + m 10 ≤ V) :
    ∀ k, k ≤ 10 + (17 * m 10 + 3) → (run simDecider ⟨m, acc, 0, false⟩ k).acc ≤ V
        ∧ ∀ x, (run simDecider ⟨m, acc, 0, false⟩ k).mem x ≤ V := by
  intro k hk
  rcases Nat.lt_or_ge k 11 with hk10 | hk10
  · exact simDecider_copy_prefix_values_le m acc V hmode hbase hmem hacc k (by omega)
  · obtain ⟨k', rfl⟩ : ∃ k', k = 10 + k' := ⟨k - 10, by omega⟩
    have hk' : k' ≤ 17 * m 10 + 3 := by omega
    rw [run_add, simDecider_copy_prefix m acc hmode]
    set IM : Mem := (((m.set 0 (m 10)).set 1 1).set 3 0).set 2 (m 13) with hIMdef
    have hIM : ∀ x, IM x ≤ V := by
      intro x
      have hm10 := hmem 10
      have hm13 := hmem 13
      simp only [hIMdef, Mem.set]
      split_ifs <;> first | omega | exact hmem x
    exact simLoop_values_le V (m 10) IM 0 (by simp [hIMdef]) (by simp [hIMdef])
      (by simp [hIMdef]; omega) (by simp [hIMdef]; omega) (by simp [hIMdef]; omega)
      (by omega) hIM k' hk'

/-- **Unconditional poly bit-cost of the copy decider.**  Discharging the width invariant, the exact
`10 + (17·m 10 + 3)`-step copy run costs `≤ (10 + 17·m 10 + 3)·(3W+1)` bits with **no** width hypothesis. -/
theorem simDecider_copy_runCost_unconditional (m : Mem) (acc V W : ℕ)
    (hmode : m 11 = 0) (hbase : 5 ≤ m 13) (hmem : ∀ x, m x ≤ V) (hacc : acc ≤ V)
    (hp : m 13 + m 10 ≤ V) (hVW : bitlen V ≤ W) (hW : 6 ≤ W) :
    runCost simDecider ⟨m, acc, 0, false⟩ (10 + (17 * m 10 + 3))
      ≤ (10 + (17 * m 10 + 3)) * (3 * W + 1) := by
  apply runCost_width_le
  intro k hk
  obtain ⟨hkacc, hkmem⟩ := simDecider_copy_values_le m acc V hmode hbase hmem hacc hp k (by omega)
  exact simDecider_widthBounded_of_value_le _ V W hkacc hkmem hVW hW

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_instrWidth
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simLoop_values_le
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_copy_runCost_unconditional
