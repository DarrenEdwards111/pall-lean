import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMSimDeciderCost
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMDiagonal
import Mathlib.Tactic

/-!
# `simDecider` synthesis: correct **and** efficient, and it realises the diagonal — step 3 ⋈ step 6

The arc proved the integrated decider's pieces in separate files: what each branch *computes* (correctness,
step 2) and that it runs in *polynomial bit-cost* (step 3).  This file ties them together — for each branch,
one statement saying **the decider both computes the right thing and does so in poly bit-cost** — and connects
the cost side to the diagonal: the same machine that escapes the class (step 6) is a concrete RAM program with
a proved running-time bound.

  `simDecider_complement_correct_efficient` — complement mode: result `= 1 - inp` (the flip) **and**
        `runCost ≤ 14·(3W+1)`.
  `simDecider_copy_correct_efficient` — copy mode: result `= incCount code` (the simulated machine's output)
        **and** `runCost ≤ (10 + (17·bound + 3))·(3W+1)`, for **any** simulated program.
  `simDecider_realises_ramDiag_efficient` — with the input bit `= sim x x`, the decider computes the diagonal
        value `ramDiag sim x` **and** does so in poly bit-cost: the diagonal of the simulator is realised by a
        concrete poly-bit-cost RAM machine.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` — it is the coherence statement that the constructive decider is at
once correct, efficient, and the diagonal-realising machine; the separation still rests on the two cited
Williams axioms.
-/

open PallLean.Paper93.DeepMath.PathB.BitCost (bitlen)

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- **Complement branch: correct and efficient.**  When `mode ≠ 0`, the decider's result is `1 - inp` (the
diagonal flip) and the whole run costs `≤ 14·(3W + 1)` bits — both, from one set of hypotheses. -/
theorem simDecider_complement_correct_efficient (m : Mem) (acc V W : ℕ)
    (hin : ∀ x, m x ≤ V) (hacc : acc ≤ V) (h1 : 1 ≤ V) (hmode : m 11 ≠ 0)
    (hV : bitlen V ≤ W) (hW : 6 ≤ W) :
    (run simDecider ⟨m, acc, 0, false⟩ 14).mem 3 = 1 - m 12
      ∧ runCost simDecider ⟨m, acc, 0, false⟩ 14 ≤ 14 * (3 * W + 1) :=
  ⟨(simDecider_complement m acc hmode).2,
   simDecider_complement_cost m acc V W hin hacc h1 hmode hV hW⟩

/-- **Copy branch: correct and efficient, for any code.**  When `mode = 0`, the decider's result is
`incCount code` (the simulated machine's output) and the whole run costs `≤ (10 + (17·bound + 3))·(3W + 1)`
bits — for an arbitrary simulated program (no all-`INC` hypothesis). -/
theorem simDecider_copy_correct_efficient (m : Mem) (acc V W : ℕ)
    (hin : ∀ x, m x ≤ V) (hacc : acc ≤ V) (h1 : 1 ≤ V) (hmode : m 11 = 0)
    (hb5 : 5 ≤ m 13) (hsum : m 13 + m 10 ≤ V) (hV : bitlen V ≤ W) (hW : 6 ≤ W) :
    (run simDecider ⟨m, acc, 0, false⟩ (10 + (17 * m 10 + 3))).mem 3 = incCount m (m 13) (m 10)
      ∧ runCost simDecider ⟨m, acc, 0, false⟩ (10 + (17 * m 10 + 3))
          ≤ (10 + (17 * m 10 + 3)) * (3 * W + 1) :=
  ⟨simDecider_copy m acc hmode hb5,
   simDecider_copy_cost_mixed m acc V W hin hacc h1 hmode hb5 hsum hV hW⟩

/-- **The decider realises the diagonal function, in poly bit-cost.**  Feeding the simulated self-value
`sim x x` as the input bit (complement mode), the decider's result is exactly the diagonal value
`ramDiag sim x = 1 - sim x x`, computed in `≤ 14·(3W + 1)` bits.  So the abstract diagonal `ramDiag` of step 4/6
is realised by a concrete RAM machine with a *proved* running-time bound — the cost side (step 3) and the
diagonal side (step 6) cohere on the same `simDecider`. -/
theorem simDecider_realises_ramDiag_efficient (sim : ℕ → ℕ → ℕ) (x : ℕ) (m : Mem) (acc V W : ℕ)
    (hin : ∀ y, m y ≤ V) (hacc : acc ≤ V) (h1 : 1 ≤ V) (hmode : m 11 ≠ 0)
    (hinp : m 12 = sim x x) (hV : bitlen V ≤ W) (hW : 6 ≤ W) :
    (run simDecider ⟨m, acc, 0, false⟩ 14).mem 3 = ramDiag sim x
      ∧ runCost simDecider ⟨m, acc, 0, false⟩ 14 ≤ 14 * (3 * W + 1) := by
  refine ⟨?_, simDecider_complement_cost m acc V W hin hacc h1 hmode hV hW⟩
  have h := (simDecider_complement m acc hmode).2
  simp only [ramDiag, h, hinp]

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_complement_correct_efficient
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_copy_correct_efficient
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.simDecider_realises_ramDiag_efficient
