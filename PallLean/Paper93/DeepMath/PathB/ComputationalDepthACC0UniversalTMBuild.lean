import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AbstractConcreteBridge

/-!
# Entry 334 — the universal-TM-table build, brick 1: the `Realizes` interface inhabited + a verified traversal primitive

Entry 333 reduced the concrete time hierarchy to one construction: a concrete `TMachine` `U` with `Realizes physU U φ
cost` — *the universal Turing machine as a transition table*.  This file **commits to that build** and lays its first
verified bricks.  The full construction is large (tape encoding of (machine, input), the rule-lookup scan, the
apply-step, the simulation loop, accept detection); this entry establishes the foundation: the `Realizes` interface is
genuinely *inhabited* (not a vacuous socket), and a first real universal-TM component — a verified multi-step **tape
traversal** — is built over the concrete model.

## What is proved (clean axioms, no `sorry`)

* **`realizes_self`** (PROVED) — `Realizes (toNTM M) M id 1`: every concrete `TMachine`, viewed as an abstract `NTM`,
  is realized by itself (identity config map, one step per step).  The `Realizes` interface of entry 333 is *inhabited*
  — a genuine simulation exists, not just the empty interface.
* **`moveHead_right`** (PROVED) — `moveHead h 1 = h + 1`: the right-move primitive.
* **`walkRight`**, **`walkRight_run`** (PROVED) — the tape-traversal machine (loop: stay in state `0`, move right) and
  its verified `k`-step run reaching head position `k` from the start — the scanning primitive a universal TM uses to
  walk the encoded transition table.

## Honest scope

This is **brick 1** of the universal-TM-table build: the simulation interface is shown inhabited (`realizes_self`), and a
genuine multi-step universal-TM component (the tape-traversal scanner) is verified over the concrete model
(`walkRight_run`).  It does **not** build the universal machine: that requires the remaining bricks — a tape encoding of
`(machine code, input)`, the rule-lookup scan (match the current `(state, symbol)` against the encoded table), the
apply-step (write/move per the matched rule), the simulation loop, and accept detection — assembled into one table `U`
with `Realizes physU U φ cost` proved.  That is a substantial classical construction, undertaken here as a real
multi-brick effort, **not faked**: each brick will be a verified concrete component.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBuild

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine CConfig Move toNTM concreteStep readSym applyTrans moveHead writeAt)
open PallLean.Paper93.DeepMath.PathB.ACC0AbstractConcreteBridge (Realizes)

/-- **The `Realizes` interface is inhabited (PROVED).**  Every concrete `TMachine` `M`, viewed as the abstract `NTM`
`toNTM M`, is realized by itself: the identity config map, one concrete step per abstract step.  This shows the entry-333
bridge interface is a genuine, non-vacuous notion — concrete simulations of abstract machines exist. -/
theorem realizes_self (M : TMachine) : Realizes (toNTM M) M id 1 where
  step c d h := ⟨d, h, rfl⟩
  accept c h := h
  init x := rfl

/-- **The right-move primitive (PROVED).**  `moveHead h 1 = h + 1`. -/
theorem moveHead_right (h : ℕ) : moveHead h (1 : Move) = h + 1 := by
  simp [moveHead]

/-- **The tape-traversal machine.**  In state `0`, on either read symbol, stay in state `0` and move right — the
universal TM's scanning loop over the encoded table. -/
def walkRight : TMachine :=
  [((0, true), (0, true, (1 : Move))), ((0, false), (0, false, (1 : Move)))]

/-- **The traversal run is verified (PROVED).**  From `(0, 0, x)`, `walkRight` runs `k` steps to a configuration in
state `0` with head at position `k` — the scanner advances one cell per step.  Proof by induction on `k`, extending the
run by one verified `walkRight` step (head `k → k+1`) via `reachIn_add`. -/
theorem walkRight_run (x : List Bool) :
    ∀ k : ℕ, ∃ tp : List Bool, reachIn (toNTM walkRight) k (0, 0, x) (0, k, tp) := by
  intro k
  induction k with
  | zero => exact ⟨x, rfl⟩
  | succ k ih =>
      obtain ⟨tp, hr⟩ := ih
      refine ⟨writeAt tp k (readSym ((0 : ℕ), k, tp)), ?_⟩
      have hstep : concreteStep walkRight (0, k, tp)
          (0, k + 1, writeAt tp k (readSym ((0 : ℕ), k, tp))) := by
        refine ⟨((0, readSym ((0 : ℕ), k, tp)), (0, readSym ((0 : ℕ), k, tp), (1 : Move))), ?_, rfl, ?_⟩
        · cases readSym ((0 : ℕ), k, tp) <;> simp [walkRight]
        · simp [applyTrans, moveHead_right]
      exact (reachIn_add (toNTM walkRight) k 1 (0, 0, x) _).mpr
        ⟨(0, k, tp), hr, ⟨_, hstep, rfl⟩⟩

/-!
**Brick 1, built.**  `realizes_self` shows the entry-333 simulation interface is inhabited (concrete machines realize
their abstract embeddings), and `walkRight_run` verifies a genuine multi-step universal-TM component — the tape-traversal
scanner reaching head `k` in `k` steps.  The universal-TM table is now under construction as a real multi-brick effort;
the remaining bricks (encode `(machine, input)`, scan-and-match the rule table, apply the rule, loop, detect accept,
assemble `U` with `Realizes physU U φ cost`) are the substantial classical construction, each to be a verified concrete
component — not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBuild

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBuild.realizes_self
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBuild.moveHead_right
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBuild.walkRight_run
