import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM

/-!
# The physical single step — atomic-step correctness (the base brick of the universal machine)

Beginning the physical `hstep` construction.  Its base case is the **atomic single-step correctness** of an actual
machine: one reachability step of `toNTM M` is exactly one `concreteStep`, so a firing transition rule carries the
configuration to `applyTrans` in exactly **one** physical step.  This is the brick the multi-step simulation
(`…ACC0SimulationStep.sim_multi`) iterates and the universal machine ultimately assembles.

## What is proved (clean axioms, no `sorry`)

* **`reachIn_one`** — one step is one transition: `reachIn (toNTM M) 1 c d ↔ concreteStep M c d`.
* **`firing_rule_step`** — a firing rule advances in one physical step: `t ∈ M → t.1 = (c.1, readSym c) →
  reachIn (toNTM M) 1 c (applyTrans c t)`.

## Honest scope

This is genuine machine-transition content — an actual machine's single step is proved correct, the atomic base of the
physical simulation.  It is **not** the universal machine: the universal `U` must *decode* the simulated machine `M`
from its own tape (the `encodeTape` layout) and perform `M`'s step via its own transitions in `B` steps — assembling
the rule-lookup, head-location, and tape-rewrite sub-machines.  That assembly (and its `B` bound) is the large
remaining construction; this file lays its base brick only.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PhysicalStep

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine TMTrans CConfig readSym applyTrans concreteStep toNTM toNTM_step)

/-- **One reachability step is one transition (proved): `reachIn (toNTM M) 1 c d ↔ concreteStep M c d`.** -/
theorem reachIn_one (M : TMachine) (c d : CConfig) :
    reachIn (toNTM M) 1 c d ↔ concreteStep M c d := by
  simp only [reachIn, exists_eq_right]
  exact toNTM_step M c d

/-- **A firing rule advances in one physical step (proved).**  If `t ∈ M` matches the current `(state, read)`, then the
machine reaches `applyTrans c t` from `c` in exactly one step. -/
theorem firing_rule_step (M : TMachine) (c : CConfig) (t : TMTrans)
    (htM : t ∈ M) (ht1 : t.1 = (c.1, readSym c)) :
    reachIn (toNTM M) 1 c (applyTrans c t) := by
  rw [reachIn_one]
  exact ⟨t, htM, ht1, rfl⟩

end PallLean.Paper93.DeepMath.PathB.ACC0PhysicalStep

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PhysicalStep.reachIn_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PhysicalStep.firing_rule_step
