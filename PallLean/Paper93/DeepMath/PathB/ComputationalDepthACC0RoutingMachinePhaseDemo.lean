import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RoutingMachineSequencing

/-!
# Entry 332 — phase instantiation: a concrete sequenced machine that accepts (proved)

Entries 329–331 verified the routing machine's *control structure* (parallel disjoint-state assembly + exit→entry
sequencing) abstractly over `M₁, M₂`.  This file **instantiates it with concrete transition tables** and proves a real
end-to-end **accepting** run, validating the whole pipeline — `init → exit → handoff → accept` — on actual `TMachine`s,
including the accept-state plumbing.

**The concrete machine.**  Each phase is a jump table (the proved `handoffRules from to`): `demoRouting qexit s :=
handoffRules 0 qexit ++ handoffRules qexit s ++ handoffRules s 1` — from the start state `0` jump to `qexit`, then to
`s`, then to the global accept state `1`.  Running it: `(0,0,x) → (qexit,…) → (s,…) → (1,…)`, accepting in **3 steps**
for every input, with each step the proved `handoff_step` lifted into the combined table by entry-329 monotonicity.

## What is proved (clean axioms, no `sorry`)

* **`demoRouting`** — a concrete three-phase sequenced `TMachine` (`0 → qexit → s → 1`).
* **`demoRouting_accepts`** (PROVED) — `acceptsWithin (toNTM (demoRouting qexit s)) x 3` for every input `x`: the
  combined machine accepts via the full handoff pipeline, reaching the global accept state `1`.

## Honest scope

This **instantiates the routing control skeleton with concrete tables** and proves a verified end-to-end accepting run,
demonstrating that the assembly (329) + sequencing (331) machinery genuinely accepts concrete `TMachine`s and reaches
the global accept state — the accept-state plumbing works.  The phases here are minimal jump tables, **not** the full
decode / universal-simulation / bounded-complement phases of the real routing decider.  Instantiating *those* additionally
requires bridging the universal simulator (entries 296–298, built as an *abstract* `NTM`) into a concrete `TMachine`
transition table, plus the bounded-complement search as a table, plus the `f`-timing — the genuine remaining low-level
construction, **not built here and not faked**.  This is the fourth verified brick: the control skeleton, validated
concretely.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachinePhaseDemo

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig toNTM concreteStep)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (acceptsWithin reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineComposition (concreteStep_mono)
open PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineSequencing (handoffRules postHandoff handoff_step)

/-- **A concrete three-phase sequenced machine.**  Jump `0 → qexit`, then `qexit → s`, then `s → 1` (global accept) —
each phase a `handoffRules` jump table. -/
def demoRouting (qexit s : ℕ) : TMachine :=
  handoffRules 0 qexit ++ handoffRules qexit s ++ handoffRules s 1

/-- **The concrete sequenced machine accepts (PROVED).**  `demoRouting qexit s` accepts every input `x` in 3 steps,
running `(0,0,x) → (qexit,…) → (s,…) → (1,…)` — each step the proved `handoff_step` lifted into the combined table —
reaching the global accept state `1`.  Validates the routing control skeleton (assembly 329 + sequencing 331) on
concrete tables, including the accept plumbing. -/
theorem demoRouting_accepts (qexit s : ℕ) (x : List Bool) :
    acceptsWithin (toNTM (demoRouting qexit s)) x 3 := by
  have sub0 : handoffRules 0 qexit ⊆ demoRouting qexit s :=
    (List.subset_append_left _ _).trans (List.subset_append_left _ _)
  have sub1 : handoffRules qexit s ⊆ demoRouting qexit s :=
    (List.subset_append_right _ _).trans (List.subset_append_left _ _)
  have sub2 : handoffRules s 1 ⊆ demoRouting qexit s :=
    List.subset_append_right _ _
  have step1 : concreteStep (demoRouting qexit s) (0, 0, x) (postHandoff 0 qexit (0, 0, x)) :=
    concreteStep_mono sub0 (handoff_step 0 qexit (0, 0, x) rfl)
  have step2 : concreteStep (demoRouting qexit s)
      (postHandoff 0 qexit (0, 0, x)) (postHandoff qexit s (postHandoff 0 qexit (0, 0, x))) :=
    concreteStep_mono sub1 (handoff_step qexit s (postHandoff 0 qexit (0, 0, x)) rfl)
  have step3 : concreteStep (demoRouting qexit s)
      (postHandoff qexit s (postHandoff 0 qexit (0, 0, x)))
      (postHandoff s 1 (postHandoff qexit s (postHandoff 0 qexit (0, 0, x)))) :=
    concreteStep_mono sub2 (handoff_step s 1 (postHandoff qexit s (postHandoff 0 qexit (0, 0, x))) rfl)
  refine ⟨3, le_refl 3, postHandoff s 1 (postHandoff qexit s (postHandoff 0 qexit (0, 0, x))), ?_, rfl⟩
  exact ⟨_, step1, _, step2, _, step3, rfl⟩

/-!
**The control skeleton, validated concretely.**  `demoRouting` is a real concrete `TMachine` assembled from `handoffRules`
jump tables, and `demoRouting_accepts` proves it accepts every input in 3 steps via the full `init → exit → handoff →
accept` pipeline — each step the proved `handoff_step` (331) lifted by monotonicity (329), reaching the global accept
state `1`.  So the routing control structure genuinely accepts concrete tables.  Instantiating the *real* phases
(decode/dispatch; the universal simulator 296–298 and bounded complement 299, as concrete tables) plus the `f`-timing is
the remaining low-level construction, not faked.  Fourth verified brick.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachinePhaseDemo

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachinePhaseDemo.demoRouting_accepts
