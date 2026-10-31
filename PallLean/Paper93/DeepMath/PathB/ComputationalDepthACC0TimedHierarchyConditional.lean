import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedEnumeration

/-!
# The time hierarchy, reduced to exactly the efficient-simulator hypothesis (rung 2, conditional) (PROVED)

This isolates the **entire** remaining machine-model gap to a single concrete hypothesis.  Writing
`InTime bound L` for "`L` is decided by some program within `bound` steps" (`∃ e, L = timedEnum bound e`),
the Williams time hierarchy `TIME(bound) ⊊ TIME(bigbound)` follows from one fact:

  `timed_hierarchy_of_simulator` — **if** some program `e₀` computes the diagonal within `bigbound`
  (`timedEnum bigbound e₀ = diag (timedEnum bound)`), **then** `∃ L, InTime bigbound L ∧ ¬ InTime bound L`.

The `¬ InTime bound`-direction is **unconditional** (`ACC0TimedEnumeration.timedEnum_diag_not_mem`); the
*only* hypothesis is `hsim` — the existence of a `bigbound`-time program computing the diagonal.  That
`hsim` **is** the efficient universal simulator (`evaln` running within `bigbound`, Hennie–Stearns
`t·polylog` overhead): the lone deep ingredient, now named exactly, with everything else proved.

  `timed_hierarchy_gap` — restates it: the hierarchy holds the moment `diag (timedEnum bound)` is in
  `InTime bigbound`.

## What is proved (clean axioms, no `sorry`)

* `InTime` — the time-bounded class (decided by some program within the budget).
* `timed_hierarchy_of_simulator` / `timed_hierarchy_gap` — `hsim ⇒ TIME(bound) ⊊ TIME(bigbound)`.

## Honest scope

The hierarchy is reduced to `hsim` (a `bigbound`-time program computing the diagonal) — the efficient
universal simulator, the deep machine-model gap that needs an `evaln` running-time bound Mathlib lacks.
**Not** discharged here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyConditional

open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel (diag)
open PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration (timedEnum timedEnum_diag_not_mem)

/-- `L` is decided by some program within `bound` steps. -/
def InTime (bound : ℕ → ℕ) (L : ℕ → Bool) : Prop := ∃ e, L = timedEnum bound e

/-- **The time hierarchy from the simulator hypothesis (proved).**  If some `bigbound`-time program
computes the diagonal, then `TIME(bound) ⊊ TIME(bigbound)` — the `¬ InTime bound` half is unconditional. -/
theorem timed_hierarchy_of_simulator (bound bigbound : ℕ → ℕ)
    (hsim : ∃ e₀, timedEnum bigbound e₀ = diag (timedEnum bound)) :
    ∃ L, InTime bigbound L ∧ ¬ InTime bound L := by
  refine ⟨diag (timedEnum bound), ?_, ?_⟩
  · obtain ⟨e₀, he₀⟩ := hsim
    exact ⟨e₀, he₀.symm⟩
  · rintro ⟨e, he⟩
    exact timedEnum_diag_not_mem bound ⟨e, he.symm⟩

/-- **The gap, named exactly (proved): the hierarchy holds once the diagonal is `bigbound`-time.** -/
theorem timed_hierarchy_gap (bound bigbound : ℕ → ℕ)
    (hgap : InTime bigbound (diag (timedEnum bound))) :
    ∃ L, InTime bigbound L ∧ ¬ InTime bound L :=
  timed_hierarchy_of_simulator bound bigbound
    (by obtain ⟨e₀, he₀⟩ := hgap; exact ⟨e₀, he₀.symm⟩)

/-!
**Rung 2 (conditional) proved.**  `TIME(bound) ⊊ TIME(bigbound)` reduces to exactly `hsim` — a
`bigbound`-time program computing the diagonal, i.e. the efficient universal simulator.  Everything else
(`¬ InTime bound`) is proved unconditionally.  Discharging `hsim` needs an `evaln` running-time bound
(Hennie–Stearns) Mathlib lacks — the deep gap.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyConditional

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyConditional.timed_hierarchy_of_simulator
