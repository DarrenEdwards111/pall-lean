import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AbstractHierarchy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedEnumeration

/-!
# `TIME(bound) ⊊ Computable`: the abstract hierarchy, discharged concretely (Williams machine model, rung 1c) (PROVED)

`ACC0AbstractHierarchy.abstract_time_hierarchy` is parametric in `Small`/`Big` with two inputs
(`hsmall`: small-class enumerability; `hbig`: the diagonal in `Big`).  Rung 1 (`ACC0TimedEnumeration`) gives
a **concrete** time-bounded class via `evaln`; here we plug it in, discharging **both** inputs and
obtaining a real strict separation:

  `timed_class_proper` — `∃ L, Computable L ∧ ¬ ∃ e, L = timedEnum bound e`: some computable language is
  decided by **no** `bound`-time program.
  `timed_collapse_false` — `¬ (∀ L, Computable L → ∃ e, L = timedEnum bound e)`: the `bound`-time class
  does **not** exhaust `Computable`.

`hsmall` holds **definitionally** (the small class *is* `Set.range (timedEnum bound)`); `hbig` is
`timedEnum_diag_computable`.  So `TIME(bound) ⊊ Computable` on the concrete `evaln` model — the abstract
hierarchy machinery is non-vacuous with a genuine timed class (stronger than the `Big := Computable`,
arbitrary-`D` instance of `ACC0ComputableHierarchy`).

## What is proved (clean axioms, no `sorry`)

* `timed_class_proper` / `timed_collapse_false` — `TIME(bound) ⊊ Computable` via the concrete `evaln` model.

## Honest scope

The *untimed* separation `TIME(bound) ⊊ Computable`, discharging the abstract hierarchy concretely.  The
Williams **time** hierarchy (`TIME(bound) ⊊ TIME(bigbound)` for `bigbound` only slightly larger) still
needs the efficient universal simulator (`evaln` overhead `≤ bigbound`) — the deep machine-model gap,
Williams-strength, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchy

open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel (diag)
open PallLean.Paper93.DeepMath.PathB.ACC0AbstractHierarchy (abstract_time_hierarchy collapse_false_of_hierarchy)
open PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration
  (timedEnum timedEnum_diag_computable)

/-- **`TIME(bound) ⊊ Computable` (proved): some computable language is decided by no `bound`-time
program.**  A concrete, non-vacuous instance of `abstract_time_hierarchy` via the `evaln` model. -/
theorem timed_class_proper (bound : ℕ → ℕ) (hb : Computable bound) :
    ∃ L, Computable L ∧ ¬ ∃ e, L = timedEnum bound e :=
  abstract_time_hierarchy (Small := fun L => ∃ e, L = timedEnum bound e) (Big := Computable)
    (timedEnum bound) (fun _ hL => hL) (timedEnum_diag_computable bound hb)

/-- **The `bound`-time class does not exhaust `Computable` (proved).** -/
theorem timed_collapse_false (bound : ℕ → ℕ) (hb : Computable bound) :
    ¬ (∀ L, Computable L → ∃ e, L = timedEnum bound e) :=
  collapse_false_of_hierarchy (Small := fun L => ∃ e, L = timedEnum bound e) (Big := Computable)
    (timedEnum bound) (fun _ hL => hL) (timedEnum_diag_computable bound hb)

/-!
**Rung 1c proved.**  `TIME(bound) ⊊ Computable` on the concrete `evaln` model — the abstract hierarchy
discharged with a genuine timed class.  The Williams *time* hierarchy (`TIME(bound) ⊊ TIME(bigbound)`)
needs the efficient universal simulator, the remaining deep gap.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchy.timed_class_proper
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchy.timed_collapse_false
