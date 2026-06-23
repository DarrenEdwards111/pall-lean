import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DiagonalizationKernel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AbstractHierarchy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0HierarchyCountable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ComputableHierarchy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BTSizeRecurrence
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedEnumeration
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedHierarchy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedModelProps
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedModelComplete
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedHierarchyConditional
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DiagHasCode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedHierarchyUnconditional

/-!
# Williams algorithmic half — machine-checked manifest of the hierarchy ladder

A single verified entry point for the **algorithmic** half of Williams' `NEXP ⊄ ACC⁰` route (the user's
point #3): the `¬ Collapse` hierarchy ladder, built rung by rung from the interface socket down to a
single concrete machine-model gap.  All clean (no `sorry`, no custom axioms); the diagonalization rungs
depend on **no axioms at all**.  Mirrors the exact-arc manifest (`ACC0IntegerExactArcManifest`).

## The ladder (9 rungs)

1. **Interface socket** — `probabilistic_route_to_NEXP_not_ACC0`: the abstract modus-ponens
   `RSRep → ACC0SatSpeedup`, `williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse`,
   `hierarchy : ¬ Collapse` ⟹ `¬ NEXPHasACC0Circuits`.  The two undischarged inputs are `williams`
   (succinct-SAT reduction) and `hierarchy` (the time hierarchy).
2. **Diagonalization kernel** — `diag_not_mem_range`: the diagonal escapes any enumeration (no axioms).
3. **Abstract hierarchy** — `abstract_time_hierarchy` / `collapse_false_of_hierarchy`: diagonalization ⇒
   strict `Small ⊊ Big`, hence `¬ Collapse`, modulo enumerability (`hsmall`) + simulability (`hbig`).
4. **Countable reduction** — `time_hierarchy_of_countable`: `hsmall` is **free** for any countable class,
   so only `hbig` remains.
5. **Computable instance** — `computable_hierarchy`: `hbig` discharged in the **untimed** regime
   (`Big := Computable`) — the structure is non-vacuous.
6. **Concrete `evaln` timed class** — `timedEnum` + `timedEnum_diag_not_mem` (the diagonal decided by no
   `bound`-time program) + `timedEnum_diag_computable` (the diagonal computable): a real step-counted model
   via Mathlib's `Nat.Partrec.Code.evaln`, not the abstract parametric `Small`.
7. **`TIME(bound) ⊊ Computable`** — `timed_class_proper` / `timed_collapse_false`: rung 6 wired into the
   abstract hierarchy, discharging **both** inputs concretely (`hsmall` definitional, `hbig` =
   `timedEnum_diag_computable`).  The hierarchy is non-vacuous with a *genuine timed class*.
8. **Timed-model metatheory** — `timedEnum_accept_mono` (acceptance monotone in the budget),
   `timedEnum_sound` (bounded ⇒ true acceptance), `timedEnum_captures_eval` (`⋃_k`-acceptance `=` true
   acceptance), `timedEnum_input_bound` (acceptance ⇒ `n < bound n`): the model is a faithful resource
   refinement of the partial-recursive semantics.
9. **Time hierarchy — conditional then unconditional** — `timed_hierarchy_of_simulator` (the hierarchy
   follows from `hsim`, a `bigbound`-time program computing the diagonal; the `¬TIME(bound)` half is
   unconditional), `diag_has_code` (that program **exists** as a concrete `Code`, by completeness over the
   computable diagonal), and `timed_hierarchy_unconditional` (**`hsim` discharged**: choosing `bigbound`
   as the diagonal-Code's halting budget gives `∃ bigbound, TIME(bound) ⊊ TIME(bigbound)` outright).

So the **bare strict time hierarchy is now unconditional** (crude `bigbound`).

## The single remaining gap

**Efficiency**: that `bigbound` can be taken only *slightly* larger than `bound` (polylog overhead), not
the diagonal-Code's opaque halting budget — i.e. an `evaln` **running-time** bound (Hennie–Stearns
`t·polylog`), together with the `williams` succinct-SAT reduction.  This efficiency is *essential* (a crude
hierarchy does **not** give `NEXP ⊄ ACC⁰`) and needs an `evaln` cost analysis Mathlib lacks —
Williams-strength, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0AlgorithmicHierarchyManifest

-- Rung 1: the interface socket
#check @ACC0BTSizeRecurrence.probabilistic_route_to_NEXP_not_ACC0

-- Rung 2: diagonalization kernel
#check @ACC0DiagonalizationKernel.diag_ne
#check @ACC0DiagonalizationKernel.diag_not_mem_range
#check @ACC0DiagonalizationKernel.no_decider_decides_own_diagonal

-- Rung 3: abstract hierarchy
#check @ACC0AbstractHierarchy.abstract_time_hierarchy
#check @ACC0AbstractHierarchy.collapse_false_of_hierarchy

-- Rung 4: countable reduction (hsmall free)
#check @ACC0HierarchyCountable.enumeration_of_countable
#check @ACC0HierarchyCountable.time_hierarchy_of_countable

-- Rung 5: computable instance (hbig discharged untimed)
#check @ACC0ComputableHierarchy.computable_diag
#check @ACC0ComputableHierarchy.computable_hierarchy

-- Rung 6: concrete evaln timed class
#check @ACC0TimedEnumeration.timedEnum
#check @ACC0TimedEnumeration.timedEnum_diag_not_mem
#check @ACC0TimedEnumeration.timedEnum_diag_computable

-- Rung 7: TIME(bound) ⊊ Computable (abstract hierarchy discharged concretely)
#check @ACC0TimedHierarchy.timed_class_proper
#check @ACC0TimedHierarchy.timed_collapse_false

-- Rung 8: timed-model metatheory (monotonicity, soundness, completeness, input bound)
#check @ACC0TimedModelProps.timedEnum_accept_mono
#check @ACC0TimedModelProps.timedEnum_sound
#check @ACC0TimedModelComplete.timedEnum_captures_eval
#check @ACC0TimedModelComplete.timedEnum_input_bound

-- Rung 9: time hierarchy — conditional, program-exists, then unconditional (crude)
#check @ACC0TimedHierarchyConditional.timed_hierarchy_of_simulator
#check @ACC0DiagHasCode.diag_has_code
#check @ACC0TimedHierarchyUnconditional.timed_hierarchy_unconditional

-- Axiom confirmation: the diagonalization rungs are axiom-free; the hierarchy is clean
#print axioms ACC0DiagonalizationKernel.diag_not_mem_range
#print axioms ACC0AbstractHierarchy.abstract_time_hierarchy
#print axioms ACC0HierarchyCountable.time_hierarchy_of_countable
#print axioms ACC0ComputableHierarchy.computable_hierarchy
#print axioms ACC0TimedHierarchy.timed_class_proper
#print axioms ACC0TimedModelComplete.timedEnum_captures_eval
#print axioms ACC0TimedHierarchyUnconditional.timed_hierarchy_unconditional

end PallLean.Paper93.DeepMath.PathB.ACC0AlgorithmicHierarchyManifest
