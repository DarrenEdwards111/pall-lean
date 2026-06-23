import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DiagonalizationKernel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AbstractHierarchy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0HierarchyCountable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ComputableHierarchy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BTSizeRecurrence

/-!
# Williams algorithmic half — machine-checked manifest of the hierarchy ladder

A single verified entry point for the **algorithmic** half of Williams' `NEXP ⊄ ACC⁰` route (the user's
point #3): the `¬ Collapse` hierarchy ladder, built rung by rung from the interface socket down to a
single concrete machine-model gap.  All clean (no `sorry`, no custom axioms); the diagonalization rungs
depend on **no axioms at all**.  Mirrors the exact-arc manifest (`ACC0IntegerExactArcManifest`).

## The ladder (5 rungs)

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

## The single remaining gap

`hbig` for the **quantitative** time classes: the diagonal computable within the big class's *budget* —
a universal simulator with **bounded overhead** + nondeterministic lazy diagonalization — together with
the `williams` succinct-SAT reduction.  That is the machine-model gap, Williams-strength, **not** built.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
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

-- Axiom confirmation: the diagonalization rungs are axiom-free; the hierarchy is clean
#print axioms ACC0DiagonalizationKernel.diag_not_mem_range
#print axioms ACC0AbstractHierarchy.abstract_time_hierarchy
#print axioms ACC0HierarchyCountable.time_hierarchy_of_countable
#print axioms ACC0ComputableHierarchy.computable_hierarchy

end PallLean.Paper93.DeepMath.PathB.ACC0AlgorithmicHierarchyManifest
