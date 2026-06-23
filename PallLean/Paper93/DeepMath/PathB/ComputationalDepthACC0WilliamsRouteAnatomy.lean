import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ToBTNormalForm
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ExactBTNormalForm
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ExactBoundedAndOr
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitSatSearchable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0HierarchyCountable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ComputableHierarchy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BTSizeRecurrence
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaIndicator

/-!
# ACC⁰ Williams route — complete anatomy (top-level capstone manifest)

A single machine-checked top-level index of the whole `NEXP ⊄ ACC⁰` (Williams) attack built this thread,
tying together **both** halves and naming the **two** genuine research walls.  Everything below is clean
(`[propext, Classical.choice, Quot.sound]`, no `sorry`, no custom axioms); the diagonalization rungs are
axiom-free.  See the per-half manifests `ACC0IntegerExactArcManifest` and
`ACC0AlgorithmicHierarchyManifest` for the full rung-by-rung indices.

## Half A — the polynomial (Beigel–Tarui) representation

For every constant-depth ACC⁰[p] circuit, build a sparse low-degree `SYM∘AND` representation:

* `acc0_to_bt_normal_form` — **RS approximant**, *all* fan-ins: degree `≤ L^D`, support `≤ (n+1)^{L^D}`
  (quasipoly), agrees `1−ε`.
* `acc0_exact_bt_normal_form` — **exact**, bounded `AND`/`OR` fan-in: eval-exact + degree `≤ w^D` +
  quasipoly support, *no approximation*.
* `toPoly_totalDegree_le_of_faninLeAndOr` — exact degree `≤ w^depth` with **unbounded MOD fan-in** (the
  realistic ACC⁰[p]; `MOD` degree `q−1` is fan-in-independent).
* `acc0circuit_sat_searchable` — the algorithmic cash-out: bounded collapse ⇒ sub-`2^n` SAT search.

## Half B — the algorithmic (`NEXP ⊄ ACC⁰`) interface

* `probabilistic_route_to_NEXP_not_ACC0` — the modus-ponens interface: SAT-speedup + `NEXP ⊆ ACC⁰`
  ⇒ `Collapse`, and `¬ Collapse` ⇒ `¬ (NEXP ⊆ ACC⁰)`.
* `time_hierarchy_of_countable` — the `¬ Collapse` structure from diagonalization (enumerability free by
  countability), modulo diagonal simulability.
* `computable_hierarchy` — the non-vacuous (untimed) instance of that structure.

## The two walls (genuine research, single ingredient each — NOT built, NOT faked)

1. **Polynomial wall** — exact-*and*-quasipoly for **unbounded `AND`/`OR` fan-in** across depth: the
   exact polynomial route no-gos (degree `=` fan-in, `ACC0ExactDegreeNoGo`) and the exact symmetric
   collapse towers.  The Beigel–Tarui **integer** (Toda) route's *core mechanism* is now **built**
   (`todaIterate_indicator`: a `MOD` gate gets a degree-`3^k` polynomial exact mod `p^{2^k}` — exact
   polylog-degree for *unbounded `MOD` fan-in*); the residual wall is the **across-depth assembly** of
   those per-gate indicators into one exact quasipoly `SYM∘AND` (and `AND`/`OR` still need RS
   approximation or the integer construction's `AC⁰` part).
2. **Algorithmic wall** — the quantitative `hbig`: the diagonal computable within the big class's
   *budget*, i.e. a bounded-overhead universal simulator + nondeterministic lazy diagonalization, plus
   the `williams` succinct-SAT reduction.

Both are Williams-strength.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0WilliamsRouteAnatomy

-- Half A: polynomial representation
#check @ACC0ToBTNormalForm.acc0_to_bt_normal_form
#check @ACC0ExactBTNormalForm.acc0_exact_bt_normal_form
#check @ACC0ExactBoundedAndOr.toPoly_totalDegree_le_of_faninLeAndOr
#check @ACC0CircuitSatSearchable.acc0circuit_sat_searchable
#check @ACC0TodaIndicator.todaIterate_indicator

-- Half B: algorithmic interface
#check @ACC0BTSizeRecurrence.probabilistic_route_to_NEXP_not_ACC0
#check @ACC0HierarchyCountable.time_hierarchy_of_countable
#check @ACC0ComputableHierarchy.computable_hierarchy

-- Clean-axiom confirmation of the two headline halves
#print axioms ACC0ExactBTNormalForm.acc0_exact_bt_normal_form
#print axioms ACC0HierarchyCountable.time_hierarchy_of_countable

end PallLean.Paper93.DeepMath.PathB.ACC0WilliamsRouteAnatomy
