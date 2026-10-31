import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0HierarchyCountable

/-!
# The abstract hierarchy, concretely instantiated in the computable regime (PROVED)

`time_hierarchy_of_countable` reduced the separation to one ingredient: the diagonal is computable
within the big class (`hbig`).  This file **discharges `hbig` concretely** in the one regime where it
needs no time-bounded simulator — the **computable** (untimed) regime — using Lean's `Computable`:

  `computable_diag` — the diagonal of a computable enumeration is computable.
  `computable_hierarchy` — for any computable enumeration `D`, the diagonal `diag D` is a **computable**
  predicate **not** in `Set.range D`: `Computable (diag D) ∧ diag D ∉ Set.range D`.

So the abstract hierarchy is **non-vacuous**: it has a genuine concrete instance.  The diagonal escapes
any computable enumeration *and* is itself computable — the classical computability diagonal, now
feeding `abstract_time_hierarchy` with `Big := Computable`.

## What is proved (clean axioms, no `sorry`)

* `computable_diag` — `Computable₂ D ⇒ Computable (diag D)`.
* `computable_hierarchy` — concrete separation: `diag D` is computable but escapes `Set.range D`.

## Honest scope — exactly the untimed instance

This discharges `hbig` for `Big := Computable` (no time bound): the diagonal is plainly computable from a
computable `D`.  The **time hierarchy** (`NTIME(2^n) ⊄ NTIME(2^n/ω(1))`) the Williams interface needs is
the *quantitative* version — there `hbig` requires the diagonal computable in the big class's **budget**,
i.e. a universal simulator with **bounded overhead** + nondeterministic lazy diagonalization.  That
overhead bound is the genuine remaining machine-model content; the untimed instance here shows the
structure is real but does **not** supply it.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ComputableHierarchy

open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel

/-- **The diagonal of a computable enumeration is computable (proved).** -/
theorem computable_diag (D : ℕ → ℕ → Bool) (hD : Computable₂ D) : Computable (diag D) := by
  have h1 : Computable (fun k => D k k) := hD.comp Computable.id Computable.id
  exact (Primrec.dom_bool _).to_comp.comp h1

/-- **The computable instance of the abstract hierarchy (proved).**  For any computable enumeration `D`,
the diagonal `diag D` is a computable predicate that escapes `Set.range D` — a genuine, non-vacuous
instance of `abstract_time_hierarchy` with `Big := Computable`. -/
theorem computable_hierarchy (D : ℕ → ℕ → Bool) (hD : Computable₂ D) :
    Computable (diag D) ∧ diag D ∉ Set.range D :=
  ⟨computable_diag D hD, diag_not_mem_range D⟩

/-!
**Computable instance proved.**  The abstract hierarchy is non-vacuous: the diagonal of a computable
enumeration is computable yet escapes it (`Big := Computable` discharges `hbig` untimed).  The *time*
hierarchy needs the diagonal computable within the big class's **budget** — a bounded-overhead universal
simulator — which this untimed instance does not provide; that overhead bound is the machine-model gap,
Williams-strength, not built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ComputableHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ComputableHierarchy.computable_diag
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ComputableHierarchy.computable_hierarchy
