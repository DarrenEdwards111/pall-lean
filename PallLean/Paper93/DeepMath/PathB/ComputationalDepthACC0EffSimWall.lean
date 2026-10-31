import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimDominating

/-!
# Efficient-simulation build, rung 4: the entire gap isolated as one overhead hypothesis (PROVED)

Rungs 1–3 built the complete reachable scaffolding: a runtime cost-measure (`diagRuntime`), the time
hierarchy with that explicit `bigbound`, and — via stability — the hierarchy for **any** budget dominating
`diagRuntime`.  The only thing left for the Williams *efficient* hierarchy is a **controlled** dominating
budget.  We isolate that as a single concrete hypothesis and discharge everything around it:

  `DiagRuntimePolyBounded bound hb` — `∃ g C k, (∀ e, diagRuntime bound hb e ≤ g e) ∧
  (∀ e, g e ≤ C·(bound e + e + 1)^k)`: the diagonal Code's runtime is bounded by a *polynomial* in the
  budget and input.  **This is exactly the efficient universal-simulation overhead** (Hennie–Stearns: a
  universal machine runs `evaln`'s `s`-step computation in `s·polylog`, hence `diagRuntime` is polynomial
  in `bound`).

  `efficient_poly_hierarchy_of_overhead` — `DiagRuntimePolyBounded ⇒ ∃ g, (g polynomially bounded) ∧
  TIME(bound) ⊊ TIME(g)`: the efficient hierarchy, with the overhead made explicit, follows immediately
  from rung 3.

So the *whole* algorithmic-half efficiency question is now this one hypothesis — everything else is proved.

## What is proved (clean axioms, no `sorry`)

* `DiagRuntimePolyBounded` — the overhead hypothesis (the named terminal ingredient).
* `efficient_poly_hierarchy_of_overhead` — it yields the efficient poly-overhead time hierarchy.

## Honest scope — the terminal wall

`DiagRuntimePolyBounded` is **not** discharged.  Discharging it is the efficient universal simulation
(Hennie–Stearns) on Mathlib's `PartrecToTM2`, obstructed by: `evaln` being `@[irreducible]` (no structural
cost model), `exists_code` yielding an *opaque* diagonal code (no runtime handle), and Mathlib carrying
*correctness* but **no running-time bounds** for the TM translation.  That is the genuine Williams-strength
gap.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimWall

open PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyConditional (InTime)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimExplicitBound (diagRuntime)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimDominating (efficient_hierarchy_of_dominating)

/-- **The terminal overhead hypothesis**: the diagonal Code's runtime is polynomially bounded in the
budget and input — i.e. the efficient universal-simulation overhead (Hennie–Stearns). -/
def DiagRuntimePolyBounded (bound : ℕ → ℕ) (hb : Computable bound) : Prop :=
  ∃ (g : ℕ → ℕ) (C k : ℕ),
    (∀ e, diagRuntime bound hb e ≤ g e) ∧ (∀ e, g e ≤ C * (bound e + e + 1) ^ k)

/-- **The efficient poly-overhead time hierarchy from the overhead hypothesis (proved).**  Everything
around the Hennie–Stearns ingredient is discharged. -/
theorem efficient_poly_hierarchy_of_overhead (bound : ℕ → ℕ) (hb : Computable bound)
    (hpoly : DiagRuntimePolyBounded bound hb) :
    ∃ (g : ℕ → ℕ) (C k : ℕ),
      (∀ e, g e ≤ C * (bound e + e + 1) ^ k) ∧ ∃ L, InTime g L ∧ ¬ InTime bound L := by
  obtain ⟨g, C, k, hdom, hgC⟩ := hpoly
  exact ⟨g, C, k, hgC, efficient_hierarchy_of_dominating bound g hb hdom⟩

/-!
**Rung 4 proved (the gap isolated).**  `TIME(bound) ⊊ TIME(g)` with `g` polynomially bounded follows from
the single hypothesis `DiagRuntimePolyBounded`.  That hypothesis **is** the efficient universal-simulation
overhead — the terminal Williams-strength wall, blocked by `evaln`'s irreducibility, `exists_code`'s opaque
output, and the absence of TM running-time bounds in Mathlib.  Everything else in the efficient-simulation
build (rungs 1–4) is proved.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimWall

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimWall.efficient_poly_hierarchy_of_overhead
