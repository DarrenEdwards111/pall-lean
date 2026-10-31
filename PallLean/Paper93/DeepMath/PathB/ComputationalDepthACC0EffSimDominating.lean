import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimExplicitBound

/-!
# Efficient-simulation build, rung 3: the hierarchy for ANY budget dominating the diagonal runtime (PROVED)

Rung 2 gave `TIME(bound) ⊊ TIME(diagRuntime)` with `diagRuntime` the diagonal Code's *minimal* runtime.
Rung 1's **stability** (`evaln_runtimeOf_stable`: `evaln` is constant at or above the runtime budget) now
lets us run the *same* diagonal program within **any** larger budget `g ≥ diagRuntime`, still computing the
diagonal exactly.  Hence:

  `efficient_hierarchy_of_dominating` — for any `g` with `diagRuntime bound hb ≤ g` pointwise,
  `∃ L, InTime g L ∧ ¬ InTime bound L`, i.e. `TIME(bound) ⊊ TIME(g)`.

This **reduces the entire efficiency question to one clean statement**: *does there exist a controlled
(only slightly super-linear) `g` with `diagRuntime ≤ g`?*  The `¬ InTime bound` half is unconditional; the
inclusion-into-`TIME(g)` half is now free for *every* dominating `g` via stability.  So the lone remaining
ingredient (rung 4) is the **overhead bound** `diagRuntime bound e ≤ g(bound, e)` with `g` efficient — the
Hennie–Stearns universal-simulation cost.

## What is proved (clean axioms, no `sorry`)

* `efficient_hierarchy_of_dominating` — `diagRuntime ≤ g ⇒ TIME(bound) ⊊ TIME(g)`.

## Honest scope

The hierarchy now holds for *any* dominating budget `g`; what remains is exhibiting a **controlled** such
`g` (rung 4), i.e. bounding `diagRuntime` by a slightly-super-linear function — the efficient
universal-simulation overhead, the deep Williams-strength gap, **not** built.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimDominating

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel (diag)
open PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration (timedEnum)
open PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyConditional
  (InTime timed_hierarchy_of_simulator)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime (evaln_runtimeOf_stable)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimExplicitBound
  (diagCode diagCode_halts diagRuntime evaln_diagRuntime)

/-- **The efficient hierarchy for any dominating budget (proved): `diagRuntime ≤ g ⇒ TIME(bound) ⊊
TIME(g)`.**  Stability lets the diagonal program run within any `g ≥ diagRuntime`, still computing the
diagonal — so the only remaining question is whether a *controlled* such `g` exists. -/
theorem efficient_hierarchy_of_dominating (bound g : ℕ → ℕ) (hb : Computable bound)
    (hdom : ∀ e, diagRuntime bound hb e ≤ g e) :
    ∃ L, InTime g L ∧ ¬ InTime bound L := by
  have key : ∀ e, Code.evaln (g e) (diagCode bound hb) e
      = some ((diag (timedEnum bound) e).toNat) := by
    intro e
    rw [evaln_runtimeOf_stable (diagCode bound hb) e (diagCode_halts bound hb e) (hdom e)]
    exact evaln_diagRuntime bound hb e
  have hsim : timedEnum g (Encodable.encode (diagCode bound hb)) = diag (timedEnum bound) := by
    funext e
    show decide (Code.evaln (g e)
      (Denumerable.ofNat Code (Encodable.encode (diagCode bound hb))) e = some 1)
        = diag (timedEnum bound) e
    rw [Denumerable.ofNat_encode, key e]
    cases h : diag (timedEnum bound) e <;> simp [h, Bool.toNat]
  exact timed_hierarchy_of_simulator bound g ⟨Encodable.encode (diagCode bound hb), hsim⟩

/-!
**Rung 3 proved.**  Via stability, `TIME(bound) ⊊ TIME(g)` for *every* `g ≥ diagRuntime`.  The efficiency
question is now exactly: exhibit a **controlled** (slightly super-linear) `g` dominating `diagRuntime` —
the universal-simulation overhead bound (rung 4), the deep gap.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimDominating

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimDominating.efficient_hierarchy_of_dominating
