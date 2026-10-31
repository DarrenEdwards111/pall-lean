import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimDominating

/-!
# Efficient-simulation build, rung 4b: the gap as "an efficient decider for the diagonal exists" (PROVED)

Rung 4 isolated the gap for the *specific* `diagCode` (from `exists_code`), which may itself be inefficient.
The honest framing decouples it from that opaque construction: the efficient hierarchy follows from the
existence of **any** code computing the diagonal whose runtime is dominated by `g`.  So the real
ingredient is the *intrinsic* statement — the diagonal language has an efficiently-running decider — not a
property of one particular code.

  `efficient_hierarchy_of_efficient_code` — for any `Code c` that computes the diagonal value
  (`(diag (timedEnum bound) e).toNat ∈ c.eval e` for all `e`) and runs within `g` (`runtimeOf c e ≤ g e`),
  `TIME(bound) ⊊ TIME(g)`.

This is the cleanest statement of the terminal wall: discharging efficiency = exhibiting *some* code for
the diagonal with controlled runtime = the efficient universal simulation (Hennie–Stearns).

## What is proved (clean axioms, no `sorry`)

* `halts_of_mem` — a defined value gives a halting budget.
* `efficient_hierarchy_of_efficient_code` — an efficiently-running diagonal decider ⇒ `TIME(bound) ⊊ TIME(g)`.

## Honest scope

The hierarchy follows from *any* efficient diagonal decider; exhibiting one (controlled `runtimeOf`) is the
efficient universal simulation — the terminal Hennie–Stearns wall (blocked by `evaln`'s irreducibility and
the absence of TM running-time bounds in Mathlib), **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimEfficientCode

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel (diag)
open PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration (timedEnum)
open PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyConditional
  (InTime timed_hierarchy_of_simulator)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime
  (runtimeOf runtimeOf_isSome evaln_runtimeOf_stable)

/-- A defined computation value yields a halting budget. -/
theorem halts_of_mem {c : Code} {e v : ℕ} (h : v ∈ c.eval e) :
    ∃ k, (Code.evaln k c e).isSome := by
  obtain ⟨k, hk⟩ := evaln_complete.mp h
  exact ⟨k, Option.isSome_iff_exists.mpr ⟨v, hk⟩⟩

/-- **The efficient hierarchy from any efficiently-running diagonal decider (proved).**  If `c` computes
the diagonal value and runs within `g`, then `TIME(bound) ⊊ TIME(g)`. -/
theorem efficient_hierarchy_of_efficient_code (bound g : ℕ → ℕ) (hb : Computable bound) (c : Code)
    (hc : ∀ e, (diag (timedEnum bound) e).toNat ∈ c.eval e)
    (hdom : ∀ e, runtimeOf c e (halts_of_mem (hc e)) ≤ g e) :
    ∃ L, InTime g L ∧ ¬ InTime bound L := by
  have key : ∀ e, Code.evaln (g e) c e = some ((diag (timedEnum bound) e).toNat) := by
    intro e
    rw [evaln_runtimeOf_stable c e (halts_of_mem (hc e)) (hdom e)]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (runtimeOf_isSome c e (halts_of_mem (hc e)))
    rw [hv]
    congr 1
    exact Part.mem_unique (evaln_sound hv) (hc e)
  have hsim : timedEnum g (Encodable.encode c) = diag (timedEnum bound) := by
    funext e
    show decide (Code.evaln (g e) (Denumerable.ofNat Code (Encodable.encode c)) e = some 1)
      = diag (timedEnum bound) e
    rw [Denumerable.ofNat_encode, key e]
    cases h : diag (timedEnum bound) e <;> simp [h, Bool.toNat]
  exact timed_hierarchy_of_simulator bound g ⟨Encodable.encode c, hsim⟩

/-!
**Rung 4b proved.**  `TIME(bound) ⊊ TIME(g)` follows from *any* code computing the diagonal within `g` —
so the terminal ingredient is the *intrinsic* statement "the diagonal has an efficiently-running decider"
(controlled `runtimeOf`), i.e. the efficient universal simulation.  That is the Hennie–Stearns wall, **not**
built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimEfficientCode

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimEfficientCode.efficient_hierarchy_of_efficient_code
