import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimRuntime
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DiagHasCode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedHierarchyConditional

/-!
# Efficient-simulation build, rung 2: the time hierarchy with an EXPLICIT runtime `bigbound` (PROVED)

`ACC0TimedHierarchyUnconditional` proved `∃ bigbound, TIME(bound) ⊊ TIME(bigbound)` but with `bigbound`
an opaque `Classical.choose`'d halting budget — *unbounded* in any analyzable way.  Rung 1's runtime
measure lets us name it canonically: `bigbound = diagRuntime`, the **least** fuel the diagonal `Code`
needs.  This is the object rung 3 will actually *bound* (the universal-simulation overhead) — you cannot
bound a `choose`.

  `diagCode` — the diagonal-computing `Code` (from `diag_has_code`).
  `diagRuntime bound hb e` — `runtimeOf (diagCode …) e` (the diagonal Code's minimal halting budget on `e`).
  `timed_hierarchy_explicit` — `TIME(bound) ⊊ TIME(diagRuntime …)`: the strict hierarchy with the
  explicit, minimal runtime `bigbound`.

## What is proved (clean axioms, no `sorry`)

* `diagCode`, `diagCode_eval` — the diagonal Code and its semantics.
* `diagRuntime` — the explicit runtime `bigbound`.
* `timed_hierarchy_explicit` — `∃ L, InTime (diagRuntime …) L ∧ ¬ InTime bound L`.

## Honest scope

`bigbound` is now the *named minimal runtime* of the diagonal Code, not a choice — but still possibly
enormous.  Rung 3 (bounding `diagRuntime` by a controlled function of `bound` — the efficient
universal-simulation overhead) is the deep Williams-strength content, **not** built here.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimExplicitBound

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel (diag)
open PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration (timedEnum)
open PallLean.Paper93.DeepMath.PathB.ACC0DiagHasCode (diag_has_code)
open PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyConditional
  (InTime timed_hierarchy_of_simulator)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime (runtimeOf runtimeOf_isSome halts_iff_dom)

/-- The diagonal-computing `Code` (from `diag_has_code`). -/
noncomputable def diagCode (bound : ℕ → ℕ) (hb : Computable bound) : Code :=
  (diag_has_code bound hb).choose

/-- Its semantics: `diagCode` computes `(diag (timedEnum bound) ·).toNat`. -/
theorem diagCode_eval (bound : ℕ → ℕ) (hb : Computable bound) :
    (diagCode bound hb).eval = (fun e => (diag (timedEnum bound) e).toNat : ℕ →. ℕ) :=
  (diag_has_code bound hb).choose_spec

/-- The diagonal Code halts on every input. -/
theorem diagCode_halts (bound : ℕ → ℕ) (hb : Computable bound) (e : ℕ) :
    ∃ k, (Code.evaln k (diagCode bound hb) e).isSome := by
  rw [halts_iff_dom, diagCode_eval bound hb]
  trivial

/-- **The explicit runtime `bigbound`**: the diagonal Code's minimal halting budget on `e`. -/
noncomputable def diagRuntime (bound : ℕ → ℕ) (hb : Computable bound) (e : ℕ) : ℕ :=
  runtimeOf (diagCode bound hb) e (diagCode_halts bound hb e)

/-- At the runtime budget, the diagonal Code returns the diagonal value. -/
theorem evaln_diagRuntime (bound : ℕ → ℕ) (hb : Computable bound) (e : ℕ) :
    Code.evaln (diagRuntime bound hb e) (diagCode bound hb) e
      = some ((diag (timedEnum bound) e).toNat) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
    (runtimeOf_isSome (diagCode bound hb) e (diagCode_halts bound hb e))
  have hmem1 : v ∈ (diagCode bound hb).eval e := evaln_sound hv
  have hmem2 : ((diag (timedEnum bound) e).toNat) ∈ (diagCode bound hb).eval e := by
    rw [diagCode_eval bound hb]; exact Part.mem_some _
  have hvv : v = (diag (timedEnum bound) e).toNat := Part.mem_unique hmem1 hmem2
  show Code.evaln (runtimeOf (diagCode bound hb) e (diagCode_halts bound hb e)) (diagCode bound hb) e
    = some ((diag (timedEnum bound) e).toNat)
  rw [hv, hvv]

/-- **The time hierarchy with the explicit runtime `bigbound` (proved): `TIME(bound) ⊊ TIME(diagRuntime)`.** -/
theorem timed_hierarchy_explicit (bound : ℕ → ℕ) (hb : Computable bound) :
    ∃ L, InTime (diagRuntime bound hb) L ∧ ¬ InTime bound L := by
  have hsim : timedEnum (diagRuntime bound hb) (Encodable.encode (diagCode bound hb))
      = diag (timedEnum bound) := by
    funext e
    show decide (Code.evaln (diagRuntime bound hb e)
      (Denumerable.ofNat Code (Encodable.encode (diagCode bound hb))) e = some 1)
        = diag (timedEnum bound) e
    rw [Denumerable.ofNat_encode, evaln_diagRuntime bound hb e]
    cases h : diag (timedEnum bound) e <;> simp [h, Bool.toNat]
  exact timed_hierarchy_of_simulator bound (diagRuntime bound hb)
    ⟨Encodable.encode (diagCode bound hb), hsim⟩

/-!
**Rung 2 proved.**  `bigbound = diagRuntime` is the diagonal Code's *named minimal runtime*, and
`TIME(bound) ⊊ TIME(diagRuntime)`.  Rung 3 bounds `diagRuntime` by a controlled function of `bound` (the
efficient universal-simulation overhead) — the deep gap.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimExplicitBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimExplicitBound.timed_hierarchy_explicit
