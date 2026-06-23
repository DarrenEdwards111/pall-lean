import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DiagHasCode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedHierarchyConditional

/-!
# An **unconditional** (crude) time hierarchy: `∃ bigbound, TIME(bound) ⊊ TIME(bigbound)` (rung 2b) (PROVED)

`ACC0TimedHierarchyConditional` reduced the hierarchy to `hsim` (a `bigbound`-time program computing the
diagonal), and `ACC0DiagHasCode` produced the program `c` (unbounded).  Here we **discharge `hsim`
outright**: choose `bigbound e` to be the *actual* halting budget of `c` on input `e` — it exists pointwise
because `c` is total (`evaln_complete`).  No efficiency is claimed, so no `evaln` running-time bound is
needed; `bigbound` need not even be computable.  This yields the strict separation with the hypothesis
removed:

  `timed_hierarchy_unconditional` — `∃ bigbound, ∃ L, InTime bigbound L ∧ ¬ InTime bound L`.

So `TIME(bound) ⊊ TIME(bigbound)` holds **unconditionally** for *some* `bigbound` — the diagonal is
decided in *some* larger budget but never within `bound`.  This is the bare strict time hierarchy; what
remains for the Williams cash-out is only **efficiency** — that `bigbound` can be taken *slightly larger*
than `bound` (polylog overhead), the Hennie–Stearns ingredient.

## What is proved (clean axioms, no `sorry`)

* `timed_hierarchy_unconditional` — `∃ bigbound`, `TIME(bound) ⊊ TIME(bigbound)`, hypothesis-free.

## Honest scope

The *crude* hierarchy (`bigbound` = the diagonal-Code's halting budget, possibly enormous and noncomputable).
The Williams cash-out needs `bigbound` **efficient** (slightly larger than `bound`) — the `evaln`
running-time bound Mathlib lacks.  **Not** built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyUnconditional

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel (diag)
open PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration (timedEnum)
open PallLean.Paper93.DeepMath.PathB.ACC0DiagHasCode (diag_has_code)
open PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyConditional
  (InTime timed_hierarchy_of_simulator)

/-- **Unconditional (crude) time hierarchy (proved): `∃ bigbound, TIME(bound) ⊊ TIME(bigbound)`.**
`bigbound e` is the diagonal-Code's actual halting budget on `e` (exists pointwise; no efficiency). -/
theorem timed_hierarchy_unconditional (bound : ℕ → ℕ) (hb : Computable bound) :
    ∃ bigbound : ℕ → ℕ, ∃ L, InTime bigbound L ∧ ¬ InTime bound L := by
  obtain ⟨c, hc⟩ := diag_has_code bound hb
  -- pointwise: the diagonal value is reached at some finite budget (c is total)
  have hex : ∀ e, ∃ k, Code.evaln k c e = some ((diag (timedEnum bound) e).toNat) := by
    intro e
    have hmem : ((diag (timedEnum bound) e).toNat) ∈ c.eval e := by rw [hc]; exact Part.mem_some _
    exact evaln_complete.mp hmem
  classical
  let bigbound : ℕ → ℕ := fun e => (hex e).choose
  have hbb : ∀ e, Code.evaln (bigbound e) c e = some ((diag (timedEnum bound) e).toNat) :=
    fun e => (hex e).choose_spec
  -- the encoded `c` computes the diagonal within `bigbound`
  have hsim : timedEnum bigbound (Encodable.encode c) = diag (timedEnum bound) := by
    funext n
    show decide (Code.evaln (bigbound n) (Denumerable.ofNat Code (Encodable.encode c)) n = some 1)
      = diag (timedEnum bound) n
    rw [Denumerable.ofNat_encode, hbb n]
    cases h : diag (timedEnum bound) n <;> simp [h, Bool.toNat]
  exact ⟨bigbound, timed_hierarchy_of_simulator bound bigbound ⟨Encodable.encode c, hsim⟩⟩

/-!
**Rung 2b proved.**  `TIME(bound) ⊊ TIME(bigbound)` holds unconditionally for *some* `bigbound` (the
diagonal-Code's halting budget) — `hsim` discharged.  Only **efficiency** (`bigbound` slightly larger than
`bound`, the Hennie–Stearns overhead) remains for the Williams cash-out.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyUnconditional

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyUnconditional.timed_hierarchy_unconditional
