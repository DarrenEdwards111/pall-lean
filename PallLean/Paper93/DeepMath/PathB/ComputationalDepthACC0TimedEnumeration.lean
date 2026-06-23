import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DiagonalizationKernel

/-!
# A concrete step-counted time-bounded enumeration (Williams machine model, rung 1) (PROVED)

The algorithmic half of the Williams route needs a **timed** machine model to discharge the two abstract
inputs of `abstract_time_hierarchy` (`hsmall`: small-class enumerability; `hbig`: the diagonal in the big
class).  Rather than build Turing machines from scratch, we use Mathlib's step-indexed universal evaluator
`Nat.Partrec.Code.evaln : ℕ → Code → ℕ → Option ℕ` (run a Gödel-numbered program for a bounded number of
steps).  This gives a **concrete** enumeration of time-bounded deciders:

  `timedEnum bound e n` — `true` iff program `e` (decoded from `ℕ`) on input `n` halts with output `1`
  within `bound n` steps.

Two genuine facts, replacing the abstract parametric `Small`/`hsmall` with a real step-counted model:

  `timedEnum_diag_not_mem` — the diagonal language `diag (timedEnum bound)` is decided by **no** program
  within the `bound` step budget (concrete time-bounded inseparability — the lower-bound half of the
  hierarchy; unconditional).
  `timedEnum_eval_computable` — the underlying `evaln` evaluation is computable (when `bound` is), via
  `primrec_evaln` — the computable core for the untimed upper bound.

The diagonal is decided by no `bound`-time program, and the underlying `evaln` evaluation is computable —
the lower-bound half plus the computable core, toward a `Computable ⊋ TIME(bound)` separation on a
*concrete* evaln-based model.

## What is proved (clean axioms, no `sorry`)

* `timedEnum` — the concrete step-counted time-bounded enumeration.
* `timedEnum_diag_escapes` / `timedEnum_diag_not_mem` — the diagonal escapes every `bound`-time decider.
* `timedEnum_eval_computable` — the underlying `evaln` evaluation is computable.

## Honest scope

This is rung 1: a concrete model with the diagonal *not `bound`-time-decidable* and the `evaln` core
computable.  The full diagonal computability and the Williams **time** hierarchy (the diagonal decidable
within a *slightly larger* budget `bigbound`) remain —
i.e. an **efficient** universal simulator (`evaln`'s running time `≤ bigbound`, Hennie–Stearns-style
`t·polylog` overhead).  That overhead bound is the remaining machine-model gap, Williams-strength, **not**
built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel (diag diag_ne diag_not_mem_range)

/-- **Concrete step-counted time-bounded enumeration.**  `timedEnum bound e n = true` iff program `e`
(decoded from `ℕ`) on input `n` halts with output `1` within `bound n` steps. -/
noncomputable def timedEnum (bound : ℕ → ℕ) (e n : ℕ) : Bool :=
  decide (Code.evaln (bound n) (Denumerable.ofNat Code e) n = some 1)

/-- **The diagonal escapes every `bound`-time decider (proved).** -/
theorem timedEnum_diag_escapes (bound : ℕ → ℕ) (e : ℕ) :
    diag (timedEnum bound) ≠ timedEnum bound e :=
  diag_ne (timedEnum bound) e

/-- **Time-bounded inseparability (proved): no program within the `bound` step budget decides the
diagonal language.**  The lower-bound half of the time hierarchy, with a concrete `evaln` model. -/
theorem timedEnum_diag_not_mem (bound : ℕ → ℕ) :
    diag (timedEnum bound) ∉ Set.range (timedEnum bound) :=
  diag_not_mem_range (timedEnum bound)

/-- **The `evaln`-evaluation underlying the diagonal is computable (proved).**  `fun k ↦ evaln (bound k)
(decode k) k` is computable when `bound` is — the computable core from which the diagonal's computability
(the untimed upper bound) is assembled. -/
theorem timedEnum_eval_computable (bound : ℕ → ℕ) (hb : Computable bound) :
    Computable (fun k : ℕ => Code.evaln (bound k) (Denumerable.ofNat Code k) k) :=
  Code.primrec_evaln.to_comp.comp ((hb.pair (Computable.ofNat Code)).pair Computable.id)

/-!
**Rung 1 proved.**  A concrete step-counted model (`evaln`): the diagonal `diag (timedEnum bound)` is
decided by **no** program within the `bound` step budget (`timedEnum_diag_not_mem`), and the underlying
`evaln` evaluation is computable (`timedEnum_eval_computable`).  Remaining sub-rungs: (i) assemble the
diagonal's full computability (`decide (· = some 1)` + `Bool.not` over `timedEnum_eval_computable`) for the
untimed `Computable ⊋ TIME(bound)` separation; (ii) the **time** hierarchy — the diagonal within a
*slightly larger* budget via an efficient universal simulator (`evaln` overhead `≤ bigbound`), the deep
machine-model gap.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration.timedEnum_diag_not_mem
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration.timedEnum_eval_computable
