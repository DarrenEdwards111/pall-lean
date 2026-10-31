import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedEnumeration

/-!
# The diagonal has a program: `hsim` narrowed to a pure running-time bound (rung 2a) (PROVED)

`ACC0TimedHierarchyConditional` reduced the time hierarchy to `hsim` — a `bigbound`-time program computing
the diagonal.  `hsim` has two parts: *(a)* a program computing the diagonal **exists**, and *(b)* it runs
within `bigbound`.  Part (a) is **proved** here: since `diag (timedEnum bound)` is computable, by Code
completeness (`Nat.Partrec.Code.exists_code`) it is `c.eval` for an actual `Code c`:

  `diag_has_code` — `∃ c : Code, c.eval = (fun e ↦ (diag (timedEnum bound) e).toNat)`.

So the simulator program is no longer hypothetical — it is a concrete `Code c`.  All that remains of `hsim`
is the **running-time** claim: that `evaln (bigbound e) c e` already returns `c`'s value (i.e. `c` halts
within `bigbound e` steps).  The gap is thus purely a time bound on a *known* program — the efficient
universal simulator (`evaln` overhead `≤ bigbound`, Hennie–Stearns `t·polylog`).

## What is proved (clean axioms, no `sorry`)

* `diag_has_code` — the diagonal is computed by an explicit `Code` (the program exists; part (a) of `hsim`).

## Honest scope

The program *exists* (Code completeness over the proved computability).  Its *running-time* within
`bigbound` (part (b) of `hsim`) needs an `evaln` running-time bound Mathlib lacks — the deep machine-model
gap, Williams-strength, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DiagHasCode

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel (diag)
open PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration (timedEnum timedEnum_diag_computable)

/-- **The diagonal has a program (proved).**  By Code completeness over `timedEnum_diag_computable`, the
diagonal is `c.eval` for an explicit `Code c` — part (a) of the simulator hypothesis `hsim`. -/
theorem diag_has_code (bound : ℕ → ℕ) (hb : Computable bound) :
    ∃ c : Code, c.eval = ((fun e => (diag (timedEnum bound) e).toNat : ℕ → ℕ) : ℕ →. ℕ) := by
  have hg : Computable (fun e => (diag (timedEnum bound) e).toNat) :=
    (Primrec.dom_bool Bool.toNat).to_comp.comp (timedEnum_diag_computable bound hb)
  exact exists_code.mp (Partrec.nat_iff.mp (Computable.partrec hg))

/-!
**Rung 2a proved.**  The diagonal-computing program is a concrete `Code` (not hypothetical).  The residue
of `hsim` is purely the running-time bound — `evaln (bigbound e) c e` returning `c`'s value — the efficient
universal simulator, the deep machine-model gap.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0DiagHasCode

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DiagHasCode.diag_has_code
