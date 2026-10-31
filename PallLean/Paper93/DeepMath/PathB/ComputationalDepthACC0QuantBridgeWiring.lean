import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0QuantError
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolynomialMethodApproximation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0QuantitativeIteration

/-!
# Wiring the quantitative depth induction to the `QuantitativeDepthBound` socket

Auditing the prime Razborov–Smolensky route turned up that **both** of its remaining "bookkeeping residuals"
were in fact already proved in the repo, only left un-wired:

* the `#subcircuits (padTrue D)` step — closed by `Layer4.mod_q_family_false` (the literal-family
  `MOD_q ∉ AC⁰[p]`), and
* the *quantitative* `Circ` structural recursion — closed by `ACC0QuantError.approximable_full`, the full
  degree+error induction: every `MOD`-free `Circ` `C` has an `F₂` approximant of degree `≤ t^{cdepth C}`
  whose error `E` satisfies `2^t · E ≤ size C · 2^n`.

The genuine remaining step was therefore purely a **wiring** one: the assembly in
`ACC0PolynomialMethodApproximation` still carried `QuantitativeDepthBound` as an undischarged socket (a
`def`-level `Prop` placeholder used as a hypothesis of `polynomial_method_contradiction`), and
`ACC0QuantitativeIteration.CircuitStructuralRecursion` was a pass-through never fed the proof. This file
connects `approximable_full` to that socket, turning `QuantitativeDepthBound` from an assumption into a
theorem.

## What is proved (clean axioms, no `sorry`)

* **`quantitativeDepthBound_of_circ`** — for every `MOD`-free `Circ` `C` and boosting `t ≥ 1`, the embedded
  Boolean function `x ↦ [Circ.eval x C]₂` satisfies `QuantitativeDepthBound _ (t^{cdepth C}) E` for the
  concrete error `E = #{x : approximant errs}`, together with the quantitative guarantee
  `2^t · E ≤ size C · 2^n`. The `hbridge` hypothesis of `polynomial_method_contradiction` is now a proof.

## Honest scope

This discharges the last **socket** of the *prime* (`p` odd prime) polynomial-method assembly by wiring in
the already-proved quantitative induction; it introduces no new mathematics. The final contradiction still
needs the Smolensky wall `SmolenskyNonNativeLowerBound` for the target — a THEOREM for prime `q`
(`algExpander_forces_high_degree`) and the OPEN `CarryRefinementCrossing` frontier for composite `q`. This
is **not** `NEXP ⊄ ACC⁰` (which needs Williams' algorithmic method, not this polynomial machinery) or
`P ≠ NP`. See `ACC_ROADMAP.md`, `ACC0_ANATOMY.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0QuantBridgeWiring

open PallLean.Paper93.DeepMath.PathB.Layer3 (boolToZMod)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitApprox (Circ)
open PallLean.Paper93.DeepMath.PathB.ACC0OrStep (perr)
open PallLean.Paper93.DeepMath.PathB.ACC0QuantDegree (cdepth)
open PallLean.Paper93.DeepMath.PathB.ACC0QuantError (approximable_full)
open PallLean.Paper93.DeepMath.PathB.ACC0PolynomialMethodApproximation (QuantitativeDepthBound LowDegreeApprox)

/-- **`QuantitativeDepthBound` discharged (PROVED).**  Wiring the proved quantitative depth induction
(`ACC0QuantError.approximable_full`) into the polynomial-method socket: for every `MOD`-free circuit `C`
and boosting `t ≥ 1`, the embedded Boolean function `x ↦ [Circ.eval x C]₂` has a degree-`≤ t^{cdepth C}`
`F₂`-approximant whose error `E` is a `2^{-t}` fraction of `size C · 2^n` (`2^t · E ≤ size C · 2^n`).
The bound `QuantitativeDepthBound _ (t^{cdepth C}) E` — previously an undischarged socket / hypothesis of
`polynomial_method_contradiction` — is now a theorem. -/
theorem quantitativeDepthBound_of_circ {n t : ℕ} (ht : 1 ≤ t) (C : Circ n) :
    ∃ E : ℕ,
      2 ^ t * E ≤ Circ.size C * Fintype.card (Fin n → Bool)
        ∧ QuantitativeDepthBound (fun x => boolToZMod 2 (Circ.eval x C)) (t ^ cdepth C) E := by
  obtain ⟨Q, hdeg, herr⟩ := approximable_full ht C
  refine ⟨(perr Q (fun x => Circ.eval x C)).card, herr, ?_⟩
  show LowDegreeApprox (fun x => boolToZMod 2 (Circ.eval x C)) (t ^ cdepth C)
      (perr Q (fun x => Circ.eval x C)).card
  exact ⟨Q, hdeg, le_refl _⟩

end PallLean.Paper93.DeepMath.PathB.ACC0QuantBridgeWiring

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0QuantBridgeWiring.quantitativeDepthBound_of_circ
