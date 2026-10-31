import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWilliamsNEXP_ACC0
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RSToSymAnd

/-!
# Williams cash-out from the polynomial method — the representation half discharged, the counting half isolated

Williams' route to `NEXP ⊄ ACC⁰` is: a nontrivial (sub-`2ⁿ`) `ACC⁰`-SAT algorithm, together with the
nondeterministic time hierarchy, refutes `NEXP ⊆ ACC⁰` (`…WilliamsNEXP_ACC0.acc0_sat_speedup_implies_NEXP_not_ACC0`).
The SAT algorithm itself has two halves:

1. **Representation** — express the `ACC⁰` circuit as a *sparse low-degree* object (a `ZMod p`-combination of
   monomial-`AND` gates, i.e. `SYM∘AND` form).  **This is exactly the polynomial method**, and it is *proved*:
   `…ACC0RSToSymAnd.lowDegPolyEval_mem_monoAND_span` puts every degree-`≤D` polynomial's cube-evaluation in the span of
   the monomial-`AND` indicators.
2. **Counting** — given the sparse representation, count satisfying assignments faster than `2ⁿ` (Beigel–Tarui /
   Williams).  **This is the open algorithmic socket** — the genuine `NEXP`-strength research target.

This file performs the cash-out at the honest level: it **discharges half 1 with the polynomial method**
(`rsMonoANDRepresentation_proved`) and chains it through the Williams skeleton, leaving exactly the *counting* socket,
the *Williams collapse* step, and the *time hierarchy* as the remaining inputs.

## What is proved (clean axioms, no `sorry`)

* `RSMonoANDRepresentation` / **`rsMonoANDRepresentation_proved`** — the polynomial-method representation (half 1),
  *discharged* (re-export of `lowDegPolyEval_mem_monoAND_span`).
* **`williams_cashout_skeleton`** — the full conditional: `(counting : RSRep → Speedup)`, `(williams)`, `(hierarchy)`,
  `(hrep)` ⇒ `¬ NEXPHasACC0Circuits` (a relabelling of the Williams skeleton with the representation factored out).
* **`williams_cashout_from_polynomial`** — the same chain with `hrep` **supplied by the polynomial method**, so the
  only remaining inputs are the *counting* socket, the *Williams* collapse, and the *hierarchy*.

## Honest scope — this is NOT `NEXP ⊄ ACC⁰`

The file proves an **implication**, not the separation.  The polynomial method discharges only the *representation*
ingredient.  The `counting` socket (sparse representation ⇒ sub-`2ⁿ` `ACC⁰`-SAT) is the algorithmic heart of Williams'
theorem and is **left open** as a named hypothesis; `williams` (the speedup-powered collapse of `NEXP ⊆ ACC⁰`) is the
algorithmic-method step; `hierarchy` (`¬ Collapse`) is the known nondeterministic time hierarchy.  None of these is
established here.  This is the faithful account of *exactly which inputs* close `NEXP ⊄ ACC⁰` and *which one* the
polynomial method supplies — nothing more.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashoutFromPolynomial

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0RSToSymAnd
open PallLean.Paper93.DeepMath.PathB.WilliamsNEXP_ACC0

/-- **The polynomial-method representation (half 1 of the `ACC⁰`-SAT algorithm).**  Every degree-`≤D` polynomial's
Boolean-cube evaluation is a `ZMod p`-combination of monomial-`AND` (`SYM∘AND`) indicators of support size `≤D`. -/
def RSMonoANDRepresentation : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n D : ℕ) (h : MvPolynomial (Fin n) (ZMod p)),
    h.totalDegree ≤ D →
    (fun x : Fin n → Bool => eval (fun i => boolToZMod p (x i)) h)
      ∈ Submodule.span (ZMod p) (Set.range (fun S : {S // S ∈ lowDegMonomials n D} =>
          fun x : Fin n → Bool => if monoAND S.1 x then (1 : ZMod p) else 0))

/-- **The representation half is discharged by the polynomial method (proved).** -/
theorem rsMonoANDRepresentation_proved : RSMonoANDRepresentation :=
  fun p _ n D h hdeg => @lowDegPolyEval_mem_monoAND_span n p _ D h hdeg

/-- **The Williams skeleton with the representation factored out (proved logic).**  Given the *counting* socket
(`RSRep → ACC⁰-SAT speedup`), Williams' collapse step, the time hierarchy, and a representation `hrep`, we get
`NEXP ⊄ ACC⁰`.  This is `acc0_sat_speedup_implies_NEXP_not_ACC0` with the speedup factored as `counting hrep`. -/
theorem williams_cashout_skeleton
    (RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (counting : RSRep → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) (hrep : RSRep) :
    ¬ NEXPHasACC0Circuits :=
  acc0_sat_speedup_implies_NEXP_not_ACC0 ACC0SatSpeedup NEXPHasACC0Circuits Collapse
    williams hierarchy (counting hrep)

/-- **The Williams cash-out from the polynomial method (proved logic).**  The representation half is *supplied* by the
polynomial method (`rsMonoANDRepresentation_proved`); the only remaining inputs are the **counting** socket
(`RSMonoANDRepresentation → ACC⁰-SAT speedup` — the open algorithmic heart), the **Williams** collapse step, and the
**time hierarchy**.  Discharging `counting` is Williams' algorithmic method — *not* done here. -/
theorem williams_cashout_from_polynomial
    (ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (counting : RSMonoANDRepresentation → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) :
    ¬ NEXPHasACC0Circuits :=
  williams_cashout_skeleton RSMonoANDRepresentation ACC0SatSpeedup NEXPHasACC0Circuits Collapse
    counting williams hierarchy rsMonoANDRepresentation_proved

end PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashoutFromPolynomial

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashoutFromPolynomial.rsMonoANDRepresentation_proved
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashoutFromPolynomial.williams_cashout_skeleton
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashoutFromPolynomial.williams_cashout_from_polynomial
