import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatSurvivorCells

/-!
# Capstone: the survivor-parameterized ACC⁰-SAT speedup

This ties the speedup sub-arc into one statement, in the parameter the corpus actually controls — the **active
(= surviving) gate count**.  Combining `decideSAT_correct` (the cell search decides SAT) with `cells_le_active`
(`#cells ≤ (n+1)^{#active}`):

> if `(n+1)^{#active} < 2^n`, then `cellSearch C` **correctly decides SAT** *and* runs in **fewer than `2^n`
> steps**.

After a restriction, `#active = #surviving`, so this is exactly: *few surviving gates ⇒ a correct SAT decision
below brute force*.  The survivor machinery (`…ACCSwitchingPipeline`, `…ACCCoreDecomposition`, `…ACCRestrictionTree`)
is what drives the survivor count down, and it feeds directly into this bound.

## What is proved (clean axioms, no `sorry`)

* `survivor_sat_speedup` — **the capstone**: in the few‑active‑gate regime, `cellSearch` is a correct,
  sub‑brute‑force SAT decider (correctness `∧` step bound).

## Honest scope

This is the headline of the cell‑search speedup, stated in the survivor parameter — a real, correct, timed algorithm
beating brute force when few gates survive.  It is the cell‑search cost model; it is **not** the full
Turing‑machine `2^{n-n^ε}` ACC⁰‑SAT theorem (the named Williams gap), and proves nothing about `NEXP/NP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatSpeedupCapstone

open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SatMachine
open PallLean.Paper93.DeepMath.PathB.ACC0SatSurvivorCells

variable {n k : ℕ}

/-- **The capstone (proved): few active/surviving gates ⇒ a correct, sub‑brute‑force SAT decider.**  In the regime
`(n+1)^{#active} < 2^n`, `cellSearch C` decides satisfiability correctly and halts in fewer than `2^n` steps.  Since
`#active = #surviving` after a restriction, the survivor machinery drives this directly. -/
theorem survivor_sat_speedup (C : Depth2ModCircuit n k)
    (hregime : (n + 1) ^ (activeSupports C.supports).card < 2 ^ n) :
    ((cellSearch C).result = true ↔ Satisfiable C.eval) ∧ (cellSearch C).steps < 2 ^ n :=
  ⟨decideSAT_correct C, lt_of_le_of_lt (cells_le_active C) hregime⟩

end PallLean.Paper93.DeepMath.PathB.ACC0SatSpeedupCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatSpeedupCapstone.survivor_sat_speedup
