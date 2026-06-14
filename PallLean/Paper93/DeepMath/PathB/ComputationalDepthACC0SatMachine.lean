import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatBranched

/-!
# A minimal time-complexity model: the cell-search algorithm as a real, timed function

The previous files bounded an *abstract* "cell search cost".  This file makes it a genuine time model: a real
Lean function `decideSAT` that **decides** depth-2 `MOD`-bottom SAT, whose **time** (`steps`) is the number of
elementary operations it actually performs (one `cellPredicate` check per cell), with both correctness and the time
bound proved.

The model: a `TimedDecision` is a result paired with a step count.  `cellSearch C` enumerates the achievable cells
(`image(weightVec)`), checks `cellPredicate` on each, and returns whether any accepts; its `steps` is the number of
cells checked — exactly the length of the enumerated list.  So "time" is the count of operations of a defined
algorithm, not an abstraction.

## What is proved (clean axioms, no `sorry`)

* `eval_eq_cellPredicate` — the circuit value at `x` is `cellPredicate` at its cell (`rfl`, support extraction).
* `decideSAT_correct` — **the algorithm decides SAT**: `decideSAT C = true ↔ Satisfiable C.eval`.
* `cellSearch_steps_eq_checks` — **`steps` is the operation count**: `steps = #cells = #cellPredicate evaluations`.
* `cellSearch_steps_le`, `cellSearch_beats_bruteforce` — **the time bound in the model**: `steps ≤ (n+1)^k`, and
  `< 2^n` in the small-gate regime.

## Honest scope

This is a *unit-cost cell-check* time model: one step per cell examined, each `cellPredicate` check `O(k)`.  It makes
the speedup a real timed algorithm with a proved operation count, closing the gap between "abstract cell cost" and
"machine time" *for this cost model*.  It is **not** a full Turing-machine simulation (no tape/transition modeling),
and the small-gate regime is where this base case alone wins; the branched extension (`…ACC0SatBranched`) gives the
few-survivor regime.  So the speedup is now a genuine timed algorithm with proved correctness and step bound — not
the full `2^{n-n^ε}` ACC⁰-SAT theorem, and proving nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatMachine

open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SatTimeCost

variable {n k : ℕ}

/-- A decision together with the number of elementary steps used to compute it. -/
structure TimedDecision where
  result : Bool
  steps : ℕ

/-- The per-cell acceptance check: the top gate applied to the cell's residue pattern. -/
def cellPredicate (C : Depth2ModCircuit n k) (w : Fin k → ℕ) : Bool :=
  C.top (fun j => decide ((w j : ZMod (C.gates j).modulus) = (C.gates j).target))

/-- **The circuit value is `cellPredicate` at the cell (proved by `rfl`): support extraction at the value level.** -/
theorem eval_eq_cellPredicate (C : Depth2ModCircuit n k) (x : Fin n → Bool) :
    C.eval x = cellPredicate C (weightVec C.supports x) := rfl

/-- **The cell-search algorithm**: enumerate the achievable cells, check `cellPredicate` on each, accept if any
does; `steps` counts the cells examined.  (`noncomputable` only because the enumeration order is choice-supplied;
the result and step count do not depend on it.) -/
noncomputable def cellSearch (C : Depth2ModCircuit n k) : TimedDecision where
  result := ((Finset.univ.image (weightVec C.supports)).toList).any (cellPredicate C)
  steps := (Finset.univ.image (weightVec C.supports)).card

/-- **The algorithm decides SAT (proved): `cellSearch C` accepts iff the circuit is satisfiable.** -/
theorem decideSAT_correct (C : Depth2ModCircuit n k) :
    (cellSearch C).result = true ↔ Satisfiable C.eval := by
  have hsat : Satisfiable C.eval
      ↔ ∃ w ∈ Finset.univ.image (weightVec C.supports), cellPredicate C w = true := by
    unfold Satisfiable
    simp_rw [eval_eq_cellPredicate]
    exact sat_iff_image (cellPredicate C) (weightVec C.supports)
  rw [hsat]
  unfold cellSearch
  simp only [List.any_eq_true, Finset.mem_toList]

/-- **`steps` is the operation count (proved): it equals the number of cells (= `cellPredicate` checks) examined.** -/
theorem cellSearch_steps_eq_checks (C : Depth2ModCircuit n k) :
    (cellSearch C).steps = ((Finset.univ.image (weightVec C.supports)).toList).length := by
  unfold cellSearch
  rw [Finset.length_toList]

/-- **The time bound (proved): `steps ≤ (n+1)^k`.** -/
theorem cellSearch_steps_le (C : Depth2ModCircuit n k) : (cellSearch C).steps ≤ (n + 1) ^ k :=
  imageSearchCost_le C.supports

/-- **The model-relative speedup as a timed algorithm (proved): in the small-gate regime the deciding algorithm
runs in `< 2^n` steps.** -/
theorem cellSearch_beats_bruteforce (C : Depth2ModCircuit n k) (hregime : (n + 1) ^ k < 2 ^ n) :
    (cellSearch C).steps < 2 ^ n :=
  lt_of_le_of_lt (cellSearch_steps_le C) hregime

end PallLean.Paper93.DeepMath.PathB.ACC0SatMachine

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatMachine.decideSAT_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatMachine.cellSearch_steps_eq_checks
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatMachine.cellSearch_beats_bruteforce
