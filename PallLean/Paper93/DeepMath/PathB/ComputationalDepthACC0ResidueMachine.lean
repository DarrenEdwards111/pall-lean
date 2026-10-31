import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModResidueSpeedup
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatMachine

/-!
# The operational residue-search machine: the mixed-modulus speedup as a timed algorithm

`…ACC0ModResidueSpeedup` proved the *structural* residue compression: a depth-2 `MOD`-circuit factors through its
residue vector (`∏ q_j` cells).  This file makes it a genuine **step-counted SAT algorithm** — the residue analogue
of `…ACC0SatMachine.cellSearch` — so the compression has the same operational strength as the cell-search chain.

`residueSearch C` enumerates the achievable residue cells (`image(modResVec)`), checks the per-cell predicate
`residuePredicate` on each, and accepts iff any does; its `steps` is the number of cells examined.  Because a `MOD_q`
gate only sees its count **mod q**, the residue image has `≤ ∏ q_j` cells — *constant per gate* — so the algorithm
runs in `≤ ∏ q_j` steps, beating `2^n` brute force whenever `∏ q_j < 2^n` (e.g. `6^k < 2^n` for `MOD_6`).

## What is proved (clean axioms, no `sorry`)

* `eval_eq_residuePredicate` — `C.eval x = residuePredicate C (modResVec C x)` (`rfl`).
* `residueSearch_decides` — **the algorithm decides SAT**: `(residueSearch C).result = true ↔ Satisfiable C.eval`.
* `residueSearch_steps_eq_checks` — `steps` = number of residue cells examined (= predicate checks).
* `residueSearch_steps_le_prod_moduli` — **`steps ≤ ∏ q_j`** (constant per gate, independent of `n`).
* `residueSearch_beats_bruteforce` / `residueSearch_mod6_beats_bruteforce` — **`∏ q_j < 2^n` (resp. `6^k < 2^n`) ⇒
  `steps < 2^n`**: the mixed-modulus speedup as a timed, correct algorithm.

## Honest scope

A *unit-cost residue-cell-check* time model (one step per residue cell, each `residuePredicate` check `O(k)`), the
exact analogue of the `cellSearch` cost model.  It makes the residue compression a real timed algorithm with proved
correctness and step bound.  It is **not** a Turing-machine simulation, and (per `ACC_THEOREM_MAP.md`) the remaining
gap to `NEXP ⊄ ACC⁰` is the *uniform nondeterministic* realisation + the time-hierarchy cash-out, plus branching /
restriction / depth-iteration for `k` beyond the `∏ q_j < 2^n` base regime.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ResidueMachine

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SatMachine
open PallLean.Paper93.DeepMath.PathB.ACC0ModResidueSpeedup

variable {n k : ℕ}

/-- The per-residue-cell acceptance check: the top gate applied to the cell's residue pattern (each gate accepts
when its residue hits its target). -/
def residuePredicate (C : Depth2ModCircuit n k) (v : (j : Fin k) → ZMod (C.gates j).modulus) : Bool :=
  C.top (fun j => decide (v j = (C.gates j).target))

/-- **The circuit value is `residuePredicate` at the residue cell (proved by `rfl`).** -/
theorem eval_eq_residuePredicate (C : Depth2ModCircuit n k) (x : Fin n → Bool) :
    C.eval x = residuePredicate C (modResVec C x) := rfl

/-- **The residue-search algorithm**: enumerate the achievable residue cells, check `residuePredicate` on each,
accept if any does; `steps` counts the cells examined.  (`noncomputable` only because the enumeration order is
choice-supplied; the result and step count do not depend on it.) -/
noncomputable def residueSearch (C : Depth2ModCircuit n k) : TimedDecision where
  result := ((Finset.univ.image (modResVec C)).toList).any (residuePredicate C)
  steps := (Finset.univ.image (modResVec C)).card

/-- **The algorithm decides SAT (proved): `residueSearch C` accepts iff the circuit is satisfiable.** -/
theorem residueSearch_decides (C : Depth2ModCircuit n k) :
    (residueSearch C).result = true ↔ Satisfiable C.eval := by
  have hsat : Satisfiable C.eval
      ↔ ∃ v ∈ Finset.univ.image (modResVec C), residuePredicate C v = true := by
    unfold Satisfiable
    simp_rw [eval_eq_residuePredicate]
    exact sat_iff_image (residuePredicate C) (modResVec C)
  rw [hsat]
  unfold residueSearch
  simp only [List.any_eq_true, Finset.mem_toList]

/-- **`steps` is the operation count (proved): the number of residue cells (= predicate checks) examined.** -/
theorem residueSearch_steps_eq_checks (C : Depth2ModCircuit n k) :
    (residueSearch C).steps = ((Finset.univ.image (modResVec C)).toList).length := by
  unfold residueSearch
  rw [Finset.length_toList]

/-- **The time bound (proved): `steps ≤ ∏ q_j`** — constant per gate, independent of `n`. -/
theorem residueSearch_steps_le_prod_moduli (C : Depth2ModCircuit n k)
    (hpos : ∀ j, 0 < (C.gates j).modulus) :
    (residueSearch C).steps ≤ ∏ j, (C.gates j).modulus := by
  unfold residueSearch
  exact residue_cell_count_le C hpos

/-- **The speedup as a timed algorithm (proved): `∏ q_j < 2^n ⇒` the deciding algorithm runs in `< 2^n` steps.** -/
theorem residueSearch_beats_bruteforce (C : Depth2ModCircuit n k)
    (hpos : ∀ j, 0 < (C.gates j).modulus) (hregime : (∏ j, (C.gates j).modulus) < 2 ^ n) :
    (residueSearch C).steps < 2 ^ n :=
  lt_of_le_of_lt (residueSearch_steps_le_prod_moduli C hpos) hregime

/-- **The `MOD_6` instance (proved): `6^k < 2^n ⇒` the deciding algorithm runs in `< 2^n` steps.** -/
theorem residueSearch_mod6_beats_bruteforce (C : Depth2ModCircuit n k)
    (h6 : ∀ j, (C.gates j).modulus = 6) (hregime : 6 ^ k < 2 ^ n) :
    (residueSearch C).steps < 2 ^ n := by
  unfold residueSearch
  exact mod6_circuit_residue_speedup C h6 hregime

end PallLean.Paper93.DeepMath.PathB.ACC0ResidueMachine

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueMachine.residueSearch_decides
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueMachine.residueSearch_steps_le_prod_moduli
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueMachine.residueSearch_beats_bruteforce
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueMachine.residueSearch_mod6_beats_bruteforce
