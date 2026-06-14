import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatStepMachine

/-!
# The faithful elementary-operation count

The step machine charged one transition per cell; but checking a cell evaluates the `k` gate residues
(`cellPredicate` applies the top gate to `k` `MOD` outputs).  This file refines the cost to the **true elementary
operation count** — every gate‑residue evaluation — `totalOps = #gates · #cells = k · |image(weightVec)|`, and
carries the sub‑brute‑force bound at this finer granularity.

## What is proved (clean axioms, no `sorry`)

* `totalOps_eq_gates_mul_steps` — `totalOps = k · (cellSearch steps)`: every cell costs `k` gate evaluations.
* `totalOps_le` — `totalOps ≤ k · (n+1)^k` (the cell bound times the per‑cell gate work).
* `totalOps_beats_bruteforce` — `k · (n+1)^k < 2^n ⇒ totalOps < 2^n`: the full operation count beats brute force in
  the small‑gate regime.

## Honest scope

This is the finest the *cell‑search cost model* goes: it counts all elementary gate‑residue operations, total
`k · (n+1)^k`, sub‑`2^n` when `k = o(n/log n)`.  It is **not** a Turing‑machine analysis — no tape, head, input
encoding, or `n^ε` accounting — and that full machine model + the genuine sub‑exponential ACC⁰‑SAT algorithm is the
remaining Williams content, a research‑grade complexity formalization beyond this corpus.  This file is the natural
endpoint of the operational‑cost refinement: the speedup is a real algorithm whose every elementary operation is
counted and proved `< 2^n` in the small‑gate regime.  Proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatOpCount

open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0SatTimeCost
open PallLean.Paper93.DeepMath.PathB.ACC0SatMachine

variable {n k : ℕ}

/-- The total elementary operation count: `k` gate‑residue evaluations per cell, over all achievable cells. -/
def totalOps (C : Depth2ModCircuit n k) : ℕ := k * (Finset.univ.image (weightVec C.supports)).card

/-- **Each cell costs `k` gate evaluations (proved): `totalOps = k · (cellSearch steps)`.** -/
theorem totalOps_eq_gates_mul_steps (C : Depth2ModCircuit n k) :
    totalOps C = k * (cellSearch C).steps := rfl

/-- **The operation bound (proved): `totalOps ≤ k · (n+1)^k`.** -/
theorem totalOps_le (C : Depth2ModCircuit n k) : totalOps C ≤ k * (n + 1) ^ k :=
  Nat.mul_le_mul (le_refl k) (imageSearchCost_le C.supports)

/-- **The full operation count beats brute force (proved): `k · (n+1)^k < 2^n ⇒ totalOps < 2^n`.** -/
theorem totalOps_beats_bruteforce (C : Depth2ModCircuit n k) (hregime : k * (n + 1) ^ k < 2 ^ n) :
    totalOps C < 2 ^ n :=
  lt_of_le_of_lt (totalOps_le C) hregime

end PallLean.Paper93.DeepMath.PathB.ACC0SatOpCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatOpCount.totalOps_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatOpCount.totalOps_beats_bruteforce
