import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatTimeCost

/-!
# The branched ACC⁰-SAT time bound: past the small-gate regime

`…ACC0SatTimeCost` proved the unbranched cell search beats brute force only when `(n+1)^k < 2^n` (small gate count
`k`).  For many gates this fails — but branching rescues it: branch over a killed coordinate set, and on each branch
**only the surviving gates matter** (killed gates are constant on the branch, by locality), so the per-branch cell
search is over the *survivor* count `r`, not `k`.

The branched cost model: `2^{#killed}` branches, each a cell search of cost `≤ (n+1)^r` (`r` survivors), so

> total `= 2^{#killed} · (n+1)^r`,

and this is `< 2^n` whenever `#killed + r` are small enough — concretely, when `#killed + #live = n` and
`(n+1)^r < 2^{#live}` (few survivors relative to the live count).  The restriction tree / core decomposition is
exactly what makes `r` small, so the branched bound fires there.

## What is proved (clean axioms, no `sorry`)

* `branched_cost_le` — the branched cost is `≤ 2^{#killed} · (n+1)^r` (per-branch cell bound via the proved
  `imageSearchCost_le` on the survivor family).
* `branched_regime` — the arithmetic: `#killed + #live = n` and `(n+1)^r < 2^{#live}` ⇒ `2^{#killed}·(n+1)^r < 2^n`.
* `branched_beats_bruteforce` — combining: in the few-survivor regime the branched cell search beats brute force.

## Honest scope

This is the *cost arithmetic* of branch-and-restrict in the cell-search model, with the per-branch cost reduced to
the survivor count `r` (the gain over the unbranched `(n+1)^k`).  The structural justification that per-branch only
survivors matter is the proved killed-gates-constant locality (`…ACC0DepthReduction.eval_const_of_support_disjoint`);
the branch enumeration correctness (SAT = OR over the `2^{#killed}` branches) is the standard branch-and-restrict
decomposition (the cost interpretation).  This extends the model-relative time bound to the **few-survivor regime**
(`r` small, e.g. via the restriction tree), past the small-gate `(n+1)^k` regime — but it is still the cell-search
model, *not* a full Turing-machine `2^{n-n^ε}` analysis, and proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatBranched

open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0SatTimeCost

variable {n : ℕ}

/-- The branched cost: `2^{#killed}` branches, each costing `cellCost`. -/
def branchedCost (killed cellCost : ℕ) : ℕ := 2 ^ killed * cellCost

/-- **The branched cost is `≤ 2^{#killed}·(n+1)^r` (proved).**  Per branch, only the `r` surviving gates matter, so
the cell search costs `≤ (n+1)^r` (by `imageSearchCost_le` on the survivor family). -/
theorem branched_cost_le {r : ℕ} (killed : ℕ) (surv : Fin r → Finset (Fin n)) :
    branchedCost killed (Finset.univ.image (weightVec surv)).card ≤ 2 ^ killed * (n + 1) ^ r := by
  unfold branchedCost
  exact Nat.mul_le_mul (le_refl _) (imageSearchCost_le surv)

/-- **The few-survivor regime arithmetic (proved): `#killed + #live = n` and `(n+1)^r < 2^{#live}` ⇒
`2^{#killed}·(n+1)^r < 2^n`.** -/
theorem branched_regime (killed live r : ℕ) (hsum : killed + live = n) (hcell : (n + 1) ^ r < 2 ^ live) :
    2 ^ killed * (n + 1) ^ r < 2 ^ n := by
  calc 2 ^ killed * (n + 1) ^ r
      < 2 ^ killed * 2 ^ live := by
        apply mul_lt_mul_of_pos_left hcell
        positivity
    _ = 2 ^ n := by rw [← pow_add, hsum]

/-- **The branched cell search beats brute force (proved): in the few-survivor regime, `branchedCost < 2^n`.**
Combining the per-branch cell bound with the regime arithmetic — `#killed + #live = n` and `(n+1)^r < 2^{#live}`. -/
theorem branched_beats_bruteforce {r : ℕ} (killed live : ℕ) (surv : Fin r → Finset (Fin n))
    (hsum : killed + live = n) (hcell : (n + 1) ^ r < 2 ^ live) :
    branchedCost killed (Finset.univ.image (weightVec surv)).card < 2 ^ n :=
  lt_of_le_of_lt (branched_cost_le killed surv) (branched_regime killed live r hsum hcell)

end PallLean.Paper93.DeepMath.PathB.ACC0SatBranched

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatBranched.branched_cost_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatBranched.branched_regime
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatBranched.branched_beats_bruteforce
