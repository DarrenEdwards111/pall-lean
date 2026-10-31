import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitModel

/-!
# Branch correctness: SAT decomposes over restricted branches

The branched algorithm enumerates assignments of a "killed" coordinate set `K` and decides SAT on each branch.
This file proves the decomposition is **correct**: a function is satisfiable iff some branch is.

A branch is an assignment `b`; `branchSAT f K b` says some input agreeing with `b` on `K` is accepted.  Then
`sat_branch_decompose`: `(∃ x, f x = true) ↔ ∃ b, branchSAT f K b`.  Only `b`'s values on `K` matter, so the
right‑hand disjunction is effectively over the `2^{|K|}` branch assignments — the algorithmic decomposition the
branched cost model assumed.

## What is proved (clean axioms, no `sorry`)

* `sat_branch_decompose` — **SAT = OR over branches**: `(∃ x, f x = true) ↔ ∃ b, branchSAT f K b`.

## Honest scope

This is the correctness of the branch‑and‑restrict decomposition (the cost interpretation of the branched bound),
proved for any Boolean function and any branch set.  It is purely the decomposition; the per‑branch fast decision
is the survivor cell bound (`…ACC0SatRestrictionActive`), and the full time bound is the branched cost
(`…ACC0SatBranched`).  Proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatBranchCorrect

variable {n : ℕ}

/-- A branch is satisfiable if some input agreeing with `b` on the killed set `K` is accepted. -/
def branchSAT (f : (Fin n → Bool) → Bool) (K : Finset (Fin n)) (b : Fin n → Bool) : Prop :=
  ∃ x, (∀ i ∈ K, x i = b i) ∧ f x = true

/-- **Branch correctness (proved): SAT decomposes over branches.**  A function is satisfiable iff some branch is. -/
theorem sat_branch_decompose (f : (Fin n → Bool) → Bool) (K : Finset (Fin n)) :
    (∃ x, f x = true) ↔ ∃ b, branchSAT f K b := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, x, fun i _ => rfl, hx⟩
  · rintro ⟨b, x, _, hx⟩
    exact ⟨x, hx⟩

end PallLean.Paper93.DeepMath.PathB.ACC0SatBranchCorrect

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatBranchCorrect.sat_branch_decompose
