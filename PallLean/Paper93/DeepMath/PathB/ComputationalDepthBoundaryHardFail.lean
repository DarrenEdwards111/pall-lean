import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverBoundary

/-!
# The observer-boundary invariant FAILS on a genuinely hard target (the permanent is fragile)

`…ObserverBoundary` proved the boundary invariant separates `MOD_q` (boundary-robust, `≥ C(m,κ)`) from `∏Xᵢ`
(boundary-fragile, `= 0`).  The natural question: does it detect *hardness*?  This file answers **no**, with a proof.

Take the **permanent** `permPoly = ∑_{σ∈Sₙ} ∏ᵢ X_{i,σ(i)}` — a genuinely hard polynomial (`VNP`-complete).  Every one
of its `n!` monomials uses *one entry from every row*.  So fixing a single row to `0` (a legitimate observer boundary,
`n²−n` variables still visible) makes **every** term vanish:

  `permPoly_restrictRow_zero` — `aeval (fix row a to 0) (permPoly) = 0`.

So the permanent is boundary-**fragile** (`BoundarySPDP = 0`), *exactly like the easy product `∏Xᵢ`*, and unlike the
easy `MOD_q`.  The boundary invariant therefore does **not** capture computational hardness: it classifies the hard
permanent as "easy" (fragile) and the easy `MOD_q` as "hard" (robust).

## What the invariant actually measures

Boundary-robustness detects a specific *algebraic* property — a **nonvanishing product structure** (a nonzero
constant term that no `0/1` restriction can annihilate), which `MOD_q`'s affine product `∏(1+(ω-1)Xᵢ)` happens to
have.  Hard functions built as *sums of products* (permanent, determinant, and any polynomial in a variable's ideal)
are killed by trivialising restrictions, so they are fragile.  Restriction-robustness ≠ hardness.

This is the honest close of the dynamic-SPDP / observer-boundary thread: of the measures tested, restriction/boundary
rank is the only one that separates `MOD_q` from `∏Xᵢ`, but it separates by nonvanishing-product structure, not by
hardness — so it does not extend to genuinely hard targets, and is not a route to an `ACC⁰` lower bound.  (Making a
hard target boundary-robust *and* proving its rank high is the barriered A3 hard-survival.)  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial

variable {n : ℕ} {F : Type*} [Field F]

/-- The **permanent** as a polynomial in `n²` variables `X_{i,j}` — genuinely hard (`VNP`-complete). -/
noncomputable def permPoly (n : ℕ) (F : Type*) [Field F] : MvPolynomial (Fin n × Fin n) F :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, X (i, σ i)

/-- **The permanent is boundary-fragile (proved).**  Fixing an entire row `a` to `0` — an observer boundary with
`n²−n` visible variables — kills the permanent, because every one of its monomials uses an entry from row `a`.  So a
genuinely hard target has `BoundarySPDP = 0`, exactly like the easy product `∏Xᵢ`: the boundary invariant does not see
its hardness. -/
theorem permPoly_restrictRow_zero (a : Fin n) :
    aeval (fun p : Fin n × Fin n => if p.1 = a then (C 0 : MvPolynomial (Fin n × Fin n) F) else X p)
      (permPoly n F) = 0 := by
  unfold permPoly
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp

end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.permPoly_restrictRow_zero
