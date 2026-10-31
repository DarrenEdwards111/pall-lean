import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitFactor

/-!
# The reverse map: factorization ⇒ circuit

The forward map (`NFrameCircuitFactor`) sent a circuit's `k` shared gates to rank `≤ k`.  The reverse
realizes a low-rank factorization as an explicit circuit: a factorization `A·B` through `k` dimensions
**is** a circuit of `k` rank-1 gates — the matrix product expands as a sum of `k` outer products, one
per shared middle wire.

* `factorization_eq_sum_gates` — `A · B = ∑_{l<k} (col l of A) ⊗ (row l of B)`: the factorization is a
  sum of `k` rank-1 gates (each `vecMulVec`, one middle wire = the `coneInter` layer).
* `decomp_eq_sparse_plus_gates` — hence a non-rigidity decomposition `M = C + A·B` is an explicit
  circuit: `s`-sparse part `C` plus `k` rank-1 gates.

Together with the forward direction:
* circuit ⇒ factorization: `k` shared gates ⇒ rank `≤ k` (`rank_le_inner_dim`);
* factorization ⇒ circuit: rank-`k` factor ⇒ `k` explicit gates (`factorization_eq_sum_gates`);
so on the linear side the `coneInter ≤ cN` residual and Valiant rigidity are the same obstruction,
*both directions* machine-checked — the shared-gate count and the low-rank/sparse decomposition are
interchangeable.

## Honest scope

This gives factorization ⇒ circuit at the gate level (an explicit `k`-gate realization of any
factorization), completing the interchange with the forward `rank_le_inner_dim`.  The one algebraic
gap that remains is *minimality* — `rank M ≤ k ⇒ ∃` a factorization through exactly `k` dims — which
needs a basis-of-the-range construction (Mathlib has no direct lemma).  That would make the gate count
exactly the rank; without it, we have: any factorization ⇒ `k` gates, and any `k`-gate circuit ⇒ rank
`≤ k`.  The famous-open core (rigidity itself) is untouched.

Nothing here proves `P ≠ NP`, resolves rigidity, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity

variable {n k : ℕ} {F : Type*} [Field F]

/-- **Factorization ⇒ gates.**  A factorization `A · B` through `k` dimensions is a sum of `k` rank-1
gates: `A · B = ∑_{l} (col l of A) ⊗ (row l of B)` — one gate per shared middle wire. -/
theorem factorization_eq_sum_gates (A : Matrix (Fin n) (Fin k) F) (B : Matrix (Fin k) (Fin n) F) :
    A * B = ∑ l : Fin k, Matrix.vecMulVec (fun i => A i l) (fun j => B l j) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]

/-- **Decomposition ⇒ circuit.**  A non-rigidity decomposition `M = C + A·B` is an explicit circuit:
the `s`-sparse part `C` plus `k` rank-1 gates. -/
theorem decomp_eq_sparse_plus_gates (M C : Matrix (Fin n) (Fin n) F)
    (A : Matrix (Fin n) (Fin k) F) (B : Matrix (Fin k) (Fin n) F) (hM : M = C + A * B) :
    M = C + ∑ l : Fin k, Matrix.vecMulVec (fun i => A i l) (fun j => B l j) := by
  rw [hM, factorization_eq_sum_gates]

end PallLean.Paper93.DeepMath.PathB.NFrameValiantRigidity
