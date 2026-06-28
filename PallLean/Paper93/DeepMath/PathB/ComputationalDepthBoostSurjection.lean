import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWalshSpan
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoosting
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMonomialAlgebra
import Mathlib

/-!
# The boosting reduction on `G` (PROVED) — toward the boosting surjection

The boosting surjection (every function on `G` realised at degree `≤ n/2 + d`) rests on two facts, both proved
here over the `{-1,+1}ⁿ` cube, building on the Walsh span (`ComputationalDepthWalshSpan`):

  `walshFn_mul` — Walsh monomials multiply by symmetric difference: `walshFn R b · walshFn T b = walshFn (R∆T) b`
        (the instantiated `{-1,+1}` product law; degree `|R∆T| ≤ |R| + |T|`).
  `evalW_fold_on_G` — **the boosting reduction**: at a point `b` where the approximator agrees with the full
        parity (`evalW aCoef b = walshFn univ b`, i.e. `b ∈ G`), every Walsh polynomial folds termwise:
            `evalW c b = Σ_S c_S · (if 2|S| ≤ n then walshFn S b  else  evalW aCoef b · walshFn Sᶜ b)`.
        Low monomials (`|S| ≤ n/2`) stay degree `≤ n/2`; high ones become `a · (degree ≤ n/2)`, degree `≤ d + n/2`.

So on `G` every `evalW c` equals a sum of degree-`≤ n/2 + d` Walsh terms.  Collecting these into a single
degree-`≤ n/2 + d` coefficient vector (via `walshFn_mul`, a convolution) and combining with `evalW_surjective`
gives the surjection `φ` of `dimension_argument` — the final coefficient-collection is the remaining wiring.
-/

open scoped symmDiff

namespace PallLean.Paper93.DeepMath.PathB.WalshSpan

variable {n : ℕ} {F : Type*} [Field F]

/-- **Walsh monomials multiply by symmetric difference.**  Instantiating the `{-1,+1}` product law at the sign
vector: `walshFn R b · walshFn T b = walshFn (R ∆ T) b`.  The product's degree is `|R ∆ T| ≤ |R| + |T|`, which is
why `a · walshFn Sᶜ` (with `a` of degree `≤ d`) stays at degree `≤ d + |Sᶜ|`. -/
theorem walshFn_mul (R T : Finset (Fin n)) (b : Fin n → Bool) :
    (walshFn R b : F) * walshFn T b = walshFn (R ∆ T) b := by
  simp only [walshFn]
  exact Boosting.prod_mul_prod_symmDiff (fun i => if b i then (-1 : F) else 1)
    (fun i => Boosting.sign_sq_one (F := F) b i) R T

/-- **The boosting reduction on `G`.**  At a point `b` where the approximator `evalW aCoef` agrees with the full
parity `walshFn univ` (the defining property of `G`), every Walsh polynomial `evalW c` folds termwise: low-degree
monomials are kept, high-degree ones `walshFn S` are replaced by `evalW aCoef b · walshFn Sᶜ b` (using the
folding identity `walshFn S = walshFn univ · walshFn Sᶜ` and the agreement).  Every term on the right has degree
`≤ n/2 + d` once `aCoef` has degree `≤ d`. -/
theorem evalW_fold_on_G (aCoef c : Finset (Fin n) → F) (b : Fin n → Bool)
    (hG : evalW aCoef b = walshFn Finset.univ b) :
    evalW c b
      = ∑ S, c S * (if 2 * S.card ≤ n then walshFn S b else evalW aCoef b * walshFn Sᶜ b) := by
  rw [evalW]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  congr 1
  by_cases h : 2 * S.card ≤ n
  · rw [if_pos h]
  · rw [if_neg h, hG]
    simp only [walshFn]
    exact Boosting.prod_eq_full_mul_prod_compl _ (fun i => Boosting.sign_sq_one b i) S

end PallLean.Paper93.DeepMath.PathB.WalshSpan

#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.walshFn_mul
#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.evalW_fold_on_G
