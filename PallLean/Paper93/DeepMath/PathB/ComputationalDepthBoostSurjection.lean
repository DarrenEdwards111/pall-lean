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

/-- **Convolution by a monomial.**  Multiplying a Walsh polynomial by a single monomial `walshFn T` *shifts* its
coefficients by symmetric difference: `evalW aCoef · walshFn T = evalW (U ↦ aCoef (U ∆ T))`.  Proof: distribute,
apply `walshFn_mul` termwise, and reindex the sum by the involution `· ∆ T`.  This is the convolution that
collects each folded high term `a · walshFn Sᶜ` back into Walsh coefficients (shifted by `Sᶜ`, hence supported on
`U` with `|U| ≤ |U ∆ Sᶜ| + |Sᶜ| ≤ d + |Sᶜ| ≤ d + n/2`). -/
theorem evalW_mul_walshFn (aCoef : Finset (Fin n) → F) (T : Finset (Fin n)) (b : Fin n → Bool) :
    evalW aCoef b * walshFn T b = evalW (fun U => aCoef (U ∆ T)) b := by
  have hinv : Function.Involutive (fun S : Finset (Fin n) => S ∆ T) := fun S => by
    show (S ∆ T) ∆ T = S
    rw [symmDiff_symmDiff_cancel_right]
  rw [evalW, evalW, Finset.sum_mul,
    ← Equiv.sum_comp hinv.toPerm (fun U => aCoef (U ∆ T) * walshFn U b)]
  refine Finset.sum_congr rfl (fun R _ => ?_)
  show aCoef R * walshFn R b * walshFn T b = aCoef ((R ∆ T) ∆ T) * walshFn (R ∆ T) b
  rw [mul_assoc, walshFn_mul, symmDiff_symmDiff_cancel_right]

/-- `evalW` is additive in the coefficient vector. -/
theorem evalW_add (c c' : Finset (Fin n) → F) (b : Fin n → Bool) :
    evalW (c + c') b = evalW c b + evalW c' b := by
  simp only [evalW, Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib]

/-- `evalW` is homogeneous in the coefficient vector. -/
theorem evalW_smul (a : F) (c : Finset (Fin n) → F) (b : Fin n → Bool) :
    evalW (a • c) b = a * evalW c b := by
  simp only [evalW, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun S _ => by ring)

/-- `evalW` commutes with finite sums of coefficient vectors. -/
theorem evalW_sum {ι : Type*} (s : Finset ι) (f : ι → Finset (Fin n) → F) (b : Fin n → Bool) :
    evalW (∑ i ∈ s, f i) b = ∑ i ∈ s, evalW (f i) b := by
  simp only [evalW, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- A single Walsh monomial is `evalW` of the indicator coefficient `Pi.single S 1`. -/
theorem walshFn_eq_evalW_single (S : Finset (Fin n)) (b : Fin n → Bool) :
    walshFn S b = evalW (Pi.single S (1 : F)) b := by
  rw [evalW, Finset.sum_eq_single S]
  · rw [Pi.single_eq_same, one_mul]
  · intro T _ hTS; rw [Pi.single_eq_of_ne hTS, zero_mul]
  · intro h; exact absurd (Finset.mem_univ S) h

/-- **The collected coefficient vector.**  Folds each monomial of `c`: low ones keep their indicator, high ones
become the approximator's coefficients shifted by `Sᶜ`.  Every contributing term has degree `≤ n/2 + d`. -/
noncomputable def collectCoef (aCoef c : Finset (Fin n) → F) : Finset (Fin n) → F :=
  ∑ S, c S • (if 2 * S.card ≤ n then Pi.single S (1 : F) else (fun U => aCoef (U ∆ Sᶜ)))

/-- **Evaluation of the collected coefficients** equals the termwise-folded sum (no `G` needed yet): linearity
(`evalW_sum`, `evalW_smul`) reduces it to the per-monomial identities `walshFn_eq_evalW_single` (low) and
`evalW_mul_walshFn` (high). -/
theorem evalW_collectCoef (aCoef c : Finset (Fin n) → F) (b : Fin n → Bool) :
    evalW (collectCoef aCoef c) b
      = ∑ S, c S * (if 2 * S.card ≤ n then walshFn S b else evalW aCoef b * walshFn Sᶜ b) := by
  rw [collectCoef, evalW_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [evalW_smul]
  congr 1
  by_cases h : 2 * S.card ≤ n
  · rw [if_pos h, if_pos h]; exact (walshFn_eq_evalW_single S b).symm
  · rw [if_neg h, if_neg h]; exact (evalW_mul_walshFn aCoef Sᶜ b).symm

/-- **The collection on `G`.**  At a point `b ∈ G` (where the approximator agrees with the full parity), the
collected degree-`≤ n/2 + d` polynomial `collectCoef aCoef c` agrees with the original `evalW c`.  So every Walsh
polynomial is matched on `G` by a degree-`≤ n/2 + d` one — the boosting surjection's defining property. -/
theorem evalW_collectCoef_on_G (aCoef c : Finset (Fin n) → F) (b : Fin n → Bool)
    (hG : evalW aCoef b = walshFn Finset.univ b) :
    evalW (collectCoef aCoef c) b = evalW c b := by
  rw [evalW_collectCoef]
  exact (evalW_fold_on_G aCoef c b hG).symm

end PallLean.Paper93.DeepMath.PathB.WalshSpan

#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.walshFn_mul
#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.evalW_fold_on_G
#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.evalW_mul_walshFn
#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.evalW_collectCoef
#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.evalW_collectCoef_on_G
