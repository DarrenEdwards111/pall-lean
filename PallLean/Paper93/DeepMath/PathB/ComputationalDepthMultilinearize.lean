import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultilinear
import Mathlib

/-!
# Multilinearization on the cube (PROVED) — `MvPolynomial.eval` = `Multilinear.eval`

On the Boolean cube `{0,1}ⁿ` every coordinate is idempotent (`x_i^k = x_i` for `k ≥ 1`), so an arbitrary
`MvPolynomial` restricted to the cube is multilinear.  This file makes that precise and **degree-preserving**,
bridging the `MvPolynomial` approximator built by the circuit recursion to the `Multilinear.eval` / Walsh world
where the boosting/dimension argument lives.

  `prod_pow_eq_monomialFn` — a single monomial `∏_{i∈d.support} (xᵢ as 0/1)^{dᵢ}` collapses to the multilinear
        monomial `monomialFn d.support` on the cube (each `0/1` coordinate is idempotent).
  `eval_eq_multilinear` — `MvPolynomial.eval` at a `0/1` point equals `Multilinear.eval` of the multilinearized
        coefficients `c S = Σ_{d : d.support = S} P.coeff d`.
  `multilinear_coeff_support` — those coefficients are **degree-preserving**: `c S = 0` whenever
        `|S| > totalDegree P` (a monomial with support `S` has degree `≥ |S|`).

Composed with `WalshSpan.eval_eq_evalW` (multilinear → Walsh, degree-preserving) this carries
`circuit_low_degree_approx`'s `{0,1}` approximator into the `{−1,+1}` Walsh basis for `boosting_surjection`.
-/

open MvPolynomial

namespace PallLean.Paper93.DeepMath.PathB.Multilinearize

variable {n p : ℕ}

/-- **A monomial collapses to a multilinear monomial on the cube.**  Over `{0,1}`, `(xᵢ)^{dᵢ} = xᵢ` for
`i ∈ d.support` (`dᵢ ≥ 1`, and `0,1` are idempotent), so `∏_{i∈d.support} (xᵢ as 0/1)^{dᵢ} = ∏_{i∈d.support} (xᵢ
as 0/1) = monomialFn d.support`. -/
theorem prod_pow_eq_monomialFn (x : Fin n → Bool) (d : Fin n →₀ ℕ) :
    (∏ i ∈ d.support, ((x i).toNat : ZMod p) ^ d i)
      = Multilinear.monomialFn (F := ZMod p) d.support x := by
  rw [Multilinear.monomialFn]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  cases x i
  · simp [zero_pow hdi]
  · simp

/-- **Multilinearization.**  `MvPolynomial.eval` at a `0/1` point equals `Multilinear.eval` of the coefficient
vector `c S = Σ_{d ∈ P.support, d.support = S} P.coeff d`: expand `eval` over the support, collapse each monomial
(`prod_pow_eq_monomialFn`), and group the monomials by their support. -/
theorem eval_eq_multilinear (P : MvPolynomial (Fin n) (ZMod p)) (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => ((x i).toNat : ZMod p)) P
      = Multilinear.eval (fun S => ∑ d ∈ P.support.filter (fun d => d.support = S), P.coeff d) x := by
  rw [MvPolynomial.eval_eq]
  simp_rw [prod_pow_eq_monomialFn]
  rw [← Finset.sum_fiberwise_of_maps_to (s := P.support) (g := fun d => d.support)
      (t := Finset.univ) (f := fun d => P.coeff d * Multilinear.monomialFn d.support x)
      (fun d _ => Finset.mem_univ _)]
  rw [Multilinear.eval]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_filter] at hd
  rw [hd.2]

/-- **The multilinearization is degree-preserving.**  If `|S| > totalDegree P`, then `c S = 0`: any monomial `d`
with `d.support = S` would have degree `(Σ dᵢ) ≥ |d.support| = |S| > totalDegree P`, impossible in the support. -/
theorem multilinear_coeff_support (P : MvPolynomial (Fin n) (ZMod p)) (S : Finset (Fin n))
    (hS : P.totalDegree < S.card) :
    (∑ d ∈ P.support.filter (fun d => d.support = S), P.coeff d) = 0 := by
  refine Finset.sum_eq_zero (fun d hd => ?_)
  rw [Finset.mem_filter] at hd
  exfalso
  have hcard : d.support.card ≤ d.sum (fun _ e => e) := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  have hdeg : (d.sum fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hd.1
  rw [hd.2] at hcard
  omega

end PallLean.Paper93.DeepMath.PathB.Multilinearize

#print axioms PallLean.Paper93.DeepMath.PathB.Multilinearize.prod_pow_eq_monomialFn
#print axioms PallLean.Paper93.DeepMath.PathB.Multilinearize.eval_eq_multilinear
#print axioms PallLean.Paper93.DeepMath.PathB.Multilinearize.multilinear_coeff_support
