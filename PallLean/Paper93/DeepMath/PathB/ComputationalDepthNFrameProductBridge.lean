import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDegreeChar
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCNormalForm

/-!
# The cube-invariant bridge: `∑∏` normal forms have low N-Frame complexity

The approximation-aware analysis (`ComputationalDepthSPDPApprox`) showed `spdpRank` is *not* cube-invariant, so the honest
bridge from `∑∏` normal forms to `ACC⁰[p]` must run through a **cube-invariant** measure.  This repo already has it —
`NFrameComplexity F f = ` minimal multilinear-representation degree of the Boolean function `f` — and the
Razborov–Smolensky lower bound (`parity_function_lower_bound`, the effective-dimension deficit) is stated against it.

This file closes the loop: the `∑∏` upper-bound machinery feeds that cube-invariant measure.

  `boolFn p` — the Boolean function `x ↦ eval (x as 0/1) p` of a polynomial `p`.
  `boolFn_mem_sqfSpan` — the reduction: on the cube `Xᵢ² = Xᵢ`, so a total-degree-`≤D` polynomial's cube-function is a
        combination of squarefree (multilinear) monomials of degree `≤D` — `boolFn p ∈ span (sqfGens F n D)`.
  `nframeComplexity_boolFn_le` — hence `NFrameComplexity F (boolFn p) ≤ totalDegree p`.
  `nframeComplexity_boolFn_sumProd_le` — **the bridge**: a shallow `∑_{i<s} ∏_{j<m} Q_{ij}` (`deg Q_{ij} ≤ t`) has
        `NFrameComplexity F (boolFn (∑∏Q)) ≤ m·t`.

So the `∑∏` normal form of C8 has **low N-Frame complexity** on the cube — a cube-invariant statement, unlike `spdpRank`.
Combined with a hard function's *high* N-Frame complexity (the repo's RS layer), this is the honest, cube-correct
separation route.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact (sqfGens)
open PallLean.Paper93.DeepMath.PathB.Layer4 (sqfEval)
open PallLean.Paper93.DeepMath.PathB.Layer3 (lowDegMonomials)
open PallLean.Paper93.DeepMath.PathB.Multilinear (monomialFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- The Boolean cube-function of a polynomial: evaluate with each variable set to `0`/`1`. -/
noncomputable def boolFn (p : MvPolynomial (Fin n) F) : (Fin n → Bool) → F :=
  fun x => MvPolynomial.eval (fun i => if x i then (1 : F) else 0) p

/-- **The multilinear reduction (proved)**.  On the cube every monomial `∏ Xᵢ^{dᵢ}` collapses to the squarefree
`∏_{i∈supp d} Xᵢ` of degree `|supp d| ≤ deg d`, so a total-degree-`≤D` polynomial's cube-function lies in the
degree-`≤D` squarefree span. -/
theorem boolFn_mem_sqfSpan (p : MvPolynomial (Fin n) F) {D : ℕ} (hD : p.totalDegree ≤ D) :
    boolFn p ∈ Submodule.span F (sqfGens F n D) := by
  classical
  have hbf : boolFn p = ∑ d ∈ p.support, (p.coeff d) • sqfEval F d.support := by
    funext x
    rw [boolFn, MvPolynomial.eval_eq, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Pi.smul_apply, smul_eq_mul, sqfEval_eq_monomialFn, monomialFn]
    congr 1
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    by_cases hxi : x i
    · simp [hxi]
    · simp [hxi, zero_pow hdi]
  rw [hbf]
  refine Submodule.sum_mem _ (fun d hd => Submodule.smul_mem _ _ ?_)
  apply Submodule.subset_span
  rw [sqfGens]
  refine ⟨⟨d.support, ?_⟩, rfl⟩
  rw [lowDegMonomials, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨Finset.subset_univ _, ?_⟩
  calc d.support.card
      ≤ d.sum (fun _ e => e) := by
        rw [Finsupp.sum]
        calc d.support.card = ∑ _i ∈ d.support, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ ∑ i ∈ d.support, d i :=
              Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd
    _ ≤ D := hD

/-- **A polynomial's cube-function has N-Frame complexity at most its total degree (proved).** -/
theorem nframeComplexity_boolFn_le (p : MvPolynomial (Fin n) F) :
    NFrameComplexity F (boolFn p) ≤ p.totalDegree :=
  nframeComplexity_le_of_mem_span (boolFn_mem_sqfSpan p (le_refl _))

/-- **The bridge (proved)**: a shallow `∑∏` of low-degree factors has low (cube-invariant) N-Frame complexity —
`NFrameComplexity F (boolFn (∑_{i<s} ∏_{j<m} Q_{ij})) ≤ m·t` when each `deg Q_{ij} ≤ t`.  This feeds the repo's
cube-invariant RS lower-bound layer, unlike `spdpRank`. -/
theorem nframeComplexity_boolFn_sumProd_le {s m t : ℕ} (Q : Fin s → Fin m → MvPolynomial (Fin n) F)
    (ht : ∀ i j, (Q i j).totalDegree ≤ t) :
    NFrameComplexity F (boolFn (∑ i, ∏ j, Q i j)) ≤ m * t := by
  refine le_trans (nframeComplexity_boolFn_le _) ?_
  refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le (fun i _ => ?_))
  refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun j _ => ht i j)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.boolFn_mem_sqfSpan
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.nframeComplexity_boolFn_sumProd_le
