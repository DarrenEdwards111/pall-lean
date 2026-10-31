import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameProductBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMODqHigh

/-!
# Extending the low side to full ACC⁰: the SYM / composite-MOD outer layer

Beigel–Tarui: every `ACC⁰` function has the shape `f = P(∑_{i<s} ∏_{j<m} Q_{ij})` — a **symmetric / composite-MOD outer
gate**, arithmetised as a *univariate* polynomial `P` over `F`, applied to the `∑∏` inner layer of C8–C11.  This file
extends the (cube-invariant) low-side N-Frame bound from the inner `∑∏` to this full BT shape.

  `totalDegree_polyAeval_le` — composition degree: `totalDegree (P(h)) ≤ deg P · totalDegree h`.
  `nframeComplexity_boolFn_polyComp_le` — `NFrameComplexity (boolFn (P(h))) ≤ deg P · totalDegree h`.
  `nframeComplexity_boolFn_symSumProd_le` — **the extended low side**: for the full BT normal form,
        `NFrameComplexity (boolFn (P(∑∏Q))) ≤ deg P · m · t`.

## Where the composite-MOD power hides — and why this does *not* separate ACC⁰

The extension is honest and *covers full `ACC⁰`* (every ACC⁰ function is some `P(∑∏)`), but the bound carries the factor
`deg P` — the degree of the arithmetised outer symmetric/`MOD` gate.  For `AC⁰[p]` (prime `p`) a `MOD_p` gate is degree
`1` over `F_p`, so `deg P` is small and the bound bites.  For a genuine composite `MOD_m` gate the arithmetisation has
**large** degree, and the bound `deg P · m · t` is quasi-polynomial — too weak to beat a hard function's linear N-Frame
complexity.  Made precise:

  `symSumProd_degree_lb_of_modq` — if `MOD_q = P(∑∏Q)` on the cube, then `deg P · m · t ≥ ⌈n/2⌉`.

So representing `MOD_q` as `SYM∘∑∏` forces the outer-degree×inner-size product to be at least linear: the composite-MOD
cost is *exactly* the `deg P` factor.  This is the honest reason the low side does not extend to a *small* bound for full
`ACC⁰` — `MOD_q ∈ ACC⁰` has high N-Frame complexity (`nframeComplexity_omegaFn_univ_ge`), so no `SYM∘∑∏` representation of
it can have small `deg P · m · t`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`; it is the quantitative anatomy of the
composite-MOD barrier.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- Composition degree: substituting a multivariate `h` into a univariate `P` multiplies total degree by `deg P`. -/
theorem totalDegree_polyAeval_le (P : Polynomial F) (h : MvPolynomial (Fin n) F) :
    (Polynomial.aeval h P).totalDegree ≤ P.natDegree * h.totalDegree := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum]
  refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le (fun k hk => ?_))
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
  exact Nat.mul_le_mul (Polynomial.le_natDegree_of_mem_supp k hk) (le_refl _)

/-- The cube-function of a univariate composition `P(h)` has N-Frame complexity `≤ deg P · totalDegree h`. -/
theorem nframeComplexity_boolFn_polyComp_le (P : Polynomial F) (h : MvPolynomial (Fin n) F) :
    NFrameComplexity F (boolFn (Polynomial.aeval h P)) ≤ P.natDegree * h.totalDegree :=
  le_trans (nframeComplexity_boolFn_le _) (totalDegree_polyAeval_le P h)

/-- **The extended low side (proved)**: the full Beigel–Tarui shape `P(∑_{i<s}∏_{j<m} Q_{ij})` — a symmetric/composite-MOD
outer gate `P` over the `∑∏` inner layer — has `NFrameComplexity (boolFn (P(∑∏Q))) ≤ deg P · m · t`. -/
theorem nframeComplexity_boolFn_symSumProd_le {s m t : ℕ} (P : Polynomial F)
    (Q : Fin s → Fin m → MvPolynomial (Fin n) F) (ht : ∀ i j, (Q i j).totalDegree ≤ t) :
    NFrameComplexity F (boolFn (Polynomial.aeval (∑ i, ∏ j, Q i j) P)) ≤ P.natDegree * (m * t) := by
  refine le_trans (nframeComplexity_boolFn_polyComp_le P _) (Nat.mul_le_mul (le_refl _) ?_)
  refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le (fun i _ => ?_))
  refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun j _ => ht i j)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The composite-MOD barrier, quantified (proved)**: if `MOD_q` is represented on the cube as `P(∑∏Q)` (a
symmetric/composite-MOD outer gate over a `∑∏` inner layer), then `deg P · m · t ≥ ⌈n/2⌉`.  So the outer-degree×inner-size
product is at least linear — the composite-MOD cost is exactly the `deg P` factor, and no such representation of `MOD_q`
can be small. -/
theorem symSumProd_degree_lb_of_modq [Fintype F] [DecidableEq F] {s m t q : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) (P : Polynomial F)
    (Q : Fin s → Fin m → MvPolynomial (Fin n) F) (ht : ∀ i j, (Q i j).totalDegree ≤ t)
    (heq : omegaFn ω (Finset.univ : Finset (Fin n)) = boolFn (Polynomial.aeval (∑ i, ∏ j, Q i j) P)) :
    n - n / 2 ≤ P.natDegree * (m * t) := by
  calc n - n / 2
      ≤ NFrameComplexity F (omegaFn ω (Finset.univ : Finset (Fin n))) :=
        nframeComplexity_omegaFn_univ_ge ω hω hq2
    _ = NFrameComplexity F (boolFn (Polynomial.aeval (∑ i, ∏ j, Q i j) P)) := by rw [heq]
    _ ≤ P.natDegree * (m * t) := nframeComplexity_boolFn_symSumProd_le P Q ht

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.nframeComplexity_boolFn_symSumProd_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.symSumProd_degree_lb_of_modq
