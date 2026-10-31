import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameProductBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMODqHigh

/-!
# Closing the separation: `MOD_q` is not a shallow `∑∏` on the cube

The two cube-invariant sides now meet:
* **Low (C10, `nframeComplexity_boolFn_sumProd_le`)** — a shallow `∑_{i<s} ∏_{j<m} Q_{ij}` (`deg Q_{ij} ≤ t`) has
  `NFrameComplexity (boolFn ∑∏Q) ≤ m·t`.
* **High (`nframeComplexity_omegaFn_univ_ge`)** — `MOD_q` (`omegaFn ω univ`, `ω` a primitive `q`-th root over `F`) has
  `NFrameComplexity ≥ n − n/2 = ⌈n/2⌉`.

Combining them:

  `hard_not_shallow_sumProd` — any Boolean function `h` with `m·t < NFrameComplexity F h` is **not** the cube-function
        of a shallow `∑∏` normal form: `h ≠ boolFn (∑_{i<s} ∏_{j<m} Q_{ij})`.
  `modq_not_shallow_sumProd` — the concrete separation: for `m·t < ⌈n/2⌉`, `MOD_q` is not computed on the Boolean cube
        by any shallow `∑∏` of degree-`≤t` factors.

This is a genuine, cube-correct, restricted separation — the two-sided N-Frame skeleton closed for the `∑∏`
(Beigel–Tarui inner-layer) model, using only the *cube-invariant* measure that C9 identified as the right one.

## Honest scope

`MOD_q` here is `omegaFn` over a field of characteristic `≠ q` (the polynomial-method / Smolensky regime), and the
separation is against **exact** cube-computation by shallow `∑∏` of low-degree factors — the BT inner layer, `m·t <
⌈n/2⌉`.  It is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`: it does not reach full `ACC⁰` (the `SYM`/composite-`MOD` outer layer
and unbounded depth are the standing barrier), and exact `∑∏`-representation is stronger than `AC⁰[p]` membership.  What
is closed is the honest restricted statement: high N-Frame complexity rules out shallow `∑∏`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- **The separation (proved)**: a Boolean function whose N-Frame complexity exceeds `m·t` cannot be the cube-function of
a shallow `∑_{i<s} ∏_{j<m} Q_{ij}` with each factor of degree `≤ t`. -/
theorem hard_not_shallow_sumProd {s m t : ℕ} (h : (Fin n → Bool) → F)
    (Q : Fin s → Fin m → MvPolynomial (Fin n) F) (ht : ∀ i j, (Q i j).totalDegree ≤ t)
    (hhard : m * t < NFrameComplexity F h) :
    h ≠ boolFn (∑ i, ∏ j, Q i j) := by
  intro heq
  have hle := nframeComplexity_boolFn_sumProd_le Q ht
  rw [← heq] at hle
  omega

/-- **`MOD_q` is not a shallow `∑∏` on the cube (proved)**: when `m·t < ⌈n/2⌉`, `omegaFn ω univ` (`MOD_q` over `F`,
`ω` a primitive `q`-th root) is not the cube-function of any shallow sum of products of degree-`≤t` factors. -/
theorem modq_not_shallow_sumProd [Fintype F] [DecidableEq F] {s m t q : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q)
    (Q : Fin s → Fin m → MvPolynomial (Fin n) F) (ht : ∀ i j, (Q i j).totalDegree ≤ t)
    (hshallow : m * t < n - n / 2) :
    omegaFn ω (Finset.univ : Finset (Fin n)) ≠ boolFn (∑ i, ∏ j, Q i j) :=
  hard_not_shallow_sumProd _ Q ht
    (lt_of_lt_of_le hshallow (nframeComplexity_omegaFn_univ_ge ω hω hq2))

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.hard_not_shallow_sumProd
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.modq_not_shallow_sumProd
