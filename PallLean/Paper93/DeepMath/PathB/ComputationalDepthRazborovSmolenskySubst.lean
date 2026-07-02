import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyComposable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiCompose

/-!
# Beigel–Tarui, rung 17: the whole-circuit RS substitution and its polylog degree

Rung 16 built the composable `OR`-gadget `orApproxComp` on arbitrary input polynomials.  This file uses it to
**recursively substitute an approximator at every gate** of an `AND`/`OR`/`NOT` formula, producing a *single*
polynomial `arithApprox subsets f` for the whole circuit, and proves the key degree fact:

> the assembled polynomial has total degree `≤ ((#subsets)·(p-1))^depth`,

i.e. **polylogarithmic** when the depth is constant and `#subsets = t = polylog` — the Razborov–Smolensky degree
reduction for a whole depth-`d` circuit (contrast rung 6's exact arithmetisation, degree `2^depth`).

The substitution follows the standard `AC⁰[p]` recipe:

  `arithApprox` — `var → Xᵢ` (degree `1`); `NOT a → 1 - approx a` (exact, no degree blow-up); `OR a b →` the composable
        gadget `orApproxComp` on the two sub-approximators; `AND a b →` De Morgan `¬OR(¬a,¬b)`, i.e.
        `1 - orApproxComp` on the *negated* sub-approximators.
  `arithApprox_totalDegree_le` — **PROVED, the composition degree bound**: `deg ≤ ((#subsets)(p-1))^depth`; each `OR`/`AND`
        level multiplies the degree by the gadget factor `(#subsets)(p-1)`, `NOT` preserves it, and a variable seeds it
        at `1`.
  `arithApprox_totalDegree_le_pow` — **PROVED**: the same bound rephrased with `D = (#subsets)(p-1)`.

We also record the substitution *semantics* (needed for the error bound, rung 18):

  `arithApproxVal` — the value-level assembled evaluator (the same recursion on field values).
  `eval_arithApprox` — **PROVED, the evaluation homomorphism**: `eval φ (arithApprox subsets f) = arithApproxVal subsets f
        φ` — evaluating the assembled polynomial is the value-level recursion, so a genuine substitution.

## Honest scope

This assembles the whole-circuit RS-substituted polynomial and proves its polylog degree and its substitution semantics
— the degree half of the whole-circuit approximation.  What remains (rung 18): the **error bound** — that
`arithApprox subsets f` computes `f.eval` off a set of `≤ #gates · 2^{n-t}` inputs, by choosing each gate's subsets via
rung 8's averaging (`exists_low_error_orApprox`) and wiring the per-gate `2^{-t}` error sets through rung 7's
`error_card_le` union bound (using `orApproxVal_fires`/`orApproxVal_allzero` for per-gate correctness off the bad set).
The composite-`MOD_m` case remains the proven two-fields barrier.  Nothing here is the Beigel–Tarui reduction in full,
`NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical
open PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase (BForm depth)

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- **The whole-circuit RS substitution**: substitute a low-degree approximator at every gate.  `var → Xᵢ`; `NOT a`
exact; `OR a b` via the composable gadget on the two sub-approximators; `AND a b` via De Morgan `¬OR(¬a,¬b)`. -/
noncomputable def arithApprox (subsets : List (Finset (Fin 2))) :
    BForm n → MvPolynomial (Fin n) (ZMod p)
  | .var i => X i
  | .bnot a => 1 - arithApprox subsets a
  | .bor a b => orApproxComp ![arithApprox subsets a, arithApprox subsets b] subsets
  | .band a b => 1 - orApproxComp ![1 - arithApprox subsets a, 1 - arithApprox subsets b] subsets

/-- The value-level assembled evaluator: the same recursion on field values (`OR`/`AND` via `orApproxVal`). -/
noncomputable def arithApproxVal (subsets : List (Finset (Fin 2))) :
    BForm n → (Fin n → ZMod p) → ZMod p
  | .var i, φ => φ i
  | .bnot a, φ => 1 - arithApproxVal subsets a φ
  | .bor a b, φ => orApproxVal ![arithApproxVal subsets a φ, arithApproxVal subsets b φ] subsets
  | .band a b, φ =>
      1 - orApproxVal ![1 - arithApproxVal subsets a φ, 1 - arithApproxVal subsets b φ] subsets

/-- **The composition degree bound (proved)**: the whole-circuit RS-substituted polynomial has total degree
`≤ ((#subsets)·(p-1))^depth` — each `OR`/`AND` level multiplies the degree by the gadget factor `(#subsets)(p-1)`, `NOT`
preserves it, and a variable seeds it at `1`.  Polylog for constant depth and `#subsets = polylog`. -/
theorem arithApprox_totalDegree_le (subsets : List (Finset (Fin 2))) (hlen : 1 ≤ subsets.length)
    (f : BForm n) :
    (arithApprox (p := p) subsets f).totalDegree ≤ (subsets.length * (p - 1)) ^ depth f := by
  have hp : 1 ≤ p - 1 := by have := (Fact.out : p.Prime).two_le; omega
  have hD1 : 1 ≤ subsets.length * (p - 1) := by simpa using Nat.mul_le_mul hlen hp
  induction f with
  | var i =>
      rw [arithApprox]; simp only [depth, pow_zero]; exact (totalDegree_X i).le
  | bnot a ih =>
      rw [arithApprox, depth]
      exact one_sub_totalDegree_le _ _ (le_trans ih (Nat.pow_le_pow_right hD1 (Nat.le_succ _)))
  | bor a b iha ihb =>
      rw [arithApprox, depth]
      have hinp : ∀ i, ((![arithApprox subsets a, arithApprox subsets b] : Fin 2 →
          MvPolynomial (Fin n) (ZMod p)) i).totalDegree
          ≤ (subsets.length * (p - 1)) ^ max (depth a) (depth b) := by
        intro i; fin_cases i
        · simpa using le_trans iha (Nat.pow_le_pow_right hD1 (le_max_left _ _))
        · simpa using le_trans ihb (Nat.pow_le_pow_right hD1 (le_max_right _ _))
      refine le_trans (orApproxComp_totalDegree_le _ subsets _ hinp) (le_of_eq ?_)
      rw [pow_succ]; ring
  | band a b iha ihb =>
      rw [arithApprox, depth]
      refine one_sub_totalDegree_le _ _ ?_
      have hinp : ∀ i, ((![1 - arithApprox subsets a, 1 - arithApprox subsets b] : Fin 2 →
          MvPolynomial (Fin n) (ZMod p)) i).totalDegree
          ≤ (subsets.length * (p - 1)) ^ max (depth a) (depth b) := by
        intro i; fin_cases i
        · simpa using
            one_sub_totalDegree_le _ _ (le_trans iha (Nat.pow_le_pow_right hD1 (le_max_left _ _)))
        · simpa using
            one_sub_totalDegree_le _ _ (le_trans ihb (Nat.pow_le_pow_right hD1 (le_max_right _ _)))
      refine le_trans (orApproxComp_totalDegree_le _ subsets _ hinp) (le_of_eq ?_)
      rw [pow_succ]; ring

/-- **The degree bound with `D = (#subsets)(p-1)` (proved)**: `deg (arithApprox subsets f) ≤ D^depth`. -/
theorem arithApprox_totalDegree_le_pow (subsets : List (Finset (Fin 2))) (hlen : 1 ≤ subsets.length)
    (f : BForm n) {D : ℕ} (hD : subsets.length * (p - 1) = D) :
    (arithApprox (p := p) subsets f).totalDegree ≤ D ^ depth f := by
  rw [← hD]; exact arithApprox_totalDegree_le subsets hlen f

/-- **The evaluation homomorphism (proved)**: evaluating the assembled polynomial at `φ` is the value-level recursion
`arithApproxVal` — so `arithApprox` is a genuine substitution (`eval` commutes with the gate composition at every
level). -/
theorem eval_arithApprox (subsets : List (Finset (Fin 2))) (φ : Fin n → ZMod p) (f : BForm n) :
    (eval φ) (arithApprox (p := p) subsets f) = arithApproxVal subsets f φ := by
  induction f with
  | var i => simp [arithApprox, arithApproxVal]
  | bnot a ih => rw [arithApprox, map_sub, map_one, ih, arithApproxVal]
  | bor a b iha ihb =>
      rw [arithApprox, eval_orApproxComp]
      have hv : (fun i => (eval φ) ((![arithApprox subsets a, arithApprox subsets b] :
            Fin 2 → MvPolynomial (Fin n) (ZMod p)) i))
          = (![arithApproxVal subsets a φ, arithApproxVal subsets b φ] : Fin 2 → ZMod p) := by
        funext i; fin_cases i <;> simp [iha, ihb]
      rw [hv, arithApproxVal]
  | band a b iha ihb =>
      rw [arithApprox, map_sub, map_one, eval_orApproxComp]
      have hv : (fun i => (eval φ) ((![1 - arithApprox subsets a, 1 - arithApprox subsets b] :
            Fin 2 → MvPolynomial (Fin n) (ZMod p)) i))
          = (![1 - arithApproxVal subsets a φ, 1 - arithApproxVal subsets b φ] : Fin 2 → ZMod p) := by
        funext i; fin_cases i <;> simp [map_sub, map_one, iha, ihb]
      rw [hv, arithApproxVal]

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.arithApprox_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.eval_arithApprox
