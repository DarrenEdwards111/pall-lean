import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DimensionCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd

/-!
# Bridging the RS low-degree machinery to the `SYM∘AND` bottom layer

The Razborov–Smolensky layer (`…Layer3*`) approximates an `AC⁰[p]` circuit by a **low-degree polynomial over `ZMod p`**,
and `eval_mem_lowDegSpan` puts that polynomial's Boolean-cube evaluation in the span of the *squarefree monomial
evaluations* `squarefreeEvalMonomial p S = (x ↦ ∏_{i∈S} boolToZMod p (xᵢ))` for `|S| ≤ D`.

This file makes the connection to the `SYM∘AND` world explicit: **the RS low-degree-span generators are exactly the
monomial-`AND` gates.**  Indeed `∏_{i∈S} boolToZMod p (xᵢ) = 1` iff every bit in `S` is set, i.e.

```
squarefreeEvalMonomial p S x  =  if monoAND S x then (1 : ZMod p) else 0.
```

So the low-degree span is the `ZMod p`-span of the monomial-`AND` indicators, and the RS approximant of an `AC⁰[p]`
circuit is a `ZMod p`-linear combination of `≤ ∑_{i≤D} C(n,i)` monomial-`AND` gates — the bottom layer of `SYM∘AND`,
with the top being the count-mod-`p` (`SYM`) gate.  This is the honest RS → `SYM∘AND` bridge **at the polynomial level**.

## What is proved (clean axioms, no `sorry`)

* `squarefreeEvalMonomial_eq_monoAND` — the RS monomial generator equals the monomial-`AND` indicator over `ZMod p`.
* `lowDegPolyEval_mem_monoAND_span` — a degree-`≤D` polynomial's cube eval lies in the `ZMod p`-span of the
  monomial-`AND` indicators (lifting `eval_mem_lowDegSpan` through the bridge).

## Honest scope

This bridges RS to the `SYM∘AND` *bottom layer* (monomial-`AND` gates) exactly.  Two honest gaps remain, both already
flagged: (1) RS is **approximate** — `acc0_approx_by_lowRankPredictor` only agrees with the `AC⁰[p]` circuit on a
`1-ε` fraction, so this gives an *approximate* `SYM∘AND`, not the exact YBT normal form; (2) turning the `ZMod p`-linear
top into the count-mod-`p` `SYM` gate is the (weighted) duplication step (`SYM` reads the count of the duplicated gate
family).  The exact `AC⁰[p] → SYM∘AND` reduction across depth remains the open structural wall
(`MixedACCDepthReductionSocket`).  Still the cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RSToSymAnd

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd

variable {n : ℕ}

/-- **The RS low-degree generator is the monomial-`AND` indicator (proved).**  `∏_{i∈S} boolToZMod p (xᵢ) = 1` iff
every bit in `S` is set. -/
theorem squarefreeEvalMonomial_eq_monoAND (p : ℕ) (S : Finset (Fin n)) (x : Fin n → Bool) :
    squarefreeEvalMonomial p S x = if monoAND S x then (1 : ZMod p) else 0 := by
  unfold squarefreeEvalMonomial monoAND boolToZMod
  by_cases h : ∀ i ∈ S, x i = true
  · rw [if_pos (by simpa using h)]
    exact Finset.prod_eq_one fun i hi => by simp [h i hi]
  · rw [if_neg (by simpa using h)]
    push_neg at h
    obtain ⟨i, hiS, hi⟩ := h
    exact Finset.prod_eq_zero hiS (by cases hxi : x i <;> simp_all)

/-- **The RS approximant is a `ZMod p`-combination of monomial-`AND` gates (proved).**  Lifting `eval_mem_lowDegSpan`
through the bridge: a degree-`≤D` polynomial's cube evaluation lies in the span of the monomial-`AND` indicators of
degree `≤ D` — the `SYM∘AND` bottom layer (`≤ ∑_{i≤D} C(n,i)` gates). -/
theorem lowDegPolyEval_mem_monoAND_span (p : ℕ) [Fact p.Prime] (D : ℕ)
    (h : MvPolynomial (Fin n) (ZMod p)) (hdeg : h.totalDegree ≤ D) :
    (fun x : Fin n → Bool => eval (fun i => boolToZMod p (x i)) h)
      ∈ Submodule.span (ZMod p)
        (Set.range (fun S : {S // S ∈ lowDegMonomials n D} =>
          fun x : Fin n → Bool => if monoAND S.1 x then (1 : ZMod p) else 0)) := by
  have hgen :
      (fun S : {S // S ∈ lowDegMonomials n D} =>
        fun x : Fin n → Bool => if monoAND S.1 x then (1 : ZMod p) else 0)
        = (fun S : {S // S ∈ lowDegMonomials n D} => squarefreeEvalMonomial p S.1) := by
    funext S x
    exact (squarefreeEvalMonomial_eq_monoAND p S.1 x).symm
  rw [hgen]
  exact eval_mem_lowDegSpan p D h hdeg

end PallLean.Paper93.DeepMath.PathB.ACC0RSToSymAnd

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RSToSymAnd.squarefreeEvalMonomial_eq_monoAND
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RSToSymAnd.lowDegPolyEval_mem_monoAND_span
