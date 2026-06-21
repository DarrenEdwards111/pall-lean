import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitReprP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd

/-!
# Brick (SYM∘AND form) — AC⁰[p] value as an `F_p`-weighted sum over `AND`-gates (proved)

The `SYM∘AND` form object for the proven `AC⁰[p]` representation.  On Boolean inputs, any polynomial `P` over `F_p` equals the
`F_p`-weighted sum, over its monomials, of `AND`-gates: `eval (bv ∘ x) P = ∑_{e ∈ support} (coeff e P) · andVal(e.support) x`,
where `andVal S x = ∏_{i∈S} bv(xᵢ) = bv(monoAND S x)` is the `AND` of the bits in `S`.  Specialised to `reprP`, an `AC⁰[p]`
circuit's value `bv(eval C x)` is exactly an `F_p`-weighted sum over `AND`-gates `monoAND(e.support)`, each of fan-in `≤
reprDegP C` — i.e. a `SYM∘AND` form (the `SYM` gate being `F_p`-linear summation), with `≤ (n+1)^{reprDegP C}` distinct
`AND`-terms (Brick AC⁰[p] cash-out).

This is the explicit `SYM∘AND` representation object built from the real `reprP` polynomial — the `AND`-gate layer with its
`F_p`-summation `SYM` gate, faithful on all Boolean inputs.

## What is proved (clean axioms, no `sorry`)

* **`andVal`**, **`andVal_eq_bv_monoAND`** (PROVED) — `andVal S x = bv (monoAND S x)` (the `AND`-gate value).
* **`eval_eq_sum_andTerms`** (PROVED) — `eval (bv ∘ x) P = ∑_{e ∈ support} coeff e P · andVal(e.support) x`.
* **`reprP_eq_sum_andTerms`** (PROVED) — `ModpOnly p C → bv(eval C x) = ∑_{e} coeff e (reprP p C) · andVal(e.support) x`.

## Honest scope

This is the `SYM∘AND` form with an `F_p`-linear (`SYM`) summation gate over `AND`-gates, faithful for `AC⁰[p]`.  It does **not**
convert the `F_p`-weighted sum into the tree's count-based `symEval` (that needs replicating each `AND`-gate by its coefficient
and reading the count mod `p` — a separate packaging step), nor handle `MOD_q`(`q≠p`)/prime-power gates, nor the Williams
cash-out.  General YBT remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SymAndForm

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (reprP ModpOnly reprP_eval)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)

variable {n p : ℕ} [Fact p.Prime]

/-- The `AND`-gate value over a support `S` in `F_p`: `∏_{i∈S} bv(xᵢ)`. -/
def andVal (S : Finset (Fin n)) (x : Fin n → Bool) : ZMod p := ∏ i ∈ S, bv (x i)

/-- **The `AND`-gate value is the `F_p`-embedding of `monoAND` (PROVED).** -/
theorem andVal_eq_bv_monoAND (S : Finset (Fin n)) (x : Fin n → Bool) :
    (andVal S x : ZMod p) = bv (monoAND S x) := by
  unfold andVal
  by_cases h : ∀ i ∈ S, x i = true
  · rw [Finset.prod_eq_one (fun i hi => by simp [bv, h i hi]),
        show monoAND S x = true by simpa [monoAND] using h]
    simp [bv]
  · push_neg at h
    obtain ⟨i, hiS, hi⟩ := h
    rw [Finset.prod_eq_zero hiS (by simp [bv, hi]),
        show monoAND S x = false by
          simp only [monoAND, decide_eq_false_iff_not]; push_neg; exact ⟨i, hiS, hi⟩]
    simp [bv]

/-- **A polynomial is the `F_p`-weighted sum over its `AND`-terms on Boolean inputs (PROVED).** -/
theorem eval_eq_sum_andTerms (P : MvPolynomial (Fin n) (ZMod p)) (x : Fin n → Bool) :
    eval (fun i => (bv (x i) : ZMod p)) P
      = ∑ e ∈ P.support, coeff e P * andVal e.support x := by
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl (fun e he => ?_)
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hei : e i ≠ 0 := Finsupp.mem_support_iff.mp hi
  cases hx : x i with
  | true => simp [bv]
  | false => simp [bv, zero_pow hei]

/-- **The `AC⁰[p]` circuit value as an `F_p`-weighted sum over `AND`-gates (PROVED): the `SYM∘AND` form.** -/
theorem reprP_eq_sum_andTerms (C : ACC0Circuit n) (x : Fin n → Bool) (h : ModpOnly p C) :
    (bv (ACC0CircuitModel.eval C x) : ZMod p)
      = ∑ e ∈ (reprP p C).support, coeff e (reprP p C) * andVal e.support x := by
  rw [← reprP_eval C x h, eval_eq_sum_andTerms]

/-!
**The SYM∘AND form object, proved.**  An `AC⁰[p]` circuit's value is exactly an `F_p`-weighted sum over `AND`-gates
`monoAND(e.support)` (`reprP_eq_sum_andTerms`), each of fan-in `≤ reprDegP C` and `≤ (n+1)^{reprDegP C}` in number — the
`SYM∘AND` form with an `F_p`-linear `SYM` gate, faithful on all Booleans.  Remaining (open, not faked): repackaging into the
count-based `symEval`, `MOD_q`/prime-power gates, the Williams cash-out.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SymAndForm

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndForm.eval_eq_sum_andTerms
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndForm.reprP_eq_sum_andTerms
