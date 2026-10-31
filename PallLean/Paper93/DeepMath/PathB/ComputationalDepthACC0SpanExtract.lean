import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DimensionCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd

/-!
# Span-coefficient extraction — from `F_p`-span to explicit count-mod-`p` multiplicities (proved)

Entries 204–205 left two residuals in the span→`SYM∘AND` bridge: the `3/4`→exact amplification (entry 206 proved its
deterministic skeleton) and the **span-coefficient extraction** — turning an `F_p`-span element into explicit monomials
with `ZMod p`-valued coefficients, representable as `AND`-copy **multiplicities** `0..p−1`.  This file *proves* that
extraction: it is linear algebra (`Submodule.mem_span_range_iff_exists_fun`) plus the `ZMod.val` representative.

The result.  An element `f` of the span of the degree-`≤D` squarefree monomials is an explicit `F_p`-linear combination
`∑_S c_S·e_S` (`span_to` via the fintype span lemma); evaluated at any input, `f x = ∑_S c_S·[monoAND_S x]` (since the
squarefree monomial evaluation `∏_{i∈S} x_i` *is* the `monoAND` indicator, `squarefree_eq_monoAND_ind`); and each
coefficient `c_S` has a multiplicity `c_S.val < p` (`ZMod.val_lt`).  This is exactly the count-mod-`p` weighted-value
form that entry 205's `saCount_sigma_cast` consumes (with `c_S.val` the number of `AND`-copies of monomial `S`).

## What is proved (clean axioms, no `sorry`)

* **`squarefree_eq_monoAND_ind`** — the squarefree monomial evaluation `∏_{i∈S} boolToZMod(x_i)` equals the `monoAND`
  indicator `if monoAND S x then 1 else 0` over `ZMod p`.
* **`span_eval_weightedCount`** — the extraction: an `F_p`-span element `f` of the degree-`≤D` squarefree monomials has
  explicit coefficients `c : {S | S ∈ lowDegMonomials n D} → ZMod p` with each multiplicity `c_S.val < p` and
  `f x = ∑_S c_S·[monoAND_{S.1} x]` for every `x` — the count-mod-`p` weighted-value form.

## Honest scope

This proves the **span-coefficient extraction** completely — that the RS `F_p`-span output (entry 204) *is* an explicit
weighted count of `monoAND` indicators with bounded (`< p`) multiplicities, the exact form entry 205's count-mod-`p`
collapse consumes.  It connects entry 204's span format to entry 205's input, discharging the multiplicity-extraction
residual.  What remains of the span→`SYM∘AND` bridge is the **`3/4`→exact amplification** — bridging the RS *approximant*
(`≥ 3/4` agreement) to an *exact* representation of the circuit — whose deterministic skeleton entry 206 proved and whose
probabilistic existence (`MajorityGoodFamily`, Chernoff) remains the named socket.  This proves the extraction, not the
amplification.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SpanExtract

open Finset
open PallLean.Paper93.DeepMath.PathB.Layer3 (squarefreeEvalMonomial boolToZMod lowDegMonomials)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)

variable {n : ℕ}

/-- **The squarefree monomial evaluation is the `monoAND` indicator (PROVED).**  `∏_{i∈S} boolToZMod(x_i)` is `1` if all
bits in `S` are set (`monoAND S x`) and `0` otherwise — over `ZMod p`. -/
theorem squarefree_eq_monoAND_ind (p : ℕ) (S : Finset (Fin n)) (x : Fin n → Bool) :
    squarefreeEvalMonomial p S x = (if monoAND S x then (1 : ZMod p) else 0) := by
  unfold squarefreeEvalMonomial monoAND
  by_cases h : ∀ i ∈ S, x i = true
  · rw [if_pos (by simpa using h)]
    apply Finset.prod_eq_one
    intro i hi
    rw [h i hi]; rfl
  · rw [if_neg (by simpa using h)]
    push_neg at h
    obtain ⟨i, hiS, hi⟩ := h
    refine Finset.prod_eq_zero hiS ?_
    simp only [boolToZMod]
    exact if_neg hi

/-- **Span-coefficient extraction (PROVED).**  An `F_p`-span element `f` of the degree-`≤D` squarefree monomials has
explicit coefficients `c_S : ZMod p`, each with multiplicity `c_S.val < p`, such that at every input `x`,
`f x = ∑_S c_S·(if monoAND_{S.1} x then 1 else 0)` — the count-mod-`p` weighted-value form (the `c_S.val` are the
`AND`-copy multiplicities that entry-205's `saCount_sigma_cast` consumes). -/
theorem span_eval_weightedCount (p : ℕ) [Fact p.Prime] {D : ℕ}
    (f : (Fin n → Bool) → ZMod p)
    (hf : f ∈ Submodule.span (ZMod p)
        (Set.range (fun S : {S // S ∈ lowDegMonomials n D} => squarefreeEvalMonomial p S.1))) :
    ∃ c : {S // S ∈ lowDegMonomials n D} → ZMod p,
      (∀ S, (c S).val < p) ∧
      ∀ x, f x = ∑ S : {S // S ∈ lowDegMonomials n D}, c S * (if monoAND S.1 x then 1 else 0) := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  rw [Submodule.mem_span_range_iff_exists_fun] at hf
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, fun S => ZMod.val_lt (c S), fun x => ?_⟩
  rw [← hc, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, squarefree_eq_monoAND_ind]

end PallLean.Paper93.DeepMath.PathB.ACC0SpanExtract

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SpanExtract.squarefree_eq_monoAND_ind
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SpanExtract.span_eval_weightedCount
