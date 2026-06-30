import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModFieldExact
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Bridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd

/-!
# The finite-field `MOD_p` gate lies in the degree-`≤(|F|−1)` monomial-`AND` span (the SYM∘AND bottom layer)

`…ACC0ModPExact.modp_mem_monoAND_span` placed the `F_p` `MOD_p` gate in the degree-`≤(p−1)` monomial-`AND` span.
This file does the same over **any** finite field `F` (order `q = p^k`), completing the prime-power-field story of
`…ACC0ModFieldExact`: combining the exact degree-`(q−1)` representation (`modField_exact_eval`) with the
general-field span lemma `Layer4.eval_mem_lowDegSpan_K`, the `MOD_p`-over-`F` gate lies in the `F`-span of the
degree-`≤(q−1)` monomial-`AND` indicators — the `SYM∘AND` bottom layer over `F_{p^k}`.

Nothing here crosses the composite-`MOD` barrier or the uniform-realization socket; nothing is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer4 (boolToField sqfEval eval_mem_lowDegSpan_K)
open PallLean.Paper93.DeepMath.PathB.Layer3 (lowDegMonomials)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)

variable {n : ℕ} {F : Type*} [Field F]

/-- **The squarefree generator is the monomial-`AND` indicator over `F` (proved).**  `∏_{i∈S} boolToField F xᵢ = 1`
iff every bit in `S` is set. -/
theorem sqfEval_eq_monoAND (S : Finset (Fin n)) (x : Fin n → Bool) :
    sqfEval F S x = if monoAND S x then (1 : F) else 0 := by
  unfold sqfEval boolToField monoAND
  by_cases h : ∀ i ∈ S, x i = true
  · rw [if_pos (by simpa using h)]
    exact Finset.prod_eq_one fun i hi => by simp [h i hi]
  · rw [if_neg (by simpa using h)]
    push_neg at h
    obtain ⟨i, hiS, hi⟩ := h
    exact Finset.prod_eq_zero hiS (by cases hxi : x i <;> simp_all)

variable [Fintype F] [DecidableEq F]

/-- **The `MOD_p`-over-`F` gate lies in the degree-`≤(|F|−1)` monomial-`AND` span over `F` (proved).**  The
prime-power-field analogue of `…ACC0ModPExact.modp_mem_monoAND_span`. -/
theorem modField_mem_monoAND_span (S : Finset (Fin n)) :
    (fun x : Fin n → Bool => boolToF (modFieldBool (F := F) S x))
      ∈ Submodule.span F
        (Set.range (fun T : {T // T ∈ lowDegMonomials n (Fintype.card F - 1)} =>
          fun x : Fin n → Bool => if monoAND T.1 x then (1 : F) else 0)) := by
  have hgen :
      (fun T : {T // T ∈ lowDegMonomials n (Fintype.card F - 1)} =>
        fun x : Fin n → Bool => if monoAND T.1 x then (1 : F) else 0)
        = (fun T : {T // T ∈ lowDegMonomials n (Fintype.card F - 1)} => sqfEval F T.1) := by
    funext T x
    exact (sqfEval_eq_monoAND T.1 x).symm
  rw [hgen]
  have hfun : (fun x : Fin n → Bool => boolToF (modFieldBool (F := F) S x))
      = (fun x : Fin n → Bool => eval (fun i => boolToField F (x i)) (modFieldPoly (F := F) S)) := by
    funext x
    exact (modField_exact_eval x S).symm
  rw [hfun]
  exact eval_mem_lowDegSpan_K F (Fintype.card F - 1) (modFieldPoly S) (modFieldPoly_totalDegree_le S)

end PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.modField_mem_monoAND_span
