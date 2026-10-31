import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModFieldSpan

/-!
# The `OR` gate is *exactly* degree `≤ |S|` over any field, and in the monomial-`AND` span

Companion to `…ACC0ModFieldExact` / `…ACC0ModFieldSpan`: the third `AC⁰[p]` gate (`OR`) over a field `F`.  By
De Morgan, `OR_S(x) = [∃ i∈S, x_i] = 1 − ∏_{i∈S}(1 − x_i)`, an **exact** degree-`≤|S|` polynomial over any field.
With the `AND` gate (`= sqfEval`, the monomial-`AND` indicator) and the `MOD_p` gate (`…ACC0ModFieldExact`), this
completes the `AC⁰[p]` gate set over the prime-power field `F_{p^k}`: every gate is an exact, degree-bounded element
of the monomial-`AND` span (the `SYM∘AND` bottom layer).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer4 (boolToField sqfEval eval_mem_lowDegSpan_K)
open PallLean.Paper93.DeepMath.PathB.Layer3 (lowDegMonomials)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)

variable {n : ℕ} {F : Type*} [Field F]

/-- The `OR` polynomial `1 − ∏_{i∈S}(1 − X_i)` over a field `F`. -/
noncomputable def orFieldPoly (S : Finset (Fin n)) : MvPolynomial (Fin n) F :=
  1 - ∏ i ∈ S, (1 - X i)

/-- **`OR` has total degree `≤ |S|` (proved).** -/
theorem orFieldPoly_totalDegree_le (S : Finset (Fin n)) :
    (orFieldPoly (F := F) S).totalDegree ≤ S.card := by
  unfold orFieldPoly
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  refine max_le (Nat.zero_le _) ?_
  refine le_trans (totalDegree_finset_prod _ _) ?_
  calc ∑ i ∈ S, ((1 : MvPolynomial (Fin n) F) - X i).totalDegree
      ≤ ∑ _i ∈ S, 1 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine le_trans (totalDegree_sub _ _) ?_
        rw [totalDegree_one, totalDegree_X]
        exact max_le (Nat.zero_le _) le_rfl
    _ = S.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- The **`OR` gate**: some bit in `S` is set. -/
def orFieldBool (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ i ∈ S, x i = true)

/-- **`OR` computed *exactly* by the degree-`≤|S|` polynomial over `F` (proved), by De Morgan.** -/
theorem orField_exact_eval (x : Fin n → Bool) (S : Finset (Fin n)) :
    eval (fun i => if x i then (1 : F) else 0) (orFieldPoly (F := F) S)
      = (boolToF (F := F) (orFieldBool S x) : F) := by
  unfold orFieldPoly orFieldBool boolToF
  rw [eval_sub, map_one, eval_prod]
  simp only [eval_sub, map_one, eval_X]
  by_cases h : ∃ i ∈ S, x i = true
  · rw [if_pos (by simpa using h)]
    obtain ⟨i, hiS, hi⟩ := h
    rw [Finset.prod_eq_zero hiS (by simp [hi]), sub_zero]
  · rw [if_neg (by simpa using h)]
    push_neg at h
    rw [Finset.prod_eq_one (fun i hiS => by cases hxi : x i <;> simp_all), sub_self]

/-- **`OR` lies in the degree-`≤|S|` monomial-`AND` span over `F` (proved).** -/
theorem orField_mem_monoAND_span (S : Finset (Fin n)) :
    (fun x : Fin n → Bool => boolToF (F := F) (orFieldBool S x))
      ∈ Submodule.span F
        (Set.range (fun T : {T // T ∈ lowDegMonomials n S.card} =>
          fun x : Fin n → Bool => if monoAND T.1 x then (1 : F) else 0)) := by
  have hgen :
      (fun T : {T // T ∈ lowDegMonomials n S.card} =>
        fun x : Fin n → Bool => if monoAND T.1 x then (1 : F) else 0)
        = (fun T : {T // T ∈ lowDegMonomials n S.card} => sqfEval F T.1) := by
    funext T x
    exact (sqfEval_eq_monoAND T.1 x).symm
  rw [hgen]
  have hfun : (fun x : Fin n → Bool => boolToF (F := F) (orFieldBool S x))
      = (fun x : Fin n → Bool => eval (fun i => boolToField F (x i)) (orFieldPoly (F := F) S)) := by
    funext x
    exact (orField_exact_eval x S).symm
  rw [hfun]
  exact eval_mem_lowDegSpan_K F S.card (orFieldPoly S) (orFieldPoly_totalDegree_le S)

end PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.orField_exact_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.orField_mem_monoAND_span
