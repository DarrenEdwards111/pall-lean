import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OrFieldExact
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SpanMulField

/-!
# A bounded-fan-in depth-2 circuit (`AND` of `OR`-gates) lies in the monomial-`AND` span over `F_{p^k}`

The depth-2 base case of the BT normal form over the prime-power field, assembled end to end from the gate
representations and the composition law:

* each `OR`-gate over `Sⱼ` lies in the degree-`≤|Sⱼ|` monomial-`AND` span (`orField_mem_sqfSpan`);
* a finite `AND` of them lies in the span with degrees summing (`sqf_prod_mem_span`).

So an `AND` of `OR`-gates (a bounded-fan-in CNF-like circuit) over `F_{p^k}` lies in the degree-`≤ ∑|Sⱼ|`
monomial-`AND` span — `andOfOrs_mem_sqfSpan`.  This is a whole (depth-2) circuit, not a single gate, exactly in the
`SYM∘AND` bottom layer.  Still bounded fan-in; the *exact unbounded-`MOD`* depth collapse remains the composite-`MOD`
barrier.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer4 (boolToField eval_mem_lowDegSpan_K)

variable {n : ℕ} {F : Type*} [Field F]

/-- **The `OR`-gate lies in the `sqfGens` span (proved).**  Restatement of `orField_mem_monoAND_span` with the
`sqfEval` generators (`sqfGens`), so it composes with `sqf_prod_mem_span`. -/
theorem orField_mem_sqfSpan (S : Finset (Fin n)) :
    (fun x : Fin n → Bool => boolToF (F := F) (orFieldBool S x))
      ∈ Submodule.span F (sqfGens F n S.card) := by
  have hfun : (fun x : Fin n → Bool => boolToF (F := F) (orFieldBool S x))
      = (fun x : Fin n → Bool => eval (fun i => boolToField F (x i)) (orFieldPoly (F := F) S)) := by
    funext x
    exact (orField_exact_eval x S).symm
  rw [hfun]
  unfold sqfGens
  exact eval_mem_lowDegSpan_K F S.card (orFieldPoly S) (orFieldPoly_totalDegree_le S)

/-- **A bounded-fan-in `AND` of `OR`-gates lies in the degree-`≤ ∑|Sⱼ|` monomial-`AND` span (proved).**  The
depth-2 base case over `F_{p^k}`, assembled from `orField_mem_sqfSpan` and `sqf_prod_mem_span`. -/
theorem andOfOrs_mem_sqfSpan {ι : Type*} (S : ι → Finset (Fin n)) (s : Finset ι) :
    (fun x : Fin n → Bool => ∏ j ∈ s, boolToF (F := F) (orFieldBool (S j) x))
      ∈ Submodule.span F (sqfGens F n (∑ j ∈ s, (S j).card)) := by
  have heq : (fun x : Fin n → Bool => ∏ j ∈ s, boolToF (F := F) (orFieldBool (S j) x))
      = ∏ j ∈ s, (fun x : Fin n → Bool => boolToF (F := F) (orFieldBool (S j) x)) := by
    funext x
    rw [Finset.prod_apply]
  rw [heq]
  exact sqf_prod_mem_span (fun j => fun x => boolToF (F := F) (orFieldBool (S j) x))
    (fun j => (S j).card) s (fun j _ => orField_mem_sqfSpan (S j))

end PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.andOfOrs_mem_sqfSpan
