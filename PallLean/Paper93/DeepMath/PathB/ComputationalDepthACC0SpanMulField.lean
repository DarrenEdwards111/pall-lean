import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModFieldSpan

/-!
# The monomial-`AND` span is closed under product (the `AND`-composition / depth law) over any field

The degree-`≤D` monomial-`AND` span over a field `F` is closed under pointwise product, with degrees adding:

```
span(deg ≤ D) · span(deg ≤ E)  ⊆  span(deg ≤ D + E).
```

Because squarefree monomials multiply by *union* on the `{0,1}` cube (`sqfEval S · sqfEval T = sqfEval (S ∪ T)`,
idempotence), the product of a degree-`≤D` and a degree-`≤E` span element is a degree-`≤(D+E)` span element.  This
is the `AND`-gate composition law for the `SYM∘AND` bottom layer over `F_{p^k}`: an `AND` of two sub-circuits, each
represented in its degree-bounded monomial-`AND` span, lands in the span with degree the sum — the multiplicative
half of the depth recurrence (the additive half being the span's own closure under `+`).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`; it is the bounded-fan-in composition step (the *exact* unbounded-`MOD` depth collapse
remains the barrier).
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer4 (sqfEval sqfEval_mul sqfEval_empty)
open PallLean.Paper93.DeepMath.PathB.Layer3 (lowDegMonomials)

variable {n : ℕ} {F : Type*} [Field F]

/-- The degree-`≤D` squarefree (monomial-`AND`) generator set over `F`. -/
def sqfGens (F : Type*) [Field F] (n D : ℕ) : Set ((Fin n → Bool) → F) :=
  Set.range (fun S : {S // S ∈ lowDegMonomials n D} => sqfEval F S.1)

/-- **The monomial-`AND` span is closed under product, degrees adding (proved).**
`span(deg ≤ D) · span(deg ≤ E) ≤ span(deg ≤ D + E)`. -/
theorem sqfSpan_mul_le (D E : ℕ) :
    Submodule.span F (sqfGens F n D) * Submodule.span F (sqfGens F n E)
      ≤ Submodule.span F (sqfGens F n (D + E)) := by
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro x ⟨y, ⟨⟨S, hS⟩, rfl⟩, z, ⟨⟨T, hT⟩, rfl⟩, rfl⟩
  simp only [sqfEval_mul]
  apply Submodule.subset_span
  refine ⟨⟨S ∪ T, ?_⟩, rfl⟩
  simp only [lowDegMonomials, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
    true_and] at hS hT ⊢
  exact le_trans (Finset.card_union_le S T) (Nat.add_le_add hS hT)

/-- **`AND`-composition (proved).**  The pointwise product of a degree-`≤D` and a degree-`≤E` monomial-`AND` span
element is a degree-`≤(D+E)` span element — the multiplicative half of the depth recurrence. -/
theorem sqf_mul_mem_span {D E : ℕ} {f g : (Fin n → Bool) → F}
    (hf : f ∈ Submodule.span F (sqfGens F n D)) (hg : g ∈ Submodule.span F (sqfGens F n E)) :
    f * g ∈ Submodule.span F (sqfGens F n (D + E)) :=
  sqfSpan_mul_le D E (Submodule.mul_mem_mul hf hg)

/-- **The constant `1` is a degree-`0` span element (proved).**  `1 = sqfEval ∅`, and `∅` is a degree-`≤0`
monomial. -/
theorem one_mem_sqfSpan : (1 : (Fin n → Bool) → F) ∈ Submodule.span F (sqfGens F n 0) := by
  rw [← sqfEval_empty F]
  apply Submodule.subset_span
  refine ⟨⟨∅, ?_⟩, rfl⟩
  simp [lowDegMonomials]

/-- **Bounded-fan-in `AND` composition (proved).**  A finite product of monomial-`AND` span elements, each of
degree `≤ D i`, lies in the span of degree `≤ ∑ D i`: `∏_{i∈s} gᵢ ∈ span(deg ≤ ∑_{i∈s} D i)`.  This is the `AND`
gate of arbitrary (bounded) fan-in for the `SYM∘AND` bottom layer over `F_{p^k}` — the depth recurrence's
multiplicative step, with degree summing over the children. -/
theorem sqf_prod_mem_span {ι : Type*} (g : ι → (Fin n → Bool) → F) (D : ι → ℕ) (s : Finset ι)
    (hg : ∀ i ∈ s, g i ∈ Submodule.span F (sqfGens F n (D i))) :
    (∏ i ∈ s, g i) ∈ Submodule.span F (sqfGens F n (∑ i ∈ s, D i)) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one_mem_sqfSpan
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact sqf_mul_mem_span (hg a (Finset.mem_insert_self a s))
      (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

end PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.sqfSpan_mul_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.sqf_mul_mem_span
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.sqf_prod_mem_span
