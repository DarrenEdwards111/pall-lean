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

/-- **The generators are monotone in degree (proved).**  `D ≤ E ⇒ sqfGens F n D ⊆ sqfGens F n E`. -/
theorem sqfGens_mono {D E : ℕ} (h : D ≤ E) : sqfGens F n D ⊆ sqfGens F n E := by
  rintro f ⟨⟨S, hS⟩, rfl⟩
  simp only [lowDegMonomials, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
    true_and] at hS
  exact ⟨⟨S, by
    simp only [lowDegMonomials, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    exact le_trans hS h⟩, rfl⟩

/-- **The span is monotone in degree (proved).** -/
theorem sqfSpan_mono {D E : ℕ} (h : D ≤ E) :
    Submodule.span F (sqfGens F n D) ≤ Submodule.span F (sqfGens F n E) :=
  Submodule.span_mono (sqfGens_mono h)

/-- **`1` is a degree-`≤D` span element for any `D` (proved).** -/
theorem one_mem_sqfSpan' (D : ℕ) : (1 : (Fin n → Bool) → F) ∈ Submodule.span F (sqfGens F n D) :=
  sqfSpan_mono (Nat.zero_le D) one_mem_sqfSpan

/-- **Bounded-fan-in `OR` composition (proved).**  By De Morgan, `OR_{i∈s} gᵢ = 1 − ∏_{i∈s}(1 − gᵢ)`; if each
`gᵢ ∈ span(deg ≤ D i)` then `1 − gᵢ ∈ span(deg ≤ D i)` (additive closure), the product is in `span(deg ≤ ∑ D i)`
(`sqf_prod_mem_span`), and so is `1 −` it.  This is the `OR` gate of arbitrary (bounded) fan-in — the disjunctive
step of the depth recurrence, the De Morgan dual of `sqf_prod_mem_span`. -/
theorem sqf_deMorgan_mem_span {ι : Type*} (g : ι → (Fin n → Bool) → F) (D : ι → ℕ) (s : Finset ι)
    (hg : ∀ i ∈ s, g i ∈ Submodule.span F (sqfGens F n (D i))) :
    (1 - ∏ i ∈ s, (1 - g i)) ∈ Submodule.span F (sqfGens F n (∑ i ∈ s, D i)) := by
  have hprod : (∏ i ∈ s, (1 - g i)) ∈ Submodule.span F (sqfGens F n (∑ i ∈ s, D i)) :=
    sqf_prod_mem_span (fun i => 1 - g i) D s
      (fun i hi => Submodule.sub_mem _ (one_mem_sqfSpan' (D i)) (hg i hi))
  exact Submodule.sub_mem _ (one_mem_sqfSpan' (∑ i ∈ s, D i)) hprod

end PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.sqfSpan_mul_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.sqf_mul_mem_span
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.sqf_prod_mem_span
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.sqf_deMorgan_mem_span
