import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverAC0pCalibration

/-!
# A dimension-restriction observer: the `finrank` residual span obeys a linear halve/square

The taxonomy check placed the AC⁰[p] degree calibration in class 3 (dimension observers, boundary = `finrank` of
a feature subspace) — distinct from the class-1 restriction observers whose boundary is `log₂` of a residual
count.  This file shows the two worlds *do* connect: the **residual-span dimension** is a `DimObserver` (class 3)
that also carries a restriction structure (class 1), obeying a *linear* halve/square calculus.

For `f : (Fin n → Bool) → K` and a free block `S`, the residual vectors `resVec S f α : (Fin n → Bool) → K` span
a subspace; its dimension is the observer boundary.  The key move: an insert-residual decomposes as

```text
  resVec (insert v S) f β  =  (1 − χ_v) · resVec S f (β[v↦false])  +  χ_v · resVec S f (β[v↦true]),
```

where `χ_v x = [x v]`.  Multiplication by `χ_v` (and `1 − χ_v`) is a **linear map**, so the insert-residual span
sits inside the sum of two images of the `S`-residual span, giving

* `dimResiduals_insert_le` — `dim(insert v S) ≤ 2 · dim(S)` (the *linear* halve, both the halve- and square-side
  in one bound — note the dimension scale needs no `+1` and no squaring);
* `dimResiduals_union_le` — `dim(S ∪ D) ≤ 2^{|D|} · dim(S)` (the partial-block/graceful bound, dimension form).

So the halve/square calculus is not confined to log-scale residual *counts*: it has a clean linear-scale form on
residual-span *dimensions* too, which is exactly the object the AC⁰[p] `DimObserver` measures.  The class-1
calculus and the class-3 dimension boundary meet here.

## Honest scope

A linear-algebra analogue of the restriction calculus, connecting the dimension observer to the restriction
structure.  No separation, no new complexity-class bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DimensionRestrictionObserver

open PallLean.Paper93.DeepMath.PathB.ObserverAC0p

variable {K : Type*} [Field K] {n : ℕ}

/-- The coordinate indicator `χ_v x = [x v]` as an element of the function space. -/
def coordChar (v : Fin n) : (Fin n → Bool) → K := fun x => if x v then 1 else 0

/-- Pointwise multiplication by a fixed function is a linear endomorphism of the function space. -/
def mulBy (g : (Fin n → Bool) → K) : ((Fin n → Bool) → K) →ₗ[K] ((Fin n → Bool) → K) where
  toFun f := g * f
  map_add' f h := by ext x; simp [Pi.mul_apply, Pi.add_apply, mul_add]
  map_smul' c f := by ext x; simp [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The residual vector of `f` on free block `S` at outside setting `α`. -/
def resVec (S : Finset (Fin n)) (f : (Fin n → Bool) → K) (α : Fin n → Bool) :
    (Fin n → Bool) → K :=
  fun x => f (fun i => if i ∈ S then x i else α i)

/-- An insert-residual is the `x v`-frozen `S`-residual. -/
theorem resVec_insert_eq (v : Fin n) (S : Finset (Fin n)) (f : (Fin n → Bool) → K)
    (β : Fin n → Bool) (x : Fin n → Bool) :
    resVec (insert v S) f β x = resVec S f (Function.update β v (x v)) x := by
  simp only [resVec]
  congr 1
  funext i
  by_cases hiv : i = v
  · subst hiv; simp [Finset.mem_insert, Function.update_self]
  · simp only [Function.update_of_ne hiv]
    by_cases hiS : i ∈ S <;> simp [Finset.mem_insert, hiv, hiS]

/-- **The insert-residual decomposition** into a linear combination of two `S`-residuals with the coordinate
indicators as coefficients. -/
theorem resVec_decomp (v : Fin n) (S : Finset (Fin n)) (f : (Fin n → Bool) → K) (β : Fin n → Bool) :
    resVec (insert v S) f β
      = mulBy (1 - coordChar v) (resVec S f (Function.update β v false))
        + mulBy (coordChar v) (resVec S f (Function.update β v true)) := by
  funext x
  rw [resVec_insert_eq]
  simp only [mulBy, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.mul_apply, Pi.sub_apply,
    Pi.one_apply, coordChar]
  cases hxv : x v <;> simp

/-- The residual-span subspace: the feature space of the dimension observer. -/
def resSpan (S : Finset (Fin n)) (f : (Fin n → Bool) → K) : Submodule K ((Fin n → Bool) → K) :=
  Submodule.span K (Set.range (resVec S f))

/-- The **dimension-restriction observer** on free block `S`: a `DimObserver` whose feature space is the
residual span. -/
noncomputable def dimResidualObserver (S : Finset (Fin n)) (f : (Fin n → Bool) → K) :
    DimObserver (Fin n → Bool) K where
  feature := resSpan S f

/-- Its boundary: the dimension of the residual span. -/
noncomputable def dimResiduals (S : Finset (Fin n)) (f : (Fin n → Bool) → K) : ℕ :=
  (dimResidualObserver S f).boundary

theorem dimResiduals_eq (S : Finset (Fin n)) (f : (Fin n → Bool) → K) :
    dimResiduals S f = Module.finrank K (resSpan S f) := rfl

/-! ## The linear halve/square calculus -/

/-- **Linear halve.**  Adding a variable to the free block at most *doubles* the residual-span dimension:
`dim(insert v S) ≤ 2 · dim(S)`.  The insert-residuals lie in the sum of two linear images of the `S`-residual
span. -/
theorem dimResiduals_insert_le (v : Fin n) (S : Finset (Fin n)) (f : (Fin n → Bool) → K) :
    dimResiduals (insert v S) f ≤ 2 * dimResiduals S f := by
  haveI : FiniteDimensional K ((Fin n → Bool) → K) := inferInstance
  have hsub : resSpan (insert v S) f
      ≤ (resSpan S f).map (mulBy (1 - coordChar v)) ⊔ (resSpan S f).map (mulBy (coordChar v)) := by
    rw [resSpan, Submodule.span_le]
    rintro _ ⟨β, rfl⟩
    rw [resVec_decomp]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left
        (Submodule.mem_map_of_mem (Submodule.subset_span ⟨Function.update β v false, rfl⟩))
    · exact Submodule.mem_sup_right
        (Submodule.mem_map_of_mem (Submodule.subset_span ⟨Function.update β v true, rfl⟩))
  rw [dimResiduals_eq, dimResiduals_eq, two_mul]
  refine le_trans (Submodule.finrank_mono hsub) ?_
  refine le_trans (Submodule.finrank_add_le_finrank_add_finrank _ _) ?_
  have h1 := Submodule.finrank_map_le (mulBy (1 - coordChar v)) (resSpan S f)
  have h2 := Submodule.finrank_map_le (mulBy (coordChar v)) (resSpan S f)
  omega

/-- **Partial-block / graceful, dimension form.**  Adding a set `D` to the free block grows the residual-span
dimension by at most `2^{|D|}`. -/
theorem dimResiduals_union_le (S D : Finset (Fin n)) (f : (Fin n → Bool) → K) :
    dimResiduals (S ∪ D) f ≤ 2 ^ D.card * dimResiduals S f := by
  classical
  induction D using Finset.induction with
  | empty => simp
  | @insert v D hv ih =>
      rw [Finset.union_insert, Finset.card_insert_of_notMem hv]
      calc dimResiduals (insert v (S ∪ D)) f
          ≤ 2 * dimResiduals (S ∪ D) f := dimResiduals_insert_le v (S ∪ D) f
        _ ≤ 2 * (2 ^ D.card * dimResiduals S f) := by omega
        _ = 2 ^ (D.card + 1) * dimResiduals S f := by rw [pow_succ]; ring

end PallLean.Paper93.DeepMath.PathB.DimensionRestrictionObserver

#print axioms PallLean.Paper93.DeepMath.PathB.DimensionRestrictionObserver.dimResiduals_insert_le
#print axioms PallLean.Paper93.DeepMath.PathB.DimensionRestrictionObserver.dimResiduals_union_le
