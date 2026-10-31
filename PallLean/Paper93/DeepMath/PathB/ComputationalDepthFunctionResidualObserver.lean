import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictionObserverCalculus

/-!
# Any function's residual count is a restriction observer — and the rectangle-cover check

This resolves the check "is the communication rectangle calibration a `RestrictionObserver`?" and, in doing so,
generalizes the calculus.

## The generalization

`blockResidualsObserver` restricted the halve/square residual-count lemmas to a `BFormula`.  But the proofs never
use that the function is a formula — only that it is a Boolean function.  `funResiduals S f` is the residual count
of an **arbitrary** `f : (Fin n → Bool) → Bool` on the free block `S`, and it satisfies the halve and square
axioms verbatim, so `functionResidualObserver f` is a `RestrictionObserver`.  `blockResidualsObserver F` is the
special case `functionResidualObserver (BFormula.eval F)`.

## The rectangle-cover check — result: NO (with a precise reason)

`ObserverRectangle.rectangleObserverBoundary C = Nat.log 2 C.cover.length` is indexed by the **cover `C`** — a
protocol witness — not by a variable subset.  There is no `count : Finset ι → ℕ` and no "add a variable to the
free block" operation, so it is **not** a `RestrictionObserver`; it is a witness-indexed *fooling* observer, in
the same class as `minProofSpaceBoundary` (sInf over refutations).  (This corrects the earlier guess that it would
be one.)

Where the restriction structure *does* live in communication: the underlying matrix's **distinct-row count** —
the residuals of the matrix's row function over column-subsets — is a `functionResidualObserver`, and it
lower-bounds the cover cost via fooling (`#rectangles ≥ #distinct behaviors`).  So the restriction calculus
governs the matrix-residual quantity, not the cover-cost boundary the calibration formalizes.

Net: the halve/square calculus is family-independent across **residual/subfunction** observers of any Boolean
function (formulas and communication matrices alike), but the cover-cost / proof-space boundaries are a distinct
(fooling) class it does not touch.

## Honest scope

A generalization of the restriction-observer instance and a delineation of the rectangle-cover boundary.  No
separation, no new complexity-class bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.FunctionResidualObserver

open PallLean.Paper93.DeepMath.PathB.RestrictionObserverCalculus

/-- The residuals of an arbitrary Boolean function `f` on a free block `S`. -/
noncomputable def funResiduals {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) :
    Finset ((Fin n → Bool) → Bool) := by
  classical
  exact Finset.univ.image
    (fun (α : Fin n → Bool) => fun x => f (fun i => if i ∈ S then x i else α i))

theorem mem_funRes {n : ℕ} {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    {g : (Fin n → Bool) → Bool} :
    g ∈ funResiduals S f ↔
      ∃ α : Fin n → Bool, (fun x => f (fun i => if i ∈ S then x i else α i)) = g := by
  classical
  constructor
  · intro h
    rw [funResiduals] at h
    obtain ⟨α, -, hα⟩ := Finset.mem_image.mp h
    exact ⟨α, hα⟩
  · rintro ⟨α, rfl⟩
    rw [funResiduals]
    exact Finset.mem_image.mpr ⟨α, Finset.mem_univ _, rfl⟩

/-- **Halve axiom for an arbitrary function.** -/
theorem funResiduals_card_le_two_mul_insert {n : ℕ} (v : Fin n) (S : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) :
    (funResiduals S f).card ≤ 2 * (funResiduals (insert v S) f).card := by
  classical
  by_cases hv : v ∈ S
  · rw [Finset.insert_eq_self.mpr hv]; omega
  · have hsub : funResiduals S f ⊆
        (funResiduals (insert v S) f ×ˢ (Finset.univ : Finset Bool)).image
          (fun p => (fun x : Fin n → Bool => p.1 (Function.update x v p.2))) := by
      intro g hg
      obtain ⟨α, rfl⟩ := mem_funRes.mp hg
      refine Finset.mem_image.mpr
        ⟨(fun x => f (fun i => if i ∈ insert v S then x i else α i), α v),
         Finset.mk_mem_product (mem_funRes.mpr ⟨α, rfl⟩) (Finset.mem_univ _), ?_⟩
      funext x
      show f (fun i => if i ∈ insert v S then (Function.update x v (α v)) i else α i)
         = f (fun i => if i ∈ S then x i else α i)
      congr 1
      funext i
      by_cases hiv : i = v
      · subst hiv
        rw [if_pos (Finset.mem_insert_self i S), Function.update_self, if_neg hv]
      · simp only [Function.update_of_ne hiv]
        by_cases hiS : i ∈ S
        · rw [if_pos (Finset.mem_insert_of_mem hiS), if_pos hiS]
        · rw [if_neg (fun h => (Finset.mem_insert.mp h).elim hiv hiS), if_neg hiS]
    calc (funResiduals S f).card
        ≤ ((funResiduals (insert v S) f ×ˢ (Finset.univ : Finset Bool)).image
            (fun p => (fun x : Fin n → Bool => p.1 (Function.update x v p.2)))).card :=
          Finset.card_le_card hsub
      _ ≤ (funResiduals (insert v S) f ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
      _ = 2 * (funResiduals (insert v S) f).card := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]; ring

/-- **Square axiom for an arbitrary function.** -/
theorem funResiduals_card_insert_le_sq {n : ℕ} (v : Fin n) (S : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) :
    (funResiduals (insert v S) f).card ≤ (funResiduals S f).card ^ 2 := by
  classical
  by_cases hv : v ∈ S
  · rw [Finset.insert_eq_self.mpr hv, sq]
    have hne : (funResiduals S f).Nonempty := by
      rw [funResiduals]; exact Finset.univ_nonempty.image _
    have h1 : 1 ≤ (funResiduals S f).card := Finset.card_pos.mpr hne
    nlinarith [h1]
  · have slice_eq : ∀ (c : Bool) (β : Fin n → Bool),
        (fun x : Fin n → Bool => f (fun i => if i ∈ insert v S then (Function.update x v c) i else β i))
          = (fun x : Fin n → Bool => f (fun i => if i ∈ S then x i else (Function.update β v c) i)) := by
      intro c β
      funext x
      congr 1
      funext i
      by_cases hiv : i = v
      · subst hiv
        rw [if_pos (Finset.mem_insert_self i S), Function.update_self, if_neg hv, Function.update_self]
      · simp only [Function.update_of_ne hiv]
        by_cases hiS : i ∈ S
        · rw [if_pos (Finset.mem_insert_of_mem hiS), if_pos hiS]
        · rw [if_neg (fun h => (Finset.mem_insert.mp h).elim hiv hiS), if_neg hiS]
    have hcard : (funResiduals (insert v S) f).card
        ≤ (funResiduals S f ×ˢ funResiduals S f).card := by
      apply Finset.card_le_card_of_injOn
        (fun g => (fun x : Fin n → Bool => g (Function.update x v false),
                   fun x : Fin n → Bool => g (Function.update x v true)))
      · intro g hg
        obtain ⟨β, rfl⟩ := mem_funRes.mp hg
        exact Finset.mk_mem_product
          (mem_funRes.mpr ⟨Function.update β v false, (slice_eq false β).symm⟩)
          (mem_funRes.mpr ⟨Function.update β v true, (slice_eq true β).symm⟩)
      · intro g _ g' _ heq
        simp only [Prod.mk.injEq] at heq
        obtain ⟨h0, h1⟩ := heq
        funext x
        cases hb : x v
        · have hx : Function.update x v false = x := by
            funext j; by_cases hjv : j = v
            · subst hjv; rw [Function.update_self, hb]
            · rw [Function.update_of_ne hjv]
          calc g x = g (Function.update x v false) := by rw [hx]
            _ = g' (Function.update x v false) := congrFun h0 x
            _ = g' x := by rw [hx]
        · have hx : Function.update x v true = x := by
            funext j; by_cases hjv : j = v
            · subst hjv; rw [Function.update_self, hb]
            · rw [Function.update_of_ne hjv]
          calc g x = g (Function.update x v true) := by rw [hx]
            _ = g' (Function.update x v true) := congrFun h1 x
            _ = g' x := by rw [hx]
    calc (funResiduals (insert v S) f).card
        ≤ (funResiduals S f ×ˢ funResiduals S f).card := hcard
      _ = (funResiduals S f).card ^ 2 := by rw [Finset.card_product, sq]

/-- **Every Boolean function's residual count is a restriction observer.**  This is the communication
matrix-residual (distinct-row) observer: the residuals over column-subsets satisfy the halve/square calculus. -/
noncomputable def functionResidualObserver {n : ℕ} (f : (Fin n → Bool) → Bool) :
    RestrictionObserver (Fin n) where
  count S := (funResiduals S f).card
  count_pos S := by
    apply Finset.card_pos.mpr
    rw [funResiduals]; exact Finset.univ_nonempty.image _
  count_le_two_mul_insert v S := funResiduals_card_le_two_mul_insert v S f
  count_insert_le_sq v S := funResiduals_card_insert_le_sq v S f

/-- The abstract calculus applies to any function's residuals: adding a set `D` of variables to the free block
changes the residual boundary by the halve/square bounds. -/
theorem functionResidual_calculus {n : ℕ} (f : (Fin n → Bool) → Bool) (S D : Finset (Fin n)) :
    (functionResidualObserver f).boundary S
        ≤ (functionResidualObserver f).boundary (S ∪ D) + D.card ∧
      (functionResidualObserver f).boundary (S ∪ D) + 1
        ≤ 2 ^ D.card * ((functionResidualObserver f).boundary S + 1) :=
  ⟨(functionResidualObserver f).boundary_le_union_add_card S D,
   (functionResidualObserver f).boundary_union_le S D⟩

end PallLean.Paper93.DeepMath.PathB.FunctionResidualObserver

#print axioms PallLean.Paper93.DeepMath.PathB.FunctionResidualObserver.funResiduals_card_le_two_mul_insert
#print axioms PallLean.Paper93.DeepMath.PathB.FunctionResidualObserver.funResiduals_card_insert_le_sq
#print axioms PallLean.Paper93.DeepMath.PathB.FunctionResidualObserver.functionResidual_calculus
