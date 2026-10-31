import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundaryDebt

/-!
# Step 4 (the debt mechanism): a fooling set forces debt `≥ K − 2^B` (proved)

The observer-time framework left **step 4** open: SAT-like geometry creates super-log total debt.  Proving it
for *general SAT under every trajectory* is the open quantifier (`P ≠ NP`) — not here.  But its **mechanism**
is provable, and is the expander-amplified content: a **fooling set** of `K` pairwise-must-separate
continuations, seen by a **boundary-`B`** observer (`≤ 2^B` states), forces debt

```
debt  ≥  K − 2^B.
```

The expander *amplifies* this — it provides a fooling set of size `K = 2^{Ω(n)}` (many pairwise-distinguishable
witness branches) — so for any **low-boundary** observer (`B = O(log n)`, `2^B = poly`) the debt is
`≥ 2^{Ω(n)} − poly` = **super-log**.  This is step 4, proved in the low-boundary regime.

## Proved (clean axioms, no `sorry`)

* `foolingSet_forces_debt` — for a fooling set `P` (`∀ x≠y ∈ P, (x,y) ∈ F`) and a view into `Fin m`,
  `P.card − m ≤ debtCount F view`.  (At most `m` elements can be alone in their states; the other `≥ K−m`
  each form a merged must-separate pair.)
* `boundary_debt_lower_bound` — with `m = 2^B`: `K − 2^B ≤ debt` for a boundary-`B` observer.
* `lowBoundary_superlog_debt` — if `K` exceeds the boundary capacity by `L` (`2^B + L ≤ K`), debt `≥ L`: the
  expander's `K = 2^{Ω(n)}` against `2^B = poly` gives super-log debt.

## Honest scope — what this is and is not

This proves the **debt mechanism**: a large fooling set forces large debt **for a fixed low-boundary view**.
Combined with the conservation (`ObserverTimeDebt.correct_needs_action`, `S_obs ≥` initial debt), a correct
*low-initial-boundary* observer must spend action `≥ K − 2^{B₀}` = super-log.  What remains **open** is the
*all-trajectories* closure: an observer may *raise* its boundary over observer time (paying action), and
ruling out *every* low-action trajectory for SAT is exactly the open all-decompositions quantifier.  So step
4's mechanism is proved and the expander amplification is realized (large `K` ⇒ large debt at low boundary);
the residual is the min-over-trajectories, named not faked.  `P ≠ NP` is not touched.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators

variable {X : Type*} [DecidableEq X]

/-- **A fooling set forces debt `≥ K − m` (proved).**  If `P` is a fooling set (every distinct pair is a
must-separate pair of `F`) and the observer's view lands in `Fin m` (`≤ m` boundary states), then the debt is
at least `|P| − m`: at most `m` elements can be alone in their states, and each of the other `≥ |P|−m` forms a
merged must-separate pair. -/
theorem foolingSet_forces_debt {m : ℕ} (P : Finset X) (view : X → Fin m) (F : Finset (X × X))
    (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F) :
    P.card - m ≤ debtCount F view := by
  classical
  set A := P.filter (fun x => ∀ y ∈ P, y ≠ x → view y ≠ view x) with hA
  -- `view` is injective on the "alone" elements `A`
  have hAinj : Set.InjOn view (A : Set X) := by
    intro x hx y hy hxy
    by_contra hne
    rw [Finset.mem_coe, hA, Finset.mem_filter] at hx hy
    exact hx.2 y hy.1 (Ne.symm hne) hxy.symm
  have hAcard : A.card ≤ m := by
    calc A.card = (A.image view).card := (Finset.card_image_of_injOn hAinj).symm
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ _
      _ = m := by simp
  -- every non-alone element is the first coordinate of a merged must-separate pair
  have hsub : P \ A ⊆ (F.filter (fun p => view p.1 = view p.2)).image Prod.fst := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxP, hxnA⟩ := hx
    rw [hA, Finset.mem_filter] at hxnA
    push_neg at hxnA
    obtain ⟨y, hyP, hyx, hyv⟩ := hxnA hxP
    exact Finset.mem_image.mpr
      ⟨(x, y), Finset.mem_filter.mpr ⟨hfool x hxP y hyP (Ne.symm hyx), hyv.symm⟩, rfl⟩
  have hdebt : (P \ A).card ≤ debtCount F view := by
    calc (P \ A).card
        ≤ ((F.filter (fun p => view p.1 = view p.2)).image Prod.fst).card :=
          Finset.card_le_card hsub
      _ ≤ (F.filter (fun p => view p.1 = view p.2)).card := Finset.card_image_le
      _ = debtCount F view := rfl
  have hPA : P.card ≤ (P \ A).card + A.card := by
    rw [Finset.card_sdiff_add_card]
    exact Finset.card_le_card Finset.subset_union_left
  omega

/-- **Boundary-`B` form.**  A boundary-`B` observer (view into `Fin (2^B)`) of a fooling set `P` carries debt
`≥ |P| − 2^B`. -/
theorem boundary_debt_lower_bound {B : ℕ} (P : Finset X) (view : X → Fin (2 ^ B))
    (F : Finset (X × X)) (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F) :
    P.card - 2 ^ B ≤ debtCount F view :=
  foolingSet_forces_debt P view F hfool

/-- **Low-boundary ⇒ super-log debt (expander-amplified).**  If the fooling set exceeds the boundary capacity
by `L` (`2^B + L ≤ |P|`), the debt is `≥ L`.  With the expander's `|P| = 2^{Ω(n)}` and `2^B = poly`, this is
super-logarithmic. -/
theorem lowBoundary_superlog_debt {B L : ℕ} (P : Finset X) (view : X → Fin (2 ^ B))
    (F : Finset (X × X)) (hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ F)
    (hbig : 2 ^ B + L ≤ P.card) :
    L ≤ debtCount F view := by
  have h := boundary_debt_lower_bound P view F hfool
  omega

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.foolingSet_forces_debt
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.lowBoundary_superlog_debt
