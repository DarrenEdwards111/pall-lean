import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFoolingDebt

/-!
# Do NP-complete reductions preserve observer-time debt? — the preservable half, and the two gaps

The proposed separation path is:
`3SAT/Label-Cover decision-hardness ⇒ expander residual non-collapse ⇒ decision-holonomy ⇒ P ≠ NP`,
with the first implication ("hardness preserved as debt") the "new maths".  This file formalizes **exactly the
part that is provable** — and proves, by locating where it stops, that the remaining part is the open core, not
a stepping stone.

**What is provable:** a *decomposition-respecting* reduction `r` (one that maps must-separate source pairs to
must-separate target pairs — hypothesis `hred`) carries a **fooling set to a fooling set**: distinguishability
is preserved, so the target's distinguishability-debt is `≥` the source's.

**Why that is not enough (the two gaps):**
1. `hred` is **non-trivial.** A general reduction may scramble the input's decomposition geometry; only
   *structure/decomposition-respecting* reductions preserve the must-separate relation.  Whether the NP-complete
   reductions one would use are decomposition-respecting is itself a real question, here an explicit hypothesis.
2. Even with `hred`, this preserves **distinguishability-debt** — the *proof/space* kind.  By the barrier
   `tseitin_unsat_of_odd_charge` (Tseitin: huge fooling set, yet decision-easy by parity), a large fooling set
   does **not** imply decision-hardness.  So transferring the fooling set transfers the *wrong* kind of debt.
   Transferring *decision*-debt is `decision-holonomy ≡ P ≠ NP`, still open.

## Proved (clean axioms, no `sorry`)

* `reduction_preserves_fooling` — if `r` is injective on `P` and `hred` holds, then `r '' P` is a fooling set
  for the target relation `F_B`.
* `reduction_transfers_debt` — consequently every boundary-`B` observer of the target carries
  distinguishability-debt `≥ |P| − 2^B` (the source's fooling debt transfers up).

## Honest conclusion

Reductions preserve the **distinguishability/proof** debt (under the explicit decomposition-respecting
condition).  They do **not**, by this mechanism, transfer **decision** hardness — that is precisely the
proof→decision gap the barriers establish.  So the path's first implication, made precise, splits into a
provable half (here) and the open half (decision-debt preservation = decision-holonomy = `P ≠ NP`).  Using a
genuinely decision-hard base family (3SAT, Label-Cover) is a better *candidate* than a toy gadget — it lacks
Tseitin's Gaussian shortcut — but its decision-hardness is itself `P ≠ NP`-conditional, so the route cannot
bootstrap an *unconditional* separation; it relocates, it does not close.  No `P ≠ NP` step — an honest map of
what reduction-preservation buys.
-/

namespace PallLean.Paper93.DeepMath.PathB.ReductionFooling

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

/-- **A decomposition-respecting reduction preserves fooling sets (proved).**  If `r` is injective on the
fooling set `P` and maps must-separate source pairs to must-separate target pairs (`hred`), then the image
`r '' P` is a fooling set for the target relation `FB`. -/
theorem reduction_preserves_fooling {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (FA : Finset (X × X)) (FB : Finset (Y × Y)) (r : X → Y) (P : Finset X)
    (hr : Set.InjOn r P)
    (hred : ∀ x ∈ P, ∀ x' ∈ P, (x, x') ∈ FA → (r x, r x') ∈ FB)
    (hfoolA : ∀ x ∈ P, ∀ x' ∈ P, x ≠ x' → (x, x') ∈ FA) :
    ∀ y ∈ P.image r, ∀ y' ∈ P.image r, y ≠ y' → (y, y') ∈ FB := by
  intro y hy y' hy' hyy
  obtain ⟨x, hxP, hxy⟩ := Finset.mem_image.mp hy
  obtain ⟨x', hx'P, hx'y⟩ := Finset.mem_image.mp hy'
  have hxx' : x ≠ x' := by
    intro h; apply hyy; rw [← hxy, ← hx'y, h]
  rw [← hxy, ← hx'y]
  exact hred x hxP x' hx'P (hfoolA x hxP x' hx'P hxx')

/-- **Distinguishability-debt transfers up a reduction (proved).**  Under the same hypotheses, every
boundary-`B` observer of the target carries debt `≥ |P| − 2^B`: the source's fooling debt is inherited.
(`|r '' P| = |P|` by injectivity, then `foolingSet_forces_debt`.) -/
theorem reduction_transfers_debt {X Y : Type*} [DecidableEq X] [DecidableEq Y] {B : ℕ}
    (FA : Finset (X × X)) (FB : Finset (Y × Y)) (r : X → Y) (P : Finset X)
    (hr : Set.InjOn r P)
    (hred : ∀ x ∈ P, ∀ x' ∈ P, (x, x') ∈ FA → (r x, r x') ∈ FB)
    (hfoolA : ∀ x ∈ P, ∀ x' ∈ P, x ≠ x' → (x, x') ∈ FA)
    (view : Y → Fin (2 ^ B)) :
    P.card - 2 ^ B ≤ debtCount FB view := by
  have hfoolB := reduction_preserves_fooling FA FB r P hr hred hfoolA
  have hcard : (P.image r).card = P.card := Finset.card_image_of_injOn hr
  have h := foolingSet_forces_debt (P.image r) view FB hfoolB
  rw [hcard] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.ReductionFooling

#print axioms PallLean.Paper93.DeepMath.PathB.ReductionFooling.reduction_preserves_fooling
#print axioms PallLean.Paper93.DeepMath.PathB.ReductionFooling.reduction_transfers_debt
