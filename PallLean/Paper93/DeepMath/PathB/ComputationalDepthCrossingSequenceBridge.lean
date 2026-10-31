import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderNoHiding
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDebtGaugeInvariance

/-!
# The restricted bridge for crossing‑sequence `K` — PROVED (non‑circular, by counting)

The global bridge `polyTime ⇒ low SPDP/dimension` is `P ≠ NP`‑hard.  Here we **prove** the restricted bridge
for the **crossing‑sequence** class `K`: an observer whose view of a continuation is determined by a
*crossing sequence* of width `w` over a state set of size `q`.

The key point — and why this is *not* circular — is that the conclusion follows by **counting**: a width‑`w`
crossing sequence over `q` states takes at most `q^w` values, so the observer can distinguish at most `q^w`
continuations.  No assumption about SPDP rank is made; it is derived from the crossing‑sequence structure.

## Proved (clean axioms, no `sorry`)

* `residual_view_card_forces_debt` — for a residual surjective onto `Fin (2^r)`, **any** view into a finite type
  `S` carries debt `≥ 2^r − |S|`: an observer with `|S|` distinguishable states cannot separate `2^r` residual
  outcomes.  (Generalises `surjective_residual_forces_debt` to an arbitrary finite codomain, via the fooling
  set + `debtCount_relabel_invariant`.)
* `crossingSequence_forces_debt` — the crossing‑sequence instance: a view into `Fin w → Fin q` (a width‑`w`
  crossing sequence over `q` states) carries debt `≥ 2^r − q^w`.
* `crossingSequence_no_separator` — **the restricted bridge**: if `q^w < 2^r` (the crossing width is below the
  residual dimension, `w·log₂ q < r`), the observer carries positive debt — it is **not** a separator.  Low
  crossing‑sequence width provably cannot realize a high‑dimensional separating view.

## Honest scope — restricted, and why it does not reach all of `P`

This discharges `restrictedBridge` (of `…NFrameHypercubeConstraint`) for `K = {crossing‑width‑`w` observers}`:
their effective dimension is `≤ w·log₂ q`, so their "SPDP‑rank reach" is bounded, and they cannot separate a
dimension‑`r` residual once `r > w·log₂ q`.  This is the classical crossing‑sequence lower‑bound model (one‑tape
/ oblivious computation), made into a debt statement — a genuine, non‑circular restricted bridge.

It is **not** the global bridge: `polyTime ⇒ low crossing width` is **false**.  Multi‑tape / RAM machines have
*unbounded* crossing sequences (information need not funnel through a single one‑dimensional cut), so a poly‑time
decider escapes this `K`.  Extending to all of `P` is the `P ≠ NP`‑hard global bridge.  So: the crossing‑sequence
restricted bridge is now a theorem; the global one remains the open wall.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingSequenceBridge

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt
open PallLean.Paper93.DeepMath.PathB.DebtGaugeInvariance

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- **Finite‑codomain debt bound (proved).**  A residual surjective onto `Fin (2^r)` forces any view into a
finite type `S` to carry debt `≥ 2^r − |S|`: with only `|S|` distinguishable states an observer cannot keep
apart `2^r` residual outcomes.  (Generalises `surjective_residual_forces_debt`.) -/
theorem residual_view_card_forces_debt {S : Type*} [Fintype S] [DecidableEq S] {r : ℕ}
    (residual : C → Fin (2 ^ r)) (hsurj : Function.Surjective residual) (view : C → S) :
    2 ^ r - Fintype.card S ≤ debtCount (residualFooling residual) view := by
  classical
  set s := Function.surjInv hsurj with hs
  set P : Finset C := Finset.univ.image s with hP
  have hsinj : Function.Injective s := Function.injective_surjInv hsurj
  have hres : ∀ o, residual (s o) = o := fun o => Function.surjInv_eq hsurj o
  have hPcard : P.card = 2 ^ r := by
    rw [hP, Finset.card_image_of_injective _ hsinj, Finset.card_univ, Fintype.card_fin]
  have hfool : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x, y) ∈ residualFooling residual := by
    intro x hx y hy hxy
    rw [residualFooling, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨ox, _, hox⟩ := Finset.mem_image.mp hx
    obtain ⟨oy, _, hoy⟩ := Finset.mem_image.mp hy
    intro hr
    have hrx : residual x = ox := by rw [← hox]; exact hres ox
    have hry : residual y = oy := by rw [← hoy]; exact hres oy
    have hoo : ox = oy := by rw [← hrx, ← hry]; exact hr
    exact hxy (by rw [← hox, ← hoy]; exact congrArg s hoo)
  set e := Fintype.equivFin S with he
  have h := foolingSet_forces_debt P (fun c => e (view c)) (residualFooling residual) hfool
  rw [hPcard] at h
  rwa [debtCount_relabel_invariant (residualFooling residual) view (⇑e) e.injective] at h

/-- **Crossing‑sequence debt (proved).**  A view determined by a width‑`w` crossing sequence over `q` states
(`view : C → (Fin w → Fin q)`) carries debt `≥ 2^r − q^w` against a dimension‑`r` residual. -/
theorem crossingSequence_forces_debt {r w q : ℕ}
    (residual : C → Fin (2 ^ r)) (hsurj : Function.Surjective residual)
    (view : C → (Fin w → Fin q)) :
    2 ^ r - q ^ w ≤ debtCount (residualFooling residual) view := by
  have h := residual_view_card_forces_debt residual hsurj view
  have hcard : Fintype.card (Fin w → Fin q) = q ^ w := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rwa [hcard] at h

/-- **The restricted bridge for crossing‑sequence `K` (proved).**  If the crossing width is below the residual
dimension (`q^w < 2^r`, i.e. `w·log₂ q < r`), a crossing‑sequence observer carries positive debt — it is **not**
a separator.  Low crossing‑sequence width provably cannot realize a high‑dimensional separating view. -/
theorem crossingSequence_no_separator {r w q : ℕ} (hlt : q ^ w < 2 ^ r)
    (residual : C → Fin (2 ^ r)) (hsurj : Function.Surjective residual)
    (view : C → (Fin w → Fin q)) :
    debtCount (residualFooling residual) view ≠ 0 := by
  have h := crossingSequence_forces_debt residual hsurj view
  omega

end PallLean.Paper93.DeepMath.PathB.CrossingSequenceBridge

#print axioms PallLean.Paper93.DeepMath.PathB.CrossingSequenceBridge.residual_view_card_forces_debt
#print axioms PallLean.Paper93.DeepMath.PathB.CrossingSequenceBridge.crossingSequence_no_separator
