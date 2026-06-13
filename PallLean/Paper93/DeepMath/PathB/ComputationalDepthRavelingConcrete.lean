import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSequenceBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTimeBoundaryPrinciple

/-!
# `raveling` for a concrete restricted `K` — proved

The raveling wedge needs `raveling : lowAction o → inK o` — every low‑action observer falls into a beatable
separator class `K`.  This was an *assumed* premise (the catch being that `K` capturing all of `P` is the wall).
Here it is **proved** for the concrete `K = {effective dimension < r}` (decision alphabet smaller than the
residual dimension).

The genuine content is the **action ⇒ dimension** step: an observer's *dynamical* action
`action B T = ∑_{τ<T} 2^{B τ}` (the time‑integrated boundary capacity) bounds the *structural* dimension of its
decision — because a single layer's capacity `2^{B τ}` is one summand of the action, so the final‑layer
decision alphabet (`≤ 2^{B (T-1)}`) is `≤ action`.  Hence `action < 2^r ⇒` decision alphabet `< 2^r =` in `K`.

## Proved (clean axioms, no `sorry`)

* `raveling_lowAction` — **raveling for `K`**: a low‑action observer (decision alphabet `≤ 2^{B (T-1)}`,
  `action B T < 2^r`) has effective dimension `< r`, i.e. lies in `K = InK · r`.
* `boundedDim_noSeparator` — **noSeparator for `K`**: any observer in `K` (alphabet `< 2^r`) carries debt
  `≥ 2^r − |alphabet| > 0` against a surjective dimension‑`r` residual, so it is not a separator
  (`residual_view_card_forces_debt`).
* `lowAction_no_separator` — the composition (the wedge for this `K`): **no low‑action observer separates the
  dimension‑`r` residual.**

## Honest scope — and exactly where `P ≠ NP` hides

This is `raveling` + `noSeparator` for one concrete, genuinely beatable `K`: bounded effective dimension.  The
action→dimension bound is real and proved.  But `K` here captures only observers whose decision alphabet is
below `2^r` — **not** every polynomial‑time observer: a poly‑*space* decider may keep a full‑dimension
(`≈ 2^n`) decision view (the brute‑force / high‑boundary escape, `hypercube_brute_force_escape`), so `raveling`
does **not** extend to all of `P`.  Making `raveling` capture every `P` observer is exactly the
`P ≠ NP`‑strength step — proved here for the restricted `K`, open (and false in the naïve model) for all of `P`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RavelingConcrete

open PallLean.Paper93.DeepMath.PathB.CrossingSequenceBridge
open PallLean.Paper93.DeepMath.PathB.TimeBoundaryPrinciple
open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The concrete separator class `K`: observers whose decision alphabet has effective dimension `< r`
(fewer than `2^r` distinguishable decision states). -/
def InK (S : Type*) [Fintype S] (r : ℕ) : Prop := Fintype.card S < 2 ^ r

/-- **raveling for `K` (proved).**  A low‑action observer lands in `K`.  Its decision alphabet is bounded by the
final layer's boundary capacity (`≤ 2^{B (T-1)}`), and that single layer's capacity is one summand of the
action, so `≤ action B T`.  Hence `action B T < 2^r ⇒ |alphabet| < 2^r`, i.e. effective dimension `< r`. -/
theorem raveling_lowAction {S : Type*} [Fintype S] (B : ℕ → ℕ) (T r : ℕ) (hT : 0 < T)
    (hdim : Fintype.card S ≤ 2 ^ B (T - 1)) (haction : action B T < 2 ^ r) :
    InK S r := by
  have hle : 2 ^ B (T - 1) ≤ action B T := by
    unfold action
    refine Finset.single_le_sum (f := fun τ => 2 ^ B τ) (fun _ _ => Nat.zero_le _) ?_
    rw [Finset.mem_range]; omega
  unfold InK
  omega

/-- **noSeparator for `K` (proved).**  An observer in `K` (decision alphabet `< 2^r`) cannot separate the `2^r`
classes of a surjective residual: it carries debt `≥ 2^r − |alphabet| > 0`. -/
theorem boundedDim_noSeparator {S : Type*} [Fintype S] [DecidableEq S] {r : ℕ}
    (hK : InK S r) (residual : C → Fin (2 ^ r)) (hsurj : Function.Surjective residual) (view : C → S) :
    debtCount (residualFooling residual) view ≠ 0 := by
  have h := residual_view_card_forces_debt residual hsurj view
  unfold InK at hK
  omega

/-- **The wedge for this `K` (proved).**  Composing `raveling_lowAction` with `boundedDim_noSeparator`: no
low‑action observer separates the dimension‑`r` residual — it always carries positive debt. -/
theorem lowAction_no_separator {S : Type*} [Fintype S] [DecidableEq S] (B : ℕ → ℕ) (T r : ℕ) (hT : 0 < T)
    (hdim : Fintype.card S ≤ 2 ^ B (T - 1)) (haction : action B T < 2 ^ r)
    (residual : C → Fin (2 ^ r)) (hsurj : Function.Surjective residual) (view : C → S) :
    debtCount (residualFooling residual) view ≠ 0 :=
  boundedDim_noSeparator (raveling_lowAction B T r hT hdim haction) residual hsurj view

end PallLean.Paper93.DeepMath.PathB.RavelingConcrete

#print axioms PallLean.Paper93.DeepMath.PathB.RavelingConcrete.raveling_lowAction
#print axioms PallLean.Paper93.DeepMath.PathB.RavelingConcrete.lowAction_no_separator
