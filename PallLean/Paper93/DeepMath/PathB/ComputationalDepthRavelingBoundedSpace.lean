import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRavelingConcrete

/-!
# Extending `raveling` to bounded‑space `P` observers

`raveling_lowAction` proved raveling for abstractly low‑action observers.  Here we extend it to a concrete,
natural `P`‑subclass: **bounded‑space deciders**.  The key — and the reason this works where a *time* bound
fails — is that a **space bound genuinely bounds the boundary**: a space‑`s` machine has at most `2^s` distinct
configurations, so the information it carries across any cut (its boundary view) takes `≤ 2^s` values.  Hence for
`s < r` its effective dimension is `< r` and it lands in `K`, unable to separate the dimension‑`r` residual.

This is exactly the regime where the time→boundary bridge holds (`subcritical_of_lowspace`): *given a space
bound*, the action is controlled.

## Proved (clean axioms, no `sorry`)

* `boundedSpace_raveling` — **raveling for `SPACE(s)`**: a space‑`s` observer (boundary config type of card
  `≤ 2^s`) with `s < r` lands in `K` (effective dimension `< r`).
* `boundedSpace_no_separator` — hence it cannot separate the dimension‑`r` residual (positive debt).
* `boundedSpaceTime_subcritical` — the dynamical form: a space‑`s`, time‑`≤ Tb` observer has `action < 2^r`
  whenever the space‑time budget `Tb·2^s < 2^r` (reusing `subcritical_of_lowspace`).

## Honest scope — and exactly where it stops

The space→boundary bound is real: bounded‑space deciders provably ravel into `K`.  But this captures only
`SPACE(s)` with `s < r ≈ Ω(n)` (sublinear / sub‑residual‑dimension space) — **not** all of `P`.  A
poly‑*space* decider may use `s = n^k ≫ r` space, giving `2^s ≫ 2^r` boundary states: it keeps a
full‑dimension view and **escapes** `K` (the brute‑force / high‑boundary escape, `hypercube_brute_force_escape`,
which exhibits a correct zero‑debt decider of full boundary `n`).  So `raveling` extends to bounded‑space `P`,
and *no further* — closing the gap to all of `P` is the `P ≠ NP`‑strength step, and is *false* in the naïve
model (high‑space deciders separate freely).
-/

namespace PallLean.Paper93.DeepMath.PathB.RavelingBoundedSpace

open PallLean.Paper93.DeepMath.PathB.RavelingConcrete
open PallLean.Paper93.DeepMath.PathB.CrossingSequenceBridge
open PallLean.Paper93.DeepMath.PathB.TimeBoundaryPrinciple
open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- **raveling for `SPACE(s)` (proved).**  A space‑`s` observer's boundary view ranges over `≤ 2^s`
configurations (a space bound *does* bound the boundary); so for `s < r` its effective dimension is `< r` and it
lands in `K`. -/
theorem boundedSpace_raveling {Cfg : Type*} [Fintype Cfg] {s r : ℕ}
    (hspace : Fintype.card Cfg ≤ 2 ^ s) (hsr : s < r) : InK Cfg r := by
  unfold InK
  exact lt_of_le_of_lt hspace (Nat.pow_lt_pow_right (by norm_num) hsr)

/-- **noSeparator for `SPACE(s)` (proved).**  A space‑`s` observer (`s < r`) cannot separate the `2^r` classes of
a surjective dimension‑`r` residual: it carries debt `≥ 2^r − 2^s > 0`. -/
theorem boundedSpace_no_separator {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg] {s r : ℕ}
    (hspace : Fintype.card Cfg ≤ 2 ^ s) (hsr : s < r)
    (residual : C → Fin (2 ^ r)) (hsurj : Function.Surjective residual) (view : C → Cfg) :
    debtCount (residualFooling residual) view ≠ 0 :=
  boundedDim_noSeparator (boundedSpace_raveling hspace hsr) residual hsurj view

/-- **The dynamical form (proved).**  A space‑`s`, time‑`≤ Tb` observer has subcritical action `< 2^r` whenever
its space‑time budget `Tb·2^s < 2^r` — the cumulative version, reusing `subcritical_of_lowspace`. -/
theorem boundedSpaceTime_subcritical (B : ℕ → ℕ) (T Tb s r : ℕ) (hT : T ≤ Tb) (hsp : ∀ τ, B τ ≤ s)
    (hbudget : Tb * 2 ^ s < 2 ^ r) :
    action B T < 2 ^ r :=
  subcritical_of_lowspace B T Tb s (2 ^ r) hT hsp hbudget

end PallLean.Paper93.DeepMath.PathB.RavelingBoundedSpace

#print axioms PallLean.Paper93.DeepMath.PathB.RavelingBoundedSpace.boundedSpace_raveling
#print axioms PallLean.Paper93.DeepMath.PathB.RavelingBoundedSpace.boundedSpace_no_separator
