import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSequenceBridge

/-!
# A concrete restricted time model: bounded‑width branching programs

The first restricted *time* model attacked after space‑tightness.  A **branching program** is a standard
computational model: a layered transition system that reads input bits and ends in a decision state.  Its two
resources are **width** `W` (states per layer) and **length** `L` (the number of read steps — a time measure).

The result: a width‑`W` branching program's decision view ranges over only `W` states, so for `W < 2^r` it
**cannot realize the boundary‑`r` separator — at any length `L`.**  Time (length) is irrelevant: no amount of
read steps compensates for bounded width in realizing the separator.

## Proved (clean axioms, no `sorry`)

* `BProg` / `BProg.run` — the layered branching‑program model and its evaluation (fold over `L` layers).
* `bp_width_no_separator` — a width‑`W` branching program with `W < 2^r` carries debt `≥ 2^r − W > 0` against a
  surjective dimension‑`r` residual: it is not a separator, **independent of its length `L`**.

## Honest scope — realization, not decision

This is the *realization* (separator / `2^r`‑way classifier) bound, not a `1`‑bit decision lower bound: it says
the boundary‑`r` *separator* needs width `≥ 2^r`, and no bounded‑width branching program realizes it.  Length
`L` (the time axis of this model) does not help — confirming that, within the branching‑program model,
separation is a *width* requirement that time cannot substitute.  A poly‑**size** branching program has width
`≤ poly`, i.e. boundary `O(log n) < r = Ω(n)`, so it too cannot realize the separator.  What this does **not**
give is a `1`‑bit *decision* lower bound: the gap between *deciding* the family and *realizing its separator* is
exactly the time‑axis bridge `ResidualSeparatorRequiresSuperpolyTime` (`…TimeAxisWall`) — the open, `P ≠ NP`‑
strength step.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundedWidthBPTime

open PallLean.Paper93.DeepMath.PathB.CrossingSequenceBridge
open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

/-- A **layered branching program** on `n` input bits: width `W` (states), length `L` (read steps).  Each layer
reads one input bit (`readIdx`) and transitions (`trans`), starting from `start`. -/
structure BProg (n W L : ℕ) where
  /-- the start state -/
  start : Fin W
  /-- which input bit layer `ℓ` reads -/
  readIdx : Fin L → Fin n
  /-- the per‑layer transition, reading the chosen input bit -/
  trans : Fin L → Fin W → Bool → Fin W

/-- Evaluation: fold the `L` layers, reading the chosen input bit at each, ending in a decision state. -/
def BProg.run {n W L : ℕ} (P : BProg n W L) (x : Fin n → Bool) : Fin W :=
  (List.finRange L).foldl (fun st ℓ => P.trans ℓ st (x (P.readIdx ℓ))) P.start

/-- **Bounded width cannot realize the separator (proved).**  A width‑`W` branching program with `W < 2^r`
carries debt `≥ 2^r − W > 0` against a surjective dimension‑`r` residual: its decision view ranges over only `W`
states, too few to separate the `2^r` classes.  This holds for **every** length `L` — time does not compensate
for bounded width. -/
theorem bp_width_no_separator {n W L r : ℕ} (hW : W < 2 ^ r)
    (P : BProg n W L) (residual : (Fin n → Bool) → Fin (2 ^ r))
    (hsurj : Function.Surjective residual) :
    debtCount (residualFooling residual) P.run ≠ 0 := by
  have h := residual_view_card_forces_debt residual hsurj P.run
  rw [Fintype.card_fin] at h
  omega

end PallLean.Paper93.DeepMath.PathB.BoundedWidthBPTime

#print axioms PallLean.Paper93.DeepMath.PathB.BoundedWidthBPTime.bp_width_no_separator
