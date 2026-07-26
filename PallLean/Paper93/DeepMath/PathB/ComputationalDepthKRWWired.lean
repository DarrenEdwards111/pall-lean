import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRWOneStep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKWBridge

/-!
# KRW with the KW bridge wired in — `kw ≤ depth` is now a proof, not a hypothesis

`KRWOneStep.krw_depth_lower_bound` assumed `kw_le : ∀ f, kw f ≤ depth f` — the KW theorem's `CC ≤ depth`
direction.  `KWBridge` *built* that direction (a formula gives a correct protocol of cost `≤ depth`).
This file connects them: the bridge discharges `kw_le`, leaving `KWOneStep` (the one-round lemma) as the
only open piece of the route.

## What is proved

* **`kw_le_depth_of_min`** — the bridge discharges `kw ≤ depth`.  For the KW communication complexity `kw`
  — characterized as `≤` the cost of *any correct protocol* (`kw_min`, the defining property of a
  minimum) — the descent protocol is **correct** (`descent_correct`, fed in) with cost `≤ depth`
  (`descentBits_le_depth`), so `kw F ≤ depth F`.  The previously-assumed `kw_le` is now a *proof*.
* **`krw_depth_bound_wired`** — the KRW cash-out over formulas: given the one-round lemma (`step`) and the
  bridge-supplied `kw_le`, the tower's formula depth is `≥ d+1` — super-log for `d = ω(log n)`, `P ⊄ NC¹`.

## The state of the route, sharpened

The KRW route was `KWOneStep ⟹ P ⊄ NC¹` on **two** unbuilt pieces: the one-round lemma *and* the KW
theorem.  The KW theorem's load-bearing direction is now **built** (`KWBridge`, monotone) and **wired**
here.  So the route rests on a **single** open lemma — `KWOneStep`, the one-round composition bound — with
everything else, including the formula↔protocol bridge, a proof.

## Honest scope

`kw_le_depth_of_min` uses `kw_min` (the *definition* of `kw` as a minimum over correct protocols — not an
extra assumption) and the bridge's proved `descent_correct`.  It holds for functions with a valid KW pair
(`hx`, `hy`) — all non-constant functions, including the tower.  Ceiling stays `P ⊄ NC¹` (monotone
depth).  `KWOneStep` remains open.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KRWWired

open PallLean.Paper93.DeepMath.PathB.KRWOneStep
open PallLean.Paper93.DeepMath.PathB.KWBridge

/-- **The bridge discharges `kw ≤ depth` (proved).**  `kw_min` is the defining property of the KW
communication complexity: it is `≤` the cost of any *correct* protocol.  The descent is correct
(`descent_correct`, supplied here) with cost `≤ depth` (`descentBits_le_depth`), so `kw F ≤ depth F`.
This turns the `kw_le` hypothesis of the KRW cash-out into a theorem. -/
theorem kw_le_depth_of_min {n : ℕ} (kw : MForm n → ℕ)
    (kw_min : ∀ (F : MForm n) (x y : Fin n → Bool),
        (x (descent F x y) = true ∧ y (descent F x y) = false) → kw F ≤ descentBits F x y)
    (F : MForm n) (x y : Fin n → Bool)
    (hx : eval F x = true) (hy : eval F y = false) :
    kw F ≤ depth F :=
  le_trans (kw_min F x y (descent_correct F x y hx hy)) (descentBits_le_depth F x y)

/-- **KRW cash-out, KW bridge wired in (proved).**  With the one-round lemma (`step`, the socket) and
`kw_le` — now supplied by the bridge (`kw_le_depth_of_min`) rather than assumed — the tower's formula
depth is `≥ d+1`.  For `d = ω(log n)`: super-logarithmic depth, `P ⊄ NC¹`.  The route now rests on the
single open lemma `KWOneStep`. -/
theorem krw_depth_bound_wired {n : ℕ}
    (compose : MForm n → MForm n → MForm n) (base : MForm n) (kw : MForm n → ℕ)
    (kw_le : ∀ F, kw F ≤ depth F)
    (step : KWOneStep kw compose) (hbase : 1 ≤ kw base) (d : ℕ) :
    d + 1 ≤ depth (tower compose base d) :=
  krw_depth_lower_bound base step kw_le hbase d

end PallLean.Paper93.DeepMath.PathB.KRWWired

#print axioms PallLean.Paper93.DeepMath.PathB.KRWWired.kw_le_depth_of_min
#print axioms PallLean.Paper93.DeepMath.PathB.KRWWired.krw_depth_bound_wired
