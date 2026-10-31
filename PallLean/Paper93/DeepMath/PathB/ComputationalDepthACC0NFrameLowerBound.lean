import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DisjointCollapse

/-!
# The N-Frame ACC⁰ lower bound, stated beside Williams — one socket, with the bridge proved

This file packages the whole N-Frame route as a single conditional theorem, the way `…ACC0WilliamsCashout` packages
the Williams route.  Williams reduces the separation to **two** sockets (the exact-quasipoly `SYM∘AND` and the time
hierarchy).  The N-Frame route reduces the holonomy lower bound to **one** socket — *cell collapse* — because its
other half (collapse ⇒ low correlation) is already a *proved* theorem (`…ACC0CellCollapseRoute.nframe_route`).

For a *class* of `ACC⁰` holonomy-predictors `sys` (each a gate count, supports, and symmetric top):

```
NFrameCellCollapse sys   (every predictor's supports collapse on some live set — the HARD open socket)
        │  nframe_acc_lower_bound   (PROVED, via the proved bridge)
        ▼
ACC0HolonomyLowerBound sys tops   (every predictor fails to correlate with some holonomy parity)
```

## What is proved (clean axioms, no `sorry`)

* `NFrameCellCollapse` / `ACC0HolonomyLowerBound` — the route's hypothesis and conclusion, over a predictor class.
* **`nframe_acc_lower_bound`** — the headline: `NFrameCellCollapse sys ⇒ ACC0HolonomyLowerBound sys tops`
  (the one-socket reduction, proved by the bridge `nframe_route` pointwise).
* **`nframe_lower_bound_disjoint`** — the socket *discharged* for disjoint-support classes: a class of predictors with
  pairwise-disjoint supports, each with a size-`≥ 3` support, satisfies the holonomy lower bound **unconditionally**
  (so the conditional is *not vacuous*).

## Honest scope — the socket is the open content, and is *false* in general

`NFrameCellCollapse` is the hard, `NP ⊄ ACC⁰`-strength socket.  It is **discharged** for bounded fragments
(`…ACC0BoundedSurvival`: bounded gate count, small footprint; `…ACC0DisjointCollapse`: disjoint supports), and
`nframe_lower_bound_disjoint` makes one such discharge explicit.  But it is **false for arbitrary support systems**: a
predictor with polynomially many wide, overlapping supports has many survivors on *every* large live set, so no
collapse occurs — that is the wall.  So the genuine open statement is cell collapse for the support systems arising
from *real* `ACC⁰` circuits *under a restriction* — the switching/restriction lemma, blocked for naive leaf-switching
by the proved `MOD` no-go.  This file pins and packages the route; it does **not** prove the socket.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NFrameLowerBound

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0DisjointCollapse

variable {n : ℕ}

/-- A class of `ACC⁰` holonomy-predictors over inputs of length `n`, indexed by `ι`: each `sys i` is a gate count
together with the gates' supports. -/
abbrev PredictorClass (ι : Type) (n : ℕ) : Type := ι → Σ k : ℕ, Fin k → Finset (Fin n)

/-- **The N-Frame cell-collapse hypothesis (the hard open socket).**  Every predictor in the class forces cell
collapse on some live set. -/
def NFrameCellCollapse {ι : Type} (sys : PredictorClass ι n) : Prop :=
  ∀ i, FullACC0ForcesCellCollapse (sys i).2

/-- **The N-Frame holonomy lower bound (the conclusion).**  Every predictor in the class — with its symmetric top
`tops i` — fails to correlate with the holonomy parity. -/
def ACC0HolonomyLowerBound {ι : Type} (sys : PredictorClass ι n)
    (tops : ∀ i, (Fin (sys i).1 → ℕ) → Bool) : Prop :=
  ∀ i, LowHolonomyCorrelation (sys i).2 (tops i)

/-- **The N-Frame route as one conditional theorem (proved).**  The cell-collapse socket implies the holonomy lower
bound — by the proved bridge `nframe_route`, applied to each predictor.  This is the N-Frame analogue of
`williams_route_reduces_to_two_sockets`, with *one* socket instead of two (the second half is already proved). -/
theorem nframe_acc_lower_bound {ι : Type} (sys : PredictorClass ι n)
    (tops : ∀ i, (Fin (sys i).1 → ℕ) → Bool) (h : NFrameCellCollapse sys) :
    ACC0HolonomyLowerBound sys tops :=
  fun i => nframe_route (sys i).2 (tops i) (h i)

/-- **The socket discharged for disjoint-support classes (proved): an *unconditional* N-Frame lower bound.**  If every
predictor in the class has pairwise-disjoint supports and at least one support of size `≥ 3`, then the holonomy lower
bound holds with no socket — the cell-collapse hypothesis is supplied by `disjoint_supports_forces_cellCollapse`. -/
theorem nframe_lower_bound_disjoint {ι : Type} (sys : PredictorClass ι n)
    (tops : ∀ i, (Fin (sys i).1 → ℕ) → Bool)
    (hd : ∀ i, ∀ a b, a ≠ b → Disjoint ((sys i).2 a) ((sys i).2 b))
    (hsize : ∀ i, ∃ j, 3 ≤ ((sys i).2 j).card) :
    ACC0HolonomyLowerBound sys tops := by
  intro i
  obtain ⟨j, hj⟩ := hsize i
  exact disjoint_supports_low_holonomy_correlation (sys i).2 (tops i) (hd i) j hj

end PallLean.Paper93.DeepMath.PathB.ACC0NFrameLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NFrameLowerBound.nframe_acc_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NFrameLowerBound.nframe_lower_bound_disjoint
