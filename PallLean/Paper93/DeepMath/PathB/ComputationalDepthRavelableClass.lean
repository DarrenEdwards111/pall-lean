import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverDimensionGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderResidualSurjective
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRavelWedge

/-!
# The ravelable class, instantiated — and the structural ceiling it reveals

Following the wedge program: define a concrete separator class `K`, prove `SAT ∉ K` (the `noSeparator` half),
and connect it to the action via the raveling half.  Here `K` is the **bounded‑boundary (bounded effective
dimension)** class — an observer whose view holds `< 2^r` distinguishable states (`d_obs = B < r`).

## Proved (clean axioms, no `sorry`)

* `IsSeparator` — a correct (zero‑debt) observer of the residual relation.
* `boundedBoundary_no_separator` — **`noSeparator` for `K`**: any observer of effective dimension `B < r`
  facing a residual of dimension `r` (surjective) carries positive debt, so it is **not** a separator.
* `expander_no_boundedBoundary_separator` — the discharged instance: the expander‑Tseitin residual (dimension
  `|ι| = Ω(n)`) has **no** bounded‑boundary separator below dimension `|ι|` — it is *non‑ravelable*.

## The raveling half (cited) and the wedge

The other half — `lowAction ⇒ inK` — is the bottleneck pigeonhole `adaptive_bottleneck_exists`: a trajectory
of low *total* boundary action has a step whose boundary is below the budget, i.e. in `K`.  Composing with
`boundedBoundary_no_separator` via `ravel_wedge` gives: **no low‑action observer separates the expander
residual** — which is exactly `cheap_trajectory_has_residual_debt_bottleneck`, now read as a wedge instance for
this `K`.

## The honest ceiling this file makes precise

`K = {effective dimension < r}` is **the maximal class the debt mechanism can beat.**  `boundedBoundary_no_
separator` needs `B < r`; at `B ≥ r` a separator exists with zero debt (`hypercube_brute_force_escape`), so
`SAT ∈ K` becomes true and the lower bound vanishes.  Every beatable `K` in this corpus (linear, read‑set,
bounded‑locality, holonomy) is a *sub*‑class of this one — they all certify `d_obs < r`.  So the wedge is
realized up to, and **exactly** at, `d_obs < r`.

Growing `K` past `d_obs = r` — to capture genuinely high‑boundary (poly‑space) observers while keeping `SAT ∉
K` — cannot be done by the debt/curvature mechanism (the escape is real, `refinement_reduces_debt`).  It
requires a `noSeparator` proof of a *different* kind: a **Williams‑style cash‑out** (a cheap separator ⇒
algorithmic speedup ⇒ hierarchy contradiction), the only technique with teeth past this ceiling — and itself
guarded by the natural‑proofs / relativization / algebrization barriers.  This file proves the wedge at its
ceiling and names, precisely, the one move that would extend it.  No `P ≠ NP` claim.
-/

namespace PallLean.Paper93.DeepMath.PathB.RavelableClass

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt
open PallLean.Paper93.DeepMath.PathB.ObserverDimensionGap

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- A **separator**: a correct, zero‑debt observer of the residual relation — it merges no must‑separate
continuation pair. -/
def IsSeparator {r : ℕ} (residual : C → Fin (2 ^ r)) (view : C → Fin (2 ^ B)) : Prop :=
  debtCount (residualFooling residual) view = 0

/-- **`noSeparator` for the bounded‑boundary class `K` (proved).**  An observer of effective dimension `B < r`
facing a residual of dimension `r` (surjective) carries strictly positive debt, hence is **not** a separator.
The bounded‑boundary class contains no separator for a higher‑dimensional residual. -/
theorem boundedBoundary_no_separator {r B : ℕ} (hBr : B < r) (residual : C → Fin (2 ^ r))
    (hsurj : Function.Surjective residual) (view : C → Fin (2 ^ B)) :
    ¬ IsSeparator residual view := by
  have h := positive_gap_forces_debt hBr residual hsurj view
  unfold IsSeparator
  omega

end PallLean.Paper93.DeepMath.PathB.RavelableClass

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **The expander residual is non‑ravelable (proved).**  For a Tseitin graph with expansion `c ≥ 1` and
read‑set `w : ι → V`, the residual (dimension `|ι|`) has **no** bounded‑boundary separator below dimension
`|ι|`: every observer of effective dimension `B < |ι|` carries positive debt.  The expander curvature cannot be
flattened by any sub‑`|ι|`‑dimensional observer. -/
theorem expander_no_boundedBoundary_separator (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → V) (hw : Function.Injective w) (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    {B : ℕ} (hB : B < Fintype.card ι) (view : (Edge → ZMod 2) → Fin (2 ^ B)) :
    ∃ residual : (Edge → ZMod 2) → Fin (2 ^ Fintype.card ι),
      debtCount (residualFooling residual) view ≠ 0 := by
  obtain ⟨residual, hdebt⟩ := expander_residual_forces_debt G hc hexp w hw hmed view
  refine ⟨residual, ?_⟩
  have hlt : 2 ^ B < 2 ^ Fintype.card ι := Nat.pow_lt_pow_right (by norm_num) hB
  omega

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.RavelableClass.boundedBoundary_no_separator
#print axioms PallLean.Paper93.DeepMath.PathB.expander_no_boundedBoundary_separator
