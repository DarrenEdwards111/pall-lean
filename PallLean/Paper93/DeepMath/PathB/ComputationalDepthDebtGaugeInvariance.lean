import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundedLocalityNonCollapse

/-!
# Observer‑invariance of the debt — the gauge‑invariant content of the N‑frame action route

HAL's N‑frame‑Lagrangian proposal needs the action/debt to be **observer‑invariant**: no change of
observer frame (gauge) may flatten it.  This file proves that invariance at the level of the debt — the
concrete, checkable backbone of the proposal's "representation‑invariance" requirement.

* A **lossless frame change** is an injective relabeling `σ` of the observer's view codomain.
* A **lossy frame change** is a coarsening (collapsing distinctions).

## Proved (clean axioms, no `sorry`)

* `debtCount_relabel_invariant` — a *lossless* frame change preserves the debt exactly: for injective `σ`,
  `debtCount F (σ ∘ view) = debtCount F view`.  Relabeling the boundary states changes nothing.
* `debtCount_le_of_frameChange` — combined with `debtCount_mono`: **no frame change can reduce the debt**.
  A frame change is either lossless (preserves debt) or lossy (a coarsening, which `debtCount_mono` shows only
  *increases* debt).  So the debt is a genuine observer‑invariant: it can only be lowered by *refining* — i.e.
  by spending more boundary — never by a gauge transformation.

## Honest status — this gives requirements (1) and (2), not (3)

HAL listed three requirements for the N‑frame action to close the gap: (1) non‑circular / concrete, (2)
representation‑invariant, (3) strong enough to defeat high‑boundary poly‑time observers.

* **(1) and (2): met here.**  `debtCount` is a concrete, checkable quantity (a `Finset.card`), and the theorems
  prove it is invariant under lossless frame changes and non‑decreasing under lossy ones — exactly
  "no gauge transformation flattens it."  This is the rigorous form of the curvature/holonomy intuition
  (cf. `expander_manyloop_holonomy`: no cheap coordinate flattening avoids the twist).
* **(3): NOT met — and this is the wall.**  Observer‑invariance forbids reducing debt *by changing frame*, but
  it does **not** forbid reducing debt *by refining* — i.e. by paying more boundary.  A high‑boundary observer
  has a larger codomain (a strictly finer frame), which is not a gauge transformation but a genuine resource
  increase, and it *can* drive debt to zero (`hypercube_brute_force_escape`).  And paying boundary is
  *time*‑cheap (`action_unbounded_by_time` / `step5_naive_bridge_false`).  So the gauge‑invariant debt is still
  a **space/distinguishability** measure; making it frame‑invariant does not make it bound *time*.

So this file delivers the genuinely provable core of HAL's proposal — the debt is observer‑invariant — while
making precise that invariance alone does not defeat the high‑boundary escape.  Closing requirement (3) is the
time→action bridge = decision‑holonomy = `P ≠ NP`, unchanged.  Not circular here (we proved a real invariance);
not a proof of the separation either.
-/

namespace PallLean.Paper93.DeepMath.PathB.DebtGaugeInvariance

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

variable {X : Type*}

/-- **Lossless frame change preserves debt (proved).**  Relabeling the observer's boundary states by an
injective `σ` leaves the distinguishability debt unchanged: `debtCount F (σ ∘ view) = debtCount F view`.  The
debt does not depend on *how* the boundary states are named — only on which continuations they merge. -/
theorem debtCount_relabel_invariant {S S' : Type*} [DecidableEq S] [DecidableEq S']
    (F : Finset (X × X)) (view : X → S) (σ : S → S') (hσ : Function.Injective σ) :
    debtCount F (fun x => σ (view x)) = debtCount F view := by
  show (F.filter (fun p => σ (view p.1) = σ (view p.2))).card
      = (F.filter (fun p => view p.1 = view p.2)).card
  rw [Finset.filter_congr (fun p _ => ⟨fun h => hσ h, fun h => congrArg σ h⟩)]

/-- **No frame change reduces the debt (proved).**  If a new frame `view'` is *coarser* than `view` composed
with a lossless relabel — i.e. it merges whatever the relabeled frame merges (`hcoarser`) — then its debt is at
least the original's.  Combined with `debtCount_relabel_invariant`, no gauge transformation (lossless relabel,
or any further coarsening) can lower the debt below the original; only refining (spending boundary) can. -/
theorem debtCount_le_of_frameChange {S S' T : Type*} [DecidableEq S] [DecidableEq S'] [DecidableEq T]
    (F : Finset (X × X)) (view : X → S) (σ : S → S') (hσ : Function.Injective σ)
    (view' : X → T) (hcoarser : ∀ x y, σ (view x) = σ (view y) → view' x = view' y) :
    debtCount F view ≤ debtCount F view' := by
  rw [← debtCount_relabel_invariant F view σ hσ]
  exact debtCount_mono F (fun x => σ (view x)) view' hcoarser

end PallLean.Paper93.DeepMath.PathB.DebtGaugeInvariance

#print axioms PallLean.Paper93.DeepMath.PathB.DebtGaugeInvariance.debtCount_relabel_invariant
#print axioms PallLean.Paper93.DeepMath.PathB.DebtGaugeInvariance.debtCount_le_of_frameChange
