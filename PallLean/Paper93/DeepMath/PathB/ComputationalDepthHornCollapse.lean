import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAffineOutput

/-!
# The horn collapse: for a nonlinear target the wall is the Uhlig horn *alone*

`AffineOutput` proved an affine-mixed circuit computes a GF(2)-affine function.  This has a sharp
consequence for `cost_super`: **SAT (its self-composite) is not affine**, so *no* affine-mixed circuit
computes it — every circuit for SAT must contain a nonlinear gate.  Hence the linear (Valiant/rigidity)
horn is **vacuously true**, and the two-horn dichotomy collapses: for a nonlinear target, `cost_super`
follows from the **nonlinear (Uhlig-sharing) horn alone**.

This is the honest sharpening of `CostSuperDichotomy`.  The wall is not two open bounds for SAT — the
rigidity horn is *discharged* (you cannot compute a nonlinear function with only affine gates), and the
entire remaining content is the Uhlig no-sharing bound.

* **`exists_not_affine` (proved)** — non-affine functions exist (`AND` on 2 bits), so the collapse is
  non-vacuous.
* **`NonlinearHorn`** — the named Uhlig horn: circuits with a nonlinear gate that compute `f` are large.
* **`linHorn_vacuous_of_not_affine` (proved)** — for non-affine `f`, no affine-mixed circuit computes
  it, so the linear horn holds trivially.
* **`lb_from_nonlinear_horn` (proved)** — hence for non-affine `f`, `NonlinearHorn f t ⟹ t ≤ cbudget f`.
* **`tower_field_from_nonlinear_horn` (proved)** — if every level-composite is non-affine, the tower's
  open field `cost_super` follows from the nonlinear horn alone.

**Honest scope.**  Proved: the linear horn is discharged for nonlinear targets and the reduction now
runs on one horn.  **Not** proved: `NonlinearHorn` for SAT — that is the Uhlig no-sharing bound, the
single open wall this route now rests on.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HornCollapse

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.CostSuperDichotomy
open PallLean.Paper93.DeepMath.PathB.AffineSemantics
open PallLean.Paper93.DeepMath.PathB.AffineOutput

variable {n : ℕ}

/-- **Non-affine functions exist (proved).**  The `2`-bit `AND` is not GF(2)-affine — so the collapse
below is non-vacuous (there really are targets forcing a nonlinear gate). -/
theorem exists_not_affine : ¬ IsAffineFn (fun x : Fin 2 → Bool => x 0 && x 1) := by
  unfold IsAffineFn; decide

/-- The **nonlinear (Uhlig) horn**: every circuit that computes `f` and contains a nonlinear gate has
`≥ t` gates.  For a non-affine target this is the whole wall. -/
def NonlinearHorn (f : (Fin n → Bool) → Bool) (t : ℕ) : Prop :=
  ∀ c : List (CGate n), computes c f → ¬ AffineMixed c → t ≤ c.length

/-- **The linear horn is vacuous for a nonlinear target (proved).**  If `f` is not affine, no
affine-mixed circuit computes it (`output_affine` would make `f` affine), so the linear horn holds
trivially — the antecedent is never satisfied. -/
theorem linHorn_vacuous_of_not_affine (f : (Fin n → Bool) → Bool) (t : ℕ)
    (hf : ¬ IsAffineFn f) :
    ∀ c : List (CGate n), computes c f → AffineMixed c → t ≤ c.length := by
  intro c hcomp haff
  exact absurd (funext hcomp ▸ output_affine c haff) hf

/-- **The lower bound from the nonlinear horn alone (proved).**  For a non-affine circuit-computable
`f`, the Uhlig horn suffices: `NonlinearHorn f t ⟹ t ≤ cbudget f` (the linear horn is discharged by
vacuity). -/
theorem lb_from_nonlinear_horn (f : (Fin n → Bool) → Bool) (t : ℕ)
    (hf : ¬ IsAffineFn f) (hcomp : ∃ c : List (CGate n), computes c f)
    (H : NonlinearHorn f t) : t ≤ cbudget f :=
  lb_from_horns f t hcomp (linHorn_vacuous_of_not_affine f t hf) H

/-- **`cost_super` from the nonlinear horn alone (proved).**  If every level-composite is non-affine
(true for SAT) and satisfies the Uhlig horn at threshold `2·cost d`, then the tower's open field
`∀ d, 2·cost d ≤ cost (d+1)` = `cost_super` holds.  The rigidity horn contributes nothing — the entire
wall is Uhlig no-sharing. -/
theorem tower_field_from_nonlinear_horn {arity cost : ℕ → ℕ}
    (composite : (d : ℕ) → (Fin (arity (d + 1)) → Bool) → Bool)
    (hnaff : ∀ d, ¬ IsAffineFn (composite d))
    (hcomp : ∀ d, ∃ c : List (CGate (arity (d + 1))), computes c (composite d))
    (nonlinHorn : ∀ d, NonlinearHorn (composite d) (2 * cost d))
    (hrel : ∀ d, cbudget (composite d) ≤ cost (d + 1)) :
    ∀ d, 2 * cost d ≤ cost (d + 1) := by
  intro d
  exact le_trans
    (lb_from_nonlinear_horn (composite d) (2 * cost d) (hnaff d) (hcomp d) (nonlinHorn d)) (hrel d)

end PallLean.Paper93.DeepMath.PathB.HornCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.HornCollapse.exists_not_affine
#print axioms PallLean.Paper93.DeepMath.PathB.HornCollapse.linHorn_vacuous_of_not_affine
#print axioms PallLean.Paper93.DeepMath.PathB.HornCollapse.lb_from_nonlinear_horn
#print axioms PallLean.Paper93.DeepMath.PathB.HornCollapse.tower_field_from_nonlinear_horn
