import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderNoHiding

/-!
# Boundary holonomy / curvature schema (a restricted "new-maths direction", NOT P≠NP)

The staged ladder (read-set, linear, bounded-locality) all bound a decomposition's *effective boundary* and
fire when it is `< r`.  The remaining open regime is high-boundary nonlinear adaptive atlases.  This file sets
up the **holonomy / curvature** schema HAL proposed: a cheap observer flattens one local chart, but moving
around a loop of charts built on expander/parity constraints and returning, the residual has **twisted** — and
that twist is unpaid distinguishability debt.

This is a SCHEMA: it makes "nonzero holonomy ⇒ debt" a theorem and exhibits a concrete `F₂` parity loop where
the holonomy is provably nonzero and the debt is maximal.  It is **not** a proof that every cheap atlas has
nonzero holonomy (that final step is `P ≠ NP`); it is the honest scaffold for that attack.

## The picture

* **Charts / transitions.**  A loop of decompositions has transition maps; their composition is the net
  transport `h : Config → Config` (the *holonomy map*).
* **Loop-invariant observer.**  A cheap observer that "returns to the same state" after the loop has
  `view ∘ h = view` — it cannot tell `c` from its transport `h c`.
* **Twist = debt.**  If the residual differs (`res (h c) ≠ res c`), then `c` and `h c` are a must-separate
  pair the observer has merged: unpaid debt.

## Proved (clean axioms, no `sorry`)

* `residualRel` — the residual must-separate relation (general codomain; generalises `residualFooling`).
* `loopHolonomy` — net transport of a loop of transition maps (their composition).
* `nonzero_holonomy_forces_debt` — if `view ∘ h = view` and the holonomy twists *some* config
  (`res (h c₀) ≠ res c₀`), then `debtCount (residualRel res) view ≥ 1`.
* `holonomy_forces_debt_card` — quantitative: the debt is at least the number of twisted configs
  (`|{c : res (h c) ≠ res c}| ≤ debtCount …`).
* `parity_loop_holonomy` — **the `F₂` instance**: for an additive residual `res : Config →+ ZMod 2`, a
  holonomy translation `v` with `res v ≠ 0` (a parity loop with *odd* net charge — the Tseitin odd-cycle
  obstruction), and any observer that flattens `v` (`view (c + v) = view c`), **every** config is twisted, so
  the debt is the full `|Config|`.
* `parity_loop_holonomy_cube` — concrete `Config = Fin L → ZMod 2`: debt `≥ 2^L`.

## Honest scope

`nonzero_holonomy_forces_debt` is real and clean; the `F₂` instance is non-vacuous (debt `= 2^L`).  But the
holonomy is supplied as a hypothesis (`res v ≠ 0` + `view` flattens `v`).  The open `P ≠ NP` content is the
*converse direction* — that **every** cheap adaptive atlas of expander Tseitin is forced to flatten some `v`
with `res v ≠ 0`, i.e. that expander constraints have nonzero curvature against *all* cheap coordinate
systems.  That is `AdaptiveResidualNonCollapse` in curvature form, and it is **not** proved here.  Next rung:
expander many-loop amplification (sum the twists of a frontier of cycles), then the forced-twist converse.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundaryDebt

open scoped BigOperators
open Finset

/-- The **residual must-separate relation**: pairs with different residual outcome (general codomain;
generalises `residualFooling`, which is the `R = Fin k` case). -/
def residualRel {Config R : Type*} [Fintype Config] [DecidableEq R]
    (res : Config → R) : Finset (Config × Config) :=
  Finset.univ.filter (fun p => res p.1 ≠ res p.2)

/-- The **holonomy map** of a loop of charts: the net transport, i.e. the composition of the loop's transition
maps applied in order. -/
def loopHolonomy {Config : Type*} (transitions : List (Config → Config)) : Config → Config :=
  fun c => transitions.foldr (fun t acc => t acc) c

/-- **Holonomy debt, quantitative (proved).**  If the observer is loop-invariant (`view ∘ h = view`, it
returns to the same state after the loop), the debt it carries is at least the number of configs whose
residual the holonomy `h` twists: each twisted `c` and its transport `h c` are a must-separate pair the
observer has merged. -/
theorem holonomy_forces_debt_card {Config R S : Type*} [Fintype Config] [DecidableEq Config]
    [DecidableEq R] [DecidableEq S]
    (res : Config → R) (h : Config → Config) (view : Config → S)
    (hinv : ∀ c, view (h c) = view c) :
    (univ.filter (fun c => res (h c) ≠ res c)).card ≤ debtCount (residualRel res) view := by
  classical
  show (univ.filter (fun c => res (h c) ≠ res c)).card
      ≤ ((residualRel res).filter (fun p => view p.1 = view p.2)).card
  apply Finset.card_le_card_of_injOn (fun c => (c, h c))
  · intro c hc
    rw [Finset.mem_coe, mem_filter] at hc
    rw [Finset.mem_coe, mem_filter]
    refine ⟨?_, (hinv c).symm⟩
    simp only [residualRel, mem_filter, mem_univ, true_and]
    exact Ne.symm hc.2
  · intro a _ b _ hab
    exact (Prod.ext_iff.mp hab).1

/-- **Nonzero holonomy forces debt (proved).**  A single twisted config suffices: if the loop-invariant
observer cannot distinguish `c₀` from its transport `h c₀` (`view (h c₀) = view c₀`) yet their residuals
differ, the debt is at least `1`. -/
theorem nonzero_holonomy_forces_debt {Config R S : Type*} [Fintype Config] [DecidableEq Config]
    [DecidableEq R] [DecidableEq S]
    (res : Config → R) (h : Config → Config) (view : Config → S)
    (hinv : ∀ c, view (h c) = view c) (c₀ : Config) (htwist : res (h c₀) ≠ res c₀) :
    1 ≤ debtCount (residualRel res) view := by
  refine le_trans ?_ (holonomy_forces_debt_card res h view hinv)
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  exact ⟨c₀, by rw [mem_filter]; exact ⟨mem_univ _, htwist⟩⟩

/-- **`F₂` parity-loop holonomy (proved).**  Let `res : Config →+ ZMod 2` be an additive residual (a parity),
`v` a holonomy translation with `res v ≠ 0` (the loop has *odd* net charge — the Tseitin odd-cycle
obstruction), and `view` an observer that flattens `v` (`view (c + v) = view c`, returns to the same state
after the loop).  Then **every** config is twisted, so the debt is the full `|Config|`. -/
theorem parity_loop_holonomy {Config S : Type*} [Fintype Config] [DecidableEq Config] [DecidableEq S]
    [AddCommGroup Config] (res : Config →+ ZMod 2) (v : Config) (hv : res v ≠ 0)
    (view : Config → S) (hview : ∀ c, view (c + v) = view c) :
    Fintype.card Config ≤ debtCount (residualRel (fun c => res c)) view := by
  have hkey := holonomy_forces_debt_card (⇑res) (fun c => c + v) view hview
  have hall : (univ.filter (fun c => (⇑res) ((fun c => c + v) c) ≠ (⇑res) c)) = (univ : Finset Config) := by
    apply Finset.filter_true_of_mem
    intro c _
    show (⇑res) (c + v) ≠ (⇑res) c
    rw [map_add]
    exact fun hcon => hv (add_eq_left.mp hcon)
  rw [hall, Finset.card_univ] at hkey
  exact hkey

/-- **Concrete cube instance (proved).**  On the Boolean cube `Fin L → ZMod 2`, a parity residual with an
odd-charge holonomy translation `v` flattened by the observer forces debt `≥ 2^L`. -/
theorem parity_loop_holonomy_cube {L : ℕ} {S : Type*} [DecidableEq S]
    (res : (Fin L → ZMod 2) →+ ZMod 2) (v : Fin L → ZMod 2) (hv : res v ≠ 0)
    (view : (Fin L → ZMod 2) → S) (hview : ∀ c, view (c + v) = view c) :
    2 ^ L ≤ debtCount (residualRel (fun c => res c)) view := by
  have h := parity_loop_holonomy res v hv view hview
  rwa [Fintype.card_fun, ZMod.card, Fintype.card_fin] at h

end PallLean.Paper93.DeepMath.PathB.BoundaryDebt

#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.holonomy_forces_debt_card
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.nonzero_holonomy_forces_debt
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.parity_loop_holonomy
#print axioms PallLean.Paper93.DeepMath.PathB.BoundaryDebt.parity_loop_holonomy_cube
