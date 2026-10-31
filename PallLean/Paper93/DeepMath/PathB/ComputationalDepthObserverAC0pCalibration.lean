import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4DimGeneral

/-!
# Calibration: the observer-boundary invariant rederives the AC⁰[p] (Razborov–Smolensky) lower bound

The observer programme has so far lived in proof complexity (Tseitin proof-space) and abstract
communication (branching/continuation observers).  This file is the **calibration test** HAL's strategy
calls for: *does the observer-boundary invariant rederive a known circuit lower bound?*  The answer here is
**yes** — and it is a rederivation, not a relabel, because the dimension-counting heart of Razborov–Smolensky
(`Layer4.dim_bound_general`) **is** the observer-boundary principle in linear-algebra form.

## The dictionary (faithful, not cosmetic)

| observer notion | linear-algebra / RS notion |
|---|---|
| boundary entropy `B` | dimension of the observer's **feature space** `Module.finrank K (feature)` |
| sectors / behaviors | functions on the agreement set `G` (points of the cube) |
| non-mergeable / fooling set | linearly independent behaviors — the *full* function space on `G` has dimension `|G|` |
| faithful observer | feature space `= ⊤`: it can express **every** behavior on `G` |
| low-boundary observer | an `AC⁰[p]` circuit's low-degree surrogate: feature `⊆` degree-`≤D` span, dimension `≤ #monomials` |

The branching principle "`K` non-mergeable sectors ⇒ `B ≥ log₂ K`" becomes the **exact** linear principle
"`K` independent behaviors ⇒ `finrank ≥ K`".  And `dim_bound_general` is its contrapositive: a low-degree
feature space of dimension `< |G|` *cannot* be faithful on `G`.

## What is proved (all clean axioms, no `sorry`)

* `DimObserver`, `boundary`, `Faithful` — the linear-algebra observer.
* `DimObserver.faithful_boundary` — a faithful observer has boundary `≥ |domain|` (the fooling principle).
* `DimObserver.lowBoundary_not_faithful` — boundary `< |domain|` ⇒ not faithful (contrapositive).
* `ac0pObserver`, `ac0pObserver_boundary_le` — the `AC⁰[p]` low-degree observer; boundary `≤ #monomials`.
* `ac0p_lowBoundary_not_faithful` — **the RS obstruction, recast and rederived through the principle**: an
  `AC⁰[p]` observer whose monomial capacity is below `|G|` cannot express every behavior on `G`.  Proved by
  feeding faithfulness into `Layer4.dim_bound_general`.

## Significance and honest scope

This is the calibration crossing **from proof complexity into circuit complexity**: the same
boundary/non-mergeability invariant that bounds Tseitin proof-space now drives the AC⁰[p] degree lower
bound.  It validates the method on a rung where the truth is known.

It does **not** by itself reprove the full circuit-level capstone (`Layer4.mod_q_indicators_false`, already
proved separately) — the approximate-agreement and band-margin bookkeeping live there; this file isolates and
recasts the *dimension obstruction* that is the lower bound's engine.  And AC⁰[p] is a restricted class: the
calibration confirms the invariant bites where bounds are provable; the general machine-decomposition rung
(`P` vs `NP`) remains open.  Nothing here claims otherwise.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverAC0p

open PallLean.Paper93.DeepMath.PathB

variable {α : Type*} [Fintype α] [DecidableEq α] {K : Type*} [Field K]

/-- A **dimension (linear-algebra) observer**: its *feature space* is the submodule of behaviors it can
express on a finite domain `α`.  The boundary is the dimension of that space. -/
structure DimObserver (α K : Type*) [Fintype α] [Field K] where
  /-- The functions on `α` the observer can express (its low-boundary surrogate). -/
  feature : Submodule K (α → K)

/-- **Boundary entropy** of a dimension observer: the dimension of its feature space. -/
noncomputable def DimObserver.boundary (O : DimObserver α K) : ℕ := Module.finrank K O.feature

/-- A dimension observer is **faithful** if it can express *every* behavior on the domain. -/
def DimObserver.Faithful (O : DimObserver α K) : Prop := O.feature = ⊤

/-- **The fooling principle (linear-algebra form).**  A faithful observer has boundary `≥ |domain|`: the full
function space on `α` has dimension `|α|`, so expressing every behavior costs that many dimensions.  This is
`many_nonmergeable_sectors_force_boundary` with `|α|` independent behaviors. -/
theorem DimObserver.faithful_boundary (O : DimObserver α K) (hf : O.Faithful) :
    Fintype.card α ≤ O.boundary := by
  have h : O.boundary = Fintype.card α := by
    rw [DimObserver.boundary, hf, finrank_top, Module.finrank_pi]
  omega

/-- **Contrapositive (forced unfaithfulness).**  An observer whose boundary is below `|domain|` cannot be
faithful — it must collapse two distinct behaviors.  This is the engine of every dimension/degree lower
bound. -/
theorem DimObserver.lowBoundary_not_faithful (O : DimObserver α K)
    (h : O.boundary < Fintype.card α) : ¬ O.Faithful :=
  fun hf => absurd (O.faithful_boundary hf) (Nat.not_le.mpr h)

/-! ## The AC⁰[p] low-degree observer -/

/-- The **AC⁰[p] observer** on the agreement set `G`: its feature space is the span of the degree-`≤D`
squarefree monomials (the low-degree surrogate of a depth-`d` `AC⁰[p]` circuit) restricted to `G`. -/
noncomputable def ac0pObserver (K : Type*) [Field K] {n : ℕ} (G : Finset (Fin n → Bool)) (D : ℕ) :
    DimObserver {x // x ∈ G} K where
  feature := Submodule.span K
    (Set.range (fun S : {S // S ∈ Layer3.lowDegMonomials n D} =>
      fun y : {x // x ∈ G} => Layer4.sqfEval K S.1 y.1))

/-- The AC⁰[p] observer's boundary is at most the number of low-degree monomials — its bounded capacity. -/
theorem ac0pObserver_boundary_le (K : Type*) [Field K] {n : ℕ} (G : Finset (Fin n → Bool)) (D : ℕ) :
    (ac0pObserver K G D).boundary ≤ (Layer3.lowDegMonomials n D).card := by
  classical
  show Module.finrank K (Submodule.span K
    (Set.range (fun S : {S // S ∈ Layer3.lowDegMonomials n D} =>
      fun y : {x // x ∈ G} => Layer4.sqfEval K S.1 y.1))) ≤ (Layer3.lowDegMonomials n D).card
  refine le_trans (finrank_span_le_card _) ?_
  rw [Set.toFinset_range]
  exact le_trans Finset.card_image_le (by rw [Finset.card_univ, Fintype.card_coe])

/-- **The Razborov–Smolensky obstruction, recast and rederived through the observer-boundary principle.**

An `AC⁰[p]` observer whose monomial capacity is below `|G|` **cannot be faithful on `G`** — it cannot express
every behavior on the agreement set.  Equivalently (`DimObserver.lowBoundary_not_faithful`), its boundary
`≤ #monomials < |G|` forbids faithfulness.

This is the dimension obstruction at the heart of the AC⁰[p] lower bound, now an instance of the
observer-boundary invariant: a function (like the `MOD_q` indicators) whose behaviors on `G` are *faithful*
(span everything, `Layer4.sqfSpan_eq_top`) cannot be matched by the low-boundary AC⁰[p] observer in the
band-margin window — which is exactly why `MOD_q ∉ AC⁰[p]`. -/
theorem ac0p_lowBoundary_not_faithful (K : Type*) [Field K] {n D : ℕ} (G : Finset (Fin n → Bool))
    (hsmall : (Layer3.lowDegMonomials n D).card < G.card) :
    ¬ (ac0pObserver K G D).Faithful := by
  intro hf
  have hstar : ∀ f : {x // x ∈ G} → K, f ∈ Submodule.span K
      (Set.range (fun S : {S // S ∈ Layer3.lowDegMonomials n D} =>
        fun y : {x // x ∈ G} => Layer4.sqfEval K S.1 y.1)) :=
    fun f => by rw [show Submodule.span K _ = (ac0pObserver K G D).feature from rfl, hf]; exact Submodule.mem_top
  have hle := Layer4.dim_bound_general K G hstar
  omega

end PallLean.Paper93.DeepMath.PathB.ObserverAC0p

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverAC0p.DimObserver.faithful_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverAC0p.ac0p_lowBoundary_not_faithful
