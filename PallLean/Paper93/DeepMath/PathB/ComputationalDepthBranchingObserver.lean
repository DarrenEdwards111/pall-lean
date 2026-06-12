import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTseitinSpaceObserver

/-!
# Branching observers — the geometric/holographic abstraction over the proved boundary bounds (Option B)

This is the **abstraction layer** that Option C anchors.  Option C
(`ComputationalDepthTseitinSpaceObserver.lean`) proved a *restricted* boundary lower bound (Tseitin
proof-space total space `≥ c·t`).  This file lifts the boundary-lower-bound *language* into a generic
structure — a `BranchingObserver` — so that the proved restricted result and the open SAT-hypercube target
become two instantiations of one theorem, with the boundary between them drawn precisely.

## The abstraction

A `BranchingObserver` over a type of `Sector`s (branches / witness regions / sectors) has:

* a **boundary entropy** `entropy : ℕ` — the number of bits of interface it can carry;
* a **view** map sending each sector to one of `2 ^ entropy` boundary states (`Fin (2 ^ entropy)`):
  an observer of entropy `B` can occupy at most `2^B` distinguishable boundary states.

Sectors are **non-mergeable** (for the observer) when their views are distinct (`Set.InjOn view`): the
observer keeps them apart at its boundary.  The central theorem is then forced:

> `many_nonmergeable_sectors_force_boundary` — if `K` sectors are mutually non-mergeable, then
> `entropy ≥ log₂ K`.

This is the holographic principle in clean form: **incompressible branching geometry forces boundary
entropy.**  It is the structural generalization of `ObserverBoundary.foolingSet_forces_boundary`.

## The hierarchy (HAL's ladder, made precise)

| Observer | Boundary lower bound | Status |
|---|---|---|
| fixed-cut communication | `equality_forces_boundary` (`B ≥ 2`) | ✅ proved, but **insufficient** (EQUALITY is easy) |
| resolution proof-space | Tseitin total space `≥ c·t` | ✅ **proved** (Option C, anchor) — boundary *size* via width/expansion |
| branching / holographic | `many_nonmergeable_sectors_force_boundary` | ✅ proved abstraction; SAT instance **conditional** |
| general machine-decomposition | the central conjecture | open, `= CookLevinFrontierHyp` |

## Honest scope — two mechanisms, not one

The branching core bounds the boundary by **sector count** (`log₂ K`).  Option C bounds it by **size**
(`c·t`, via width/expansion).  These are *different* mechanisms; I do **not** claim the Tseitin space bound
produces exponentially many non-mergeable sectors — it does not (a single width-`w` clause separates
assignments into only two classes, not `2^w`).  Both are genuine lower bounds on an observer's boundary, and
for Tseitin the size mechanism is the stronger one.  The SAT-hypercube instantiation
(`sat_sectors_conditionally_force_boundary`) is honestly **conditional**: its non-mergeability hypothesis is
exactly the open content (that a faithful observer of a SAT-decider cannot merge the witness sectors under
*every* admissible decomposition).  Nothing here asserts that.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.ObserverBoundary

/-- A **branching observer** over a sector type: a boundary entropy `B = entropy` and a `view` placing each
sector into one of `2 ^ entropy` boundary states.  (Codomain `Fin (2 ^ entropy)` bakes in the capacity:
an observer of entropy `B` occupies at most `2^B` boundary states.) -/
structure BranchingObserver (Sector : Type*) where
  /-- Boundary entropy: bits of interface the observer carries. -/
  entropy : ℕ
  /-- The observer's boundary view of each sector (at most `2 ^ entropy` distinct states). -/
  view : Sector → Fin (2 ^ entropy)

namespace BranchingObserver

variable {Sector : Type*}

/-- Sectors `T` are **non-mergeable** for the observer when it gives them pairwise-distinct boundary views:
it keeps them apart at its boundary. -/
def Nonmergeable (O : BranchingObserver Sector) (T : Finset Sector) : Prop :=
  Set.InjOn O.view (T : Set Sector)

/-- **The branching/holographic boundary principle (proved).**  If an observer keeps `K` sectors mutually
non-mergeable, then its boundary entropy is `≥ log₂ K`.  Incompressible branching geometry forces boundary
entropy.  (Structural generalization of `foolingSet_forces_boundary`.) -/
theorem many_nonmergeable_sectors_force_boundary (O : BranchingObserver Sector)
    (T : Finset Sector) (hnm : O.Nonmergeable T) :
    Nat.log 2 T.card ≤ O.entropy := by
  have hcard : T.card ≤ 2 ^ O.entropy := by
    calc T.card = (T.image O.view).card := (Finset.card_image_of_injOn hnm).symm
      _ ≤ Fintype.card (Fin (2 ^ O.entropy)) := Finset.card_le_univ _
      _ = 2 ^ O.entropy := Fintype.card_fin _
  exact foolingSet_forces_boundary T.card O.entropy hcard

/-- **Exponentially many non-mergeable sectors force super-logarithmic boundary.**  If at least `2 ^ k`
sectors are mutually non-mergeable, the observer's boundary entropy is `≥ k`.  (This is the shape a
separation would use: `k = ω(log n)` non-mergeable witness sectors ⇒ super-logarithmic boundary.) -/
theorem exp_nonmergeable_sectors_force_boundary (O : BranchingObserver Sector)
    (T : Finset Sector) (hnm : O.Nonmergeable T) {k : ℕ} (hmany : 2 ^ k ≤ T.card) :
    k ≤ O.entropy := by
  have hlog : k ≤ Nat.log 2 T.card := by
    calc k = Nat.log 2 (2 ^ k) := (Nat.log_pow (by norm_num) k).symm
      _ ≤ Nat.log 2 T.card := Nat.log_mono_right hmany
  exact le_trans hlog (many_nonmergeable_sectors_force_boundary O T hnm)

end BranchingObserver

/-! ## Non-vacuity anchor: a concrete observer the principle bites on (fixed-cut, EQUALITY)

Mirrors `ObserverBoundary.equality_forces_boundary`: four sectors with distinct boundary views (the EQUALITY
matrix rows) force entropy `≥ 2`.  Shows the abstraction is non-empty and the bound is tight. -/

/-- The EQUALITY observer: four sectors (`Fin 4`), each given its own boundary state in
`Fin (2 ^ 2) = Fin 4`.  Its four rows are mutually non-mergeable. -/
def eqObserver : BranchingObserver (Fin 4) where
  entropy := 2
  view := fun i => ⟨i.val, by have := i.isLt; omega⟩

theorem eqObserver_nonmergeable : eqObserver.Nonmergeable Finset.univ := by
  intro x _ y _ h
  simpa [eqObserver, Fin.ext_iff] using h

/-- The four EQUALITY sectors being non-mergeable force boundary entropy `≥ 2` — the principle bites,
exactly as the fixed-cut `equality_forces_boundary`.  (Still insufficient for hardness: EQUALITY is easy.) -/
theorem eqObserver_forces_boundary : 2 ≤ eqObserver.entropy := by
  have h := eqObserver.many_nonmergeable_sectors_force_boundary Finset.univ eqObserver_nonmergeable
  have hcard : (Finset.univ : Finset (Fin 4)).card = 4 := by simp
  rw [hcard] at h
  simpa using h

/-! ## Option B target: the SAT-hypercube witness observer (conditional)

Sectors are the satisfying assignments (witness regions) of a SAT instance on `{0,1}^n`.  The boundary
principle applies *verbatim* — but its non-mergeability hypothesis is the open content: that a faithful
observer of a SAT-decider must keep the witness sectors apart under *every* admissible decomposition. -/

/-- **Conditional SAT-hypercube boundary bound.**  For a SAT instance with witness set `W ⊆ {0,1}^n`, *if* a
branching observer keeps the witnesses non-mergeable, then its boundary entropy is `≥ log₂ |W|`.  The
hypothesis `hnm` is precisely the open content (a faithful observer cannot merge witness sectors); nothing
here discharges it. -/
theorem sat_sectors_conditionally_force_boundary {n : ℕ}
    (O : BranchingObserver (Fin n → Bool)) (W : Finset (Fin n → Bool))
    (hnm : O.Nonmergeable W) :
    Nat.log 2 W.card ≤ O.entropy :=
  O.many_nonmergeable_sectors_force_boundary W hnm

/-- **Conditional separation shape.**  If a SAT instance has `≥ 2 ^ k` witnesses and a faithful observer
keeps them non-mergeable, its boundary entropy is `≥ k`.  With `k = ω(log n)` this is super-logarithmic — a
separation — but it rests entirely on the open non-mergeability hypothesis. -/
theorem sat_exponential_sectors_force_boundary {n k : ℕ}
    (O : BranchingObserver (Fin n → Bool)) (W : Finset (Fin n → Bool))
    (hnm : O.Nonmergeable W) (hmany : 2 ^ k ≤ W.card) :
    k ≤ O.entropy :=
  O.exp_nonmergeable_sectors_force_boundary W hnm hmany

/-! ## Anchor to Option C: the proved restricted boundary lower bound

The resolution proof-space observer is the rung where a boundary lower bound is *actually proved*.  Re-stated
here so the abstraction's central quantity (a large boundary) is realized by genuine mathematics — via the
boundary-*size* mechanism (width/expansion), the stronger sibling of the sector-counting principle above. -/

/-- **Proved anchor (Option C).**  Every blackboard resolution refutation of the expander-Tseitin axioms has
proof-space observer boundary (total space) `≥ c·t`.  This is the worked example proving the
boundary-lower-bound language is not empty — established by width/expansion, not sector counting. -/
theorem resolution_proofSpace_boundary_anchor
    {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
    (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TseitinResolution.TConstr G charge v a)
    (Axiom : ResolutionClause (TseitinResolution.TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C →
      ∃ v : V, SemanticMeasure.Implies TseitinResolution.TSat (TseitinResolution.TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht : 1 < t) (hcard : 4 * t ≤ Fintype.card V)
    {M : Configuration (TseitinResolution.TLit Edge)}
    (Ref : Blackboard TseitinResolution.tcompl Axiom M)
    (hbot : (∅ : ResolutionClause (TseitinResolution.TLit Edge)) ∈ M) :
    c * t ≤ TseitinSpaceObserver.observerBoundary Ref :=
  TseitinSpaceObserver.tseitin_proofSpace_observer_lower_bound G charge hunsat Axiom haxiom hc hexp ht
    hcard Ref hbot

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.BranchingObserver.many_nonmergeable_sectors_force_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.eqObserver_forces_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.sat_exponential_sectors_force_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.resolution_proofSpace_boundary_anchor
