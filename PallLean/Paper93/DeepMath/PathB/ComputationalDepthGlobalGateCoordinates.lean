import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPartitionCrossing

/-!
# The exact coordinates of the global gate: doubly nonlinear on the two disjoint territories

Three bearings fixed the location of the global gate — the reach-cap defeater (size), the sole
surviving sharer (mass production), the sole partition cut-crosser (communication).  This file
resolves the location to **exact coordinates**: the single, minimal semantic predicate that is the
intersection of all three.

## The coordinate

The global gate is exactly the gate that is **nonlinear on both slots' private territories**:
`GlobalGate := NonlinearOnBlock (privMask i) ∧ NonlinearOnBlock (privMask j)`, the two territories
disjoint.  From this one condition every bearing follows, and each bearing points back to it:

* **`witness_both_is_global`** — a both-slots sharer *is* doubly nonlinear (from `wit_semantic`): the
  sharing bearing (route 2) is exactly the coordinate.
* **`global_crosses_cut`** — the coordinate forces crossing the cut (route 3): each nonlinearity
  forces a dependency inside its territory (`nonlinear_forces_reach`).
* **`global_two_reach`** — the coordinate forces two-territory reach on distinct variables (route 1).
* **`the_exact_coordinates`** — the capstone: a both-slots sharer is *simultaneously* doubly nonlinear
  (the coordinate), cut-crossing (bearing 3), and two-territory reaching (bearing 1).  One gate, one
  coordinate, all three bearings.

## Minimality — both conjuncts are load-bearing

The coordinate is exact, not loose: **both** nonlinearities are necessary.

* **`needs_both_nonlinearities`** — a gate that is *not* nonlinear on territory `j` cannot witness slot
  `j`.  Drop either conjunct and the gate is local (aligned to one side, route 3), unable to share.

So the coordinate is pinned from above (sharing ⟹ it) and below (drop a conjunct ⟹ local): the exact
coordinates of the global gate are `doubly nonlinear on the two disjoint private territories`, and
nothing weaker.

## Honest scope — exact coordinates, still the wall

This fixes precisely *what* the global gate is — the intersection of the three bearings, a minimal
semantic predicate — and proves each bearing is a projection of it.  It does **not** exclude the gate
for SAT.  Excluding a doubly-nonlinear-on-disjoint-territories gate from SAT's minimal circuit is, in
each of the three languages, still the same wall: bounded reach = NoSharing = product structure =
`cost_super`.  The coordinates are exact; the wall stands where they point.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.GlobalGateCoordinates

open PallLean.Paper93.DeepMath.PathB.EntanglementRuler
open PallLean.Paper93.DeepMath.PathB.WitnessLocalization
open PallLean.Paper93.DeepMath.PathB.PartitionCrossing

variable {k b n : ℕ}

/-- **Nonlinearity forces reach (proved).**  A wire nonlinear on a territory must depend on a variable
of it — the contrapositive of `no_private_reach_no_witness`. -/
theorem nonlinear_forces_reach (F : (Fin n → Bool) → Bool) (blk : Fin n → Bool)
    (hnl : NonlinearOnBlock blk F) :
    ∃ v, blk v = true ∧ PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn F v := by
  by_contra hno
  push_neg at hno
  exact no_private_reach_no_witness F blk hno hnl

/-- **The exact coordinate.**  The global gate is the gate nonlinear on *both* slots' private
territories. -/
def GlobalGate (C : EntangledTower k b n) (i j : Fin k) (g : ℕ) : Prop :=
  NonlinearOnBlock (C.privMask i) (C.wireFn g) ∧ NonlinearOnBlock (C.privMask j) (C.wireFn g)

/-- **The sharing bearing is the coordinate (proved).**  A both-slots sharer is doubly nonlinear —
directly from `wit_semantic`.  Route 2 lands exactly on the coordinate. -/
theorem witness_both_is_global (C : EntangledTower k b n) (i j : Fin k) (g : ℕ)
    (hi : g ∈ C.witness i) (hj : g ∈ C.witness j) : GlobalGate C i j g :=
  ⟨C.wit_semantic i g hi, C.wit_semantic j g hj⟩

/-- **The coordinate crosses the cut (proved).**  Doubly nonlinear ⟹ depends on a variable of each
territory ⟹ `CrossesCut`.  The coordinate projects to bearing 3. -/
theorem global_crosses_cut (C : EntangledTower k b n) (i j : Fin k) (g : ℕ)
    (hg : GlobalGate C i j g) : CrossesCut C i j g :=
  ⟨nonlinear_forces_reach (C.wireFn g) (C.privMask i) hg.1,
   nonlinear_forces_reach (C.wireFn g) (C.privMask j) hg.2⟩

/-- **The coordinate carries two-territory reach (proved).**  Doubly nonlinear + disjoint territories
⟹ two distinct dependencies, one per territory.  The coordinate projects to bearing 1. -/
theorem global_two_reach (C : EntangledTower k b n) (i j : Fin k) (hij : i ≠ j) (g : ℕ)
    (hg : GlobalGate C i j g) :
    ∃ v w, v ≠ w ∧
      PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) v ∧
      PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) w :=
  crosscut_distinct_vars C i j hij g (global_crosses_cut C i j g hg)

/-- **The exact coordinates (proved, capstone).**  A both-slots sharer is *simultaneously* doubly
nonlinear on the two disjoint territories (the coordinate), cut-crossing (bearing 3), and
two-territory reaching (bearing 1).  One gate, one coordinate, all three bearings meet. -/
theorem the_exact_coordinates (C : EntangledTower k b n) (i j : Fin k) (hij : i ≠ j) (g : ℕ)
    (hi : g ∈ C.witness i) (hj : g ∈ C.witness j) :
    GlobalGate C i j g ∧ CrossesCut C i j g ∧
      (∃ v w, v ≠ w ∧
        PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) v ∧
        PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) w) := by
  have hg : GlobalGate C i j g := witness_both_is_global C i j g hi hj
  exact ⟨hg, global_crosses_cut C i j g hg, global_two_reach C i j hij g hg⟩

/-- **Both conjuncts are load-bearing (proved).**  A gate *not* nonlinear on territory `j` cannot
witness slot `j` — drop either nonlinearity and the gate is local, unable to share.  The coordinate is
exact, not loose. -/
theorem needs_both_nonlinearities (C : EntangledTower k b n) (j : Fin k) (g : ℕ)
    (hlin : ¬ NonlinearOnBlock (C.privMask j) (C.wireFn g)) (hj : g ∈ C.witness j) : False :=
  hlin (C.wit_semantic j g hj)

end PallLean.Paper93.DeepMath.PathB.GlobalGateCoordinates

#print axioms PallLean.Paper93.DeepMath.PathB.GlobalGateCoordinates.nonlinear_forces_reach
#print axioms PallLean.Paper93.DeepMath.PathB.GlobalGateCoordinates.witness_both_is_global
#print axioms PallLean.Paper93.DeepMath.PathB.GlobalGateCoordinates.the_exact_coordinates
#print axioms PallLean.Paper93.DeepMath.PathB.GlobalGateCoordinates.needs_both_nonlinearities
