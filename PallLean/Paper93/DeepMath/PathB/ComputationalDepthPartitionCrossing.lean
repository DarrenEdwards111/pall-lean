import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementRuler

/-!
# The third direction: the global gate is the sole gate crossing the territory partition

Two routes already converge on the same object — the **global gate** reading both slots' disjoint
private territories:

* **size side** (`LocalizationBound`) — a global gate defeats every sub-`n` reach cap;
* **sharing side** (`AttackNoSharing`) — a global gate is the sole surviving sharer.

Here is a third, independent lens: **communication across the partition**.  Split the variables into
two players — Alice holds slot `i`'s territory, Bob holds slot `j`'s — and ask which gate must
**cross the cut**.  A gate depending only on Alice's variables (or only Bob's) is aligned with the
partition and needs no communication; a gate depending on *both* crosses the cut.  The global gate is
exactly the cut-crosser — the sole obstruction to the computation respecting the product (rectangle)
structure of the partition, and hence the sole source of communication cost.

## The convergence

* **`shared_gate_crosses_cut`** — a gate witnessing both slots **crosses the cut** (depends on a
  variable of each territory).  Sharing ⟹ crossing.
* **`crosscut_distinct_vars`** — a cut-crossing gate depends on two **distinct** variables, one in
  each disjoint territory: crossing ⟹ two-territory **reach** (the size side's currency).
* **`sharer_is_crosscut_is_reach`** — the capstone: from the sharing hypothesis alone, the gate
  crosses the cut *and* carries two-territory reach.  The **sharer** (route 2), the **cut-crosser**
  (route 3), and the **reach-bearer** (route 1) are one and the same gate.
* **`no_crosscut_is_aligned`** — the communication content: a gate that does *not* cross the cut is
  aligned to one side (fails to depend on the other).  So a circuit with no cut-crossing gates has
  every gate on one side of the partition — a **product / rectangle** structure, communication-trivial.
  The cut-crosser is the sole thing forcing the two territories to interact.

## Honest scope — three independent lenses, one object; excluding it is cost_super

The global gate is now characterized three ways, each from a different pillar: it is the reach-cap
defeater (combinatorial size), the sole surviving sharer (mass production), and the sole partition
cut-crosser (communication).  Three independent structural roles, one gate — the convergence is the
signal that this is the real core, not an artifact of one framing.  Excluding it for SAT's minimal
circuit is, in each language, the same wall: bounded reach = NoSharing = product/rectangle structure
= `cost_super`.  This does not prove any of them; it shows they are one obstruction seen from three
sides.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PartitionCrossing

open PallLean.Paper93.DeepMath.PathB.EntanglementRuler

variable {k b n : ℕ}

/-- A gate **crosses the cut** between territories `i` and `j` if it depends on a variable of each —
it couples Alice's side and Bob's side, and so requires communication across the partition. -/
def CrossesCut (C : EntangledTower k b n) (i j : Fin k) (g : ℕ) : Prop :=
  (∃ v, C.privMask i v = true ∧
      PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) v) ∧
  (∃ w, C.privMask j w = true ∧
      PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) w)

/-- **Sharing crosses the cut (proved).**  A gate witnessing both slots depends on a variable of each
territory — it crosses the partition.  Route 2 (sharing) lands on route 3 (crossing). -/
theorem shared_gate_crosses_cut (C : EntangledTower k b n) (i j : Fin k) (g : ℕ)
    (hi : g ∈ C.witness i) (hj : g ∈ C.witness j) : CrossesCut C i j g :=
  ⟨witness_forces_reach C i g hi, witness_forces_reach C j g hj⟩

/-- **Crossing forces two-territory reach (proved).**  A cut-crossing gate depends on two distinct
variables, one in each disjoint territory.  Route 3 (crossing) lands on route 1 (reach). -/
theorem crosscut_distinct_vars (C : EntangledTower k b n) (i j : Fin k) (hij : i ≠ j) (g : ℕ)
    (hc : CrossesCut C i j g) :
    ∃ v w, v ≠ w ∧
      PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) v ∧
      PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) w := by
  obtain ⟨⟨v, hv, hdv⟩, ⟨w, hw, hdw⟩⟩ := hc
  refine ⟨v, w, ?_, hdv, hdw⟩
  intro hvw
  have hjfalse : C.privMask j v = false := C.priv_disjoint i j hij v hv
  rw [hvw, hw] at hjfalse
  exact Bool.noConfusion hjfalse

/-- **The convergence capstone (proved).**  From the sharing hypothesis alone, the gate crosses the
cut *and* carries two-territory reach.  The sharer (route 2), the cut-crosser (route 3), and the
reach-bearer (route 1) are one and the same gate. -/
theorem sharer_is_crosscut_is_reach (C : EntangledTower k b n) (i j : Fin k) (hij : i ≠ j) (g : ℕ)
    (hi : g ∈ C.witness i) (hj : g ∈ C.witness j) :
    CrossesCut C i j g ∧
      (∃ v w, v ≠ w ∧
        PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) v ∧
        PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) w) := by
  have hcc := shared_gate_crosses_cut C i j g hi hj
  exact ⟨hcc, crosscut_distinct_vars C i j hij g hcc⟩

/-- **No crossing means aligned to one side (proved).**  A gate that does not cross the cut fails to
depend on one of the two territories — it lives entirely on Alice's side or Bob's side.  So a circuit
without cut-crossing gates has every gate aligned with the partition: a product / rectangle structure,
communication-trivial.  The cut-crosser is the sole gate forcing the two territories to interact. -/
theorem no_crosscut_is_aligned (C : EntangledTower k b n) (i j : Fin k) (g : ℕ)
    (hnc : ¬ CrossesCut C i j g) :
    (∀ v, C.privMask i v = true →
        ¬ PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) v) ∨
    (∀ w, C.privMask j w = true →
        ¬ PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) w) := by
  by_cases hi : ∃ v, C.privMask i v = true ∧
      PallLean.Paper93.DeepMath.PathB.EntanglementRuler.DependsOn (C.wireFn g) v
  · right
    intro w hw hd
    exact hnc ⟨hi, ⟨w, hw, hd⟩⟩
  · left
    intro v hv hd
    exact hi ⟨v, hv, hd⟩

end PallLean.Paper93.DeepMath.PathB.PartitionCrossing

#print axioms PallLean.Paper93.DeepMath.PathB.PartitionCrossing.shared_gate_crosses_cut
#print axioms PallLean.Paper93.DeepMath.PathB.PartitionCrossing.crosscut_distinct_vars
#print axioms PallLean.Paper93.DeepMath.PathB.PartitionCrossing.sharer_is_crosscut_is_reach
#print axioms PallLean.Paper93.DeepMath.PathB.PartitionCrossing.no_crosscut_is_aligned
