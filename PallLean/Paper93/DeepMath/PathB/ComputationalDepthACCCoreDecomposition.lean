import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCOverlapDesign

/-!
# Core decomposition: separating easy from hard overlap

The star probe showed concentrated overlap is removable; the design probe showed the variance bound cannot see the
difference and the distinguishing quantity is `|overlapCoords|`.  This file generalizes the star surgery into a
clean **dichotomy** that holds for *any* support family.

The canonical core of any family is `overlapCoords = {v : v lies in ≥ 2 supports}`.  We prove:

* **killing the core disjointifies** (`kill_overlap_gives_disjointOnLive`) — the converse of
  `disjointify_requires_kill`, giving the exact characterization `disjointOnLive ↔ overlapCoords killed`;
* **the restricted family is genuinely pairwise disjoint** (`restricted_pairwise_disjoint`) — after killing the
  core, `supports j ∩ L` are pairwise disjoint, so the disjoint variance pipeline fires;
* **the disjoint variance bound returns** (`core_decomposition_variance`) — `Var[X] ≤ k·s·p` for the restricted
  family, with the `k²λ` overlap term *gone*.

So **the surgery cost to remove all overlap is exactly `|overlapCoords|`**, and the dichotomy is sharp:

* `|overlapCoords|` small ⇒ killing it is cheap ⇒ the family reduces to disjoint (the easy case, e.g. the star
  where `overlapCoords ⊆ core`);
* `|overlapCoords|` large ⇒ no small kill disjointifies (the hard spread case) ⇒ the genuine `NP ⊄ ACC⁰` wall.

## What is proved (clean axioms, no `sorry`)

* `kill_overlap_gives_disjointOnLive`, `disjointOnLive_iff` — killing the core disjointifies, and the iff.
* `restricted_pairwise_disjoint` — the core‑killed restricted family is pairwise disjoint.
* `core_decomposition_variance` — the restricted family has the disjoint bound `Var ≤ k·s·p`.

## Honest reading

This is the exact generalization of `core_surgery`: *every* family has a canonical core (`overlapCoords`) whose
removal reduces it to a disjoint family with the clean `k·s·p` variance.  The single number `|overlapCoords|` is the
cost and the dividing line — small (easy, removable) vs large (hard, the spread/Håstad regime).  Nothing here makes
the hard case easy; it pins the difficulty to one explicit cardinality.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCCoreDecomposition

open PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingVariance
open PallLean.Paper93.DeepMath.PathB.ACCOverlapDesign

variable {n k : ℕ}

/-- **Killing the core disjointifies (proved): if every overlap coordinate is dead, the supports are disjoint on
the live set.**  The converse of `disjointify_requires_kill`. -/
theorem kill_overlap_gives_disjointOnLive (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : Disjoint (overlapCoords supports) L) : disjointOnLive supports L := by
  intro v hv
  by_contra hc
  push_neg at hc
  have hov : v ∈ overlapCoords supports := by
    rw [overlapCoords, Finset.mem_filter]; exact ⟨Finset.mem_univ _, by omega⟩
  exact Finset.disjoint_left.mp h hov hv

/-- **The exact characterization (proved): the supports are disjoint on `L` iff every overlap coordinate is
dead.** -/
theorem disjointOnLive_iff (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    disjointOnLive supports L ↔ Disjoint (overlapCoords supports) L :=
  ⟨disjointify_requires_kill supports L, kill_overlap_gives_disjointOnLive supports L⟩

/-- **The core‑killed restricted family is pairwise disjoint (proved).**  After killing the core, the restricted
supports `supports j ∩ L` share no live coordinate, so they are pairwise disjoint. -/
theorem restricted_pairwise_disjoint (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : disjointOnLive supports L) (i j : Fin k) (hij : i ≠ j) :
    Disjoint (supports i ∩ L) (supports j ∩ L) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  rw [Finset.mem_inter] at hvi hvj
  have hinc : 2 ≤ incidence supports v := by
    have hsub : ({i, j} : Finset (Fin k)) ⊆ Finset.univ.filter (fun l => v ∈ supports l) := by
      intro l hl
      rw [Finset.mem_insert, Finset.mem_singleton] at hl
      rw [Finset.mem_filter]
      rcases hl with rfl | rfl
      · exact ⟨Finset.mem_univ _, hvi.1⟩
      · exact ⟨Finset.mem_univ _, hvj.1⟩
    calc 2 = ({i, j} : Finset (Fin k)).card := (Finset.card_pair hij).symm
      _ ≤ incidence supports v := Finset.card_le_card hsub
  have := h v hvi.2
  omega

/-- **The disjoint variance bound returns (proved): after killing the core, `Var[X] ≤ k·s·p`.**  The restricted
family is pairwise disjoint, so `variance_disjoint_le` applies — the `k²·λ` overlap term is gone.  The cost of this
reduction is `|overlapCoords|`: the dividing line between easy (small core) and hard (large core) overlap. -/
theorem core_decomposition_variance (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) (h : disjointOnLive supports L)
    (s : ℕ) (hfan : ∀ i, (supports i).card ≤ s) :
    variance p (fun j => supports j ∩ L) ≤ (k : ℝ) * s * p := by
  refine variance_disjoint_le p hp0 hp1 (fun j => supports j ∩ L) s ?_ ?_
  · intro i; exact le_trans (Finset.card_le_card Finset.inter_subset_left) (hfan i)
  · intro i j hij; exact restricted_pairwise_disjoint supports L h i j hij

end PallLean.Paper93.DeepMath.PathB.ACCCoreDecomposition

#print axioms PallLean.Paper93.DeepMath.PathB.ACCCoreDecomposition.kill_overlap_gives_disjointOnLive
#print axioms PallLean.Paper93.DeepMath.PathB.ACCCoreDecomposition.disjointOnLive_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACCCoreDecomposition.restricted_pairwise_disjoint
#print axioms PallLean.Paper93.DeepMath.PathB.ACCCoreDecomposition.core_decomposition_variance
