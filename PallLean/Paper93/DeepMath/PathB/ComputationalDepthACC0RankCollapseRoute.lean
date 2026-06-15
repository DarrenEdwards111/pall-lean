import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCollapseRoute
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ParityRankCardinality

/-!
# Rank-based cell collapse — the sharper collapse condition (rank, not survivor count)

The survivor-count collapse `2^{#survivors} < |L|` (`…ACC0CellCollapseRoute`) is *crude*: for **overlapping** supports
many gates survive yet induce few distinct cells.  The number of cells is really governed by the **`F₂`-rank** of the
support incidence, not the survivor count.  This file introduces the rank-based collapse condition and proves it is
the **sharper / more achievable** one.

A direction note first.  Since rank `≤` number of generators,
`supportRank supports L ≤ survivingCount supports L`, so `2^{supportRank} ≤ 2^{#survivors}`.  Hence the implication
runs `CellCollapse ⇒ RankCellCollapse` (the rank condition is *weaker*, i.e. *easier to force*) — **not** the reverse.
That is exactly the point: the open socket should be the rank one, because it is more achievable.

## What is proved (clean axioms, no `sorry`)

* `incidenceVec` / `survivorIncidence` / `supportRank` — the `F₂` incidence vectors of the surviving supports
  (restricted to `L`) and the dimension of their span.
* **`supportRank_le_survivingCount`** — `supportRank supports L ≤ survivingCount supports L` (rank `≤` #generators,
  via `finrank_span_finset_le_card` + `card_image_le`).
* `RankCellCollapse supports L := 2^{supportRank supports L} < |L|`.
* **`cell_collapse_implies_rank_collapse`** — `CellCollapse supports L ⇒ RankCellCollapse supports L`: the (crude)
  survivor collapse implies the (sharp) rank collapse.  So the rank socket is *weaker* than the survivor socket.
* `FullACC0ForcesRankCollapse` — the rank-based socket (weaker than `FullACC0ForcesCellCollapse`).
* **`full_cell_collapse_implies_full_rank_collapse`** — and the socket implication lifts: the survivor socket implies
  the rank socket.

## Honest scope — why this is the right move, and what is still open

The rank route *weakens the open socket* (`FullACC0ForcesRankCollapse` is easier than the survivor version) and is the
correct cell count for overlapping/`MOD₂` supports: the number of reachable parity cells is `2^{rank}`
(`…ACC0ParityRankCardinality.parity_reachable_card = 2^{finrank}`), not `2^{#survivors}`.  The genuine next target is
the **sharp bridge** `RankCellCollapse ⇒ low correlation` (re-running the pigeonhole with `#cells ≤ 2^{rank}`, fed by
`parity_reachable_card`), which is *not* obtained by composing with the existing survivor bridge (that needs the
*stronger* survivor collapse).  Forcing `supportRank < log₂|L|` for real `ACC⁰` under a restriction is the
rank-flavoured switching lemma — still open, `NP ⊄ ACC⁰`-strength.  This file builds the rank route and proves it is
the sharper condition; it does **not** close the socket.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RankCollapseRoute

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute

variable {k n : ℕ}

/-- The `F₂` incidence vector of a support: the indicator of `S` over the cube coordinates. -/
def incidenceVec (S : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ S then 1 else 0

/-- The incidence vectors of the supports that survive the live set `L` (restricted to `L`). -/
noncomputable def survivorIncidence (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    Finset (Fin n → ZMod 2) :=
  (Finset.univ.filter (fun j => ¬ Disjoint (supports j) L)).image
    (fun j => incidenceVec (supports j ∩ L))

/-- **The support rank**: the `F₂`-dimension of the span of the surviving supports' incidence vectors — the true
governor of the cell count (`#cells ≤ 2^{supportRank}`), `≤ survivingCount`. -/
noncomputable def supportRank (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) : ℕ :=
  Set.finrank (ZMod 2) (↑(survivorIncidence supports L) : Set (Fin n → ZMod 2))

/-- **Rank `≤` survivor count (proved).**  The span of `m` incidence vectors has dimension `≤ m`, and there are at
most `survivingCount` of them. -/
theorem supportRank_le_survivingCount (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) :
    supportRank supports L ≤ survivingCount supports L := by
  unfold supportRank survivorIncidence survivingCount
  exact le_trans (finrank_span_finset_le_card _) Finset.card_image_le

/-- **Rank-based cell collapse**: `2^{supportRank} < |L|` — the sharp condition. -/
def RankCellCollapse (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) : Prop :=
  2 ^ supportRank supports L < L.card

/-- **The crude survivor collapse implies the sharp rank collapse (proved).**  Since `supportRank ≤ survivingCount`,
`2^{#survivors} < |L|` gives `2^{rank} < |L|`.  So the rank socket is *weaker* (more achievable). -/
theorem cell_collapse_implies_rank_collapse (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : CellCollapse supports L) : RankCellCollapse supports L :=
  lt_of_le_of_lt
    (Nat.pow_le_pow_right (by norm_num) (supportRank_le_survivingCount supports L)) h

/-- **The rank-based socket** (weaker than `FullACC0ForcesCellCollapse`): some live set has rank `< log₂|L|`. -/
def FullACC0ForcesRankCollapse (supports : Fin k → Finset (Fin n)) : Prop :=
  ∃ L : Finset (Fin n), RankCellCollapse supports L

/-- **The survivor socket implies the rank socket (proved): the rank route's open target is weaker.** -/
theorem full_cell_collapse_implies_full_rank_collapse (supports : Fin k → Finset (Fin n))
    (h : FullACC0ForcesCellCollapse supports) : FullACC0ForcesRankCollapse supports := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, cell_collapse_implies_rank_collapse supports L hL⟩

end PallLean.Paper93.DeepMath.PathB.ACC0RankCollapseRoute

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankCollapseRoute.supportRank_le_survivingCount
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankCollapseRoute.cell_collapse_implies_rank_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankCollapseRoute.full_cell_collapse_implies_full_rank_collapse
