import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFramePartialRowBound

/-!
# N-Frame: kill-cost SCOUT — exploratory statements, not a rung

SCOUT FILE (rung-24 candidate material, deliberately minimal abstractions).  This is
exploratory Lean in the pressure-chamber tradition: closure rules and expansion enter as
HYPOTHESES, not definitions, so the exact provable statements surface before anything is
frozen.  The graph is a bare neighbourhood function; symmetry/regularity are hypotheses;
`D` = dead singletons; `K w` = the neighbours of `w` reachable only through killed
pair-functionals.

  `closed_dead_pays_boundary` — a closed dead set pays its whole edge boundary in killed
        pairs (one line once closure is phrased right — the content is in the phrasing).
  `closed_dead_alternative` — with expansion as a hypothesis: small closed dead sets cost
        `c·|D|` killed pairs, or the dead set is half the graph.
  `blocked_live_count` — the live-decomposition count: vertices with NO live route through
        any neighbour number at most `|D| + (killed pairs)/d` — outside a small dead set
        with a small kill budget, almost every singleton has a live decomposition.

## Honest scope — what the layer-3 red-team established (PROBE_PORT_FAMILY.md, task 3b)

These lemmas are TRUE and are the layer-2 expansion alternative of the kill-cost analysis.
They are also, by the completed red-team, NOT SUFFICIENT for `(2+c)N` on any ∃-semantics
selector family: the parity-locked dead-sector refuge has hosting-capacity/kill-cost ratio
`≥ 1.4` at every degree (both sides scale as selector-positions-per-functional), so the
adversary can always afford a small dead sector and host all balanced mass inside it, where
∃-maximization washes out everything but per-slot emptiness.  The surviving route that
still needs these lemmas is the parity-semantics family (`sat3X⊕`), where the probe steers
the summation coset rather than a satisfiability slice.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameKillCostScout

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer in
theorem scout_filter_card_sum_comm {β γ : Type*} (B : Finset β) (W : Finset γ)
    (p : β → γ → Prop) [∀ b w, Decidable (p b w)] :
    ∑ b ∈ B, (W.filter (fun w => p b w)).card
      = ∑ w ∈ W, (B.filter (fun b => p b w)).card :=
  filter_card_sum_comm B W p

variable {v : ℕ}

/-- Directed edge boundary of a vertex set under a bare neighbourhood function. -/
def edgeBoundary (nbr : Fin v → Finset (Fin v)) (A : Finset (Fin v)) : ℕ :=
  ∑ w ∈ A, ((nbr w) \ A).card

/-- Scout expansion, as a hypothesis-shaped predicate: every not-too-large set has
edge boundary at least `c` times its size.  Supplied later by a Ramanujan instantiation;
never proved here. -/
def Expander (nbr : Fin v → Finset (Fin v)) (c : ℕ) : Prop :=
  ∀ A : Finset (Fin v), 2 * A.card ≤ v → c * A.card ≤ edgeBoundary nbr A

/-- Scout dead-closure: a dead singleton's live neighbours are all behind killed pairs. -/
def DeadClosed (nbr : Fin v → Finset (Fin v)) (D : Finset (Fin v))
    (K : Fin v → Finset (Fin v)) : Prop :=
  ∀ w ∈ D, (nbr w) \ D ⊆ K w

/-- **SCOUT 1 (proved)**: a closed dead set pays its whole edge boundary in killed pairs. -/
theorem closed_dead_pays_boundary (nbr : Fin v → Finset (Fin v))
    (D : Finset (Fin v)) (K : Fin v → Finset (Fin v))
    (hclosed : DeadClosed nbr D K) :
    edgeBoundary nbr D ≤ ∑ w ∈ D, (K w).card :=
  Finset.sum_le_sum fun w hw => Finset.card_le_card (hclosed w hw)

/-- **SCOUT 2 (proved)**: the expansion alternative — a closed dead set is charged `c·|D|`
killed pairs, or it is more than half the graph. -/
theorem closed_dead_alternative (nbr : Fin v → Finset (Fin v)) (c : ℕ)
    (hexp : Expander nbr c)
    (D : Finset (Fin v)) (K : Fin v → Finset (Fin v))
    (hclosed : DeadClosed nbr D K) :
    c * D.card ≤ ∑ w ∈ D, (K w).card ∨ v < 2 * D.card := by
  by_cases h : 2 * D.card ≤ v
  · exact Or.inl (le_trans (hexp D h) (closed_dead_pays_boundary nbr D K hclosed))
  · exact Or.inr (by omega)

/-- **SCOUT 3 (proved)**: the live-decomposition count.  `B` = vertices with no live route
(all non-killed neighbours dead).  On a `d`-regular symmetric graph,
`d·|B| ≤ (killed pairs) + d·|D|` — outside a small dead set with a small kill budget,
almost every singleton has a live decomposition through a neighbour. -/
theorem blocked_live_count (nbr : Fin v → Finset (Fin v)) (d : ℕ)
    (hreg : ∀ w, (nbr w).card = d)
    (hsym : ∀ w w', w' ∈ nbr w → w ∈ nbr w')
    (D : Finset (Fin v)) (K : Fin v → Finset (Fin v))
    (B : Finset (Fin v))
    (hB : ∀ w ∈ B, (nbr w) \ K w ⊆ D) :
    d * B.card ≤ (∑ w ∈ B, (K w).card) + d * D.card := by
  classical
  have hper : ∀ w ∈ B, d ≤ (K w).card
      + (D.filter (fun u => u ∈ nbr w)).card := by
    intro w hw
    have hsub : nbr w ⊆ K w ∪ D.filter (fun u => u ∈ nbr w) := by
      intro u hu
      by_cases hK : u ∈ K w
      · exact Finset.mem_union_left _ hK
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, hu⟩)
        exact hB w hw (Finset.mem_sdiff.mpr ⟨hu, hK⟩)
    calc d = (nbr w).card := (hreg w).symm
      _ ≤ (K w ∪ D.filter (fun u => u ∈ nbr w)).card := Finset.card_le_card hsub
      _ ≤ (K w).card + (D.filter (fun u => u ∈ nbr w)).card :=
          Finset.card_union_le _ _
  have hsum : ∑ _w ∈ B, d
      ≤ ∑ w ∈ B, ((K w).card + (D.filter (fun u => u ∈ nbr w)).card) :=
    Finset.sum_le_sum hper
  rw [Finset.sum_const, smul_eq_mul, mul_comm] at hsum
  rw [Finset.sum_add_distrib] at hsum
  -- exchange the double count and cap by regularity
  have hcomm : ∑ w ∈ B, (D.filter (fun u => u ∈ nbr w)).card
      = ∑ u ∈ D, (B.filter (fun w => u ∈ nbr w)).card :=
    scout_filter_card_sum_comm B D (fun (w : Fin v) (u : Fin v) => u ∈ nbr w)
  have hcap : ∀ u ∈ D, (B.filter (fun w => u ∈ nbr w)).card ≤ d := by
    intro u _
    have hsub2 : B.filter (fun w => u ∈ nbr w) ⊆ nbr u := by
      intro w hwmem
      exact hsym w u (Finset.mem_filter.mp hwmem).2
    calc (B.filter (fun w => u ∈ nbr w)).card
        ≤ (nbr u).card := Finset.card_le_card hsub2
      _ = d := hreg u
  have hDsum : ∑ u ∈ D, (B.filter (fun w => u ∈ nbr w)).card ≤ d * D.card := by
    have h := Finset.sum_le_sum hcap
    rwa [Finset.sum_const, smul_eq_mul, mul_comm] at h
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameKillCostScout

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKillCostScout.closed_dead_pays_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKillCostScout.closed_dead_alternative
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKillCostScout.blocked_live_count
