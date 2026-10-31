import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheReasonGeneral

/-!
# The reason with overlapping witnesses: which part of the counting argument survives

Dropping `wit_disjoint`, what part of `the_reason`'s counting argument is recoverable?  The argument had
four steps; three survive, one fails.  This file names exactly what survives.

The disjoint argument: (1) each block needs `≥ b` witnesses; (2) witnesses `⊆ gates`; (3) *disjoint* ⟹
`|⋃ wᵢ| = Σ|wᵢ| = k·b`; (4) `|gates| ≥ |⋃ wᵢ|`.  Steps (1),(2),(4) use no disjointness — they **survive**.
Only (3) fails: with overlap, `|⋃ wᵢ| < Σ|wᵢ|`.  So what survives is the bound in terms of the **union** —
the *distinct* witness gates — not the sum.

## What is proved

* **`survives_single`** — the single-block floor survives *any* overlap: `b ≤ |gates|`.  The union contains
  at least one full witness, so the circuit needs at least `b` gates no matter how much it shares.
* **`survives_union`** — the strongest survivor: `|⋃ wᵢ| ≤ |gates|`.  The circuit needs at least as many
  gates as there are **distinct** witness gates across all blocks.
* **`full_bound_of_distinct`** — the full bound is recovered *iff* the witnesses stay distinct: if
  `k·b ≤ |⋃ wᵢ|` then `k·b ≤ |gates|`.  Disjoint ⟹ `|⋃ wᵢ| = k·b`; overlap ⟹ `|⋃ wᵢ| < k·b`.

## Honest scope — what survives is the distinctness bound; the full bound is distinctness = cost_super

So the recoverable core is `|gates| ≥ |distinct witnesses|` — it ranges from the floor `b` (total overlap) to
the ceiling `k·b` (fully disjoint), and equals `k·b − overlap` (`the_reason_general`).  The counting argument
survives *entirely except the one step* "distinct ⟹ sum".  Recovering `k·b` means proving the witnesses
stay distinct — that the circuit *cannot* reuse a witness across blocks — which for SAT's shared-input tower
is exactly `cost_super`.  The surviving bound is real and general; the missing piece is one quantity, the
distinctness (`= k·b − overlap`), and bounding it is the single wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.WhatSurvives

open PallLean.Paper93.DeepMath.PathB.TheReasonGeneral

/-- **The single-block floor survives (proved).**  For any block `i`, `b ≤ |gates|` — even under total
overlap.  The circuit contains that block's `≥ b` witnesses, which are gates.  Uses no disjointness. -/
theorem survives_single {k b : ℕ} (C : GeneralCircuit k b) (i : Fin k) : b ≤ C.gates.card :=
  le_trans (C.wit_size i) (Finset.card_le_card (C.wit_sub i))

/-- **The union (distinctness) bound survives (proved).**  `|⋃ wᵢ| ≤ |gates|` — the circuit needs at least as
many gates as there are *distinct* witness gates across all blocks.  The strongest recoverable bound; uses no
disjointness. -/
theorem survives_union {k b : ℕ} (C : GeneralCircuit k b) :
    (Finset.univ.biUnion C.witness).card ≤ C.gates.card := by
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨i, _, hxi⟩ := hx
  exact C.wit_sub i hxi

/-- **The full bound is recovered iff the witnesses stay distinct (proved).**  If the distinct witness gates
already number `≥ k·b` (`k·b ≤ |⋃ wᵢ|`), then `k·b ≤ |gates|`.  Disjoint gives `|⋃ wᵢ| = k·b`; overlap makes
it smaller.  So the full reason survives exactly to the extent the witnesses are distinct. -/
theorem full_bound_of_distinct {k b : ℕ} (C : GeneralCircuit k b)
    (hdistinct : k * b ≤ (Finset.univ.biUnion C.witness).card) : k * b ≤ C.gates.card :=
  le_trans hdistinct (survives_union C)

end PallLean.Paper93.DeepMath.PathB.WhatSurvives

#print axioms PallLean.Paper93.DeepMath.PathB.WhatSurvives.survives_union
#print axioms PallLean.Paper93.DeepMath.PathB.WhatSurvives.full_bound_of_distinct
