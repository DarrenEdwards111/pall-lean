import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAttackNoSharing

/-!
# The seam drill: does disjointness force the collision bound? A concrete tower says NO — reach does

`DemandGrowthSeam` showed collapse needs a **near-total** seam-collision (a gate serving `> ½` of both
copies).  The natural hope: the copies' *disjoint private territories* make such a collision
impossible — a straddler serving both would have to be in two disjoint places at once.  This file
tests that hope on a **concrete disjoint tower** and reports the honest answer.

The answer is **NO — disjointness alone does not forbid the collision.**  A single **global** gate can
serve two disjoint copies at once; disjointness constrains how *territories* relate, not how far one
*gate* reaches.  The only ceiling on collision is the gate's **reach** (`mult ≤ depCard`,
`collision_bounded_by_reach`), and reach is unbounded without localization.

## What is proved — on `straddleExample : EntangledTower 2 1 4` ((x₀∧x₁)⊕(x₂∧x₃))

* **`straddle_gate_serves_two`** — gate `0` serves BOTH copies (blocks `0` and `1`): a seam-collision
  exists.  (This is `AttackNoSharing.global_gate_is_shared`, read as a collision.)
* **`disjoint_admits_collision`** — the territories ARE pairwise disjoint (`priv_disjoint`) AND the
  collision exists.  Disjointness and a full collision coexist — the hoped contradiction fails.
* **`straddle_beats_disjoint_bound`** — the collision is real mass-production: the circuit has `1`
  gate, strictly below the disjoint (no-sharing) requirement `k·b = 2·1 = 2`.  One global gate does
  the work of two.
* **`collision_bounded_by_reach`** — the true ceiling: a gate's collision `mult` is at most its reach
  `depCard` (`mult_le_depCard`).  Not disjointness — *reach*.  A global gate (high `depCard`) can
  collide as much as it reaches.
* **`local_forbids_collision`** — the missing ingredient: under full locality (`AllLocal`, bounded
  reach), no gate serves two copies (`local_circuit_no_cross_sharing`) — the collision vanishes.

## Honest verdict

The base case + seam law + disjointness do **not** force a lower bound on the straddler that
contradicts `> ½`-collision.  A concrete disjoint, doubly-nonlinear tower (`straddleExample`) collapses
below its own disjoint bound through a single global gate.  The `> ½`-collision is contradicted by
disjointness **only when combined with bounded reach (localization)** — which is `cost_super` /
`LocalizationBound`.  So the drill lands the seam wall exactly on localization, now with a concrete
witness that disjointness alone is not enough.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SeamDisjointnessProbe

open PallLean.Paper93.DeepMath.PathB.AttackNoSharing
open PallLean.Paper93.DeepMath.PathB.EntanglementRuler
open PallLean.Paper93.DeepMath.PathB.TheReasonShared

/-- A **seam-collision** at gate `g`: `g` serves two distinct copies (witnesses two distinct blocks).
This is the demand-side `shared > 0` of `DemandGrowthSeam`, at the gate level. -/
def ServesTwoCopies {k b n : ℕ} (C : EntangledTower k b n) (g : ℕ) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧ g ∈ C.witness i ∧ g ∈ C.witness j

/-- **The concrete disjoint tower has a seam-collision (proved).**  Gate `0` of `straddleExample`
serves both blocks — a straddler across the two disjoint copies. -/
theorem straddle_gate_serves_two : ServesTwoCopies straddleExample 0 :=
  ⟨0, 1, by decide, global_gate_is_shared.1, global_gate_is_shared.2⟩

/-- **Disjointness and a collision coexist (proved) — the answer is NO.**  `straddleExample` has
pairwise-disjoint private territories AND a gate serving both copies.  Disjointness does not forbid the
collision. -/
theorem disjoint_admits_collision :
    (∀ i j, i ≠ j → ∀ v, straddleExample.privMask i v = true → straddleExample.privMask j v = false)
    ∧ ServesTwoCopies straddleExample 0 :=
  ⟨straddleExample.priv_disjoint, straddle_gate_serves_two⟩

/-- **The collision is genuine mass-production (proved).**  `straddleExample` computes the demand
`k·b = 2·1 = 2` with only `1` gate — strictly below the disjoint (no-sharing) requirement.  One global
gate does two copies' work. -/
theorem straddle_beats_disjoint_bound : straddleExample.gates.card < 2 * 1 := by decide

/-- **The true ceiling on collision is REACH, not disjointness (proved).**  A gate's collision `mult`
(how many copies it serves) is at most its reach `depCard` (how many variables it depends on).
Disjointness makes the served private variables distinct, but a global gate with large `depCard` can
still serve many copies.  This is `mult_le_depCard` read as a collision bound. -/
theorem collision_bounded_by_reach {k b n : ℕ} (C : EntangledTower k b n) (g : ℕ) :
    mult (toShared C) g ≤ (depSet C g).card :=
  mult_le_depCard C g

/-- **Localization forbids the collision (proved) — the missing ingredient.**  Under full locality
(every gate single-territory), no gate serves two copies.  So the `> ½`-collision is contradicted by
disjointness ONLY together with bounded reach — which is `cost_super`. -/
theorem local_forbids_collision {k b n : ℕ} (C : EntangledTower k b n) (hall : AllLocal C) (g : ℕ) :
    ¬ ServesTwoCopies C g := by
  rintro ⟨i, j, hij, hi, hj⟩
  exact local_circuit_no_cross_sharing C hall i j hij g ⟨hi, hj⟩

end PallLean.Paper93.DeepMath.PathB.SeamDisjointnessProbe

#print axioms PallLean.Paper93.DeepMath.PathB.SeamDisjointnessProbe.straddle_gate_serves_two
#print axioms PallLean.Paper93.DeepMath.PathB.SeamDisjointnessProbe.disjoint_admits_collision
#print axioms PallLean.Paper93.DeepMath.PathB.SeamDisjointnessProbe.straddle_beats_disjoint_bound
#print axioms PallLean.Paper93.DeepMath.PathB.SeamDisjointnessProbe.collision_bounded_by_reach
#print axioms PallLean.Paper93.DeepMath.PathB.SeamDisjointnessProbe.local_forbids_collision
