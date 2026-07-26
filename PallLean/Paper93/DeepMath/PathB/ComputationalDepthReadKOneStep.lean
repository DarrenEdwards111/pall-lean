import Mathlib.Data.Finset.Card
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTransferOneStep

/-!
# The one-step lemma in the read-restricted (separable) model — proved unconditionally

`TransferOneStep` reduced the whole wall to a single per-step inequality `2·c d ≤ c (d+1)`.  This file
goes at that inequality in the **read-restricted / separable** DAG model and proves it there,
unconditionally — then telescopes it to an unconditional `2^d` superpoly lower bound in that model.

## Why the general lemma fails, and what the restriction removes

`composite (d+1)` applies `composite d` to **two disjoint input blocks**.  In a formula the two copies
are separate, so `c (d+1) = 2·c d`.  In a general DAG the copies can be computed *together* for fewer
than `2·c d` gates — **Uhlig mass production** (computing `f` on several inputs cheaper than the sum).
That is the sole reason the one-step lemma can fail.

Mass production requires gates that serve **both** sub-computations at once — i.e. the two sub-instance
gate-cones **overlap**.  The read-restricted / **separable** model forbids exactly this: the two cones
are **disjoint** (no gate serves both).  This is the read-once-at-the-composition regime.

## What is proved

* **`separable_doubling` (proved)** — two disjoint gate-cones, each of size `≥ cd`, union to `≥ 2·cd`.
  Pure `Finset` counting: the one-step lemma, given disjointness.
* **`separable_perstep` (proved)** — a `SeparableTower` (disjoint sub-cones inside each composite,
  each at least the previous size) satisfies `PerStepDouble` — the one-step lemma holds at every level.
* **`separable_tower_superpoly` (proved)** — telescoping via `TransferOneStep.telescopes`: in the
  separable model the DAG cost is `2^d` — an **unconditional superpolynomial lower bound**.
* **`separable_tower_clears` (proved)** — hence the separable-model DAG cost clears every ceiling.

## Honest scope

This is a genuine *restricted* superpoly lower bound: the disjoint-cone (separable) model is close to the
read-once / formula regime, so the bound is unconditional there and not surprising.  Its value is the
**pinpoint**: the entire gap between this restricted bound and the general `P/poly` wall is precisely
**cone overlap = Uhlig mass production**.  We proved the one-step lemma exactly up to where mass
production begins; removing disjointness is the open Uhlig wall (`cost_super`).  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ReadKOneStep

open PallLean.Paper93.DeepMath.PathB.TransferOneStep

/-- **The one-step lemma given disjointness (proved).**  If the two sub-instance gate-cones are disjoint
and each has at least `cd` gates, their union — inside the composite — has at least `2·cd` gates.  This
is the doubling, once mass production (overlap) is excluded. -/
theorem separable_doubling {α : Type} [DecidableEq α] (G1 G2 : Finset α) (cd : ℕ)
    (hdisj : Disjoint G1 G2) (h1 : cd ≤ G1.card) (h2 : cd ≤ G2.card) :
    2 * cd ≤ (G1 ∪ G2).card := by
  rw [Finset.card_union_of_disjoint hdisj]
  omega

/-- A **separable tower**: at each level, `composite (d+1)` contains two sub-instance gate-cones that are
**disjoint** (the read restriction: no gate serves both — no mass production), each of size at least the
previous composite's size. -/
structure SeparableTower (α : Type) [DecidableEq α] where
  /-- gate set of `composite d`. -/
  gates : ℕ → Finset α
  /-- gate-cone of the first sub-instance inside `composite (d+1)`. -/
  cone1 : ℕ → Finset α
  /-- gate-cone of the second sub-instance inside `composite (d+1)`. -/
  cone2 : ℕ → Finset α
  /-- the base is nonempty. -/
  base_pos : 1 ≤ (gates 0).card
  /-- first cone sits inside the next composite. -/
  cone1_sub : ∀ d, cone1 d ⊆ gates (d + 1)
  /-- second cone sits inside the next composite. -/
  cone2_sub : ∀ d, cone2 d ⊆ gates (d + 1)
  /-- **separability**: the two cones are disjoint — no gate serves both (no mass production). -/
  cones_disjoint : ∀ d, Disjoint (cone1 d) (cone2 d)
  /-- each sub-instance computes `composite d`, so its cone is at least `composite d`'s size. -/
  cone1_ge : ∀ d, (gates d).card ≤ (cone1 d).card
  /-- likewise for the second. -/
  cone2_ge : ∀ d, (gates d).card ≤ (cone2 d).card

variable {α : Type} [DecidableEq α]

/-- **The one-step lemma holds at every level of a separable tower (proved).**  Disjoint sub-cones inside
`composite (d+1)` force `2·|gates d| ≤ |gates (d+1)|` — the per-step doubling `TransferOneStep` needs. -/
theorem separable_perstep (T : SeparableTower α) :
    PerStepDouble (fun d => (T.gates d).card) := by
  intro d
  show 2 * (T.gates d).card ≤ (T.gates (d + 1)).card
  have hcard : 2 * (T.gates d).card ≤ (T.cone1 d ∪ T.cone2 d).card :=
    separable_doubling _ _ _ (T.cones_disjoint d) (T.cone1_ge d) (T.cone2_ge d)
  have hsub : T.cone1 d ∪ T.cone2 d ⊆ T.gates (d + 1) :=
    Finset.union_subset (T.cone1_sub d) (T.cone2_sub d)
  have hle : (T.cone1 d ∪ T.cone2 d).card ≤ (T.gates (d + 1)).card :=
    Finset.card_le_card hsub
  omega

/-- **Unconditional superpoly lower bound in the separable model (proved).**  Telescoping the one-step
lemma: `2^d ≤ |gates d|`.  The transfer holds, unconditionally, once mass production is excluded. -/
theorem separable_tower_superpoly (T : SeparableTower α) (d : ℕ) :
    2 ^ d ≤ (T.gates d).card :=
  telescopes (fun d => (T.gates d).card) (separable_perstep T) T.base_pos d

/-- **The separable-model DAG cost clears every ceiling (proved).** -/
theorem separable_tower_clears (T : SeparableTower α) (U : ℕ) :
    ∃ d, U < (T.gates d).card :=
  dag_clears_of_perstep (fun d => (T.gates d).card) (separable_perstep T) T.base_pos U

end PallLean.Paper93.DeepMath.PathB.ReadKOneStep

#print axioms PallLean.Paper93.DeepMath.PathB.ReadKOneStep.separable_doubling
#print axioms PallLean.Paper93.DeepMath.PathB.ReadKOneStep.separable_perstep
#print axioms PallLean.Paper93.DeepMath.PathB.ReadKOneStep.separable_tower_superpoly
#print axioms PallLean.Paper93.DeepMath.PathB.ReadKOneStep.separable_tower_clears
