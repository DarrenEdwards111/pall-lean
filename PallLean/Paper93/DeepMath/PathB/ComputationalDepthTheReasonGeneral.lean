import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# Can we apply the reason to the unrestricted case? No — and here is exactly why

`the_reason` proved `k·b ≤ |gates(C)|` for the **disjoint** target, for arbitrary `C`.  The question: can we
drop the disjointness and apply it in general?  **No.**  The disjoint proof used, as its one load-bearing
step, that pairwise-disjoint sets have `|⋃ wᵢ| = Σ|wᵢ|`.  In the **unrestricted** case the witness sets may
**overlap** (a single gate witnessing several blocks — sharing), and then `|⋃ wᵢ| < Σ|wᵢ|`: the union is
smaller than the sum by exactly the overlap.

So the general reason gives only `k·b ≤ |gates| + overlap`, not `k·b ≤ |gates|`.  The `overlap` term is the
sharing; it is `0` iff the witnesses are disjoint; and bounding it on SAT's shared tower is `cost_super`.

## What is proved

* **`the_reason_general`** — for *any* circuit (no disjointness), `k·b ≤ |gates| + overlap`.  The reason
  degrades by exactly the overlap.
* **`disjoint_recovers`** — with `overlap = 0` (disjoint), it recovers `the_reason`: `k·b ≤ |gates|`.
* **`overlap_collapses`** — the general bound genuinely fails: a circuit whose witnesses *totally* overlap
  has `|gates| = b < k·b`.  So `the_reason` cannot be applied unrestricted — `k·b ≤ |gates|` is *false*
  there.

## Honest scope — the overlap term is the wall

Applying the reason to the unrestricted case does not give `k·b ≤ |gates|`; it gives `k·b ≤ |gates| +
overlap`, and `overlap_collapses` shows the extra term is real — with full sharing the true lower bound
drops from `k·b` all the way to `b`.  To recover `k·b` you must force `overlap` small — no cross-block
witness sharing — which is exactly the disjoint (restricted) hypothesis.  For SAT's composition tower, whose
copies share inputs, bounding the overlap is `cost_super`.  So: the reason is proved for disjoint witnesses;
it **cannot** be transferred to overlapping witnesses without proving the overlap bounded, and that is the
single wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TheReasonGeneral

open scoped BigOperators

/-- A circuit computing the `k`-block target, **without** disjointness — the witness sets may overlap. -/
structure GeneralCircuit (k b : ℕ) where
  /-- the gates -/
  gates : Finset ℕ
  /-- block `i`'s witness gates (may overlap across blocks) -/
  witness : Fin k → Finset ℕ
  /-- each block's witnesses are real gates -/
  wit_sub : ∀ i, witness i ⊆ gates
  /-- each block needs at least `b` witness gates -/
  wit_size : ∀ i, b ≤ (witness i).card

/-- The **overlap** (sharing): how much the sum of witness sizes exceeds their union — `0` iff disjoint. -/
def overlap {k b : ℕ} (C : GeneralCircuit k b) : ℕ :=
  (∑ i, (C.witness i).card) - (Finset.univ.biUnion C.witness).card

/-- **The general reason (proved).**  Without disjointness, the reason degrades by exactly the overlap:
`k·b ≤ |gates| + overlap`.  The union of witnesses can be smaller than the sum by the overlap, so the bound
on `|gates|` alone is only `k·b − overlap`. -/
theorem the_reason_general {k b : ℕ} (C : GeneralCircuit k b) :
    k * b ≤ C.gates.card + overlap C := by
  have hsub : (Finset.univ.biUnion C.witness) ⊆ C.gates := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact C.wit_sub i hxi
  have hle : (Finset.univ.biUnion C.witness).card ≤ ∑ i, (C.witness i).card := Finset.card_biUnion_le
  have hconst : (∑ _i : Fin k, b) = k * b := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  have hsum : k * b ≤ ∑ i, (C.witness i).card := by
    rw [← hconst]
    exact Finset.sum_le_sum (fun i _ => C.wit_size i)
  have hgates : (Finset.univ.biUnion C.witness).card ≤ C.gates.card := Finset.card_le_card hsub
  have hover : overlap C = (∑ i, (C.witness i).card) - (Finset.univ.biUnion C.witness).card := rfl
  omega

/-- **Disjoint recovers the full reason (proved).**  With no overlap (`overlap = 0`, disjoint witnesses),
`k·b ≤ |gates|` — exactly `the_reason`. -/
theorem disjoint_recovers {k b : ℕ} (C : GeneralCircuit k b) (h0 : overlap C = 0) :
    k * b ≤ C.gates.card := by
  have h := the_reason_general C
  omega

/-- A circuit whose two witness sets **totally overlap** — both are `{0,1,2}`. -/
def collapsedCircuit : GeneralCircuit 2 3 where
  gates := {0, 1, 2}
  witness := fun _ => {0, 1, 2}
  wit_sub := fun _ => Finset.Subset.refl _
  wit_size := fun _ => by decide

/-- **The general bound genuinely fails (proved).**  Under total witness overlap, `|gates| = 3 < 6 = k·b`.
So `the_reason`'s conclusion `k·b ≤ |gates|` is **false** for the unrestricted circuit — it cannot be
applied there.  (Only `k·b ≤ |gates| + overlap` survives, and here `overlap = 3` makes up the difference.) -/
theorem overlap_collapses : collapsedCircuit.gates.card < 2 * 3 := by decide

end PallLean.Paper93.DeepMath.PathB.TheReasonGeneral

#print axioms PallLean.Paper93.DeepMath.PathB.TheReasonGeneral.the_reason_general
#print axioms PallLean.Paper93.DeepMath.PathB.TheReasonGeneral.overlap_collapses
