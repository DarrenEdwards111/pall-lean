import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4WeightRepr

/-!
# Layer 4 (Route A, piece 3 — intersection bookkeeping)

To run the `q` residue-indicator circuits together, their agreement sets `G_0,…,G_{q-1}` must be combined
into a single set `G = ⋂_{j<q} G_j` on which *every* indicator approximant is valid (this `G` is the
`(Finset.range q).inf A` fed to `qary_reduction_from_indicators`).  The union bound:
\[
  |⋂_{j<q} G_j| \;\ge\; 2^n - \sum_{j<q}|G_j^c| ,
\]
so if each complement is small enough — `|G_j^c| ≤ 2^n/(4q)`, i.e. `4q·|G_j^c| ≤ 2^n` — then
`|⋂ G_j| ≥ (3/4)·2^n`, the `(3/4)`-fraction the Smolensky contradiction (`dim_contradiction_general`)
needs.  `inter_three_quarters` proves exactly this, sorry-free.

The per-set hypothesis `4q·|G_j^c| ≤ 2^n` is the **tight** agreement bound: it is what a parameterised
`exists_large_agreement_set` delivers under the tighter horizon `p^t ≥ 4q·s` (the only difference from the
existing `p^t ≥ 4·s ⇒ 3·2^n ≤ 4·|G_j|` is the constant `4 ↦ 4q`, tracing through the same
`|cbad| ≤ s·2^n/p^t` error count).  That parameterisation is the last remaining ingredient; the
combinatorial bookkeeping it feeds is done here.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open Finset

/-- **Intersection bookkeeping.**  If each of the `q` agreement sets `A j` has a complement small enough
(`4q·|(A j)^c| ≤ 2^n`), then their intersection `⋂_{j<q} A j` (= `(range q).inf A`) covers a `(3/4)`-fraction:
`3·2^n ≤ 4·|⋂_{j<q} A j|` — exactly `dim_contradiction_general`'s size hypothesis. -/
theorem inter_three_quarters (q : ℕ) (hq : 0 < q) {n : ℕ} (A : ℕ → Finset (Fin n → Bool))
    (hG : ∀ j ∈ Finset.range q, 4 * q * (Finset.univ \ A j).card ≤ 2 ^ n) :
    3 * 2 ^ n ≤ 4 * ((Finset.range q).inf A).card := by
  -- Union bound: the complement of the intersection is contained in the union of the complements.
  have hsub : (Finset.univ \ (Finset.range q).inf A)
      ⊆ (Finset.range q).biUnion (fun j => Finset.univ \ A j) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_biUnion]
    by_contra hcon
    push_neg at hcon
    apply hx.2
    rw [Finset.mem_inf]
    intro j hj
    have hxj := hcon j hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hxj
    exact hxj
  have hcard : (Finset.univ \ (Finset.range q).inf A).card
      ≤ ∑ j ∈ Finset.range q, (Finset.univ \ A j).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  -- `4·∑ |G_jᶜ| ≤ 2^n` from the per-set bound `4q·|G_jᶜ| ≤ 2^n` (sum over `q` terms, cancel `q`).
  have key : 4 * q * ∑ j ∈ Finset.range q, (Finset.univ \ A j).card ≤ q * 2 ^ n := by
    rw [Finset.mul_sum]
    calc ∑ j ∈ Finset.range q, 4 * q * (Finset.univ \ A j).card
        ≤ ∑ j ∈ Finset.range q, 2 ^ n := Finset.sum_le_sum (fun j hj => hG j hj)
      _ = q * 2 ^ n := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hsum : 4 * ∑ j ∈ Finset.range q, (Finset.univ \ A j).card ≤ 2 ^ n :=
    Nat.le_of_mul_le_mul_left
      (by rw [show q * (4 * ∑ j ∈ Finset.range q, (Finset.univ \ A j).card)
                = 4 * q * ∑ j ∈ Finset.range q, (Finset.univ \ A j).card from by ring]; exact key) hq
  have h4c : 4 * (Finset.univ \ (Finset.range q).inf A).card ≤ 2 ^ n :=
    le_trans (mul_le_mul_left' hcard 4) hsum
  have huniv : Fintype.card (Fin n → Bool) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have htot : (Finset.univ \ (Finset.range q).inf A).card + ((Finset.range q).inf A).card = 2 ^ n := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, huniv]
  omega

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.inter_three_quarters
