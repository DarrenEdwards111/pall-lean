import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max

/-!
# The reason with overlapping witnesses — what survives

`TheReason` proved the body of the `∀` in the disjoint case: any circuit for the `k`-block disjoint
target has `≥ k·b` gates, because the per-block witness sets are pairwise disjoint and disjoint sets
add.  SAT's tower shares inputs, so witnesses may OVERLAP.  Here we drop `wit_disjoint` entirely and
prove exactly what survives — and exhibit what provably does not.

## The accounting that survives: multiplicity

Define `mult g` = the number of blocks gate `g` witnesses.  The double-counting identity
(`incidence_count`) is unconditional: `Σᵢ |wᵢ| = Σ_{g ∈ gates} mult g` — witness mass is conserved;
sharing never destroys it, it only CONCENTRATES it.  Everything below is that identity read in
different directions.

* **`floor_survives`** — `b ≤ |gates|`: the single-block bound survives; the `k`-multiplier is what
  is at risk.
* **`the_reason_shared`** — the pro-rata bound: if every gate witnesses `≤ r` blocks, then
  `k·b ≤ r·|gates|`.  The reason survives DIVIDED BY the sharing multiplicity.
* **`disjoint_case_recovered`** — `r = 1` is exactly the old theorem: disjoint witnesses have
  `mult ≤ 1` (`mult_le_one_of_disjoint`), and the pro-rata bound at `r = 1` is `k·b ≤ |gates|`.
  `TheReason` is the multiplicity-one slice of this file.
* **`pigeonhole_shared_gate`** — the dual reading, with NO multiplicity hypothesis: every circuit
  contains a gate `g₀` with `k·b ≤ mult g₀ · |gates|`.  A SMALL circuit is forced to contain a HUB —
  a single gate witnessing `≥ k·b/|gates|` blocks at once.  Cheapness does not evade the witness
  mass; it concentrates it into god-gates (cf. `GodMoveFace`).
* **`graded_survivor`** — the handoff-facing form: sharing bounded `D`-fold below the block count
  (`r·D ≤ k`) leaves a `D`-fold bound `D·b ≤ |gates|`.  This is the graceful-degradation direction
  the Route 2 ⟶ Route 4 handoff needs: magnification does not need NO sharing, only sharing that
  falls short of total by a factor.

## What provably does NOT survive

* **`collapse_disjoint_bound_fails`** — with full overlap the `k`-multiplier is genuinely lost, not
  unproved: `collapseWitness` has `k = 3` blocks, `b = 3`, all witness sets EQUAL — `|gates| = 3 < 9`,
  and every gate has `mult = 3 = k` (`collapse_mult_full`).  Without a multiplicity bound, nothing
  beyond the floor `b` is true.

## Honest scope — the wall, now quantitative

The unconditional survivors are the floor and the pigeonhole; the `k`-multiplier survives exactly
pro rata to `r`.  So the single remaining wall has a PARAMETER: `cost_super` for the tower is
precisely the claim that no small circuit sustains multiplicity `≈ k` — i.e. bounding `r` IS
Uhlig/no-sharing.  This file does not bound `r` (that is the open content); it proves that `r` is
the only thing left to bound, and that the price of not bounding it is concentration into hub
gates, not escape.  As in `TheReason`, per-block witness counts enter as structure fields; the
proved content is the aggregation.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TheReasonShared

open scoped BigOperators

/-- A circuit computing the `k`-block target with SHARED inputs: gates, and for each block a set of
witness gates (`⊆ gates`, size `≥ b`) — with NO disjointness requirement.  One gate may witness many
blocks. -/
structure SharedCircuitForTarget (k b : ℕ) where
  /-- the gates of the circuit -/
  gates : Finset ℕ
  /-- block `i`'s witness gates -/
  witness : Fin k → Finset ℕ
  /-- each block's witnesses are real gates -/
  wit_sub : ∀ i, witness i ⊆ gates
  /-- each block needs at least `b` witness gates -/
  wit_size : ∀ i, b ≤ (witness i).card

/-- The **sharing multiplicity** of a gate: how many blocks it witnesses. -/
def mult {k b : ℕ} (C : SharedCircuitForTarget k b) (g : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter (fun i => g ∈ C.witness i)).card

/-- A block's witness count, as an indicator sum over the gates. -/
theorem witness_card_as_sum {k b : ℕ} (C : SharedCircuitForTarget k b) (i : Fin k) :
    (C.witness i).card = ∑ g ∈ C.gates, (if g ∈ C.witness i then 1 else 0) := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr (C.wit_sub i), ← Finset.card_eq_sum_ones]

/-- A gate's multiplicity, as an indicator sum over the blocks. -/
theorem mult_as_sum {k b : ℕ} (C : SharedCircuitForTarget k b) (g : ℕ) :
    mult C g = ∑ i : Fin k, (if g ∈ C.witness i then 1 else 0) := by
  rw [mult, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- **Witness mass is conserved (proved, unconditional).**  Double counting the block–gate
incidences: `Σᵢ |wᵢ| = Σ_g mult g`.  Sharing never destroys witness mass — it concentrates it. -/
theorem incidence_count {k b : ℕ} (C : SharedCircuitForTarget k b) :
    (∑ i, (C.witness i).card) = ∑ g ∈ C.gates, mult C g := by
  calc (∑ i, (C.witness i).card)
      = ∑ i : Fin k, ∑ g ∈ C.gates, (if g ∈ C.witness i then 1 else 0) :=
        Finset.sum_congr rfl (fun i _ => witness_card_as_sum C i)
    _ = ∑ g ∈ C.gates, ∑ i : Fin k, (if g ∈ C.witness i then 1 else 0) := Finset.sum_comm
    _ = ∑ g ∈ C.gates, mult C g :=
        Finset.sum_congr rfl (fun g _ => (mult_as_sum C g).symm)

/-- The total witness demand `k·b` is under the witness mass (each block supplies `≥ b`). -/
theorem kb_le_witness_sum {k b : ℕ} (C : SharedCircuitForTarget k b) :
    k * b ≤ ∑ i, (C.witness i).card := by
  have hconst : (∑ _i : Fin k, b) = k * b := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  calc k * b = ∑ _i : Fin k, b := hconst.symm
    _ ≤ ∑ i, (C.witness i).card := Finset.sum_le_sum (fun i _ => C.wit_size i)

/-- **The floor survives (proved).**  One block already forces `b ≤ |gates|`.  What sharing
threatens is only the `k`-multiplier. -/
theorem floor_survives {k b : ℕ} (C : SharedCircuitForTarget k b) (hk : 1 ≤ k) :
    b ≤ C.gates.card :=
  le_trans (C.wit_size ⟨0, hk⟩) (Finset.card_le_card (C.wit_sub ⟨0, hk⟩))

/-- **The pro-rata survivor (proved).**  If every gate witnesses at most `r` blocks, the reason
survives divided by `r`: `k·b ≤ r·|gates|`.  At `r = 1` this is `TheReason.the_reason`; at `r = k`
it degenerates to the floor.  The sharing multiplicity is EXACTLY the exchange rate between the
disjoint bound and the truth. -/
theorem the_reason_shared {k b : ℕ} (C : SharedCircuitForTarget k b) (r : ℕ)
    (hr : ∀ g ∈ C.gates, mult C g ≤ r) : k * b ≤ r * C.gates.card := by
  have h1 : k * b ≤ ∑ g ∈ C.gates, mult C g := by
    rw [← incidence_count]; exact kb_le_witness_sum C
  have h2 : ∑ g ∈ C.gates, mult C g ≤ C.gates.card • r :=
    Finset.sum_le_card_nsmul C.gates (mult C) r hr
  have h3 : C.gates.card • r = r * C.gates.card := by
    have hsm : C.gates.card • r = C.gates.card * r := by simp
    rw [hsm, Nat.mul_comm]
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

/-- The pro-rata bound at multiplicity `1`. -/
theorem the_reason_r_one {k b : ℕ} (C : SharedCircuitForTarget k b)
    (hr : ∀ g ∈ C.gates, mult C g ≤ 1) : k * b ≤ C.gates.card := by
  have h := the_reason_shared C 1 hr
  rwa [Nat.one_mul] at h

/-- Disjoint witnesses have multiplicity `≤ 1`: no gate can lie in two disjoint sets. -/
theorem mult_le_one_of_disjoint {k b : ℕ} (C : SharedCircuitForTarget k b)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C.witness i) (C.witness j)) (g : ℕ) :
    mult C g ≤ 1 := by
  by_contra hgt
  have h2 : 1 < mult C g := by omega
  rw [mult] at h2
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h2
  rw [Finset.mem_filter] at hi hj
  exact (Finset.disjoint_left.mp (hdisj i j hij) hi.2) hj.2

/-- **The old reason is the `r = 1` slice (proved).**  `TheReason.the_reason` re-derived inside the
shared framework: disjointness ⟹ multiplicity `≤ 1` ⟹ the full `k·b` bound. -/
theorem disjoint_case_recovered {k b : ℕ} (C : SharedCircuitForTarget k b)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C.witness i) (C.witness j)) :
    k * b ≤ C.gates.card :=
  the_reason_r_one C (fun g _ => mult_le_one_of_disjoint C hdisj g)

/-- **The pigeonhole dual (proved, NO multiplicity hypothesis).**  Every circuit for the target
contains a hub gate `g₀` with `k·b ≤ mult g₀ · |gates|`.  A small circuit does not evade the
witness mass — it is forced to concentrate it: `|gates| ≤ G` forces a gate witnessing `≥ k·b/G`
blocks simultaneously. -/
theorem pigeonhole_shared_gate {k b : ℕ} (C : SharedCircuitForTarget k b)
    (hk : 1 ≤ k) (hb : 1 ≤ b) :
    ∃ g ∈ C.gates, k * b ≤ mult C g * C.gates.card := by
  have hwne : (C.witness ⟨0, hk⟩).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le hb (C.wit_size ⟨0, hk⟩))
  obtain ⟨g1, hg1⟩ := hwne
  have hgne : C.gates.Nonempty := ⟨g1, C.wit_sub ⟨0, hk⟩ hg1⟩
  obtain ⟨g₀, hg₀, hmax⟩ := Finset.exists_max_image C.gates (mult C) hgne
  refine ⟨g₀, hg₀, ?_⟩
  have h1 : k * b ≤ ∑ g ∈ C.gates, mult C g := by
    rw [← incidence_count]; exact kb_le_witness_sum C
  have h2 : ∑ g ∈ C.gates, mult C g ≤ C.gates.card • mult C g₀ :=
    Finset.sum_le_card_nsmul C.gates (mult C) (mult C g₀) hmax
  have h3 : C.gates.card • mult C g₀ = mult C g₀ * C.gates.card := by
    have hsm : C.gates.card • mult C g₀ = C.gates.card * mult C g₀ := by simp
    rw [hsm, Nat.mul_comm]
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

/-- **The graded survivor (proved)** — the handoff-facing form.  Sharing bounded `D`-fold below the
block count (`r·D ≤ k`) leaves a `D`-fold bound: `D·b ≤ |gates|`.  Magnification does not need
sharing to be absent, only to fall short of total by a factor — this is that statement. -/
theorem graded_survivor {k b : ℕ} (C : SharedCircuitForTarget k b) (r D : ℕ) (hr1 : 1 ≤ r)
    (hshare : ∀ g ∈ C.gates, mult C g ≤ r) (hgap : r * D ≤ k) :
    D * b ≤ C.gates.card := by
  have h := the_reason_shared C r hshare
  have h2 : r * (D * b) ≤ r * C.gates.card := by
    calc r * (D * b) = r * D * b := (Nat.mul_assoc r D b).symm
      _ ≤ k * b := Nat.mul_le_mul_right b hgap
      _ ≤ r * C.gates.card := h
  exact Nat.le_of_mul_le_mul_left h2 hr1

/-! ### The collapse is real: full overlap attains the floor -/

/-- Full overlap: `3` blocks, all witness sets EQUAL, `3` gates in total. -/
def collapseWitness : SharedCircuitForTarget 3 3 where
  gates := {0, 1, 2}
  witness := fun _ => {0, 1, 2}
  wit_sub := fun _ => Finset.Subset.refl _
  wit_size := fun _ => by decide

/-- The collapsed circuit has only `b = 3` gates … -/
theorem collapse_card : collapseWitness.gates.card = 3 := by decide

/-- … so the disjoint bound `k·b = 9` FAILS under sharing: the `k`-multiplier is genuinely lost,
not merely unproved. -/
theorem collapse_disjoint_bound_fails : ¬ (3 * 3 ≤ collapseWitness.gates.card) := by decide

/-- … and the witness mass went nowhere: every gate is a maximal hub (`mult = 3 = k`), exactly as
the pigeonhole demands (`9 ≤ 3·3`). -/
theorem collapse_mult_full : ∀ g ∈ collapseWitness.gates, mult collapseWitness g = 3 := by decide

/-! ### The reason for all: `|gates| ≥ k·b − overlap`, for arbitrary circuits -/

/-- The **distinct witnesses**: the union of all witness sets. -/
def distinctWitnesses {k b : ℕ} (C : SharedCircuitForTarget k b) : Finset ℕ :=
  Finset.univ.biUnion C.witness

/-- The **overlap**: the double-counted witness mass — total demand minus distinct supply. -/
def overlap {k b : ℕ} (C : SharedCircuitForTarget k b) : ℕ :=
  (∑ i, (C.witness i).card) - (distinctWitnesses C).card

/-- Distinct witnesses are real gates. -/
theorem distinctWitnesses_subset {k b : ℕ} (C : SharedCircuitForTarget k b) :
    distinctWitnesses C ⊆ C.gates := by
  intro x hx
  rw [distinctWitnesses, Finset.mem_biUnion] at hx
  obtain ⟨i, _, hxi⟩ := hx
  exact C.wit_sub i hxi

/-- Inclusion–exclusion, ℕ-clean: distinct witnesses plus overlap is exactly the witness mass. -/
theorem union_card_add_overlap {k b : ℕ} (C : SharedCircuitForTarget k b) :
    (distinctWitnesses C).card + overlap C = ∑ i, (C.witness i).card :=
  Nat.add_sub_cancel' Finset.card_biUnion_le

/-- **The reason for all (proved, arbitrary circuit, no hypotheses).**
`k·b ≤ |gates| + overlap` — equivalently `|gates| ≥ k·b − overlap`: every circuit pays the full
disjoint bound EXCEPT what it double-counts.  This is a genuine `∀`-body — it holds for every `C`
with no side condition — but its strength is contingent on ONE adversary-controlled scalar:
`overlap C`.  Bounding that scalar below `k·b − (target)` for all small circuits IS `cost_super`. -/
theorem the_reason_with_overlap {k b : ℕ} (C : SharedCircuitForTarget k b) :
    k * b ≤ C.gates.card + overlap C := by
  have h1 : k * b ≤ ∑ i, (C.witness i).card := kb_le_witness_sum C
  have h2 : (distinctWitnesses C).card + overlap C = ∑ i, (C.witness i).card :=
    union_card_add_overlap C
  have h3 : (distinctWitnesses C).card ≤ C.gates.card :=
    Finset.card_le_card (distinctWitnesses_subset C)
  omega

/-- Disjoint witnesses have zero overlap … -/
theorem overlap_eq_zero_of_disjoint {k b : ℕ} (C : SharedCircuitForTarget k b)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C.witness i) (C.witness j)) :
    overlap C = 0 := by
  have hcard : (distinctWitnesses C).card = ∑ i, (C.witness i).card :=
    Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)
  rw [overlap, hcard, Nat.sub_self]

/-- … so at `overlap = 0` the reason-for-all IS the old disjoint theorem. -/
theorem disjoint_recovered_via_overlap {k b : ℕ} (C : SharedCircuitForTarget k b)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C.witness i) (C.witness j)) :
    k * b ≤ C.gates.card := by
  have h := the_reason_with_overlap C
  rw [overlap_eq_zero_of_disjoint C hdisj] at h
  omega

/-- On the full-overlap witness the bound is TIGHT: `overlap = 6` and `9 ≤ 3 + 6` exactly — the
adversary's saving is precisely its double-counting, no more. -/
theorem collapse_overlap : overlap collapseWitness = 6 := by decide

end PallLean.Paper93.DeepMath.PathB.TheReasonShared

#print axioms PallLean.Paper93.DeepMath.PathB.TheReasonShared.the_reason_shared
#print axioms PallLean.Paper93.DeepMath.PathB.TheReasonShared.pigeonhole_shared_gate
#print axioms PallLean.Paper93.DeepMath.PathB.TheReasonShared.disjoint_case_recovered
#print axioms PallLean.Paper93.DeepMath.PathB.TheReasonShared.graded_survivor
#print axioms PallLean.Paper93.DeepMath.PathB.TheReasonShared.collapse_disjoint_bound_fails
#print axioms PallLean.Paper93.DeepMath.PathB.TheReasonShared.the_reason_with_overlap
#print axioms PallLean.Paper93.DeepMath.PathB.TheReasonShared.disjoint_recovered_via_overlap
#print axioms PallLean.Paper93.DeepMath.PathB.TheReasonShared.collapse_overlap
