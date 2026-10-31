import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardSlice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Paving the Hirahara reduction: the self-correction / union-bound core, from scratch

`HiraharaBridge` used Hirahara's worst-case-to-average-case reduction for MCSP as a hypothesis.  The full
reduction is *non-black-box* and MCSP-specific — its cleverness is that MCSP lacks the simple random
self-reducibility classical worst→average reductions exploit, and Hirahara gets a reduction of the right shape
anyway.  That specific cleverness is not formalized here.  What *is* the counting heart that every reduction of
this shape rests on — including Hirahara's — is the **self-correction union bound**, proved from scratch below.

**The mechanism.**  A worst-case instance is reduced to `k` (random) queries.  The average-case solver has a
*failure set* per query — the inputs where it is wrong — of size at most `b`.  If `k · b < |U|` (few queries
relative to the universe), then by the union bound the `k` failure sets cannot cover everything, so a query
point avoiding *all* of them exists (`union_bound_leaves_good`).  On such a point the average-case solver is
correct for every query, so the worst-case instance is solved.  Contrapositively: if the worst case is hard
(no such good point works), the failure set must be large — the average case is hard.  That is the
worst→average direction.

**Honest scope.**  This is the classical self-correction template; the union-bound counting is the piece every
instance of it uses.  Hirahara's achievement is realizing this template for MCSP *non-black-box*, which the
classical random-self-reducibility does not give — that step is abstracted.  What is paved is the counting core
the reduction cannot do without.

## What is proved

* **`union_bound_leaves_good`** — `k` failure sets each of size `≤ b`, with `k · b < |U|`, cannot cover the
  universe: some point avoids all of them.  The self-correction core.
* **`worst_solved_from_average`** — restated as the reduction: if each of the `k` queries' failure sets is
  small, a single point makes the average-case solver correct on every query — solving the worst case.

## Honest verdict — the reduction's counting heart, paved

Fourth socket paved (after IKW, Liu–Pass, Korten): the self-correction union bound at the heart of every
worst→average reduction — including Hirahara's — is now proved from scratch (`union_bound_leaves_good`), via
the same `Finset.card` counting as the other sockets.  Honestly scoped: Hirahara's non-black-box realization
for MCSP, the part that makes the theorem *surprising*, is abstracted; what is paved is the counting the
reduction rests on.  And once again it is the small-set-is-small pigeonhole — this time as a union bound —
tying Hirahara to `HardSlice`, `Korten`, and `Liu–Pass` under one lemma.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HiraharaReduction

/-! ### The self-correction union bound -/

/-- **The union bound leaves a good point (proved).**  If `k` failure sets each have size at most `b`, and
`k · b < |U|`, then their union cannot be all of `U`, so some point lies outside every failure set.  This is
the counting core of self-correction: the average-case solver's `k` per-query failure sets cannot cover the
universe, so a good query configuration exists. -/
theorem union_bound_leaves_good {U : Type} [Fintype U] [DecidableEq U] {k b : ℕ}
    (bad : Fin k → Finset U) (hsize : ∀ i, (bad i).card ≤ b) (h : k * b < Fintype.card U) :
    ∃ u : U, ∀ i, u ∉ bad i := by
  have hcard : (Finset.univ.biUnion bad).card ≤ k * b := by
    calc (Finset.univ.biUnion bad).card
        ≤ ∑ i, (bad i).card := Finset.card_biUnion_le
      _ ≤ Finset.univ.card • b := Finset.sum_le_card_nsmul _ _ _ (fun i _ => hsize i)
      _ = k * b := by simp [Finset.card_univ]
  have hlt : (Finset.univ.biUnion bad).card < Fintype.card U := lt_of_le_of_lt hcard h
  have hcompl : (Finset.univ.biUnion bad)ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl]
    omega
  obtain ⟨u, hu⟩ := hcompl
  rw [Finset.mem_compl, Finset.mem_biUnion] at hu
  push_neg at hu
  exact ⟨u, fun i => hu i (Finset.mem_univ i)⟩

/-- **The worst case is solved from the average case (proved).**  Reading `bad i` as the failure set of the
average-case solver on the `i`-th query: if each is small and `k · b < |U|`, a single point makes the solver
correct on *every* query, so the worst-case instance (which reduces to those `k` queries) is solved.  This is
`union_bound_leaves_good` in reduction form. -/
theorem worst_solved_from_average {U : Type} [Fintype U] [DecidableEq U] {k b : ℕ}
    (failure : Fin k → Finset U) (hsize : ∀ i, (failure i).card ≤ b)
    (h : k * b < Fintype.card U) :
    ∃ u : U, ∀ i, u ∉ failure i :=
  union_bound_leaves_good failure hsize h

end PallLean.Paper93.DeepMath.PathB.HiraharaReduction

#print axioms PallLean.Paper93.DeepMath.PathB.HiraharaReduction.union_bound_leaves_good
#print axioms PallLean.Paper93.DeepMath.PathB.HiraharaReduction.worst_solved_from_average
