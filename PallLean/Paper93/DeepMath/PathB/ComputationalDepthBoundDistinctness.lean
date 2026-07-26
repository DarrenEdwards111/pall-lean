import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# Bounding the distinctness, in a restricted case: private witnesses

`WhatSurvives` reduced the wall to one quantity: the **distinctness** `|⋃ wᵢ|` — the number of distinct
witness gates.  Bounding it below (proving it large) recovers the lower bound.  Here we bound it in a
restricted case: when each block keeps a set of **private** witness gates — gates *unique* to that block,
that sharing cannot collapse — the distinctness is at least `k·p`.

**The idea.**  Suppose each block `i` has a private witness set `privᵢ ⊆ wᵢ` of size `≥ p`, and the private
sets are pairwise disjoint (private = unique to block `i`).  Then the `k` private sets are `k·p` distinct
gates, so `|gates| ≥ k·p`.  The sharing can pile up on the *non-private* parts all it likes — the private
gates stay distinct, and they alone force the bound.

## What is proved

* **`distinctness_bounded`** — with `p` private witness gates per block (disjoint across blocks),
  `k·p ≤ |gates|`.  The distinctness is bounded below by `k·p`.
* **`oneBlockCircuit`** — non-vacuous.

## Honest scope — the private part is the bound; driving it to zero on SAT is cost_super

This genuinely bounds the distinctness: `|gates| ≥ k·p` whenever each block retains `p` private (unshared)
witnesses.  It interpolates the whole range — `p = b` (fully private, no sharing) recovers the disjoint
`k·b`; `p = 1` still gives `≥ k`; and any bounded sharing that leaves `p` private gates per block gives `k·p`.

The one restriction is that the private part `p` is **fixed and positive** — each block keeps `p` witnesses
sharing can't reach.  SAT's composition tower lets the adversary **share freely**, driving the private part
`p` toward `0` (every witness reused across blocks, nothing private left).  Proving each block *must* retain
`p` private witnesses under unbounded sharing — that the circuit *cannot* make everything shared — is exactly
`cost_super`.  So the distinctness is bounded by the private part in the restricted (fixed-`p`) case;
proving the private part survives unbounded sharing is the single wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundDistinctness

open scoped BigOperators

/-- A circuit where each block keeps `p` **private** witness gates: `priv i ⊆ gates`, size `≥ p`, pairwise
disjoint (unique to each block — sharing cannot collapse them). -/
structure CircuitWithPrivate (k p : ℕ) where
  /-- the gates -/
  gates : Finset ℕ
  /-- block `i`'s private witness gates -/
  priv : Fin k → Finset ℕ
  /-- private witnesses are real gates -/
  priv_sub : ∀ i, priv i ⊆ gates
  /-- each block keeps at least `p` private witnesses -/
  priv_size : ∀ i, p ≤ (priv i).card
  /-- private = unique to the block: the private sets are pairwise disjoint -/
  priv_disjoint : ∀ i j, i ≠ j → Disjoint (priv i) (priv j)

/-- **The distinctness is bounded below (proved).**  With `p` private witness gates per block, pairwise
disjoint, the circuit has at least `k·p` gates: `k·p ≤ |gates|`.  The private sets are `k·p` distinct gates,
and sharing on the rest cannot touch them. -/
theorem distinctness_bounded {k p : ℕ} (C : CircuitWithPrivate k p) : k * p ≤ C.gates.card := by
  have hsub : (Finset.univ.biUnion C.priv) ⊆ C.gates := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact C.priv_sub i hxi
  have hcard : (Finset.univ.biUnion C.priv).card = ∑ i, (C.priv i).card :=
    Finset.card_biUnion (fun i _ j _ hij => C.priv_disjoint i j hij)
  have hconst : (∑ _i : Fin k, p) = k * p := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  calc k * p = ∑ _i : Fin k, p := hconst.symm
    _ ≤ ∑ i, (C.priv i).card := Finset.sum_le_sum (fun i _ => C.priv_size i)
    _ = (Finset.univ.biUnion C.priv).card := hcard.symm
    _ ≤ C.gates.card := Finset.card_le_card hsub

/-- **Non-vacuous (proved).**  One block with `2` private gates `{0,1}` — distinctness `2 ≤ 2`. -/
def oneBlockCircuit : CircuitWithPrivate 1 2 where
  gates := {0, 1}
  priv := fun _ => {0, 1}
  priv_sub := fun _ => Finset.Subset.refl _
  priv_size := fun _ => by decide
  priv_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij

end PallLean.Paper93.DeepMath.PathB.BoundDistinctness

#print axioms PallLean.Paper93.DeepMath.PathB.BoundDistinctness.distinctness_bounded
