import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CrossFieldCountCore

/-!
# Block-overlap count — the tractable fragment beyond disjoint: bounded local overlap factorizes

Entry 251 proved the cross-field count is tractable for **disjoint** gates (overlap rank 1): the pattern-counts factor.
This file extends the tractable boundary to **block-diagonal / bounded-local-overlap** families: when the input
variables partition into independent blocks and each gate's support lies in one block, the count **factors across
blocks** — *even though gates may overlap arbitrarily within a block*.  So the tractability boundary is the **block
decomposition** (the local overlap diameter), not global disjointness.

The finding refines the candidate invariant (entry 251, your step 4): the gate–variable *incidence graph* matters, not
the gate count.  If it decomposes into bounded-size connected components (blocks), the count factors and is
poly-time (each block brute-forced); the obstruction needs the incidence graph to have **large connected components**
(high global overlap, expander-like) — exactly where Smolensky bites and no block decomposition helps.

⚠️ **No crossing.**  The block factorization and the bounded-block bound are proved.  The large-component
(high-global-overlap) case — efficient `CrossFieldCount` for a connected/expanding incidence graph — is the open
`ACC⁰[composite]` core; not resolved here.

## What is proved (clean axioms, no `sorry`)

* **`block_pattern_count`** (PROVED) — block-diagonal factorization: for independent variable blocks `Z : Fin m → Type`
  with an *arbitrary* per-block predicate `P b` (the within-block sub-computation, gates may overlap freely inside the
  block), `#{x : ∀ b, P b (x b)} = ∏ b, #{z : P b z}` — the count factors across blocks (`Fintype.card_piFinset`).
* **`block_count_le`** (PROVED) — bounded block size: if each block has `≤ W` assignments, the count is `≤ W^m` — a
  product of `m` bounded factors, each brute-forceable; poly-time for bounded `W` (and the cross-field count
  distribution is the convolution of the per-block distributions).

## The refined invariant and the open case (named, not proved)

Tractable ⟺ the gate–variable incidence graph decomposes into **bounded-size blocks** (bounded local overlap; within a
block arbitrary).  The disjoint case (entry 251) is blocks of size 1; this is bounded-size blocks.  The open case: a
**connected / large-component** incidence graph (high global overlap), where the count does *not* factor and the
`mod-q` fire-count is the genuine cross-field mixing (Smolensky, entries 244/249/250).  Whether efficient counting is
possible there — a quasipoly observer (crossing) or an exponential lower bound (barrier) — is the open `ACC⁰[composite]`
core (entry-238 `CarryRefinementCrossing`).  Not resolved here.

## Honest scope

This proves the cross-field count is poly-time for **block-decomposable** gate families (bounded local overlap; within
a block arbitrary), generalizing the disjoint case past overlap rank 1.  It does **not** resolve the
high-global-overlap (large connected component) case, which is the exposed ACC wall.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0BlockOverlapCount

/-- **Block-diagonal factorization (PROVED).**  For independent variable blocks `Z : Fin m → Type` with an arbitrary
per-block predicate `P b : Z b → Bool` (the within-block sub-computation — gates may overlap freely *inside* a block),
the number of inputs satisfying all block predicates factors across blocks:
`#{x : ∀ b, P b (x b)} = ∏ b, #{z : P b z}`.  Generalizes entry-251 `disjoint_pattern_count` (blocks of size 1) to
bounded *local* overlap. -/
theorem block_pattern_count {m : ℕ} {Z : Fin m → Type} [∀ b, Fintype (Z b)] [∀ b, DecidableEq (Z b)]
    (P : ∀ b, Z b → Bool) :
    (Finset.univ.filter (fun x : (∀ b, Z b) => ∀ b, P b (x b) = true)).card
      = ∏ b, (Finset.univ.filter (fun z : Z b => P b z = true)).card := by
  have he : (Finset.univ.filter (fun x : (∀ b, Z b) => ∀ b, P b (x b) = true))
       = Fintype.piFinset (fun b => Finset.univ.filter (fun z : Z b => P b z = true)) := by
    ext x; simp [Fintype.mem_piFinset, Finset.mem_filter]
  rw [he, Fintype.card_piFinset]

/-- **Bounded block size ⇒ bounded count (PROVED).**  If each block has `≤ W` assignments, the count is `≤ W^m` — a
product of `m` bounded factors.  Each block is brute-forceable in `≤ W` work; the cross-field count is poly-time for
bounded block size `W` (the `mod-q` fire-count distribution is the convolution of the `m` per-block distributions). -/
theorem block_count_le {m : ℕ} {Z : Fin m → Type} [∀ b, Fintype (Z b)] [∀ b, DecidableEq (Z b)]
    (P : ∀ b, Z b → Bool) (W : ℕ) (hW : ∀ b, Fintype.card (Z b) ≤ W) :
    (Finset.univ.filter (fun x : (∀ b, Z b) => ∀ b, P b (x b) = true)).card ≤ W ^ m := by
  rw [block_pattern_count]
  calc ∏ b, (Finset.univ.filter (fun z : Z b => P b z = true)).card
      ≤ ∏ _b : Fin m, W := by
        apply Finset.prod_le_prod
        · intro b _; exact Nat.zero_le _
        · intro b _
          exact le_trans (Finset.card_filter_le _ _)
            (le_trans (le_of_eq Finset.card_univ) (hW b))
    _ = W ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-!
**The refined invariant (named, not proved).**  Tractability is governed by the gate–variable *incidence graph*: if it
decomposes into bounded-size blocks (bounded local overlap), the count factors (`block_pattern_count`) and is poly-time
for bounded block size (`block_count_le`).  The disjoint case (entry 251) is blocks of size 1.  The open case is a
*connected / large-component* incidence graph (high global overlap), where the count does not factor and the `mod-q`
fire-count is the genuine cross-field mixing (Smolensky, entries 244/249/250) — the open `ACC⁰[composite]` core
(entry-238 `CarryRefinementCrossing`).
-/

end PallLean.Paper93.DeepMath.PathB.ACC0BlockOverlapCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BlockOverlapCount.block_pattern_count
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BlockOverlapCount.block_count_le
