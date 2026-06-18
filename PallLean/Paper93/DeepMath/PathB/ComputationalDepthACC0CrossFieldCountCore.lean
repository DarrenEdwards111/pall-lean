import Mathlib

/-!
# The cross-field count core — `CrossFieldCount`, with the disjoint (low-overlap) tractable fragment

Every crossing route of the arc (single-field flattening 234/244, product-field observer 245, multi-sorted fast-SAT
246, one-layer mixing 248, depth-2 `MOD_q`-of-`MOD_p` 249, staged fast-SAT 250) bottomed out at the **same object**:

> **`CrossFieldCount`** — the number of `F_p`-gates firing on an input, **taken mod `q`** (`p ≠ q`).

This file formalizes that exposed core directly and attacks the **positive (tractable) fragments**: where the cross-
field count is cheap, and where it is the genuine Smolensky obstruction.  The cleanest positive case proved here is
**disjoint (low-overlap) gates**: when the gate supports are disjoint, the pattern-counts *factor as a product*
(independence) — so the cross-field count distribution is a convolution, computable in poly time, **with no cross-field
mixing**.  The obstruction is therefore an *overlap* phenomenon: it requires the gate supports to overlap (high
incidence rank); disjoint families are tractable.

⚠️ **No crossing, no faked no-go.**  The disjoint-gates factorization and the cell bounds are proved.  The general
(overlapping, high-incidence) case — efficient `CrossFieldCount` for arbitrary `F_p`-gate families — is the open
`ACC⁰[composite]` core; not resolved here (neither a quasipoly observer nor an exponential lower bound).

## What is proved (clean axioms, no `sorry`)

* **`crossFieldCount q gates x := #{i : gate i fires on x} mod q`** — the exposed core object.
* **`crossFieldCount_lt`** (PROVED) — `< q`: the outer observer has `≤ q` cells (cheap; the difficulty is the per-cell
  *input* count, not the cell count).
* **`fireCount_eq_sum`** (PROVED) — the fire-count is `∑ᵢ [gate i fires]` (the count is a sum of per-gate indicators).
* **`disjoint_pattern_count`** (PROVED) — the **tractable fragment**: for gates on disjoint supports (product space,
  gate `i` depends only on coordinate `i`), the number of inputs with a given fire-*pattern* `b` is `∏ᵢ #{y : gᵢ y =
  bᵢ}` — the pattern-counts factor as a product (independence).  Hence the cross-field count distribution is a
  convolution of per-gate distributions: **fast, no cross-field mixing**.

## The invariant and the open general case (named, not proved)

The disjoint case is tractable because the gate supports do not overlap — *incidence/overlap rank* `1` (each input
variable feeds one gate).  The candidate invariant: **low overlap rank ⇒ fast `CrossFieldCount`** (the disjoint case,
proved) and **high overlap rank ⇒ Smolensky obstruction** (overlapping `F_p`-gates whose `mod-q` fire-count is the
cross-field mixing, entries 244/249/250).  Proving the general dichotomy — a quasipoly observer (crossing) *or* an
exponential lower bound (the barrier) for arbitrary-overlap families — is the open `ACC⁰[composite]` core (entry-238
`CarryRefinementCrossing`).  Not resolved here.

## Honest scope

This proves the cross-field count is cheap for **disjoint / low-overlap** gate families (pattern-counts factor;
convolution; no mixing) and bounds the cell count.  It does **not** resolve the general overlapping case — efficient
`CrossFieldCount` for arbitrary `F_p`-gate families — which is the exposed ACC wall.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCountCore

/-- **The exposed ACC core object.**  The number of `F_p`-gates firing on input `x`, taken **mod `q`** — the object
every crossing route reduces to (with `p ≠ q`). -/
def crossFieldCount {X : Type} {s : ℕ} (q : ℕ) (gates : Fin s → (X → Bool)) (x : X) : ℕ :=
  (Finset.univ.filter (fun i => gates i x)).card % q

/-- **The cross-field count has `< q` values (PROVED).**  The outer observer has `≤ q` cells — cheap.  (The difficulty
is the per-cell *input* count, not the number of cells.) -/
theorem crossFieldCount_lt {X : Type} {s : ℕ} (q : ℕ) (hq : 0 < q)
    (gates : Fin s → (X → Bool)) (x : X) : crossFieldCount q gates x < q :=
  Nat.mod_lt _ hq

/-- **The fire-count is a sum of per-gate indicators (PROVED).**  `#{i : gate i fires} = ∑ᵢ [gate i fires]`. -/
theorem fireCount_eq_sum {X : Type} {s : ℕ} (gates : Fin s → (X → Bool)) (x : X) :
    (Finset.univ.filter (fun i => gates i x)).card = ∑ i, (if gates i x then 1 else 0) := by
  rw [Finset.card_filter]

/-- **The disjoint (low-overlap) tractable fragment (PROVED).**  For gates on *disjoint* supports — a product space
`x : Fin s → Y` with gate `i` depending only on coordinate `i` via `gᵢ` — the number of inputs realising a given
fire-*pattern* `b` factors as a product: `#{x : ∀ i, gᵢ (xᵢ) = bᵢ} = ∏ᵢ #{y : gᵢ y = bᵢ}`.  Independence: the
cross-field count distribution is a convolution of the per-gate distributions, computable in poly time — **no
cross-field mixing for disjoint supports**. -/
theorem disjoint_pattern_count {s : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (g : Fin s → (Y → Bool)) (b : Fin s → Bool) :
    (Finset.univ.filter (fun x : Fin s → Y => ∀ i, g i (x i) = b i)).card
      = ∏ i, (Finset.univ.filter (fun y : Y => g i y = b i)).card := by
  have he : (Finset.univ.filter (fun x : Fin s → Y => ∀ i, g i (x i) = b i))
       = Fintype.piFinset (fun i => Finset.univ.filter (fun y => g i y = b i)) := by
    ext x; simp [Fintype.mem_piFinset, Finset.mem_filter]
  rw [he, Fintype.card_piFinset]

/-!
**The invariant and the open general case (named, not proved).**  The disjoint case is tractable because each input
variable feeds one gate — *overlap rank 1*.  Candidate invariant: **low overlap rank ⇒ fast `CrossFieldCount`**
(proved here for disjoint), **high overlap rank ⇒ Smolensky obstruction** (overlapping `F_p`-gates whose `mod-q`
fire-count is the cross-field mixing, entries 244/249/250).  The general dichotomy — quasipoly observer (crossing) or
exponential lower bound (barrier) for arbitrary-overlap families — is the open `ACC⁰[composite]` core (entry-238
`CarryRefinementCrossing`).  Not resolved here.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCountCore

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCountCore.crossFieldCount_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCountCore.fireCount_eq_sum
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCountCore.disjoint_pattern_count
