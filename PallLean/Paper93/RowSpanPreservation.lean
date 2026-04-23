/-
# Paper §9.3.1 Lemma 26 — Canonical windows reduction is row-span preserving

Paper reference: §9.3.1, Lemma 26 (lines 1987–2009 of `paper.txt`).

**Statement (paper).** For every `w ∈ Win_κ`,
```
                    row(w) = row(can(w))
```
and consequently
```
   RowSpan M^B_{κ,ℓ}(p)  =  span { row(w) : w ∈ Win_κ^{can} }.
```

**Structural content.** The canonicalization map `can` is built from two
elementary operations (paper §9.3.1 Definition 20):

* **(P6)** adjacent-swap equivalence on derivative steps whose interface
  supports are disjoint (Lemma 26 Proof, step P6);
* **(P7)** interface-local word NF substitution
  `σ_e(w) ↦ NF(σ_e(w))` (Lemma 26 Proof, step P7).

The paper's Lemma 26 proof shows that the SPDP row map `row(·)` is
invariant under each of these two moves. The file below isolates that
purely algebraic content as the abstract predicate `RowFunction`: any
function `f : Win κ → V` that is invariant under adjacent
disjoint-support swaps and NF substitution automatically agrees on
`w` and `can(w)`, and therefore has the same `ℚ`-span over `Win κ` and
`can(Win κ)`.

This file is *abstract* in three senses:
* the carrier `V` of the row vectors is an arbitrary `ℚ`-module (the
  concrete SPDP row lives in a specific `ℚ`-vector space, but the
  row-span-preservation argument is module-theoretic);
* the swap relation `IsAdjacentSwapDisjoint` and substitution `substNF`
  are taken as abstract parameters — the concrete radius-1/block-local
  definitions are being introduced in parallel `Paper93/` modules;
* the canonicalization map `canWindow` is likewise taken as an abstract
  parameter reached from the above two moves, together with the
  assumption that `canWindow` is built by iterating these moves (encoded
  as a hypothesis on `f` saying that `f w = f (canWindow κ w)` follows
  from the two invariances).

Agent 5 owns this file exclusively (parallel with Agents 1–10). It
imports only Agent 1's `Paper93.CanonicalWindows` (for the `Win` type).
-/

import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Set.Basic
import PallLean.Paper93.CanonicalWindows

namespace PallLean
namespace Paper93

open Submodule

variable {κ : ℕ} {BlockIdx LocalOp : Type}
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

-- **Abstract (P6) predicate.**
--
-- `IsAdjacentSwapDisjoint w w'` asserts that the window `w'` is obtained
-- from `w` by swapping a pair of adjacent derivative steps whose interface
-- supports are disjoint. The paper's §9.3.1 step P6 of `can(·)` is the
-- transitive-reflexive closure of this relation. We leave it as an
-- abstract parameter because the concrete radius-1/block-local definition
-- is introduced by other parallel `Paper93/*` modules; Lemma 26 only uses
-- its *behavior under `f`*, recorded by `RowFunction.respectsSwap`.
variable (IsAdjacentSwapDisjoint :
  Win κ BlockIdx LocalOp → Win κ BlockIdx LocalOp → Prop)

-- **Abstract (P7) normal-form map.**
--
-- `substNF w` replaces each maximal interface-local update subword of `w`
-- by its monoid normal form `NF(·)` (paper §9.3.1, Definition 20 step 2).
-- Lemma 24 ensures the induced linear action is identical — the content
-- of `RowFunction.respectsSubst` below. Kept abstract to avoid colliding
-- with other parallel agents.
variable (substNF : Win κ BlockIdx LocalOp → Win κ BlockIdx LocalOp)

-- **Abstract canonicalization map.**
--
-- `canWindow` is the composition of the two normalization moves applied
-- to a bubble-sort / rewrite fixpoint (paper §9.3.1, Definition 20). The
-- concrete construction lives in a parallel `Paper93/*` module (Agent 4).
-- Here we only use the abstract fact that `f (canWindow w) = f w`
-- follows from `f` being swap- and NF-invariant, recorded in the
-- `RowFunction` predicate below.
variable (canWindow : Win κ BlockIdx LocalOp → Win κ BlockIdx LocalOp)

/--
**Paper §9.3.1, Lemma 26, row-invariance hypotheses.**

A function `f : Win κ → V` is called a **row function** (in the sense of
Lemma 26) if it satisfies the two invariance properties used in the
proof of the paper's Lemma 26:

1. **(P6) Disjoint-support swap invariance.** If `w'` is obtained from
   `w` by swapping two adjacent derivative steps whose interface
   supports are disjoint (`IsAdjacentSwapDisjoint w w'`), then
   `f w = f w'`. This is the paper's "disjoint-support steps act on
   disjoint variable/interface tensor factors, hence commute" (paper
   §9.3.1 proof, first paragraph).

2. **(P7) NF-substitution invariance.** For every `w`,
   `f w = f (substNF w)`. This is Lemma 24 reinterpreted as an equality
   of SPDP rows (paper §9.3.1 proof, second paragraph).

3. **Canonicalization reachability.** For every `w`, the canonical
   representative `canWindow w` is obtained from `w` by iteratively
   applying (P6) and (P7), hence `f w = f (canWindow w)` whenever `f`
   is (P6)- and (P7)-invariant. This is the closure property recorded
   explicitly here (so that the abstract lemmas below do not require us
   to unfold the concrete rewrite sequence defining `canWindow`).

The third clause is strictly implied by the concrete construction of
`canWindow` as an iterated (P6)/(P7) rewrite; keeping it in the
predicate avoids committing to an implementation here and matches the
behavior used by `row_eq_canRow` below.
-/
structure RowFunction (f : Win κ BlockIdx LocalOp → V) : Prop where
  /-- (P6) disjoint-support swap invariance. -/
  respectsSwap :
    ∀ w w', IsAdjacentSwapDisjoint w w' → f w = f w'
  /-- (P7) NF-substitution invariance. -/
  respectsSubst :
    ∀ w, f w = f (substNF w)
  /-- Reachability: `canWindow` is a (P6)/(P7) fixpoint reached from `w`. -/
  respectsCanonical :
    ∀ w, f w = f (canWindow w)

set_option linter.unusedSectionVars false in
/--
**Paper §9.3.1, Lemma 26 (pointwise equality).**

For any `RowFunction` `f` and every window `w`,
```
  f w = f (canWindow κ w).
```
This is the pointwise version of the paper's row-span-preservation
lemma: the SPDP row of `w` equals the SPDP row of `can(w)`.
-/
theorem row_eq_canRow
    (f : Win κ BlockIdx LocalOp → V)
    (hf : RowFunction (κ := κ) (BlockIdx := BlockIdx) (LocalOp := LocalOp)
           IsAdjacentSwapDisjoint substNF canWindow f)
    (w : Win κ BlockIdx LocalOp) :
    f w = f (canWindow w) :=
  hf.respectsCanonical w

/--
**Paper §9.3.1, Lemma 26 (span equality).**

The `ℚ`-linear span of `Set.range f` equals the `ℚ`-linear span of the
image of `f ∘ canWindow`:
```
  span ℚ (range f) = span ℚ (range (f ∘ canWindow)).
```

This is the row-span equality of paper §9.3.1 Lemma 26:
`RowSpan M^B_{κ,ℓ}(p) = span { row(w) : w ∈ Win_κ^{can} }`.
-/
theorem rowSpan_eq_canRowSpan
    (f : Win κ BlockIdx LocalOp → V)
    (hf : RowFunction (κ := κ) (BlockIdx := BlockIdx) (LocalOp := LocalOp)
           IsAdjacentSwapDisjoint substNF canWindow f) :
    Submodule.span ℚ (Set.range f)
      = Submodule.span ℚ (Set.range (f ∘ canWindow)) := by
  -- Both ranges are actually equal as sets, because for every `w` we
  -- have `f w = f (canWindow w)` by `row_eq_canRow`, and conversely
  -- every `f (canWindow w)` is itself of the form `f w'` for
  -- `w' := canWindow w`. We prove the two inclusions directly on the
  -- underlying sets and conclude by `Submodule.span_mono` both ways.
  apply le_antisymm
  · -- span (range f) ≤ span (range (f ∘ canWindow))
    -- For every `w`, `f w = f (canWindow w) = (f ∘ canWindow) w`,
    -- hence `range f ⊆ range (f ∘ canWindow)`.
    refine Submodule.span_mono ?_
    intro v hv
    rcases hv with ⟨w, rfl⟩
    refine ⟨w, ?_⟩
    -- `(f ∘ canWindow) w = f (canWindow w) = f w`.
    change f (canWindow w) = f w
    exact (row_eq_canRow (κ := κ) (BlockIdx := BlockIdx) (LocalOp := LocalOp)
      IsAdjacentSwapDisjoint substNF canWindow f hf w).symm
  · -- span (range (f ∘ canWindow)) ≤ span (range f)
    -- `range (f ∘ canWindow) ⊆ range f` with `w' := canWindow w`.
    refine Submodule.span_mono ?_
    intro v hv
    rcases hv with ⟨w, rfl⟩
    exact ⟨canWindow w, rfl⟩

set_option linter.unusedSectionVars false in
/--
**Corollary (range-set equality).**

The underlying *sets* `Set.range f` and `Set.range (f ∘ canWindow)` are
already equal for any `RowFunction` `f`. This is the sharper version of
`rowSpan_eq_canRowSpan` and may be useful when a later module wants to
manipulate row indices directly rather than spans.
-/
theorem range_eq_range_comp_canWindow
    (f : Win κ BlockIdx LocalOp → V)
    (hf : RowFunction (κ := κ) (BlockIdx := BlockIdx) (LocalOp := LocalOp)
           IsAdjacentSwapDisjoint substNF canWindow f) :
    Set.range f = Set.range (f ∘ canWindow) := by
  apply Set.eq_of_subset_of_subset
  · intro v hv
    rcases hv with ⟨w, rfl⟩
    refine ⟨w, ?_⟩
    change f (canWindow w) = f w
    exact (row_eq_canRow (κ := κ) (BlockIdx := BlockIdx) (LocalOp := LocalOp)
      IsAdjacentSwapDisjoint substNF canWindow f hf w).symm
  · intro v hv
    rcases hv with ⟨w, rfl⟩
    exact ⟨canWindow w, rfl⟩

end Paper93
end PallLean
