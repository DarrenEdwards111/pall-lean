/-
  PallLean/Paper93/Unified/AllBoundedMatches.lean
  ============================================================================

  Agent O4 of O (parallel) — Matching-form ⇒ universal-form generator bridge
  for `WithinProfileBound.allBoundedProfilePostSpan` at the truncated
  Cook-Levin setting.

  ## Scope

  This file exposes the paper-faithful bridge from the *matching-form*
  per-row `ProfileMatches` Prop (Agent N1,
  `Paper93/Matching/ProfileMatches.lean`, commit `74160bf`) to the
  *universal-form* generator structure of
  `WithinProfileBound.allBoundedProfilePostSpan` at the truncated
  Cook-Levin factor list.

  Recall that
  `WithinProfileBound.allBoundedProfilePostSpan B κ ℓ factors constraintType h`
  is the `Submodule.span ℚ` of the set
  ```
  U(h) := ⋃ (S : List (Fin n)) (_ : S.length ≤ κ)
          (shift : MvPolynomial (Fin n) ℚ) (_ : shift.vars ⊆ S.toFinset),
          (fun g => mlProj (shift * g))
            '' boundedProfileClassifiedSet factors constraintType S h
  ```
  whose elements — the *generators* in the categorical sense — have
  the form `p = mlProj (shift * g)` with
  `g ∈ boundedProfileClassifiedSet ... S h`.

  The deliverable here is the following pair of theorems:

    * `allBoundedPostSpan_generator_extract` — structural extraction
      of the `(S, shift, g)` triple for every generator
      `p ∈ U(bp.toHistogram)`. This is the inverse of
      `Set.mem_iUnion` + `Set.mem_image` composition used to define
      `allBoundedProfilePostSpan` and provides the raw per-generator
      structure.

    * `allBoundedPostSpan_generator_matches_bp` — given a generator
      `p ∈ U(bp.toHistogram)` at a bounded profile `bp` whose
      histogram is the Kronecker row profile
      `rowProfile M n hn htb hns S shift i` (Agent N1's definition),
      there exists a row index `i` together with the admissible
      `(S, shift)` data such that `ProfileMatches M n hn htb hns S
      shift i bp` holds and `p = mlProj (shift * g)` for the
      corresponding classified-set representative `g`.

      In the important special case where `bp.toHistogram` actually
      *is* a row profile for some factor index `i` (i.e. the
      Kronecker indicator at `cookLevinConstraintType M n hn htb hns i`),
      the bridge delivers the paper-faithful per-row generator
      decomposition with `ProfileMatches` built in.

  The bridge connects the *matching-form* Prop structure used by
  Agents N2 / N3 (`CookLevinPerTypeRowEmbeddings_concreteW_matching`,
  `cookLevinProfileTemplateCollapse_from_matching`) with the
  *universal-form* generator structure of
  `allBoundedProfilePostSpan` consumed by Agents M17 / M18
  (`cookLevinProfileSubspace_contains_postSpan_direct`).

  ## Why not `p = mlProj (shift * iterDerivList S (factor i))`?

  The task prompt's aspirational conclusion
  `p = mlProj (shift * iterDerivList S (cookLevinFactorList ... i).get)`
  does **not** hold for a general generator of
  `allBoundedProfilePostSpan`. By the Lean-level definition of
  `boundedProfileClassifiedSet`, every classified representative `g`
  is a *product* over all factor indices:
  ```
  g = ∏_{j : Fin L} iterDerivList (d j) (factors j)
  ```
  where `d : Fin L → List (Fin n)` is a per-factor derivative
  distribution with `∑ j, (d j).length ≤ S.length` and
  `derivCountProfile constraintType d = h`.

  The per-row slice `p = mlProj (shift * iterDerivList S (factor i))`
  is a strictly *stronger* form: it would require `(d j)` to be
  nonempty for exactly one `j = i` and empty for all other
  `j ≠ i`, and would additionally require that non-trivial `iterDerivList`
  factors collapse to identity under `mlProj`. Neither condition
  follows from the raw generator membership.

  The paper-faithful bridge theorem therefore delivers the
  `(S, shift, g)` triple with `g ∈ boundedProfileClassifiedSet`
  (the product form), plus `ProfileMatches` at an externally supplied
  row index `i`. Downstream consumers that additionally require the
  per-row single-factor reduction can apply a factor-collapse
  argument (Leibniz product structure ⇒ single-factor derivative) as
  a separate step.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * No Classical.* beyond `propext` / `Classical.choice` / `Quot.sound`.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.Paper93.Matching.IterDerivProfile
import PallLean.WithinProfileBound

namespace PallLean.Paper93.Unified

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP
open PallLean.Paper93
open PallLean.Paper93.Matching

/-! ## 1. Structural extraction of a generator of `allBoundedProfilePostSpan`

For every element `p` of the underlying spanning *set* of
`allBoundedProfilePostSpan ... h` (i.e. the union over `(S, shift)`
pairs that appears as the `Submodule.span` argument in the definition
of `allBoundedProfilePostSpan`), we expose the triple `(S, shift, g)`
that witnesses `p = mlProj (shift * g)` together with the full
admissibility data: `S.length ≤ κ`, `shift.vars ⊆ S.toFinset`, and
`g ∈ boundedProfileClassifiedSet factors constraintType S h`.

This is the per-generator structural extraction used by the
matching-form ⇒ universal-form bridge below. -/

/-- **Structural extraction of an `allBoundedProfilePostSpan` generator.**

For every element `p` of the underlying generating set `U(h)` of
`allBoundedProfilePostSpan B κ ℓ factors constraintType h`, there
exist:

  * a derivative-index list `S : List (Fin n)` with `S.length ≤ κ`;

  * a shift polynomial `shift : MvPolynomial (Fin n) ℚ` with
    `shift.vars ⊆ S.toFinset`; and

  * a classified-set representative
    `g ∈ boundedProfileClassifiedSet factors constraintType S h`

such that `p = mlProj (shift * g)`.

The proof unfolds the `Set.mem_iUnion` / `Set.mem_image` layers of
the definition of the generating set. -/
theorem allBoundedPostSpan_generator_extract
    {n L : ℕ}
    (κ _ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (h : ProfileHistogram)
    (p : MvPolynomial (Fin n) ℚ)
    (hp : p ∈
      (⋃ (S : List (Fin n)) (_ : S.length ≤ κ)
         (shift : MvPolynomial (Fin n) ℚ) (_ : shift.vars ⊆ S.toFinset),
         (fun g => mlProj (shift * g)) ''
           boundedProfileClassifiedSet factors constraintType S h)) :
    ∃ (S : List (Fin n)) (_hSlen : S.length ≤ κ)
      (shift : MvPolynomial (Fin n) ℚ) (_hshift_vars : shift.vars ⊆ S.toFinset)
      (g : MvPolynomial (Fin n) ℚ),
        g ∈ boundedProfileClassifiedSet factors constraintType S h ∧
        p = mlProj (shift * g) := by
  -- `_ℓ` placeholder unused in the generating set (only `κ` appears).
  -- Cleanup: discharge the `_` holes by `Set.mem_iUnion` case analysis.
  rcases Set.mem_iUnion.mp hp with ⟨S, hS⟩
  rcases Set.mem_iUnion.mp hS with ⟨hSlen, hS'⟩
  rcases Set.mem_iUnion.mp hS' with ⟨shift, hshift⟩
  rcases Set.mem_iUnion.mp hshift with ⟨hshift_vars, himage⟩
  rcases himage with ⟨g, hg_class, hg_eq⟩
  -- `hg_eq : (fun g => mlProj (shift * g)) g = p`, i.e. `mlProj (shift * g) = p`.
  refine ⟨S, hSlen, shift, hshift_vars, g, hg_class, hg_eq.symm⟩

/-! ## 2. Bridge: matching-form `ProfileMatches` from generator structure

For every generator `p` of the underlying spanning set of
`allBoundedProfilePostSpan ... bp.toHistogram`, together with any
factor index `i : Fin (cookLevinFactorList M n hn htb hns).length`
such that `bp.toHistogram = rowProfile M n hn htb hns S shift i`,
the paper-faithful matching predicate `ProfileMatches M n hn htb hns
S shift i bp` holds by definition (the matching predicate is
definitionally the histogram equality that the hypothesis asserts).

This is the kernel-only bridge from the universal-form generator
structure of `allBoundedProfilePostSpan` to the matching-form
`ProfileMatches` Prop consumed by the N-stack row embeddings. -/

/-- **Matching-form `ProfileMatches` from a classified-set
representative.**

Given a bounded profile `bp` and a row index `i` such that
`bp.toHistogram = rowProfile M n hn htb hns S shift i`, the matching
predicate `ProfileMatches M n hn htb hns S shift i bp` holds.

This is the immediate unfolding of the definition of `ProfileMatches`
as the histogram equality
`bp.toHistogram = rowProfile M n hn htb hns S shift i`. -/
theorem profileMatches_of_toHistogram_eq_rowProfile
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length)
    (bp : WithinProfileBound.BoundedProfile (Nat.log 2 n))
    (hEq : bp.toHistogram
      = rowProfile M n hn htb hns S shift i) :
    ProfileMatches M n hn htb hns S shift i bp := hEq

/-- **Bridge: matching-form `ProfileMatches` for a generator of
`allBoundedProfilePostSpan ... bp.toHistogram`.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)`,
every bounded profile `bp : BoundedProfile (Nat.log 2 n)`, every
element `p` of the underlying spanning set of
`allBoundedProfilePostSpan ... bp.toHistogram` at the compiled
Cook-Levin factor list, and every row index `i` whose row profile
matches `bp.toHistogram`, there exist:

  * a derivative-index list `S : List (Fin n)` with
    `S.length ≤ Nat.log 2 n` (the κ bound of the generator),

  * a shift polynomial `shift : MvPolynomial (Fin n) ℚ` with
    `shift.vars ⊆ S.toFinset`,

  * a classified-set representative `g` lying in
    `boundedProfileClassifiedSet` at the corresponding profile,

such that:

  * `ProfileMatches M n hn htb hns S shift i bp` holds, and

  * `p = mlProj (shift * g)`.

The `ProfileMatches` clause is supplied by the hypothesis that the
bounded profile's histogram coincides with the Kronecker row
profile of the chosen row index `i` — which is precisely Agent N1's
matching-form admissibility predicate (Paper §9 Lemma 31 part (1)).

This is the paper-faithful `Route C ⇒ Route A` bridge: it connects
the *universal-form* generator structure of the bounded-profile
post-span (used by the M-stack agents M17 / M18) to the
*matching-form* per-row admissibility predicate (used by the N-stack
agents N1 / N2 / N3). -/
theorem allBoundedPostSpan_generator_matches_bp
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (bp : WithinProfileBound.BoundedProfile (Nat.log 2 n))
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length)
    (p : MvPolynomial (Fin n) ℚ)
    (hp : p ∈
      (⋃ (S : List (Fin n)) (_ : S.length ≤ Nat.log 2 n)
         (shift : MvPolynomial (Fin n) ℚ) (_ : shift.vars ⊆ S.toFinset),
         (fun g => mlProj (shift * g)) ''
           boundedProfileClassifiedSet
             (fun j => (WithinProfileBound.cookLevinFactorList M n hn htb hns).get j)
             (WithinProfileBound.cookLevinConstraintType M n hn htb hns) S bp.toHistogram))
    (hMatch : ∃ S shift,
      bp.toHistogram = rowProfile M n hn htb hns S shift i) :
    ∃ (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ),
      ProfileMatches M n hn htb hns S shift i bp ∧
      ∃ (g : MvPolynomial (Fin n) ℚ),
        g ∈ boundedProfileClassifiedSet
            (fun j => (WithinProfileBound.cookLevinFactorList M n hn htb hns).get j)
            (WithinProfileBound.cookLevinConstraintType M n hn htb hns) S bp.toHistogram ∧
        p = mlProj (shift * g) := by
  -- Step 1: extract the `(S_gen, shift_gen, g_gen)` triple realising
  -- the generator `p`.
  obtain ⟨S_gen, hSlen, shift_gen, hshift_vars, g_gen, hg_class, hp_eq⟩ :=
    allBoundedPostSpan_generator_extract
      (Nat.log 2 n) (Nat.log 2 n)
      (fun j => (WithinProfileBound.cookLevinFactorList M n hn htb hns).get j)
      (WithinProfileBound.cookLevinConstraintType M n hn htb hns)
      bp.toHistogram p hp
  -- Step 2: unpack the matching witness `(S_match, shift_match, hEq)`
  -- for the row index `i`.
  obtain ⟨S_match, shift_match, hEq⟩ := hMatch
  -- Step 3: derive `ProfileMatches` at `(S_match, shift_match, i, bp)`
  -- from the histogram equality `hEq`.
  have hMatches : ProfileMatches M n hn htb hns S_match shift_match i bp :=
    profileMatches_of_toHistogram_eq_rowProfile
      M n hn htb hns S_match shift_match i bp hEq
  -- Step 4: but `ProfileMatches` only depends on the histogram
  -- equality (the `S`/`shift` arguments to `rowProfile` are unused
  -- in its definition), so `ProfileMatches` also holds for the
  -- generator's `(S_gen, shift_gen)` data. This is the paper's
  -- observation that the matching predicate is really a per-row
  -- histogram equality, with the `(S, shift)` slots retained only
  -- for shape compatibility with §9 Lemma 31's quantifier body.
  have hMatches_gen : ProfileMatches M n hn htb hns S_gen shift_gen i bp := by
    -- Unfold both `ProfileMatches` and `rowProfile` to reduce to
    -- `bp.toHistogram = (fun τ => if ... = τ then 1 else 0)`, which
    -- does not depend on `S` or `shift`.
    show bp.toHistogram = rowProfile M n hn htb hns S_gen shift_gen i
    -- `rowProfile` is defined as a function of `i` alone; the `S`
    -- and `shift` arguments are marked unused (`_S`, `_shift`).
    -- Hence `rowProfile M n hn htb hns S shift i` is definitionally
    -- equal for any `S`, `shift`.
    have hrp_eq : rowProfile M n hn htb hns S_gen shift_gen i
        = rowProfile M n hn htb hns S_match shift_match i := by
      unfold rowProfile
      rfl
    rw [hrp_eq]
    exact hEq
  -- Step 5: package the conclusion.
  refine ⟨S_gen, shift_gen, hMatches_gen, g_gen, hg_class, hp_eq⟩

/-! ## 3. Corollary: `Submodule.span`-flavoured generator bridge

As a convenience for consumers that work with the `.carrier` set of
`allBoundedProfilePostSpan` directly (rather than with its underlying
generating set), we expose the specialisation of the bridge above to
elements `p ∈ (allBoundedProfilePostSpan ...).carrier` *that
additionally* are already known to lie in the generating set. The
existential decomposition is unchanged; only the membership
hypothesis shape differs.

Note: for arbitrary elements of `(allBoundedProfilePostSpan
...).carrier` (i.e. general linear combinations of generators), the
per-row decomposition below does **not** hold without an auxiliary
linearity argument; this corollary only addresses the generator
layer. -/

/-- **Corollary: generator-layer bridge at the `Submodule` level.**

For every generator `p` of `allBoundedProfilePostSpan B κ ℓ
(cookLevinFactorList.get) cookLevinConstraintType bp.toHistogram`
that lies already in the underlying spanning set (i.e. is of the
form `mlProj (shift * g)` for some admissible `(S, shift, g)`
triple), and for every row index `i` whose row profile coincides
with `bp.toHistogram`, the matching-form `ProfileMatches` predicate
holds for the extracted `(S_gen, shift_gen, i, bp)` tuple and the
generator is realised as `mlProj (shift_gen * g_gen)` for the
extracted classified-set representative `g_gen`.

This corollary routes directly through
`allBoundedPostSpan_generator_matches_bp` with the underlying-set
membership hypothesis as input, and is the form consumed by the
matching-form row-embedding discharge pipeline (N2 / N3) at the
subspace level. -/
theorem allBoundedPostSpan_generator_matches_bp_of_mem_underlying
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : BlockPartition n)
    (bp : WithinProfileBound.BoundedProfile (Nat.log 2 n))
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length)
    (p : MvPolynomial (Fin n) ℚ)
    (hp_under : p ∈
      (⋃ (S : List (Fin n)) (_ : S.length ≤ Nat.log 2 n)
         (shift : MvPolynomial (Fin n) ℚ) (_ : shift.vars ⊆ S.toFinset),
         (fun g => mlProj (shift * g)) ''
           boundedProfileClassifiedSet
             (fun j => (WithinProfileBound.cookLevinFactorList M n hn htb hns).get j)
             (WithinProfileBound.cookLevinConstraintType M n hn htb hns) S bp.toHistogram))
    (hMatch : ∃ S shift,
      bp.toHistogram = rowProfile M n hn htb hns S shift i) :
    p ∈ WithinProfileBound.allBoundedProfilePostSpan B (Nat.log 2 n) (Nat.log 2 n)
      (fun j => (WithinProfileBound.cookLevinFactorList M n hn htb hns).get j)
      (WithinProfileBound.cookLevinConstraintType M n hn htb hns) bp.toHistogram ∧
    ∃ (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ),
      ProfileMatches M n hn htb hns S shift i bp ∧
      ∃ (g : MvPolynomial (Fin n) ℚ),
        g ∈ boundedProfileClassifiedSet
            (fun j => (WithinProfileBound.cookLevinFactorList M n hn htb hns).get j)
            (WithinProfileBound.cookLevinConstraintType M n hn htb hns) S bp.toHistogram ∧
        p = mlProj (shift * g) := by
  refine ⟨?_, ?_⟩
  · -- Submodule membership: `p` is in the underlying set, hence in
    -- the submodule (the span of that set).
    apply Submodule.subset_span
    exact hp_under
  · -- Matching-form bridge conclusion.
    exact allBoundedPostSpan_generator_matches_bp
      M n hn htb hns bp i p hp_under hMatch

/-! ## 4. Kernel-only axiom trace

Both deliverables above should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Lean 4 kernel axioms. No bespoke axiom is introduced; the two
theorems route through:

  * `Set.mem_iUnion` + `Set.mem_image` (standard Mathlib set-theory
    lemmas; kernel-only).

  * `Submodule.subset_span` (standard Mathlib linear-algebra lemma;
    kernel-only).

  * Agent N1's `ProfileMatches` definition (definitional equality
    of the histogram `bp.toHistogram` and the Kronecker row
    profile `rowProfile M n hn htb hns S shift i`); note that
    `rowProfile` does not depend on its `S` / `shift` arguments,
    so the histogram equality does not depend on the specific
    `(S, shift)` realisation. -/

#print axioms allBoundedPostSpan_generator_extract
#print axioms profileMatches_of_toHistogram_eq_rowProfile
#print axioms allBoundedPostSpan_generator_matches_bp
#print axioms allBoundedPostSpan_generator_matches_bp_of_mem_underlying

end PallLean.Paper93.Unified
