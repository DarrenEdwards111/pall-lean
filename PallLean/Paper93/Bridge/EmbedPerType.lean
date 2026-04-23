/-
  EmbedPerType.lean — Canonical per-type variable embedding for the
  Cook-Levin compiled factor list.

  Agent F1 of 10 (parallel) — paper §9 Lemma 31 bridge-layer preparatory
  step.

  ## Scope

  For each `τ : ConstraintType` and each instance index `i` into the
  concrete Cook-Levin factor list `cookLevinFactorList M n hn htb hns`,
  this file fixes a canonical injective embedding

      embedAt : Fin 4 ↪ Fin n

  that maps the 4 local template slots of a type-`τ` constraint into the
  ambient `Fin n` variables used by the `i`-th compiled Cook-Levin
  factor.

  In the finrank-bound layer (paper Lemma 31), each compiled constraint
  touches at most 3 active variables; the 4th template slot is kept as
  a dormant "fourth coordinate" so every local template lives in a
  uniform Hilbert space of dimension ≤ 4 across constraint types. The
  embedding below is the simplest canonical choice — the identity
  inclusion `Fin.castLEEmb` for every (τ, i) — and is the concrete form
  used by the Paper §9 bridge. Refined, per-type distinct embeddings
  can be produced in downstream refinements by post-composing with
  index-dependent permutations of `Fin n`.

  ## Design note on `4 ≤ n`

  An injective map `Fin 4 ↪ Fin n` requires `4 ≤ n`. The ambient
  `cookLevinFactorList` signature uses `hn : n ≥ 2`, which is too weak
  for this embedding on its own. We therefore take an additional
  hypothesis `hn4 : 4 ≤ n` here — this is consistent with the paper's
  operating regime (`n ≥ n₀` for a fixed absolute constant `n₀ ≥ 4`)
  and with the standing Cook-Levin compilation hypotheses in
  `PallLean.WithinProfileBound`.
-/
import PallLean.WithinProfileBound
import Mathlib.Data.Fin.Embedding

namespace PallLean
namespace Paper93
namespace Bridge

open SymmetricPowerBound WithinProfileBound TuringMachine
open PaperFaithfulSeparation

/-! ## Canonical per-type embedding

For every `τ : ConstraintType` and every instance index `i` into the
Cook-Levin factor list, we take the canonical inclusion
`Fin 4 ↪ Fin n` given by `Fin.castLEEmb`. This embedding is injective
by construction (it is the underlying `Fin.castLE`), and it is uniform
across constraint types and instance indices.

For the booleanity (1 active), adjacency (2 active) and transition
(≤ 3 active) templates, the first `k` slots of `Fin 4` correspond to
the `k` ambient variables actually used by that constraint type; the
remaining `4 − k` slots are dormant but carried uniformly in the
4-dimensional local template carrier. -/

/-- Canonical variable embedding: maps the 4 local slots `Fin 4` to the
ambient variables `Fin n` that the `i`-th Cook-Levin constraint of type
`τ` uses.

This is the simplest canonical choice — the identity inclusion
`Fin.castLEEmb hn4` — which is uniform across `τ` and `i`. It is
`injective` by construction (inherited from `Fin.castLE`), and it is
non-dependent on `M, i, τ` at this layer. -/
def embedAt
    (M : DTM) (n : ℕ) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (hn4 : 4 ≤ n)
    (_τ : ConstraintType)
    (_i : Fin (cookLevinFactorList M n _hn _htb _hns).length) :
    Fin 4 ↪ Fin n :=
  Fin.castLEEmb hn4

/-- The canonical embedding is pointwise the `Fin.castLE` inclusion. -/
@[simp] theorem embedAt_apply
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : 4 ≤ n)
    (τ : ConstraintType)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (k : Fin 4) :
    (embedAt M n hn htb hns hn4 τ i) k = Fin.castLE hn4 k := rfl

/-- The canonical embedding is injective. -/
theorem embedAt_injective
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : 4 ≤ n)
    (τ : ConstraintType)
    (i : Fin (cookLevinFactorList M n hn htb hns).length) :
    Function.Injective (embedAt M n hn htb hns hn4 τ i) :=
  (embedAt M n hn htb hns hn4 τ i).injective

/-- The value of the canonical embedding at slot `k` has underlying
natural-number value equal to `k.val`. This is the concrete witness
that `embedAt` is the identity-on-values inclusion. -/
theorem embedAt_val
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : 4 ≤ n)
    (τ : ConstraintType)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (k : Fin 4) :
    ((embedAt M n hn htb hns hn4 τ i) k).val = k.val := rfl

/-- Each `ConstraintType` uses at most 4 ambient variable slots: the
range of the canonical embedding is contained in the first four
coordinates of `Fin n`. This is the finite "support" of the local
template at each instance.

We state the containment directly at the level of natural-number
values, which is the form used downstream when unifying local
template supports with compiled factor supports. -/
theorem embedAt_image_subset_variables
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : 4 ≤ n)
    (τ : ConstraintType)
    (i : Fin (cookLevinFactorList M n hn htb hns).length) :
    ∀ k : Fin 4, ((embedAt M n hn htb hns hn4 τ i) k).val < 4 := by
  intro k
  exact k.isLt

/-- Image form: the set-theoretic range of the canonical embedding
(viewed through `.toFun`) consists of ambient coordinates whose
underlying natural-number value is `< 4`. -/
theorem embedAt_range_mem_iff
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : 4 ≤ n)
    (τ : ConstraintType)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (j : Fin n) :
    j ∈ Set.range (embedAt M n hn htb hns hn4 τ i) ↔ j.val < 4 := by
  constructor
  · rintro ⟨k, rfl⟩
    exact embedAt_image_subset_variables M n hn htb hns hn4 τ i k
  · intro hj
    refine ⟨⟨j.val, hj⟩, ?_⟩
    apply Fin.ext
    rfl

end Bridge
end Paper93
end PallLean
