/-
  PallLean/Paper93/Matching/RowEmbeddingsMatching.lean

  Paper §9 Lemma 31 part (1) — paper-faithful row-embeddings Prop with
  admissibility precondition (`matching h`).

  Agent N2 (parallel).

  ## Scope

  The existing bundle
  `PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW`
  (Agent M17, `Paper93/Direct/PerTypeComposition.lean`, commit
  `5b96899`) is the *unconditional* per-generator row-embedding
  statement at Agent J1's concrete
  `W := fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ`. It
  asserts that **every** generator
  `mlProj (shift * iterDerivList S (factor i))` lies in
  `cookLevinProfileSubspace bp W`, regardless of whether the
  generator actually contributes to the profile `bp` or is
  identically zero.

  Paper §9 Lemma 31 part (1) as stated on page 93 is subtly weaker:
  it only requires the row embedding for generators that **match
  the profile `h`** — i.e. for which the iterated derivative
  `∂^S (factor i)` actually realises the derivative-count histogram
  `bp.toHistogram τ` on the `τ`-labelled factors.

  Agent N1 (`Paper93/Matching/ProfileMatches.lean`, commit
  `74160bf`) exposed the matching predicate `ProfileMatches` as the
  local-type-statistics admissibility relation. This file exposes
  the paper-faithful row-embeddings variant

    `CookLevinPerTypeRowEmbeddings_concreteW_matching`

  obtained by adding `ProfileMatches … bp` to the quantifier body
  of Agent M17's unconditional Prop.

  ## Paper-faithfulness

  Paper §9 Lemma 31 part (1) reads (paraphrased):

    "For every bounded profile `h`, every iterated-derivative
     prefix `S` of length ≤ κ, every shift `m` of degree ≤ ℓ, and
     every factor index `i` such that the derivative pattern
     (S, i) **matches** `h`, the row `mlProj(m · ∂_S (factor i))`
     lies in the profile subspace `V_h`."

  The matching clause `ProfileMatches M n hn htb hns S shift i bp`
  is the precondition that filters the quantifier to only those
  (S, shift, i) triples whose derivative signature realises
  `bp.toHistogram`. On the Cook-Levin factor list with
  `cookLevinConstraintType`, this restricts the per-type row
  embedding to the admissible derivative patterns only.

  ## Relationship to Agent M17's unconditional bundle

  The unconditional bundle
  `CookLevinPerTypeRowEmbeddings_concreteW M n hn htb hns hn4`
  (no `matching h` precondition) trivially implies the matching
  variant: one simply forgets the precondition. Conversely, the
  paper-faithful matching variant is the **intended** statement of
  §9 Lemma 31 part (1) and is what downstream route-A arguments
  actually need.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/

import Mathlib.Data.Fin.Embedding
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.WithinProfileBound

namespace PallLean.Paper93.Matching

open MvPolynomial TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Wiring (concreteW)

/-! ## Paper-faithful row-embeddings Prop with `matching h` precondition

The Prop below is the paper-faithful statement of §9 Lemma 31 part
(1): row embeddings hold on *those* generators that MATCH the
bounded profile `bp`, as measured by N1's `ProfileMatches` relation
(`Paper93/Matching/ProfileMatches.lean`, commit `74160bf`). -/

/-- **Paper-faithful row embeddings with admissibility.**

Rows `mlProj(shift · ∂_S (factor i))` whose derivative signature
MATCHES the bounded profile `bp` (via N1's `ProfileMatches`
relation) lie in the profile subspace
`cookLevinProfileSubspace bp (fun τ => concreteW n hn4
(Fin.castLEEmb hn4) τ)`.

This corresponds to paper §9 Lemma 31 part (1): the per-type row
embeddings are asserted **only on the admissible** (S, shift, i)
triples, not unconditionally. -/
def CookLevinPerTypeRowEmbeddings_concreteW_matching
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (bp : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_ : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_ : shift.totalDegree ≤ Nat.log 2 n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length),
    ProfileMatches M n hn htb hns S shift i bp →
    MultilinearSPDP.mlProj
        (shift * SPDP.iterDerivList S
          ((cookLevinFactorList M n hn htb hns).get i)) ∈
      cookLevinProfileSubspace bp
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)

/-! ## Forgetting the matching precondition

The unconditional Agent M17 bundle
`CookLevinPerTypeRowEmbeddings_concreteW` trivially implies the
matching variant, since the matching variant only adds an extra
hypothesis in the quantifier body. We do not formalise the
forgetful map here, because doing so would require unfolding the
unconditional bundle via `CookLevinPerTypeSpanning` and re-deriving
the per-generator statement from the `boundedProfileClassifiedSet`
quantifier — that re-derivation is a downstream responsibility. -/

end PallLean.Paper93.Matching
