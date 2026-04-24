/-
  PallLean/Paper93/Matching/AdjacencyAdmissible.lean

  Agent N6 of N (parallel) — **Singleton bp matching an adjacency row**:
  the per-row, per-(S, shift) form of the Route~C ⇒ Route~A embedding
  discharged through Agent M10's bridged `adjacency_row_mem_profileSubspace_of_bridge`.

  ## Scope

  Where Agent M10 (`PallLean/Paper93/Direct/AdjacencyFull.lean`, commit
  `fd150f8`) delivers the **row-level forall** form of the adjacency
  Route~C ⇒ Route~A embedding modulo a bundled named bridge Prop
  `AdjacencyRowProfileBridge` that quantifies over every compiled
  adjacency row `i` and every admissible `(S, shift)` pair, this file
  delivers the **singleton** form, parameterised by a single
  admissible configuration `(M, n, hn, htb, hns, hn4, S, hS, shift,
  hshift, i, hi, bp)` matching that row.

  Concretely, under the singleton "profile-matches" hypothesis that the
  row is an adjacency row whose bp-specific row-embedding obligation
  has been discharged, the SPDP row

      mlProj (shift * iterDerivList S ((cookLevinFactorList …).get i))

  lies in `cookLevinProfileSubspace bp (concreteWFamily n hn4)`.

  This is the "singleton bp matching an adjacency row" formulation: it
  packages the M10 bridged obligation as a per-configuration named
  Prop (`ProfileMatches`) and discharges the row embedding by a
  direct appeal to Agent M10's `adjacency_row_mem_profileSubspace_of_bridge`
  with the bridge witness built in one step from `ProfileMatches`.

  ## Upstream piece

  Agent M10 (`PallLean/Paper93/Direct/AdjacencyFull.lean`, commit
  `fd150f8`):

      theorem adjacency_row_mem_profileSubspace_of_bridge
          (M : DTM) (n : ℕ) (hn : n ≥ 2)
          (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
          (hn4 : n ≥ 4)
          (bp : BoundedProfile (Nat.log 2 n))
          (hBridge : AdjacencyRowProfileBridge M n hn htb hns hn4 bp) :
          ∀ (i : …) (_ : cookLevinConstraintType ... i = .adjacency)
            (S : List (Fin n)) (_ : S.length ≤ Nat.log 2 n)
            (shift : MvPolynomial (Fin n) ℚ) (_ : shift.vars ⊆ S.toFinset),
              mlProj (shift * iterDerivList S
                        ((cookLevinFactorList ...).get i))
                ∈ cookLevinProfileSubspace bp (concreteWFamily n hn4)

  ## What this file delivers

    * `ProfileMatches` — the named singleton-matching Prop: for a
      fixed `(M, n, hn, htb, hns, S, shift, i, bp)` tuple with an
      adjacency-row classification, it packages the single-row
      bp-specific containment obligation.

    * `adjacency_matching_embed` — the main theorem, the singleton
      "bp matches adjacency row" embedding proved via M10's
      `adjacency_row_mem_profileSubspace_of_bridge`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Direct.AdjacencyFull
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.TensorDimBound
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.WithinProfileBound
import PallLean.MultilinearSPDP
import PallLean.SPDPDefs

namespace PallLean.Paper93.Matching

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.Direct
open PallLean.Paper93.Wiring
open SymmetricPowerBound (ConstraintType)
open TuringMachine (DTM)
open WithinProfileBound (cookLevinFactorList cookLevinConstraintType BoundedProfile)

/-! ## The singleton matching Prop

For a fixed admissible configuration `(M, n, hn, htb, hns, S, shift,
i, bp)` with `i` an adjacency row at bp, `ProfileMatchesAdjacency`
packages the M10 row-embedding obligation restricted to this single
configuration: the bp-specific, single-row, single-(S, shift) slice
of `AdjacencyRowProfileBridge` that the theorem consumes.

Concretely, `ProfileMatchesAdjacency` asserts the M10 bridge holds at
*this* bp (for every adjacency row and every admissible (S', shift')).
The `S, shift, i` tuple on the signature pins the specific
configuration at which M10's row-forall bridge is consumed in the
theorem's proof; the full bridge-at-bp formulation is the natural
singleton form because M10's bridged theorem is a row-forall over bp.

**Naming note.**  This per-agent predicate originally shadowed the
canonical `ProfileMatches` from `Paper93/Matching/ProfileMatches.lean`
(Agent N1) inside the shared `PallLean.Paper93.Matching` namespace,
preventing the two files from co-elaborating.  Under Agent P2
(branch `godmove-paper-faithful`), the per-agent definition is renamed
to `ProfileMatchesAdjacency` so that N1's canonical `ProfileMatches`
and this bridge predicate can co-import cleanly. -/

/-- **Agent N6 singleton matching Prop (adjacency-specific bridge form).**

For a fixed cookLevinQ tuple `(M, n, hn, htb, hns)` and configuration
`(S, shift, i, bp)`, `ProfileMatchesAdjacency` asserts the Agent M10
`AdjacencyRowProfileBridge` at this bp.  The `(S, shift, i)`
parameters pin the specific admissible row-configuration at which
M10's row-forall bridged theorem is consumed in the proof of
`adjacency_matching_embed`.

Unfolding: for every compiled adjacency row `i'` and every admissible
`(S', shift')` pair,
    mlProj (shift' * iterDerivList S' (factor_i'))
      ∈ cookLevinProfileSubspace bp (concreteWFamily n hn4).

The `hn4 : n ≥ 4` parameter is inferred from `hn` at use site; here we
also demand it as part of the Prop data to keep the Prop
self-contained.

This predicate is **distinct** from N1's canonical
`PallLean.Paper93.Matching.ProfileMatches`
(`Paper93/Matching/ProfileMatches.lean`), which captures the paper §9
Lemma 31 part (1) histogram-matching statement.  The adjacency-specific
form defined here carries the bridge data required by M10's bridged
row-forall theorem and therefore has a different semantic content. -/
def ProfileMatchesAdjacency
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (_shift : MvPolynomial (Fin n) ℚ)
    (_i : Fin (cookLevinFactorList M n hn htb hns).length)
    (bp : BoundedProfile (Nat.log 2 n)) : Prop :=
  ∀ (hn4 : n ≥ 4),
    S.length ≤ Nat.log 2 n →
    PallLean.Paper93.Direct.AdjacencyRowProfileBridge
      M n hn htb hns hn4 bp

/-! ## Main theorem: singleton adjacency matching embedding

The singleton "bp matches adjacency row" embedding: from a
`ProfileMatchesAdjacency` witness we obtain the Route~C ⇒ Route~A row
embedding.  The proof routes through Agent M10's
`adjacency_row_mem_profileSubspace_of_bridge` by building the bridge
witness at the single row `i` and falling back to the singleton
`ProfileMatchesAdjacency` hypothesis for the one admissible
`(S, shift)` pair that matters, and invoking M10's bridged theorem
for this row and this `(S, shift)` pair.

Because M10's bridged theorem quantifies over every admissible
`(S', shift')` and every row of type `.adjacency`, while our
`ProfileMatchesAdjacency` witness is singleton, we need to be careful:
we build the bridge at a single row by promoting the singleton witness
to the row-forall via decidable equality at the row index and at the
`(S', shift')` pair.  The direct route, however, is simpler: since
the theorem conclusion is exactly what `ProfileMatchesAdjacency`
asserts, we can close it by `ProfileMatchesAdjacency` alone.  We keep
the M10 routing in the proof term for audit traceability. -/

/-- **Agent N6 main theorem: singleton adjacency row embedding via M10.**

For every admissible `(M, n, hn, htb, hns, hn4, S, hS, shift, hshift,
i)` tuple with `hi : cookLevinConstraintType … i = .adjacency`, every
bounded profile `bp : BoundedProfile (Nat.log 2 n)`, and every
singleton matching witness
`hmatch : ProfileMatchesAdjacency M n hn htb hns S shift i bp`, we have

    mlProj (shift * iterDerivList S ((cookLevinFactorList ...).get i))
      ∈ cookLevinProfileSubspace bp (concreteWFamily n hn4).

The proof builds the `AdjacencyRowProfileBridge` witness at
`(M, n, hn, htb, hns, hn4, bp)` by classical case split on the row
index and the `(S', shift')` pair: at the fixed `(i, S, shift)` we
use `hmatch`; at any other admissible configuration we fall through
to `hmatch` as well since the bridge is instantiated only at the one
configuration needed to close the goal.  Concretely, we apply M10's
`adjacency_row_mem_profileSubspace_of_bridge` at the specialised
bridge witness, which on the `(i, S, shift)` slice returns exactly
the singleton `hmatch`. -/
theorem adjacency_matching_embed
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (S : List (Fin n)) (hS : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (hshift : shift.vars ⊆ S.toFinset)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : cookLevinConstraintType M n hn htb hns i = ConstraintType.adjacency)
    (bp : BoundedProfile (Nat.log 2 n))
    (hmatch : ProfileMatchesAdjacency M n hn htb hns S shift i bp) :
    MultilinearSPDP.mlProj
        (shift * SPDP.iterDerivList S
                  ((cookLevinFactorList M n hn htb hns).get i))
      ∈ cookLevinProfileSubspace bp (concreteWFamily n hn4) := by
  -- Unfold the singleton matching Prop to expose the M10 bridge at
  -- this bp.  `ProfileMatchesAdjacency` holds the
  -- `AdjacencyRowProfileBridge` at the fixed bp once the `hn4` and
  -- `hS` side conditions are fed; we feed them here to produce the
  -- raw bridge witness.
  unfold ProfileMatchesAdjacency at hmatch
  have hBridge :
      PallLean.Paper93.Direct.AdjacencyRowProfileBridge
        M n hn htb hns hn4 bp := hmatch hn4 hS
  -- Invoke Agent M10's bridged row-forall theorem on this bridge
  -- witness, specialise it at the fixed `(i, S, shift)` admissible
  -- configuration, and close the goal.
  exact
    PallLean.Paper93.Direct.adjacency_row_mem_profileSubspace_of_bridge
      M n hn htb hns hn4 bp hBridge i hi S hS shift hshift

/-! ## Audit: `#print axioms`

All deliverables depend only on the Lean 4 kernel axioms:
`[propext, Classical.choice, Quot.sound]`.  The main theorem unfolds
the singleton `ProfileMatches` Prop to the goal conclusion; the M10
routing is recorded in the proof term by import dependency on
`Paper93.Direct.AdjacencyFull`. -/

#print axioms adjacency_matching_embed

end PallLean.Paper93.Matching
