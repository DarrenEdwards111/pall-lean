/-
  PallLean/Paper93/Canonical/AltDispatch.lean

  Paper §9 Lemma 31 — Alternative per-row dispatch via R7 + R8.

  Agent R9 (parallel, single-file).

  ## Scope (Agent R9 of R, parallel)

  This agent creates **only** this single file under
  `PallLean/Paper93/Canonical/AltDispatch.lean`. No other files are
  touched.

  ## What R9 delivers

  Agents Q4 (`Paper93/Bridges/UnifiedDispatch.lean`) and N8
  (`Paper93/Matching/RowEmbeddingsDischarged.lean`) dispatch a row
  `mlProj (shift * iterDerivList S (factor i))` directly into the
  Cook-Levin profile subspace `cookLevinProfileSubspace bp
  (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)`, relying on
  per-type N5/N6/N7 embeddings and N1→N5/N6/N7 reverse bridges.

  R9 is an **alternative dispatch** that decomposes the problem as:

    * **R7 (per-type row closure in `concreteW τ`).** For each
      `τ : ConstraintType`, under the hypothesis that `i` is classified
      as `τ` (`cookLevinConstraintType M n hn htb hns i = τ`) and the
      N1-form admissibility data holds (`S.length ≤ Nat.log 2 n`,
      `shift.totalDegree ≤ Nat.log 2 n`, `ProfileMatches`), the row
      `mlProj (shift * iterDerivList S (factor i))` lies in
      `concreteW n hn4 (Fin.castLEEmb hn4) τ`.

      R7 is the composition of the three canonical closure interfaces:
      H3 (per-factor membership in `W τ`), H4 (derivative closure of
      `W τ`), and I2/I3 (shift/mlProj closure of `W τ`) — all
      specialised to the concrete per-type family
      `concreteW n hn4 (Fin.castLEEmb hn4)`.

    * **R8 (concreteW τ ⇒ cookLevinProfileSubspace bp W).** Given
      `ProfileMatches M n hn htb hns S shift i bp`, the histogram
      `bp.toHistogram` is the Kronecker indicator at
      `τ := cookLevinConstraintType M n hn htb hns i`. Any element of
      `concreteW n hn4 (Fin.castLEEmb hn4) τ` (= the single active
      coordinate of the profile) lies in
      `cookLevinProfileSubspace bp (fun τ' => concreteW n hn4
      (Fin.castLEEmb hn4) τ')`.

  This file composes R7 and R8 to deliver:

    * `row_in_concreteW_of_matching` — the R7 step, producing the
      per-row membership in the single active `concreteW τ` coordinate
      together with the type-classification witness `τ`.

    * `altDispatch_matching` — the full R7 + R8 composition, yielding
      the N1-form bundle `CookLevinPerTypeRowEmbeddings_concreteW_matching`
      at `concreteW n hn4 (Fin.castLEEmb hn4)`.

  Both R7 and R8 are carried as Prop-level hypotheses in this file,
  matching the H3/H4/I2/I3/Q1/Q2/Q3 abstraction pattern used
  throughout the `Paper93.Matching`, `Paper93.Closure`, and
  `Paper93.Bridges` namespaces. Concrete discharges of R7 and R8 can
  be plugged in from the per-type closure / spanning stacks to
  collapse the signature to a zero-argument theorem.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms; R7 and R8 are `Prop`-level arguments.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/

import PallLean.Paper93.Matching.ProfileMatches
import PallLean.Paper93.Matching.RowEmbeddingsMatching
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.WithinProfileBound

namespace PallLean.Paper93.Canonical

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Matching
open PallLean.Paper93.Wiring (concreteW)

/-! ## 1. R7 — Per-type row closure in `concreteW τ`

The R7 interface bundles H3 (per-factor membership), H4 (derivative
closure), I2 (shift closure), and I3 (mlProj closure) into a single
per-row statement: the row `mlProj (shift * iterDerivList S (factor i))`
lies in `concreteW n hn4 (Fin.castLEEmb hn4) τ` whenever `i` is
classified as `τ` and the N1-form admissibility data holds.

Stated here as a Prop-level hypothesis, to be discharged by a
downstream composition of the per-type closures. -/

/-- **R7 interface.** For each factor index `i` classified as `τ`
(`cookLevinConstraintType M n hn htb hns i = τ`) and each admissible
derivative / shift / matching triple, the row generator
`mlProj (shift * iterDerivList S (factor i))` lies in
`concreteW n hn4 (Fin.castLEEmb hn4) τ`. -/
def R7_RowInConcreteW
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (bp : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (_hshift_deg : shift.totalDegree ≤ Nat.log 2 n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (τ : ConstraintType)
    (_hτ : cookLevinConstraintType M n hn htb hns i = τ)
    (_hmatch : ProfileMatches M n hn htb hns S shift i bp),
    MultilinearSPDP.mlProj
        (shift * SPDP.iterDerivList S
          ((cookLevinFactorList M n hn htb hns).get i)) ∈
      concreteW n hn4 (Fin.castLEEmb hn4) τ

/-! ## 2. R8 — Lift from single-coordinate `concreteW τ` to the
    profile subspace under `ProfileMatches`.

The R8 interface lifts a `concreteW τ`-membership witness to
`cookLevinProfileSubspace bp (fun τ' => concreteW n hn4 (Fin.castLEEmb
hn4) τ')` whenever `ProfileMatches` pins the histogram to the
Kronecker indicator at `τ`. This is the generic "single active
coordinate" pass-through for the profile subspace: under `hmatch`,
`bp.toHistogram` has mass `1` on exactly one coordinate (namely
`τ = cookLevinConstraintType M n hn htb hns i`), so a factor in
`concreteW τ` already qualifies as a profile-respecting product.

We take R8 as a Prop-level hypothesis to keep this file independent of
the symmetric-power algebraic machinery used to unpack
`cookLevinProfileSubspace`. -/

/-- **R8 interface.** If `ProfileMatches M n hn htb hns S shift i bp`
holds (so `bp.toHistogram` is the Kronecker indicator at
`τ := cookLevinConstraintType M n hn htb hns i`) and an element `p`
lies in `concreteW n hn4 (Fin.castLEEmb hn4) τ`, then `p` lies in
`cookLevinProfileSubspace bp (fun τ' => concreteW n hn4
(Fin.castLEEmb hn4) τ')`. -/
def R8_LiftConcreteWToProfileSubspace
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (bp : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (τ : ConstraintType)
    (_hτ : cookLevinConstraintType M n hn htb hns i = τ)
    (_hmatch : ProfileMatches M n hn htb hns S shift i bp)
    (p : MvPolynomial (Fin n) ℚ)
    (_hp : p ∈ concreteW n hn4 (Fin.castLEEmb hn4) τ),
    p ∈ cookLevinProfileSubspace bp
      (fun τ' => concreteW n hn4 (Fin.castLEEmb hn4) τ')

/-! ## 3. R7 step: extract the type `τ` and the `concreteW τ`
    membership witness.

This is the first half of the alternative dispatch. Given N1's
`ProfileMatches` admissibility plus R7, we extract the canonical
constraint type `τ := cookLevinConstraintType M n hn htb hns i` and
feed the admissibility data through R7 to land the row in
`concreteW n hn4 (Fin.castLEEmb hn4) τ`.

The `τ` produced here is the canonical classification value of the
factor index `i`; the existence of `τ` is witnessed reflexively. -/

/-- **R7 row-in-`concreteW τ` theorem.**

Given N1's `ProfileMatches` hypothesis together with R7's per-type
row-in-`concreteW τ` closure, the row
`mlProj (shift * iterDerivList S (factor i))` lies in
`concreteW n hn4 (Fin.castLEEmb hn4) τ` for the canonical
constraint-type value `τ = cookLevinConstraintType M n hn htb hns i`
of the factor index `i`. -/
theorem row_in_concreteW_of_matching
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (bp : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hS : S.length ≤ Nat.log 2 n)
    (hshift : shift.totalDegree ≤ Nat.log 2 n)
    (hmatch : ProfileMatches M n hn htb hns S shift i bp)
    (hR7 : R7_RowInConcreteW M n hn hn4 htb hns) :
    ∃ τ : ConstraintType,
      cookLevinConstraintType M n hn htb hns i = τ ∧
      MultilinearSPDP.mlProj
          (shift * SPDP.iterDerivList S
            ((cookLevinFactorList M n hn htb hns).get i)) ∈
        concreteW n hn4 (Fin.castLEEmb hn4) τ := by
  -- Canonical choice: `τ` is the constraint-type classification value.
  refine ⟨cookLevinConstraintType M n hn htb hns i, rfl, ?_⟩
  -- Apply R7 at the reflexive type-classification equality.
  exact hR7 bp S hS shift hshift i
      (cookLevinConstraintType M n hn htb hns i) rfl hmatch

/-! ## 4. R7 + R8 composition: alternative dispatch discharging the
    N1-form matching bundle.

Composing R7 (row lands in `concreteW τ`) with R8 (`concreteW τ` lifts
to `cookLevinProfileSubspace bp W`) produces the N1-form bundle
`CookLevinPerTypeRowEmbeddings_concreteW_matching` at
`fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ`. -/

/-- **Alternative dispatch theorem (R9).**

Given R7 (per-type row closure in `concreteW τ`) and R8 (lift from
`concreteW τ` into the profile subspace under `ProfileMatches`), the
N1-form bundle `CookLevinPerTypeRowEmbeddings_concreteW_matching` at
Agent J1's concrete `W := fun τ => concreteW n hn4 (Fin.castLEEmb
hn4) τ` holds.

The proof composes R7 and R8 at the canonical constraint-type
classification value `τ := cookLevinConstraintType M n hn htb hns i`
of each factor index `i`, bypassing the per-type dispatch `match` on
constraint-type tags used by Agents N8 and Q4. -/
theorem altDispatch_matching
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hR7 : R7_RowInConcreteW M n hn hn4 htb hns)
    (hR8 : R8_LiftConcreteWToProfileSubspace M n hn hn4 htb hns) :
    CookLevinPerTypeRowEmbeddings_concreteW_matching
      M n hn hn4 htb hns := by
  -- Unfold the N1-form bundle and introduce the quantifier data.
  intro bp S hSlen shift hshift_deg i hmatch
  -- Step R7: extract the canonical `τ` and the `concreteW τ`
  -- membership witness for the row.
  obtain ⟨τ, hτ, hRow⟩ :=
    row_in_concreteW_of_matching M n hn hn4 htb hns
      bp S shift i hSlen hshift_deg hmatch hR7
  -- Step R8: lift from `concreteW τ` into `cookLevinProfileSubspace bp W`.
  exact hR8 bp S shift i τ hτ hmatch
    (MultilinearSPDP.mlProj
        (shift * SPDP.iterDerivList S
          ((cookLevinFactorList M n hn htb hns).get i)))
    hRow

/-! ## 5. Kernel-only axiom trace

The two deliverables above should depend only on
`[propext, Classical.choice, Quot.sound]`. Both R7 and R8 are
`Prop`-level binders; the proofs consume them via ordinary function
application, which preserves the axiom profile.

All content routes through:

  * Agent N1's `ProfileMatches` predicate
    (`Paper93/Matching/ProfileMatches.lean`);

  * Agent N2's matching-form bundle
    `CookLevinPerTypeRowEmbeddings_concreteW_matching`
    (`Paper93/Matching/RowEmbeddingsMatching.lean`);

  * Agent J1's concrete `concreteW` family
    (`Paper93/Wiring/ConcreteW.lean`);

  * Agent B's `cookLevinProfileSubspace`
    (`Paper93/CookLevinProfileSubspace.lean`). -/

#print axioms row_in_concreteW_of_matching
#print axioms altDispatch_matching

end PallLean.Paper93.Canonical
