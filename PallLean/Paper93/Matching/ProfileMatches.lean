/-
  PallLean/Paper93/Matching/ProfileMatches.lean

  Paper §9 Lemma 31, part (1): "local type statistics matching h".

  Scope of this file.

  The paper-faithful rank bound for the compiled Cook-Levin factor list
  classifies each factor row by its constraint type via
  `WithinProfileBound.cookLevinConstraintType`.  Part (1) of Lemma 31
  then asks whether the *profile histogram* of a given bounded profile
  `bp : BoundedProfile (Nat.log 2 n)` matches the per-row constraint
  type statistics of a fixed factor row `i`.

  We formalise this admissibility predicate as `ProfileMatches`.  For
  each factor index `i`, the "row profile" is the Kronecker indicator
  on `cookLevinConstraintType ... i`: it assigns `1` to the single
  constraint type absorbed by row `i` and `0` to every other type.
  The predicate `ProfileMatches` then states that the histogram
  `bp.toHistogram` coincides with that row profile as a function
  `ConstraintType → ℕ`.

  This file is intentionally narrow: it only fixes the *statement* of
  the matching predicate.  No rank, finrank, or spanning content is
  claimed here.  Downstream callers (Paper §9 Lemma 31 discharges) can
  consume `ProfileMatches` as a simple equality of histograms without
  re-deriving its definition.

  Kernel-only: this file introduces two plain `def`s and no axioms.
-/

import PallLean.WithinProfileBound

namespace PallLean.Paper93.Matching

open SymmetricPowerBound TuringMachine MvPolynomial

/-- Row profile of factor index `i` in the compiled Cook-Levin factor
list.

This is the Kronecker indicator of the constraint type absorbed by row
`i`: it assigns `1` to `cookLevinConstraintType M n hn htb hns i` and
`0` to every other constraint type.  Concretely, summed over
`τ : ConstraintType` this profile has total mass `1`, reflecting the
fact that each factor row contributes to exactly one constraint type.

The arguments `S : List (Fin n)` and `shift : MvPolynomial (Fin n) ℚ`
are not used in the definition of the profile itself (which depends
only on the per-row constraint type classification), but are retained
in the signature to match Paper §9 Lemma 31 part (1), where the
matching predicate is applied to a specific derivative / shift context
arising from `iterDerivList S factor_i`.

The admissibility result of Lemma 31 part (1) then boils down to: for
each row `i` the bounded profile `bp` matches this row profile iff
`bp.toHistogram` is the indicator at `cookLevinConstraintType ... i`.
-/
noncomputable def rowProfile
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_S : List (Fin n)) (_shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length) :
    ConstraintType → ℕ := fun τ =>
  if WithinProfileBound.cookLevinConstraintType M n hn htb hns i = τ then 1 else 0

/-- Paper §9 Lemma 31 part (1): "local type statistics matching h".

A bounded profile `bp` at radius `Nat.log 2 n` *matches* the derivative
profile of `iterDerivList S factor_i` iff the histogram `bp.toHistogram`
agrees pointwise, as a function `ConstraintType → ℕ`, with the row
profile of factor index `i` under the canonical Cook-Levin constraint
type classification `cookLevinConstraintType`.

Equivalently, unfolding `rowProfile`:

* `bp.toHistogram` has mass `1` on the single constraint type
  `cookLevinConstraintType M n hn htb hns i`, and mass `0` elsewhere.

This matches the per-row local-type statistic used in Paper §9
Lemma 31 part (1) and is the form consumed by downstream discharges
of the within-profile finrank frontier.
-/
def ProfileMatches
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length)
    (bp : WithinProfileBound.BoundedProfile (Nat.log 2 n)) : Prop :=
  bp.toHistogram = rowProfile M n hn htb hns S shift i

/-- Unfolding lemma: `ProfileMatches` is exactly the pointwise equality
`bp.toHistogram τ = rowProfile … τ` for every constraint type `τ`. -/
theorem profileMatches_iff
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length)
    (bp : WithinProfileBound.BoundedProfile (Nat.log 2 n)) :
    ProfileMatches M n hn htb hns S shift i bp ↔
      ∀ τ : ConstraintType,
        bp.toHistogram τ = rowProfile M n hn htb hns S shift i τ := by
  unfold ProfileMatches
  constructor
  · intro hEq τ
    exact congrFun hEq τ
  · intro hPt
    funext τ
    exact hPt τ

/-- The row profile has total mass exactly one: it is the Kronecker
indicator on the single absorbed constraint type. -/
theorem rowProfile_mass
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length) :
    profileMass (rowProfile M n hn htb hns S shift i) = 1 := by
  classical
  unfold profileMass rowProfile
  -- The sum is `∑ τ, if cookLevinConstraintType … i = τ then 1 else 0`,
  -- i.e. the count of the unique `τ` equal to `cookLevinConstraintType … i`.
  set c : ConstraintType := WithinProfileBound.cookLevinConstraintType M n hn htb hns i
  -- Reduce to `Finset.sum_ite_eq`.
  have hsum :
      ∑ τ : ConstraintType, (if c = τ then (1 : ℕ) else 0)
        = 1 := by
    have hmem : c ∈ (Finset.univ : Finset ConstraintType) := Finset.mem_univ _
    -- `Finset.sum_ite_eq` : `∑ x ∈ s, if a = x then f x else 0 = if a ∈ s then f a else 0`.
    rw [Finset.sum_ite_eq (Finset.univ : Finset ConstraintType) c (fun _ => (1 : ℕ))]
    simp [hmem]
  exact hsum

/-- If `ProfileMatches` holds, then the histogram of `bp` has mass one. -/
theorem profileMatches_mass
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length)
    (bp : WithinProfileBound.BoundedProfile (Nat.log 2 n))
    (h : ProfileMatches M n hn htb hns S shift i bp) :
    profileMass bp.toHistogram = 1 := by
  have hEq : bp.toHistogram = rowProfile M n hn htb hns S shift i := h
  rw [hEq]
  exact rowProfile_mass M n hn htb hns S shift i

end PallLean.Paper93.Matching
