/-
  PallLean/Paper93/Canonical/MassOne.lean

  Agent R7 — helper lemmas forcing the `bp.toHistogram` of a row-profile
  match to be a Kronecker δ with total mass exactly one.

  ## Scope

  N1 (`PallLean/Paper93/Matching/ProfileMatches.lean`) defines the
  canonical row-profile match

      ProfileMatches M n hn htb hns S shift i bp
        ↔ bp.toHistogram = rowProfile M n hn htb hns S shift i,

  where `rowProfile … i τ := if cookLevinConstraintType … i = τ then 1
  else 0`. This file derives three downstream "shape" consequences of
  `ProfileMatches` that are repeatedly needed by Agents R1–R4:

    * `profileMatches_total_mass` — `∑ τ, bp.toHistogram τ = 1`, i.e.
      the histogram of a matched `bp` has total mass exactly one.

    * `profileMatches_at_type` — if `cookLevinConstraintType … i = τ`
      then `bp.toHistogram τ = 1`.

    * `profileMatches_at_other_type` — if
      `cookLevinConstraintType … i = τ` and `τ' ≠ τ` then
      `bp.toHistogram τ' = 0`.

  Together these three lemmas pin down `bp.toHistogram` as the
  Kronecker indicator at the single absorbed constraint type, which is
  the exact shape consumed by the bridging route-C ⇒ route-A
  discharges (Agents R1–R4).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms; proofs reduce via `congrFun`, `Finset.sum_ite_eq`,
      and elementary `if_pos`/`if_neg` normalisation.
    * Expected `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
-/
import PallLean.Paper93.Matching.ProfileMatches

namespace PallLean.Paper93.Canonical

open PallLean.Paper93.Matching
open SymmetricPowerBound TuringMachine MvPolynomial
open WithinProfileBound

/-- **Total mass one.**

If the bounded profile `bp` matches the row profile of factor index
`i`, then the sum of `bp.toHistogram` over all constraint types is
exactly one.  This is the "delta-function" total-mass consequence of
the row-profile match, and is the statement consumed by Agents R1–R4
as the entry point into the Kronecker-δ shape of `bp.toHistogram`.

The proof unfolds `ProfileMatches` into the pointwise equality
`bp.toHistogram = rowProfile …` and reduces the resulting sum
`∑ τ, if cookLevinConstraintType … i = τ then 1 else 0` to `1` via
`Finset.sum_ite_eq` at the distinguished type
`cookLevinConstraintType … i ∈ Finset.univ`.
-/
theorem profileMatches_total_mass
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length)
    (bp : WithinProfileBound.BoundedProfile (Nat.log 2 n))
    (h : ProfileMatches M n hn htb hns S shift i bp) :
    (Finset.univ : Finset ConstraintType).sum (fun τ => bp.toHistogram τ) = 1 := by
  classical
  -- Rewrite `bp.toHistogram` to the row profile via the matching hypothesis,
  -- then reduce to `rowProfile_mass` (which is definitionally `profileMass`).
  have hEq : bp.toHistogram = rowProfile M n hn htb hns S shift i := h
  -- `Finset.univ.sum (fun τ => bp.toHistogram τ)` is definitionally
  -- `profileMass bp.toHistogram`; conclude via `profileMatches_mass`.
  have hMass : profileMass bp.toHistogram = 1 :=
    profileMatches_mass M n hn htb hns S shift i bp h
  -- The statement's LHS reduces to `profileMass bp.toHistogram` by `rfl`
  -- (since `profileMass` is `∑ τ : ConstraintType, h τ`).
  show profileMass bp.toHistogram = 1
  exact hMass

/-- **Mass one at the absorbed type.**

If `bp` matches the row profile of factor index `i` and
`cookLevinConstraintType … i = τ`, then `bp.toHistogram τ = 1`.

This records that, at the distinguished constraint type absorbed by
row `i`, the matched histogram attains its full unit mass.  Combined
with `profileMatches_at_other_type` below, this pins `bp.toHistogram`
as the Kronecker indicator at `cookLevinConstraintType … i`.

The proof applies the pointwise equality
`bp.toHistogram τ = rowProfile … τ` at `τ`, unfolds `rowProfile`,
and dispatches the resulting `if`-expression via `if_pos hi`.
-/
theorem profileMatches_at_type
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length)
    (bp : WithinProfileBound.BoundedProfile (Nat.log 2 n))
    (τ : ConstraintType)
    (hi : WithinProfileBound.cookLevinConstraintType M n hn htb hns i = τ)
    (h : ProfileMatches M n hn htb hns S shift i bp) :
    bp.toHistogram τ = 1 := by
  -- Pointwise equality from `ProfileMatches`.
  have hEq : bp.toHistogram = rowProfile M n hn htb hns S shift i := h
  have hPt : bp.toHistogram τ = rowProfile M n hn htb hns S shift i τ :=
    congrFun hEq τ
  -- Unfold `rowProfile` and fire `if_pos hi`.
  rw [hPt]
  unfold rowProfile
  exact if_pos hi

/-- **Zero mass at every other type.**

If `bp` matches the row profile of factor index `i`,
`cookLevinConstraintType … i = τ`, and `τ' ≠ τ`, then
`bp.toHistogram τ' = 0`.

This is the "off the absorbed type" half of the Kronecker-δ shape:
every constraint type other than the single absorbed type
`cookLevinConstraintType … i` receives zero mass under the matched
histogram.  Together with `profileMatches_at_type`, this characterises
`bp.toHistogram` up to the Kronecker indicator on the absorbed type.

The proof applies the pointwise equality at `τ'`, unfolds `rowProfile`,
and dispatches the resulting `if`-expression via `if_neg`, using the
fact that `cookLevinConstraintType … i = τ ≠ τ'`.
-/
theorem profileMatches_at_other_type
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length)
    (bp : WithinProfileBound.BoundedProfile (Nat.log 2 n))
    (τ τ' : ConstraintType)
    (hi : WithinProfileBound.cookLevinConstraintType M n hn htb hns i = τ)
    (hne : τ' ≠ τ)
    (h : ProfileMatches M n hn htb hns S shift i bp) :
    bp.toHistogram τ' = 0 := by
  -- Pointwise equality from `ProfileMatches`.
  have hEq : bp.toHistogram = rowProfile M n hn htb hns S shift i := h
  have hPt : bp.toHistogram τ' = rowProfile M n hn htb hns S shift i τ' :=
    congrFun hEq τ'
  -- Convert `τ' ≠ τ` into `cookLevinConstraintType … i ≠ τ'`.
  have hneq : WithinProfileBound.cookLevinConstraintType M n hn htb hns i ≠ τ' := by
    intro hEq'
    -- From `cookLevinConstraintType … i = τ` and
    -- `cookLevinConstraintType … i = τ'` we would get `τ = τ'`, contradiction.
    have : τ = τ' := hi.symm.trans hEq'
    exact hne this.symm
  -- Unfold `rowProfile` and fire `if_neg hneq`.
  rw [hPt]
  unfold rowProfile
  exact if_neg hneq

/-! ## Kernel-only axioms trace -/

#print axioms PallLean.Paper93.Canonical.profileMatches_total_mass
#print axioms PallLean.Paper93.Canonical.profileMatches_at_type
#print axioms PallLean.Paper93.Canonical.profileMatches_at_other_type

end PallLean.Paper93.Canonical
