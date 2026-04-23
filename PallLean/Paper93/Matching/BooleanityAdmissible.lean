/-
  PallLean/Paper93/Matching/BooleanityAdmissible.lean

  Agent N5 of N (parallel) — booleanity-row *matching-bp* admissibility
  and embedding.

  ## Scope

  This file specialises Agent M5's booleanity row→V_h embedding
  (`PallLean.Paper93.Direct.booleanity_row_mem_profileSubspace`,
  commit `0283d4f`) to the *matching bounded profile* produced by a
  row-profile match. Concretely, we expose:

    * `ProfileMatches` — the matching predicate at the singleton
      booleanity bounded profile: `bp.toHistogram` agrees with the
      singleton derivative-count histogram produced by placing all
      `S.length` derivatives on a single booleanity factor.

    * `booleanity_matching_embed` — the M5 embedding read off at a
      matching `bp`: given a booleanity factor index `i`, a bounded
      derivative list `S`, a shift polynomial whose variables are
      contained in `S.toFinset`, and a matching `bp`, the SPDP row
      `mlProj (shift * iterDerivList S (factor_i))` lies in
      `cookLevinProfileSubspace bp (concreteW …)`.

  The proof is a pure unpacking of the matching hypothesis into the
  `hbp_shape_S` argument of Agent M5, followed by an application of
  `booleanity_row_mem_profileSubspace`. The M5 hypotheses
  (`CookLevinFactorMemPerType`, `DerivClosurePerType`,
  `PerTypeShiftMlprojClosure` at `concreteW`) are carried through as
  Prop-level arguments, keeping this file free of bespoke axioms.

  ## Deliverable

    * `booleanity_matching_embed` — matching-bp form of the M5
      row→V_h embedding at `concreteW` for the booleanity constraint
      type.

  ## Upstream content used

    * Agent M5 (`booleanity_row_mem_profileSubspace`,
      `Paper93/Direct/BooleanityFull.lean`) — the direct row→V_h
      embedding with the `hbp_shape_S` shape hypothesis on `bp`.

    * `singletonBooleanityProfile` (same file) — the singleton
      derivative-count histogram placing all `S.length` derivatives on
      the booleanity coordinate.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms; the M5 hypotheses are carried as Prop-level
      arguments.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Direct.BooleanityFull

namespace PallLean.Paper93.Matching

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound SPDP MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Direct
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring

/-! ## The matching predicate

`ProfileMatches` captures the "matching bp" condition used by the
Route C ⇒ Route A translation at the truncated level: the bounded
profile `bp` has the singleton booleanity histogram at the derivative
list `S`, and the shift polynomial `shift` has its variables in
`S.toFinset`. This is exactly the data packaged by the booleanity
row-profile match in the paper's §9 Lemma 31 setup. -/

/-- **Matching predicate for the singleton booleanity bounded profile.**

For a cookLevinQ parameter tuple `(M, n, hn, htb, hns)`, a bounded
derivative list `S`, a shift polynomial `shift`, a factor index `i`,
and a bounded profile `bp`, the predicate `ProfileMatches M n hn htb
hns S shift i bp` asserts that:

* `S.length ≤ Nat.log 2 n` (the derivative list is short enough to fit
  inside the bounded profile's per-coordinate budget);

* `shift.vars ⊆ S.toFinset` (the shift respects the derivative list);

* `bp.toHistogram = singletonBooleanityProfile S` (the bp places all
  `S.length` derivative mass on the booleanity coordinate, matching the
  row profile of a single booleanity factor).

The factor index `i` is recorded to keep the predicate indexed by the
booleanity row whose profile `bp` matches. -/
def ProfileMatches (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (bp : BoundedProfile (Nat.log 2 n)) : Prop :=
  S.length ≤ Nat.log 2 n ∧
    shift.vars ⊆ S.toFinset ∧
      bp.toHistogram = singletonBooleanityProfile S

/-- Length-bound projection from `ProfileMatches`. -/
theorem ProfileMatches.length_le {M : DTM} {n : ℕ} {hn : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {S : List (Fin n)}
    {shift : MvPolynomial (Fin n) ℚ}
    {i : Fin (cookLevinFactorList M n hn htb hns).length}
    {bp : BoundedProfile (Nat.log 2 n)}
    (h : ProfileMatches M n hn htb hns S shift i bp) :
    S.length ≤ Nat.log 2 n :=
  h.1

/-- Shift-variable projection from `ProfileMatches`. -/
theorem ProfileMatches.shift_vars_subset {M : DTM} {n : ℕ} {hn : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {S : List (Fin n)}
    {shift : MvPolynomial (Fin n) ℚ}
    {i : Fin (cookLevinFactorList M n hn htb hns).length}
    {bp : BoundedProfile (Nat.log 2 n)}
    (h : ProfileMatches M n hn htb hns S shift i bp) :
    shift.vars ⊆ S.toFinset :=
  h.2.1

/-- Histogram-shape projection from `ProfileMatches`. -/
theorem ProfileMatches.toHistogram_eq {M : DTM} {n : ℕ} {hn : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {S : List (Fin n)}
    {shift : MvPolynomial (Fin n) ℚ}
    {i : Fin (cookLevinFactorList M n hn htb hns).length}
    {bp : BoundedProfile (Nat.log 2 n)}
    (h : ProfileMatches M n hn htb hns S shift i bp) :
    bp.toHistogram = singletonBooleanityProfile S :=
  h.2.2

/-! ## The matching-bp embedding theorem

At a matching `bp`, the M5 embedding closes without any additional
shape hypothesis: the `ProfileMatches` data is exactly the `hbp_shape`
argument of `booleanity_row_mem_profileSubspace`, and the `S`-length
and `shift`-variable hypotheses are projected out. -/

/-- **Booleanity-row admissibility and embedding at matching bp.**

For every cookLevinQ parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4`, every booleanity factor index `i`, every bounded
derivative list `S` and shift polynomial `shift`, every bounded
profile `bp` at radius `Nat.log 2 n` matching the singleton booleanity
profile, and every choice of the M5 hypotheses
(`CookLevinFactorMemPerType`, `DerivClosurePerType`,
`PerTypeShiftMlprojClosure` at `concreteW`), the SPDP row
`mlProj (shift * iterDerivList S (cookLevinFactorList.get i))` lies in
`cookLevinProfileSubspace bp (concreteW n hn4 (Fin.castLEEmb hn4))`.

The proof is a direct application of
`booleanity_row_mem_profileSubspace`: the shape hypothesis is supplied
by `ProfileMatches.toHistogram_eq`, the length hypothesis by
`ProfileMatches.length_le`, and the shift-variable hypothesis by
`ProfileMatches.shift_vars_subset`. -/
theorem booleanity_matching_embed
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hFactor : CookLevinFactorMemPerType M n hn htb hns
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hDerivClos : DerivClosurePerType (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hShiftMlproj : PerTypeShiftMlprojClosure (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : cookLevinConstraintType M n hn htb hns i
            = ConstraintType.booleanity)
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ)
    (bp : BoundedProfile (Nat.log 2 n))
    (hmatch : ProfileMatches M n hn htb hns S shift i bp) :
    MultilinearSPDP.mlProj
        (shift * SPDP.iterDerivList S
          ((cookLevinFactorList M n hn htb hns).get i))
      ∈ PallLean.Paper93.cookLevinProfileSubspace bp
          (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) := by
  -- Unpack the matching data: length, shift-var, and histogram shape.
  have hSlen : S.length ≤ Nat.log 2 n := hmatch.length_le
  have hshiftvars : shift.vars ⊆ S.toFinset := hmatch.shift_vars_subset
  have hbp_shape_S : bp.toHistogram = singletonBooleanityProfile S :=
    hmatch.toHistogram_eq
  -- Apply Agent M5's booleanity_row_mem_profileSubspace at (bp, i, S, shift).
  exact booleanity_row_mem_profileSubspace
    M n hn htb hns hn4 bp hFactor hDerivClos hShiftMlproj
    i hi S hSlen shift hshiftvars hbp_shape_S

/-! ## Kernel-only axiom trace

The deliverable should depend only on
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms booleanity_matching_embed

end PallLean.Paper93.Matching
