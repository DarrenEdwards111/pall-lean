/-
  PallLean/Paper93/Bridges/BooleanityProfileBridge.lean

  Agent Q1 — semantic bridge from N5's booleanity-specific
  `ProfileMatchesBooleanity` predicate to N1's canonical
  `ProfileMatches` predicate, at booleanity factor indices.

  ## Background

  N1 (`PallLean.Paper93.Matching.ProfileMatches.lean`) fixes the
  canonical Paper §9 Lemma 31 part (1) matching predicate:

      bp.toHistogram = rowProfile M n hn htb hns S shift i

  where `rowProfile … i τ = if cookLevinConstraintType … i = τ then 1
  else 0` is the Kronecker indicator at the row's constraint type, of
  total mass `1`.

  N5 (`PallLean.Paper93.Matching.BooleanityAdmissible.lean`) introduces
  a booleanity-specific strengthening

      bp.toHistogram = singletonBooleanityProfile S

  where `singletonBooleanityProfile S τ = if τ = booleanity then
  S.length else 0` has total mass `S.length` (all derivative steps
  deposited on the booleanity coordinate).

  The two profiles *disagree* in general: `rowProfile` counts the
  factor's type with mass `1`, while `singletonBooleanityProfile`
  counts each of the `S.length` derivative steps individually. They
  agree only when

      (a) `cookLevinConstraintType … i = ConstraintType.booleanity`
          (the factor row really is a booleanity row), and
      (b) `S.length = 1`
          (exactly one derivative step, so the histograms both put
          mass `1` on booleanity and `0` elsewhere).

  ## Scope (Agent Q1)

  This file provides the **conditional semantic bridge**

      ProfileMatchesBooleanity M n hn htb hns S shift i bp  ⇒
      ProfileMatches           M n hn htb hns S shift i bp

  under the two side conditions (a) and (b) above. We choose
  **Option C**: a single-derivative `S.length = 1` bridge at a
  booleanity factor index. Option A (`S = []`) does not give the
  implication because the N1 profile has mass `1` while the N5 profile
  with `S = []` has mass `0`; Option B (a calibrated variant) would
  require modifying the upstream N1/N5 definitions and is outside this
  agent's scope.

  ## Deliverable

    * `booleanityProfile_bridge` — the conditional implication
      `ProfileMatchesBooleanity ⇒ ProfileMatches` at a booleanity
      factor index with `S.length = 1`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Only uses the structural projections from N5 and the definitional
      unfolding of N1's `rowProfile`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.Paper93.Matching.BooleanityAdmissible

namespace PallLean.Paper93.Bridges

open MvPolynomial SymmetricPowerBound TuringMachine
open WithinProfileBound
open PallLean.Paper93.Matching
open PallLean.Paper93.Direct

/-- **Pointwise histogram equality at a booleanity factor with a
single derivative.**

For any booleanity factor index `i` (i.e.
`cookLevinConstraintType … i = ConstraintType.booleanity`) and any
singleton derivative list `S` (i.e. `S.length = 1`), the N5
booleanity-specific histogram `singletonBooleanityProfile S` coincides
pointwise with N1's row-profile indicator
`rowProfile M n hn htb hns S shift i`.

This is the key arithmetic lemma underlying the semantic bridge
below: both sides put mass `1` on `booleanity` and mass `0` on every
other constraint type. -/
theorem singletonBooleanityProfile_eq_rowProfile_of_booleanity
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : cookLevinConstraintType M n hn htb hns i
            = ConstraintType.booleanity)
    (hSlen : S.length = 1) :
    singletonBooleanityProfile (n := n) S
      = rowProfile M n hn htb hns S shift i := by
  classical
  funext τ
  -- Unfold both profiles.
  unfold singletonBooleanityProfile rowProfile
  -- Rewrite `cookLevinConstraintType … i` using `hi` and `S.length`
  -- using `hSlen`.
  rw [hi, hSlen]
  -- Goal: `(if τ = booleanity then 1 else 0)
  --       = (if booleanity = τ then 1 else 0)`.
  -- Case split on `τ = booleanity`.
  by_cases hτ : τ = ConstraintType.booleanity
  · -- τ = booleanity: both conditions hold.
    subst hτ
    simp
  · -- τ ≠ booleanity: both conditions fail.
    have hτ' : ConstraintType.booleanity ≠ τ := fun h => hτ h.symm
    simp [hτ, hτ']

/-- **Semantic bridge: N5 ⇒ N1 for booleanity factor indices.**

Given the hypotheses
  * `hi : cookLevinConstraintType M n hn htb hns i
            = ConstraintType.booleanity`
    (the factor row at index `i` is a booleanity row), and
  * `hSlen : S.length = 1`
    (exactly one derivative step is applied),
the N5 predicate `ProfileMatchesBooleanity` implies the N1 canonical
predicate `ProfileMatches` on the same data.

This discharges the Route~C ⇒ Route~A translation at the booleanity
constraint type for a single-derivative admissibility window: a
bounded profile `bp` whose histogram matches the singleton booleanity
profile (N5) also matches the row-profile indicator (N1), hence is
admissible by the canonical Paper §9 Lemma 31 part (1) predicate.

This is a **conditional** bridge: the two predicates genuinely
differ when `S.length ≠ 1` (N5 has mass `S.length`, N1 has mass `1`)
or when the factor row is not booleanity (N5 always places mass on
booleanity, N1 places mass on the row's actual type). Removing either
hypothesis requires a different bridge (e.g. via a calibrated matching
variant). -/
theorem booleanityProfile_bridge
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : cookLevinConstraintType M n hn htb hns i
            = ConstraintType.booleanity)
    (hSlen : S.length = 1)
    (bp : BoundedProfile (Nat.log 2 n))
    (h5 : ProfileMatchesBooleanity M n hn htb hns S shift i bp) :
    ProfileMatches M n hn htb hns S shift i bp := by
  -- Unfold N1's `ProfileMatches` and combine the N5 histogram shape
  -- with the pointwise equality of profiles.
  unfold ProfileMatches
  have hbp_shape : bp.toHistogram = singletonBooleanityProfile S :=
    h5.toHistogram_eq
  have hProfEq :
      singletonBooleanityProfile (n := n) S
        = rowProfile M n hn htb hns S shift i :=
    singletonBooleanityProfile_eq_rowProfile_of_booleanity
      M n hn htb hns S shift i hi hSlen
  exact hbp_shape.trans hProfEq

/-! ## Kernel-only axiom trace

The deliverable should depend only on
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms booleanityProfile_bridge

end PallLean.Paper93.Bridges
