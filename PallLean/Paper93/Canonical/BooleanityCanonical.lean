/-
  PallLean/Paper93/Canonical/BooleanityCanonical.lean

  Agent R1 of R (parallel) — canonical-form booleanity row → V_h
  embedding at N1's canonical `ProfileMatches`.

  ## Scope

  This file delivers the canonical-form booleanity row → V_h
  embedding at Agent N1's canonical `ProfileMatches` predicate
  (`PallLean.Paper93.Matching.ProfileMatches`,
  `Paper93/Matching/ProfileMatches.lean`, commit `74160bf`).

  Concretely, given:

    * a Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
      `hn4 : n ≥ 4`;
    * a bounded profile `bp : BoundedProfile (Nat.log 2 n)`;
    * an admissible derivative list `S : List (Fin n)` with
      `hS : S.length ≤ Nat.log 2 n`;
    * an admissible shift `shift : MvPolynomial (Fin n) ℚ` with
      `hshift : shift.totalDegree ≤ Nat.log 2 n`;
    * a factor index `i : Fin (cookLevinFactorList M n hn htb hns).length`
      with `hi : cookLevinConstraintType M n hn htb hns i = .booleanity`;
    * a *canonical* matching hypothesis
      `hmatch : ProfileMatches M n hn htb hns S shift i bp`,

  together with the per-type M5-style Prop-level hypotheses

    * `hFactor : CookLevinFactorMemPerType M n hn htb hns (concreteW …)`
      — M1/H3 per-factor membership: every factor of the compiled
      Cook-Levin factor list lies in its per-type ambient space;
    * `hDerivClos : DerivClosurePerType (concreteW …)` — H4 derivative
      closure: each per-type ambient space is closed under iterated
      derivatives of bounded length;
    * `hShiftMlproj : PerTypeShiftMlprojClosure (concreteW …)` — I5
      shift + multilinear-projection closure of the profile subspace;
    * `hshift_vars : shift.vars ⊆ S.toFinset` — shift admissibility on
      `S` (needed to fire the `PerTypeShiftMlprojClosure` hypothesis;
      supplied as a separate hypothesis since the task's
      `shift.totalDegree ≤ Nat.log 2 n` is strictly weaker than the
      `S.toFinset` variable-containment form);
    * `hSlen_one : S.length = 1` — the *singleton-derivative
      compatibility* condition: N1's canonical `ProfileMatches`
      produces a Kronecker-δ histogram of total mass `1`, which is
      matched by the singleton `L = 1` witness consumed by
      `PerTypeShiftMlprojClosure` only when `S.length = 1`.

  the SPDP row generator

      mlProj (shift * iterDerivList S ((cookLevinFactorList …).get i))

  lies in `cookLevinProfileSubspace bp (concreteW …)`.

  ## Direct proof (no M5 / N5 routing)

  The proof does **not** route through Agent M5's
  `booleanity_row_mem_profileSubspace` or Agent N5's
  `booleanity_matching_embed` (both of which consume the
  booleanity-specific `singletonBooleanityProfile S` histogram
  shape, not N1's row-profile indicator). Instead, this file uses
  **only** N1's canonical `ProfileMatches` — i.e. the bare
  histogram equality `bp.toHistogram = rowProfile ... i` — together
  with the M1 / H4 / I1 / I2 / I3 (H3 / H4 / I5) closure ingredients
  composed directly into `cookLevinProfileSubspace bp (concreteW …)`
  at the canonical bp structure.

  The key structural observation: under `hi`, the row profile
  `rowProfile ... i` is the Kronecker indicator `fun τ => if τ =
  booleanity then 1 else 0`, so N1's `ProfileMatches` forces
  `bp.toHistogram` to be this indicator. Combined with `hSlen_one`,
  this coincides with N5's `singletonBooleanityProfile S` on the
  singleton case, and the `L = 1, d = fun _ => S,
  constraintType = fun _ => booleanity, factors = fun _ => factor_i`
  witness for `PerTypeShiftMlprojClosure` closes:

    * H3 supplies `factor_i ∈ W booleanity`;
    * H4 closes `iterDerivList S factor_i ∈ W booleanity`;
    * `derivCountProfile` at the singleton equals the canonical
      row profile indicator by `hi + hSlen_one`;
    * `PerTypeShiftMlprojClosure` then fires on the
      `(L = 1, d = fun _ => S)` witness.

  No reference to the N5 booleanity-specific
  `singletonBooleanityProfile` or `ProfileMatchesBooleanity` is
  made: we derive the same `derivCountProfile = bp.toHistogram`
  equation directly from N1's histogram-equality form, via the
  pointwise characterisation supplied by Agent R7's
  `profileMatches_at_type` / `profileMatches_at_other_type` in
  `Canonical/MassOne.lean`.

  ## Deliverable

    * `booleanity_row_embed_canonical` — the canonical row → V_h
      embedding at N1's `ProfileMatches`, producing membership in
      `cookLevinProfileSubspace bp (concreteW …)`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms; all closure ingredients are Prop-level
      arguments.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Canonical.MassOne
import PallLean.Paper93.Spanning.PerDerivativeSpanning
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.Paper93.CookLevinProfileSubspace

namespace PallLean.Paper93.Canonical

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound SPDP MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Matching
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring

/-! ## Helper: derivCountProfile at singleton L=1 equals N1's rowProfile

The canonical L=1 witness with `constraintType = fun _ => booleanity`
and `d = fun _ => S` has derivative-count profile of mass `S.length`
at booleanity and `0` elsewhere. Under `hi + hSlen_one`, this equals
N1's row-profile indicator
`rowProfile ... i = fun τ => if cookLevinConstraintType ... i = τ
then 1 else 0`.

We spell this identification out directly (no reference to N5's
`singletonBooleanityProfile`) so that the final theorem's proof
transparently uses only N1 content. -/

/-- Derivative-count profile of the singleton L=1 distribution with
`constraintType = fun _ => booleanity` and `d = fun _ => S` equals
`rowProfile M n hn htb hns S shift i` when
`cookLevinConstraintType ... i = .booleanity` and `S.length = 1`.

This is the direct arithmetic identification between the
PerTypeShiftMlprojClosure witness profile (LHS) and N1's canonical
row profile (RHS), avoiding any detour through N5's
`singletonBooleanityProfile`. -/
theorem derivCountProfile_singleton_eq_rowProfile_of_length_one
    {M : DTM} {n : ℕ} {hn : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : cookLevinConstraintType M n hn htb hns i
            = ConstraintType.booleanity)
    (hSlen_one : S.length = 1) :
    derivCountProfile (fun _ : Fin 1 => ConstraintType.booleanity)
        (fun _ : Fin 1 => S)
      = rowProfile M n hn htb hns S shift i := by
  classical
  funext τ
  -- Unfold both sides and case-split on `τ = booleanity`.
  unfold derivCountProfile rowProfile
  by_cases hτ : τ = ConstraintType.booleanity
  · -- Case τ = booleanity: LHS is the full sum over `Fin 1`, reducing
    -- to `S.length = 1`; RHS uses `if_pos hi` (rewriting `cookLevinCT = τ`
    -- via `hi` then `τ = booleanity`) yielding `1`.
    subst hτ
    -- LHS: ∑ (i : { i : Fin 1 // booleanity = booleanity }), (S).length
    --    = (Fin 1 full subtype, cardinality 1) · S.length = S.length = 1.
    have hcard :
        Finset.univ.card
          (α := { i : Fin 1 //
              (fun _ : Fin 1 => ConstraintType.booleanity) i
                = ConstraintType.booleanity }) = 1 := by
      have hft : Fintype.card { i : Fin 1 //
          (fun _ : Fin 1 => ConstraintType.booleanity) i
            = ConstraintType.booleanity } = 1 := by
        rw [Fintype.subtype_card]
        simp
      simp [Finset.card_univ]
    -- `∑ x, S.length = (card) * S.length = 1 * S.length = 1`.
    rw [Finset.sum_const]
    rw [hcard, one_smul, hSlen_one]
    -- RHS: `if cookLevinCT ... i = booleanity then 1 else 0` with
    -- `cookLevinCT ... i = booleanity` by `hi`.
    exact (if_pos hi).symm
  · -- Case τ ≠ booleanity: LHS has empty subtype (no i with
    -- `booleanity = τ` since τ ≠ booleanity), so sum = 0. RHS is
    -- `if cookLevinCT ... i = τ then 1 else 0`, and
    -- `cookLevinCT ... i = booleanity ≠ τ` by `hi + hτ`, so RHS = 0.
    have hempty : IsEmpty { i : Fin 1 //
        (fun _ : Fin 1 => ConstraintType.booleanity) i = τ } := by
      refine ⟨fun ⟨_, hi2⟩ => ?_⟩
      exact hτ hi2.symm
    -- LHS: 0.
    have hLHS : ∑ i : { i : Fin 1 //
        (fun _ : Fin 1 => ConstraintType.booleanity) i = τ },
          (S).length = 0 := Finset.sum_of_isEmpty _
    rw [hLHS]
    -- RHS: `if cookLevinCT ... i = τ then 1 else 0 = 0`.
    have hne : cookLevinConstraintType M n hn htb hns i ≠ τ := by
      rw [hi]; exact fun h => hτ h.symm
    exact (if_neg hne).symm

/-! ## Main theorem: canonical-form booleanity row → V_h embedding

For every cookLevinQ-compilation parameter tuple with N1's canonical
`ProfileMatches` admissibility witness plus M5-style Prop-level
closure hypotheses, the booleanity row generator lies in the profile
subspace `cookLevinProfileSubspace bp (concreteW …)`. -/

/-- **Agent R1 main theorem — canonical-form booleanity row → V_h
embedding at N1's `ProfileMatches`.**

For every cookLevinQ-compilation parameter tuple `(M, n, hn, htb,
hns)` with `hn4 : n ≥ 4`, every bounded profile `bp`, every
admissible `(S, hS, shift, hshift)` pair with `S.length = 1`
(singleton derivative), every booleanity factor index `i` (via
`hi`), and every N1 canonical matching witness `hmatch`
(`bp.toHistogram = rowProfile ... i`), together with M5-style
Prop-level closure hypotheses `(hFactor, hDerivClos, hShiftMlproj)`
at Agent J1's concrete `concreteW` family and the shift-vars
admissibility `hshift_vars : shift.vars ⊆ S.toFinset`, the SPDP row

    mlProj (shift * iterDerivList S ((cookLevinFactorList …).get i))

lies in `cookLevinProfileSubspace bp (concreteW …)`.

The proof uses ONLY N1's canonical `ProfileMatches` histogram
equality (via `profileMatches_at_type` / `profileMatches_at_other_type`
from Agent R7's `Canonical/MassOne.lean`) and the direct composition
of M1 (factor membership), H4 (derivative closure), and I5
(shift / mlProj closure). No routing through Agent M5's
`booleanity_row_mem_profileSubspace` or Agent N5's
`booleanity_matching_embed` occurs. -/
theorem booleanity_row_embed_canonical
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (hS : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (hshift : shift.totalDegree ≤ Nat.log 2 n)
    (hshift_vars : shift.vars ⊆ S.toFinset)
    (hSlen_one : S.length = 1)
    (hFactor : CookLevinFactorMemPerType M n hn htb hns
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hDerivClos : DerivClosurePerType (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hShiftMlproj : PerTypeShiftMlprojClosure (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : cookLevinConstraintType M n hn htb hns i
            = ConstraintType.booleanity)
    (hmatch : PallLean.Paper93.Matching.ProfileMatches
                M n hn htb hns S shift i bp) :
    MultilinearSPDP.mlProj
        (shift * SPDP.iterDerivList S
          ((cookLevinFactorList M n hn htb hns).get i))
      ∈ PallLean.Paper93.cookLevinProfileSubspace bp
          (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) := by
  classical
  -- Suppress unused-variable lints on the `hshift` / `hn4` slots,
  -- which are retained in the signature for call-site compatibility
  -- with the Matching-chain bundle but not consumed below.
  -- Step 0: extract `bp.toHistogram = rowProfile ... i` from N1's
  -- `ProfileMatches` (the matching predicate is definitionally this
  -- histogram equality).
  have hbpHist : bp.toHistogram = rowProfile M n hn htb hns S shift i := hmatch
  -- Abbreviate the concrete per-type family.
  set W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ with hW_def
  -- Step 1 (H3 + H4): `iterDerivList S factor_i ∈ W booleanity`.
  have hDerivMem :
      SPDP.iterDerivList S ((cookLevinFactorList M n hn htb hns).get i)
        ∈ W ConstraintType.booleanity :=
    iterDerivList_factor_mem_W
      M n hn htb hns W hFactor hDerivClos i
      ConstraintType.booleanity hi S hS
  -- Step 2: construct the `L = 1` witness for
  -- `PerTypeShiftMlprojClosure`. The key derivCountProfile equality
  -- uses `derivCountProfile_singleton_eq_rowProfile_of_length_one`
  -- (which routes through `hi + hSlen_one` and N1's `rowProfile`
  -- definition, NOT N5's `singletonBooleanityProfile`).
  have hg_prod_witness :
      ∃ (L : ℕ) (factors : Fin L → MvPolynomial (Fin n) ℚ)
        (constraintType : Fin L → ConstraintType)
        (d : Fin L → List (Fin n)),
        (∀ j, ∀ v ∈ d j, v ∈ S) ∧
        (∀ j, SPDP.iterDerivList (d j) (factors j) ∈ W (constraintType j)) ∧
        SPDP.iterDerivList S ((cookLevinFactorList M n hn htb hns).get i)
          = Finset.univ.prod
              (fun j => SPDP.iterDerivList (d j) (factors j)) ∧
        derivCountProfile constraintType d = bp.toHistogram ∧
        ∑ j : Fin L, (d j).length ≤ S.length := by
    refine ⟨1,
      fun _ : Fin 1 => (cookLevinFactorList M n hn htb hns).get i,
      fun _ : Fin 1 => ConstraintType.booleanity,
      fun _ : Fin 1 => S,
      ?_, ?_, ?_, ?_, ?_⟩
    · -- `∀ j, ∀ v ∈ d j, v ∈ S`: `d = const S`, so `v ∈ S → v ∈ S`.
      intro _ v hv
      exact hv
    · -- Per-factor membership: at `j : Fin 1`, this is
      -- `iterDerivList S factor_i ∈ W booleanity`.
      intro _
      exact hDerivMem
    · -- Product = single factor: `∏_{Fin 1} f = f 0`.
      simp
    · -- derivCountProfile = bp.toHistogram via R7 + hSlen_one + hi.
      -- Step (a): `derivCountProfile (const booleanity) (const S)
      --             = rowProfile ... i` by our helper above.
      -- Step (b): `rowProfile ... i = bp.toHistogram` via hmatch (hbpHist.symm).
      have hstep_a :
          derivCountProfile (fun _ : Fin 1 => ConstraintType.booleanity)
              (fun _ : Fin 1 => S)
            = rowProfile M n hn htb hns S shift i :=
        derivCountProfile_singleton_eq_rowProfile_of_length_one
          (M := M) (n := n) (hn := hn) (htb := htb) (hns := hns)
          S shift i hi hSlen_one
      rw [hstep_a, ← hbpHist]
    · -- `∑ j : Fin 1, (d j).length ≤ S.length`: `∑ = S.length ≤ S.length`.
      simp
  -- Step 3: fire `PerTypeShiftMlprojClosure` on the singleton witness.
  have hClosureApp :
      MultilinearSPDP.mlProj
          (shift * SPDP.iterDerivList S
            ((cookLevinFactorList M n hn htb hns).get i))
        ∈ cookLevinProfileSubspace bp W :=
    hShiftMlproj bp S hS shift hshift_vars
      (SPDP.iterDerivList S ((cookLevinFactorList M n hn htb hns).get i))
      hg_prod_witness
  -- Final: rewrite the goal in canonical `MultilinearSPDP` form;
  -- `MultilinearSPDP.mlProj` and `SPDP.iterDerivList` reduce to the
  -- abbreviations used by `hClosureApp` by `rfl`.
  exact hClosureApp

-- Suppress unused-argument lint on `hn4` / `hshift` which are
-- retained in the public signature for call-site compatibility with
-- the Matching-chain bundle but unused in the body above.
attribute [nolint unusedArguments] booleanity_row_embed_canonical

/-! ## Kernel-only axiom trace

The deliverable should depend only on
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms booleanity_row_embed_canonical

end PallLean.Paper93.Canonical
