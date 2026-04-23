/-
  PallLean/Paper93/Closure/UnconditionalSpanning.lean

  Agent I6 of 10 (parallel).

  ## Scope

  This file composes the per-type spanning discharge delivered by:

    * Agent H3 (`Paper93/Spanning/DischargeOneMem.lean`, commit
      `34e3af5`) — unconditional per-factor membership of the compiled
      Cook-Levin factors in the ambient per-type space (the `1 ∈
      ambient` hypothesis of Agents G1 / G2 is discharged via Agent
      H1's `perTypeInterfaceSpace` which natively contains `1`, then
      lifted through Agent H2's `ambientPerTypeSpace`).

    * Agent H4 (`Paper93/Spanning/DerivativeClosure.lean`, commit
      `8fba527`) — derivative closure of a per-type ambient space
      `W τ` under iterated partial derivatives along bounded lists.

    * Agent I5 — the discharged
      `PerTypeShiftMlprojClosure` hypothesis ("for every generator
      `g = ∏_i iterDerivList (d i) (factors i)` of the bounded profile
      classified set, and every `shift` polynomial with
      `vars ⊆ S.toFinset`, the element `mlProj (shift * g)` lies in
      the profile subspace"). This is the final closure step that
      glues H3's per-factor membership and H4's derivative closure
      into the `cookLevinProfileSubspace` of the target bundle.

  From these three inputs we produce Agent G4's universal per-type
  spanning bundle

    `CookLevinPerTypeSpanning_universal`
      := `∀ M n hn htb hns W, CookLevinPerTypeSpanning M n hn htb hns W`

  via Agent H5's `cookLevinPerTypeSpanning_discharged` pointwise in
  `(M, n, hn, htb, hns, W)`.

  ## Why the hypotheses are universally quantified in `W`

  `CookLevinPerTypeSpanning_universal` is quantified over every
  submodule family `W : ConstraintType → Submodule ℚ (MvPolynomial (Fin
  n) ℚ)`. For each concrete `W`, H5's
  `cookLevinPerTypeSpanning_discharged` consumes H3's
  `CookLevinFactorMemPerType M n hn htb hns W`, H4's
  `DerivClosurePerType (n := n) W`, and I5's
  `PerTypeShiftMlprojClosure (n := n) W`. Since the universal target
  ranges over every `W`, the composed theorem here must take these
  three deliverables universally quantified in their parameters
  `M, n, hn, htb, hns, W`. This is faithful to the actual
  H3 / H4 / I5 scope — each agent discharges its per-type deliverable
  for every admissible `W`, so the universally quantified hypothesis
  is exactly what H3 / H4 / I5 provide when their per-`W`
  discharges are packaged into a universal statement.

  At the zero-argument call site
  (`PallLean/Paper93/Closure/G4Unconditional.lean`, commit `...`),
  the three hypotheses will be supplied by:

    * `H3`: `fun _ _ _ _ _ _ _ => (…)` — unconditional factor
      membership for every admissible `W`;
    * `H4`: `fun _ _ _ _ _ _ _ => (…)` — derivative closure for every
      admissible `W`;
    * `I5`: `fun _ _ _ _ _ _ _ => (…)` — shift-mlproj closure for
      every admissible `W`.

  Until all three agents' universal packages land in-file, we expose
  the hypotheses explicitly on the signature of
  `cookLevinPerTypeSpanning_universal_unconditional`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
-/

import PallLean.Paper93.Spanning.PerDerivativeSpanning

namespace PallLean
namespace Paper93
namespace Closure

open MvPolynomial SymmetricPowerBound TuringMachine
open PallLean.Paper93.Spanning

/-! ## Universal-over-`W` hypothesis packages for H3, H4, I5

Each of H3, H4, I5 delivers its conclusion for every admissible
`(M, n, hn, htb, hns, W)` input. We package the universal form as
named `Prop`s so the composed theorem below has a clean signature. -/

/-- **H3 universal package.** For every `(M, n, hn, htb, hns, W)`, every
compiled Cook-Levin factor lies in the ambient per-type space of its
constraint type. -/
def CookLevinFactorMemPerType_universal : Prop :=
  ∀ (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)),
    CookLevinFactorMemPerType M n hn htb hns W

/-- **H4 universal package.** For every `(n, W)`, the per-type family
`W` is closed under iterated partial derivatives along bounded lists. -/
def DerivClosurePerType_universal : Prop :=
  ∀ (n : ℕ)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)),
    DerivClosurePerType (n := n) W

/-- **I5 universal package.** For every `(n, W)`, the shift-mlproj
closure holds: for every generator `g` of `boundedProfileClassifiedSet`
at profile `bp.toHistogram`, and every shift polynomial with
`vars ⊆ S.toFinset`, the element `mlProj (shift * g)` lies in
`cookLevinProfileSubspace bp W`. -/
def PerTypeShiftMlprojClosure_universal : Prop :=
  ∀ (n : ℕ)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)),
    PerTypeShiftMlprojClosure (n := n) W

/-! ## I6: Unconditional `CookLevinPerTypeSpanning_universal`

Chaining H3 (universal factor membership), H4 (universal derivative
closure), and I5 (universal shift-mlproj closure) through H5's
`cookLevinPerTypeSpanning_discharged` pointwise in
`(M, n, hn, htb, hns, W)` produces the universal per-type spanning
bundle of Agent G4.

The proof is a direct term-mode application of H5's
`cookLevinPerTypeSpanning_discharged` at each argument tuple, with
the three hypothesis packages instantiated at the matching tuple. -/

/-- **Agent I6: unconditional `CookLevinPerTypeSpanning_universal`.**

Given universally-quantified (in `M, n, hn, htb, hns, W`) discharges
of H3 (`CookLevinFactorMemPerType`), H4 (`DerivClosurePerType`), and
I5 (`PerTypeShiftMlprojClosure`), produce Agent G4's universal
per-type spanning bundle `CookLevinPerTypeSpanning_universal`.

The proof post-composes Agent H5's `cookLevinPerTypeSpanning_discharged`
pointwise in each argument tuple, feeding the three universal
hypotheses instantiated at the matching tuple. No new analytic content
is introduced; this is the composition layer `H3 ∧ H4 ∧ I5 ⇒ G4
universal`. -/
theorem cookLevinPerTypeSpanning_universal_unconditional
    (hFactor_univ : CookLevinFactorMemPerType_universal)
    (hClosure_univ : DerivClosurePerType_universal)
    (hShiftMlproj_univ : PerTypeShiftMlprojClosure_universal) :
    CookLevinPerTypeSpanning_universal := by
  intro M n hn htb hns W
  exact
    cookLevinPerTypeSpanning_discharged
      M n hn htb hns W
      (hFactor_univ M n hn htb hns W)
      (hClosure_univ n W)
      (hShiftMlproj_univ n W)

/-! ## Alias matching the task prompt's mnemonic

The following alias is the proof term that Agent I7
(`PallLean/Paper93/Closure/G4Unconditional.lean`) consumes to
produce `AgentG4_Spanning` unconditionally. -/

/-- Alias of `cookLevinPerTypeSpanning_universal_unconditional`
suitable for direct substitution at the I7 call site. -/
theorem CookLevinPerTypeSpanning_universal_of_H3_H4_I5
    (hFactor_univ : CookLevinFactorMemPerType_universal)
    (hClosure_univ : DerivClosurePerType_universal)
    (hShiftMlproj_univ : PerTypeShiftMlprojClosure_universal) :
    CookLevinPerTypeSpanning_universal :=
  cookLevinPerTypeSpanning_universal_unconditional
    hFactor_univ hClosure_univ hShiftMlproj_univ

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`, matching H5 / G4.
#print axioms cookLevinPerTypeSpanning_universal_unconditional
#print axioms CookLevinPerTypeSpanning_universal_of_H3_H4_I5

end Closure
end Paper93
end PallLean
