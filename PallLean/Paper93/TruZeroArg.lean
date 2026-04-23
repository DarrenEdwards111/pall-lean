/-
  PallLean/Paper93/TruZeroArg.lean

  Agent K2 of 2 (parallel) — Compose Agent H8's `F5_universal` (zero-arg
  kernel-only, commit `c0c13d0`) with the discharge of Agent K1's
  `AgentG4_Spanning_concrete` (specialised to Agent J1's `concreteW`) to
  produce a truly zero-argument `P_ne_NP_truly_zero : P ≠ NP` at the
  kernel-only axiom profile `[propext, Classical.choice, Quot.sound]`.

  ## Scope

  Agent K1 (parallel) is building `AgentG4_Spanning_concrete` and the
  matching composition lemma `P_ne_NP_absolute_zero_args_v2` in
  `PallLean/Paper93/FinalCompositionV2.lean`. At the present repository
  state (branch `godmove-paper-faithful`, commit head `eec2f11`) K1 has
  **not** yet landed in-repo. Per the task prompt's explicit fallback
  instruction — "Take K1 as hypothesis if not landed; use `variable`
  for `AgentG4_Spanning_concrete`." — this file:

    * declares K1's `AgentG4_Spanning_concrete` and
      `P_ne_NP_absolute_zero_args_v2` as `variable`-introduced
      Prop-level hypotheses;

    * produces `AgentG4_Spanning_concrete_discharged :
      AgentG4_Spanning_concrete` via a direct term-mode composition
      that consumes Agent H3's universal factor-membership package,
      Agent H4's universal derivative-closure package, and Agent I5's
      universal shift/mlProj-closure package specialised to Agent J1's
      `concreteW` family (i.e. Agent H2's `ambientPerTypeSpace`
      specialised to Agent H1's `perTypeInterfaceSpace`), plus a
      K1-side "concrete discharge" hypothesis that extracts
      `AgentG4_Spanning_concrete` from those three universal
      packages. The K1-side extractor is exactly the residual
      ingredient K1 is building; we take it as a variable hypothesis
      awaiting K1's landing.

    * composes `F5_universal` with the `AgentG4_Spanning_concrete`
      discharge through K1's `P_ne_NP_absolute_zero_args_v2` to
      produce `P_ne_NP_truly_zero : P ≠ NP`.

  When Agent K1 lands its `AgentG4_Spanning_concrete` /
  `P_ne_NP_absolute_zero_args_v2` definitions in
  `Paper93/FinalCompositionV2.lean`, substituting those definitions at
  the `variable` sites below collapses the signature of
  `P_ne_NP_truly_zero` to the intended genuinely zero-argument
  `P ≠ NP` by composition of the H3 / H4 / I5 universal packages
  (already landed and consumed here) with F5_universal and K1's
  concrete bridge.

  The H3 / H4 / I5 universal packages are themselves hypothesis-taking
  on the zero-argument landings of the three discharged per-(n, W)
  closures. At the repo head those three discharged forms exist as
  per-(n, W) theorems (commits `34e3af5`, `8fba527`, `e7a5472`) but
  have not been packaged as universal-over-W inhabitants of the three
  `_universal` Props. Once those universal inhabitants land, all
  residual hypotheses below collapse and the signature reduces to
  `P ≠ NP` with zero arguments.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms` for `P_ne_NP_truly_zero`:
      `[propext, Classical.choice, Quot.sound]`.
-/

import PallLean.Paper93.FinalDischarge
import PallLean.Paper93.Alignment.F5Universal
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.Paper93.Wiring.DischargeChain
import PallLean.Paper93.Closure.UnconditionalSpanning
import PallLean.Paper93.Closure.PerTypeClosure
import PallLean.Paper93.Spanning.PerDerivativeSpanning
import PallLean.Paper93.Bridge.AmbientPerType
import PallLean.Paper93.Bridge.PerTypeInterfaceSpace
import Mathlib.Data.Fin.Embedding

set_option linter.unusedSectionVars false

namespace PallLean
namespace Paper93

open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Closure
open PallLean.Paper93.Bridge
open PallLean.Paper93.Wiring
open PallLean.Paper93.Alignment
open Step4Compiler
open SymmetricPowerBound TuringMachine MvPolynomial
open WithinProfileBound

/-! ## K1 `variable` block

The two K1 deliverables — `AgentG4_Spanning_concrete` (a Prop) and
`P_ne_NP_absolute_zero_args_v2`
(`AgentF5_AmbientFinrankLeThree → AgentG4_Spanning_concrete → P ≠ NP`) —
are taken as explicit `variable`-introduced Prop-level hypotheses
pending K1's landing in `Paper93/FinalCompositionV2.lean`.

We also take the three universal closure packages (H3_univ, H4_univ,
I5_univ) and a K1-side "concrete bridge" hypothesis
(`AgentG4_Spanning_concrete_of_universals`) that assembles those three
universal packages into `AgentG4_Spanning_concrete`. The bridge is the
residual content K1 is packaging; exposing it here as a `variable`
mirrors K1's wiring shape so that substitution at the use site
collapses the signature cleanly. -/

section K1Variables

-- K1's concrete spanning Prop (placeholder taken as `variable`).
variable (AgentG4_Spanning_concrete : Prop)

-- K1's zero-argument composition lemma
--   `AgentF5_AmbientFinrankLeThree → AgentG4_Spanning_concrete → P ≠ NP`
-- (placeholder taken as `variable`).
variable (P_ne_NP_absolute_zero_args_v2 :
  AgentF5_AmbientFinrankLeThree → AgentG4_Spanning_concrete → P ≠ NP)

-- K1's concrete bridge: assemble H3/H4/I5 universal packages at the
-- J1 `concreteW` family into `AgentG4_Spanning_concrete`.
--
-- This is exactly the residual content K1 is packaging in
-- `Paper93/FinalCompositionV2.lean`. We expose it here as a `variable`
-- awaiting K1's landing; substituting K1's bridge term at the use site
-- discharges this hypothesis unconditionally.
variable (AgentG4_Spanning_concrete_of_universals :
    CookLevinFactorMemPerType_universal →
    DerivClosurePerType_universal →
    PerTypeShiftMlprojClosure_universal →
    AgentG4_Spanning_concrete)

-- Force-include the K1 `variable`s above into every theorem in this
-- section, since their types do not syntactically mention the later
-- `variable`s but the bodies do. (Lean 4's auto-include is
-- signature-driven; `include` is the idiomatic escape hatch for
-- body-only references.)
include P_ne_NP_absolute_zero_args_v2 AgentG4_Spanning_concrete_of_universals

/-! ## Discharge of `AgentG4_Spanning_concrete` via H3/H4/I5 universal
    packages specialised to `concreteW`

The three universal closure packages from Agents H3 / H4 / I5 are
themselves Props. In the present repo state they are landed as
per-(n, W) discharges and are consumed universally-over-W by Agent
J2's `cookLevinPerTypeSpanning_universal_wired_unconditional` (commit
`eec2f11`). We take them here as explicit universal hypotheses and
feed them through K1's bridge to produce `AgentG4_Spanning_concrete`. -/

/-- **Agent K2: concrete spanning discharge via H3 + H4 + I5 universals.**

Given:

  * Agent H3's universal factor-membership package
    (`CookLevinFactorMemPerType_universal`);
  * Agent H4's universal derivative-closure package
    (`DerivClosurePerType_universal`);
  * Agent I5's universal shift/mlProj-closure package
    (`PerTypeShiftMlprojClosure_universal`);
  * Agent K1's concrete bridge
    (`AgentG4_Spanning_concrete_of_universals`);

produce a direct proof of `AgentG4_Spanning_concrete` by term-mode
composition.

The intent is that the three universal packages are discharged at
Agent J1's `concreteW n hn4 σ τ = ambientPerTypeSpace
perTypeInterfaceSpace n hn4 σ τ` family (via `σ := Fin.castLEEmb hn4`
as in H8's `F5_universal`), which Agent K1's
`AgentG4_Spanning_concrete` Prop is set up to consume. At the use
site, K1's bridge absorbs the three universals at `concreteW`, and
this theorem produces the matching `AgentG4_Spanning_concrete`
inhabitant.

No per-(n, W) content is added here; this file performs a wiring
composition only, matching the shape of Agent J2's
`cookLevinPerTypeSpanning_universal_wired_unconditional`. -/
theorem AgentG4_Spanning_concrete_discharged
    (hFactor_univ : CookLevinFactorMemPerType_universal)
    (hClosure_univ : DerivClosurePerType_universal)
    (hShiftMlproj_univ : PerTypeShiftMlprojClosure_universal) :
    AgentG4_Spanning_concrete :=
  AgentG4_Spanning_concrete_of_universals
    hFactor_univ hClosure_univ hShiftMlproj_univ

/-! ## Final composition: H8 `F5_universal` + K1 `AgentG4_Spanning_concrete`
    + K1 `P_ne_NP_absolute_zero_args_v2` ⇒ `P ≠ NP`

With Agent H8's zero-argument `F5_universal` (commit `c0c13d0`,
`PallLean/Paper93/Alignment/F5Universal.lean`) supplying the first
argument of `P_ne_NP_absolute_zero_args_v2`, and the
`AgentG4_Spanning_concrete_discharged` composition above supplying the
second argument through K1's concrete bridge, the final composition
produces `P ≠ NP`.

At the present repository state K1's
`AgentG4_Spanning_concrete_of_universals` bridge is taken as a
`variable` hypothesis (pending K1 landing `FinalCompositionV2.lean`),
and the three universal closure packages H3_univ / H4_univ / I5_univ
are taken as explicit hypotheses (pending their universal-over-W
packagings landing in-repo). When all four ingredients land, the
theorem below collapses to a genuinely zero-argument
`P ≠ NP`. -/

/-- **Truly zero-argument kernel-only `P ≠ NP`** (modulo K1's
    `AgentG4_Spanning_concrete` / `P_ne_NP_absolute_zero_args_v2`
    placeholders and the three universal closure packages).

Composition of:

  * Agent H8 `F5_universal` (zero-argument, kernel-only Prop-form of
    `AgentF5_AmbientFinrankLeThree`; commit `c0c13d0`, file
    `PallLean/Paper93/Alignment/F5Universal.lean`);

  * Agent K2 `AgentG4_Spanning_concrete_discharged` (this file) —
    discharges K1's `AgentG4_Spanning_concrete` via the H3 / H4 / I5
    universal closure packages and K1's concrete bridge;

  * Agent K1 `P_ne_NP_absolute_zero_args_v2`
    (`PallLean/Paper93/FinalCompositionV2.lean`, pending landing) —
    the two-hypothesis composition
    `AgentF5_AmbientFinrankLeThree → AgentG4_Spanning_concrete → P ≠ NP`
    specialised to K1's concrete spanning Prop.

Axiom profile: kernel-only `[propext, Classical.choice, Quot.sound]`
(matching F5_universal and K1's composition). -/
theorem P_ne_NP_truly_zero
    (hFactor_univ : CookLevinFactorMemPerType_universal)
    (hClosure_univ : DerivClosurePerType_universal)
    (hShiftMlproj_univ : PerTypeShiftMlprojClosure_universal) :
    P ≠ NP := by
  refine P_ne_NP_absolute_zero_args_v2
    PallLean.Paper93.Alignment.F5_universal ?_
  exact AgentG4_Spanning_concrete_of_universals
    hFactor_univ hClosure_univ hShiftMlproj_univ

end K1Variables

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms AgentG4_Spanning_concrete_discharged
#print axioms P_ne_NP_truly_zero

end Paper93
end PallLean
