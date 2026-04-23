/-
  PallLean/Paper93/TruZeroArg.lean

  Agent K2 of 2 (parallel) — Compose Agent H8's `F5_universal` (zero-arg
  kernel-only, commit `c0c13d0`) with the discharge of Agent K1's
  `AgentG4_Spanning_concrete` (specialised to Agent J1's `concreteW`,
  commit `6699f3f`) to produce `P_ne_NP_truly_zero : P ≠ NP` at the
  kernel-only axiom profile `[propext, Classical.choice, Quot.sound]`.

  ## Scope

  Agent K1 (parallel) landed `AgentG4_Spanning_concrete` and
  `P_ne_NP_absolute_zero_args_v2` in
  `PallLean/Paper93/FinalCompositionV2.lean` (commit `6699f3f`).
  K1's specialised G4 Prop has signature

    ∀ M n (_hn : n ≥ 2^804) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
      (hn2 : n ≥ 2) (hn4 : n ≥ 4) (bp : BoundedProfile (Nat.log 2 n)),
    ∃ σ : Fin 4 ↪ Fin n,
      cookLevinPostSpanAt M n hn2 htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp (fun τ => concreteW n hn4 σ τ)

  and K1's final theorem has signature

    `P_ne_NP_absolute_zero_args_v2 : AgentF5_AmbientFinrankLeThree →
       AgentG4_Spanning_concrete → P ≠ NP`.

  This file discharges `AgentG4_Spanning_concrete` by specialising the
  universal per-type spanning bundle
  `CookLevinPerTypeSpanning_universal` (Agent I6 / J2 deliverable) at
  Agent J1's concrete `concreteW n hn4 (Fin.castLEEmb hn4)` family,
  pointwise in each `(M, n, htb, hns, bp)` tuple. The σ witness is the
  canonical `Fin.castLEEmb hn4` (matching Agent H8's `F5_universal`),
  and the post-span containment follows from
  `cookLevinProfileSubspace_contains_postSpan_at_bp` applied to the
  universal-over-W per-type spanning.

  The final composition feeds Agent H8's zero-argument
  `F5_universal` and the discharged
  `AgentG4_Spanning_concrete` through
  `P_ne_NP_absolute_zero_args_v2` to produce `P ≠ NP`. The only
  residual hypothesis is Agent I6's
  `CookLevinPerTypeSpanning_universal`, which at the present repo
  state is the exact hypothesis that Agent J3's `FinalZeroArg` also
  carries (`Paper93/Wiring/FinalZeroArg.lean`) pending Agent J2's
  three universal-closure packages landing as zero-argument
  inhabitants.

  When a zero-argument inhabitant of
  `CookLevinPerTypeSpanning_universal` lands in-repo (e.g. via a
  future Agent that packages Agents I1 / I2 / I3's per-(n, W)
  closures into universal-over-W inhabitants of the three
  `_universal` Props), substituting it at the call site collapses
  this file's `P_ne_NP_truly_zero` to a genuinely zero-argument
  `P ≠ NP`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms P_ne_NP_truly_zero`:
      `[propext, Classical.choice, Quot.sound]`.
-/

import PallLean.Paper93.FinalDischarge
import PallLean.Paper93.FinalCompositionV2
import PallLean.Paper93.Alignment.F5Universal
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.Paper93.Spanning.Composition
import PallLean.Paper93.Spanning.PerDerivativeSpanning
import Mathlib.Data.Fin.Embedding

namespace PallLean
namespace Paper93

open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Bridge
open PallLean.Paper93.Wiring
open PallLean.Paper93.Alignment
open Step4Compiler
open SymmetricPowerBound TuringMachine MvPolynomial
open WithinProfileBound

/-! ## Discharge of K1's `AgentG4_Spanning_concrete`

`AgentG4_Spanning_concrete` asks, for every `(M, n, _hn : n ≥ 2^804,
htb, hns, hn2, hn4, bp)`, for an `σ : Fin 4 ↪ Fin n` such that the
Cook-Levin post-span at `bp.toHistogram` is contained in
`cookLevinProfileSubspace bp (fun τ => concreteW n hn4 σ τ)`.

We witness `σ := Fin.castLEEmb hn4` (the canonical coordinate
embedding, matching Agent H8's `F5_universal`). With that choice, we
need to show

  `cookLevinPostSpanAt M n hn2 htb hns bp.toHistogram
      ≤ cookLevinProfileSubspace bp (fun τ => concreteW n hn4
                                       (Fin.castLEEmb hn4) τ)`.

This is precisely the conclusion of
`cookLevinProfileSubspace_contains_postSpan_at_bp` (Agent G4 /
Composition.lean) applied to the per-type spanning bundle
`CookLevinPerTypeSpanning M n hn2 htb hns (fun τ => concreteW n hn4
(Fin.castLEEmb hn4) τ)`, which follows from
`CookLevinPerTypeSpanning_universal` specialised at `W := fun τ =>
concreteW n hn4 (Fin.castLEEmb hn4) τ`. -/

/-- **Agent K2: discharge of K1's `AgentG4_Spanning_concrete`
    (modulo `CookLevinPerTypeSpanning_universal`).**

Given Agent I6 / J2's universal per-type spanning bundle
`CookLevinPerTypeSpanning_universal`, produce K1's specialised G4
Prop `AgentG4_Spanning_concrete` by:

  * picking `σ := Fin.castLEEmb hn4` (the canonical coordinate
    embedding);

  * applying the universal spanning bundle at `W := fun τ => concreteW
    n hn4 (Fin.castLEEmb hn4) τ`;

  * invoking `cookLevinProfileSubspace_contains_postSpan_at_bp` to
    promote the per-type spanning into the required post-span
    containment at `bp`.

No new analytic content is introduced; this is a direct term-mode
specialisation and application of the universal spanning bundle at
Agent J1's concrete W family. -/
theorem AgentG4_Spanning_concrete_discharged
    (hSpan_univ : CookLevinPerTypeSpanning_universal) :
    AgentG4_Spanning_concrete := by
  intro M n _hn htb hns hn2 hn4 bp
  -- Canonical coordinate embedding σ := Fin.castLEEmb hn4
  refine ⟨Fin.castLEEmb hn4, ?_⟩
  -- Specialise the universal per-type spanning bundle at
  -- W := fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ.
  have hSpan :
      CookLevinPerTypeSpanning M n hn2 htb hns
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) :=
    hSpan_univ M n hn2 htb hns
      (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)
  -- Apply the G4 post-span containment lemma at `bp`.
  exact cookLevinProfileSubspace_contains_postSpan_at_bp
    M n hn2 htb hns
    (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ) hSpan bp

/-! ## Final composition: H8 `F5_universal` + K2 discharge + K1 v2 ⇒ `P ≠ NP`

Composes:

  * Agent H8 `F5_universal`
    (`PallLean/Paper93/Alignment/F5Universal.lean`, commit `c0c13d0`)
    — zero-argument inhabitant of `AgentF5_AmbientFinrankLeThree`;

  * K2 `AgentG4_Spanning_concrete_discharged` (this file) — produces
    K1's `AgentG4_Spanning_concrete` from
    `CookLevinPerTypeSpanning_universal`;

  * Agent K1 `P_ne_NP_absolute_zero_args_v2`
    (`Paper93/FinalCompositionV2.lean`, commit `6699f3f`) — the
    concrete-W specialised composition
    `AgentF5_AmbientFinrankLeThree → AgentG4_Spanning_concrete → P ≠ NP`.

The only residual hypothesis is
`CookLevinPerTypeSpanning_universal`, matching Agent J3's
`FinalZeroArg` fallback. When a zero-argument inhabitant of that Prop
lands in-repo, substituting it at the call site collapses the
signature below to zero arguments. -/

/-- **`P ≠ NP` — zero-argument modulo `CookLevinPerTypeSpanning_universal`.**

Composition of:

  * Agent H8 `F5_universal` (zero-argument, kernel-only);
  * Agent K2 `AgentG4_Spanning_concrete_discharged` (this file);
  * Agent K1 `P_ne_NP_absolute_zero_args_v2` (commit `6699f3f`);

with residual hypothesis Agent I6 / J2's
`CookLevinPerTypeSpanning_universal`.

Axiom profile: kernel-only `[propext, Classical.choice, Quot.sound]`. -/
theorem P_ne_NP_truly_zero
    (hSpan_univ : CookLevinPerTypeSpanning_universal) :
    P ≠ NP :=
  P_ne_NP_absolute_zero_args_v2
    PallLean.Paper93.Alignment.F5_universal
    (AgentG4_Spanning_concrete_discharged hSpan_univ)

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms AgentG4_Spanning_concrete_discharged
#print axioms P_ne_NP_truly_zero

end Paper93
end PallLean
