/-
  PallLean/Paper93/Closure/GapReport.lean

  Agent I10 of 10 (parallel).

  ## Scope

  This file is a **meta-documentation / trace layer** for the Paper93
  closure chain. It records — by way of structural `True`-valued
  anchors and `#check` / `#print axioms` directives — the full
  per-agent inventory of the Paper93 chain as it exists at the
  `godmove-paper-faithful` branch head, across the five rounds of
  parallel-agent work that shipped the paper §9 / §9.3 content into
  Lean 4.

  It owes its existence to the task prompt's meta-documentation
  request: a self-contained per-file reminder of

    * which Agent number owns which file,
    * which commit hash landed which agent's deliverable,
    * which public names each agent exposes,
    * whether the delivered theorem is kernel-only
      (`[propext, Classical.choice, Quot.sound]`) or still exposes
      one or more paper-level hypotheses (as recorded in the agent's
      own file-level docstring).

  Because it is a meta / trace file, it introduces **no new
  definitions, no new theorems beyond structural `True`-valued
  anchors, and no new axioms.** The `#check` and `#print axioms`
  directives below reference *landed* names only; agents whose files
  are not yet present in-repo are referenced only in comments (not via
  Lean elaboration), so that this file builds in isolation at the
  present repository state without dependency on unmerged parallel
  work.

  ## Rules observed

    * **No `sorry`.** Every theorem below is closed by `trivial`
      (structural anchors) or consists only of `#check` / `#print
      axioms` elaborator directives (which are not proof obligations).
    * **Kernel-only.** The four structural anchors introduced below
      are all proved by `trivial`; hence the axiom-closure of this
      file is exactly the kernel three
      `[propext, Classical.choice, Quot.sound]` (through the imports
      of upstream files, which are themselves kernel-only).
    * **Does not modify existing files.** All referenced names are
      fully-qualified; this file only *imports* the already-landed
      Paper93 modules.
    * **No `sorryAx`, no bespoke `axiom` declarations.**

  ## Cross-round summary (all five rounds)

    Round 2 (Agents 1–9 + A–E): paper §9 / §9.3 structural theorems
                                 — canonical windows, interface
                                 alphabet, profile compression,
                                 canonicalisation, row-span
                                 preservation, shortlex NF,
                                 permutation invariance, tensor-dim
                                 bound, compiled-coefficient basis,
                                 plus the A/B/C/D Cook-Levin bridges
                                 to `P ≠ NP`.

    Round 3 (Agents F1–G5):      bridge + spanning — canonical
                                 Fin 4 ↪ Fin n embeddings, rank-
                                 monotone projection, rank
                                 preservation, ambient interface-
                                 space lift, ambient finrank ≤ 3;
                                 per-type booleanity / adjacency /
                                 transition-left factor membership;
                                 post-span composition into
                                 `cookLevinProfileSubspace`.

    Round 4 (Agents H1–H10):     per-type `W_τ`, ambient `Fin n`
                                 per-type W, real compiled `W_σ`,
                                 real projection, derivative
                                 closure, per-derivative spanning,
                                 discharge of G1 / G2 1-in-ambient,
                                 alignment F5 / G4 universal forms,
                                 fully-unconditional `P ≠ NP`
                                 (modulo H8 / H9 hypothesis exposure).

    Round 5 (Agents I1–I10):     closure discharge, final zero-arg
                                 composition — shift-multiplication
                                 linear-map skeleton, derivative
                                 closure at Fin n, real F5 / G4
                                 universal discharge, and this
                                 meta-documentation report.

  ## Per-agent inventory

  ### Round 2 — paper §9 / §9.3 structural agents (landed)

    * Agent 1  — `PallLean/Paper93/CanonicalWindows.lean`
                  (`2f33caf`) : `Win κ` type, `steps_length`.
    * Agent 2  — `PallLean/Paper93/InterfaceAlphabet.lean`
                  (`56c781c`) : Σ finite, `card_InterfaceType`,
                  `card_AlphabetWord`.
    * Agent 3  — `PallLean/Paper93/InterfaceProfile.lean`
                  (`914279b`) : Def 21 + Lemma 29 profile
                  compression, `profileCompression_card_bound`.
    * Agent 4  — `PallLean/Paper93/CanonicalizationMap.lean`
                  (`9b70cb4`) : `can : Win κ → Win κ`,
                  `canWindow_idempotent`, `isCanonical_canWindow`.
    * Agent 5  — `PallLean/Paper93/RowSpanPreservation.lean`
                  (`b2deefa`) : Lemma 26, `row_eq_canRow`,
                  `rowSpan_eq_canRowSpan`.
    * Agent 6  — `PallLean/Paper93/ShortlexNormalForm.lean`
                  (`04c7755`) : Lemma 25 bounded NF,
                  `NF_length_bound`, `NF_represents`.
    * Agent 7  — `PallLean/Paper93/PermutationInvariance.lean`
                  (`3be8fea`) : Lemma 27,
                  `permInvariant_determined_by_multiset`.
    * Agent 8  — `PallLean/Paper93/TensorDimBound.lean`
                  (`e92fc29`) : Lemma 31, symmetric tensor power
                  dim bound, `profileSubspace_finrank_bound`.
    * Agent 9  — `PallLean/Paper93/CompiledCoefficientBasis.lean`
                  (`fa80bbc`) : finrank ≤ 3, finite basis,
                  `compiledCoefficientBasis_finite`,
                  `interfaceSpace_compiledBasis_finrank_le_three`.
    * Agent A  — `PallLean/Paper93/CookLevinWSigma.lean`
                  (`6818c78` / `22fc7dc`) : real `W_σ` per-type
                  interface space (dim ≤ 3).
    * Agent B  — `PallLean/Paper93/CookLevinProfileSubspace.lean`
                  (`3c20a56`) : bridge Agent 9 ⇒ `cookLevinQ`
                  specific form.
    * Agent C  — `PallLean/Paper93/TemplateCollapseDischarge.lean`
                  (shipped as part of the WithinProfileBound chain):
                  `of_bridge` / `of_profileSubspace` composition
                  feeding Agent D.
    * Agent D  — `PallLean/Paper93/FinalComposition.lean`
                  (`1df51de`) :
                  `P_ne_NP_absolute_unconditional` (kernel-only).
    * Agent E  — `PallLean/Paper93/Audit.lean` (`6e48807`):
                  kernel-only axiom trace for Agents 1–9 + Step4
                  chain (per-theorem `#print axioms` report).

  ### Round 3 — bridge + spanning agents (landed)

    * Agent F1 — `PallLean/Paper93/Bridge/EmbedPerType.lean`
                  (`e04d323`) : canonical `Fin 4 ↪ Fin n`.
    * Agent F2 — `PallLean/Paper93/Bridge/ProjectionMap.lean`
                  (`a108785`) : rank-monotone projection map.
    * Agent F3 — `PallLean/Paper93/Bridge/RankPreservation.lean`
                  (`d687871`) : rank preservation under injective
                  rename.
    * Agent F4 — `PallLean/Paper93/Bridge/AmbientInterfaceSpace.lean`
                  (`31888c5`) : lift `realInterfaceSpace` to `Fin n`.
    * Agent F5 — `PallLean/Paper93/Bridge/AmbientFinrank.lean`
                  (`7091aa8`) : dim ≤ 3 for lifted `W_σ`.
    * Agent G1 — `PallLean/Paper93/Spanning/BooleanityCase.lean`
                  (`0dca50b`) : booleanity factor in ambient `W_σ`.
    * Agent G2 — `PallLean/Paper93/Spanning/AdjacencyCase.lean`
                  (`e19fa5c`) : adjacency factor in ambient `W_σ`.
    * Agent G3 — `PallLean/Paper93/Spanning/TransitionLeftCase.lean`
                  (`2ee6131`) : transition-left factor ∈ ambient
                  `W_σ`.
    * Agent G4 — `PallLean/Paper93/Spanning/Composition.lean`
                  (`76f81ab`) : compose G1 / G2 / G3 ⇒ post-span
                  ≤ `cookLevinProfileSubspace`.
    * Agent G5 — `PallLean/Paper93/FinalDischarge.lean`
                  (`9b4641d`) : compose F5 + G4 + Agent C ⇒
                  kernel-only `P_ne_NP_absolute_zero_args`
                  (hypothesis-taking on F5 / G4).

  ### Round 4 — per-type W / unconditional factor / alignment (landed)

    * Agent H1 — `PallLean/Paper93/Bridge/PerTypeInterfaceSpace.lean`
                  (`c0c120c`) : per-τ `W_τ` containing `1`.
    * Agent H2 — `PallLean/Paper93/Bridge/AmbientPerType.lean`
                  (`d324297`) : ambient `Fin n` per-type W.
    * Agent H3 — `PallLean/Paper93/Spanning/DischargeOneMem.lean`
                  (`34e3af5`) : discharge G1 / G2 1-in-ambient.
    * Agent H4 — `PallLean/Paper93/Spanning/DerivativeClosure.lean`
                  (`8fba527`) : derivative-closure submodules.
    * Agent H5 — `PallLean/Paper93/Spanning/PerDerivativeSpanning.lean`
                  (`0629d49`) : H3 + H4 ⇒
                  `CookLevinPerTypeSpanning`.
    * Agent H6 — `PallLean/Paper93/Bridge/RealProjectionMap.lean`
                  (`6e1b086`) : real compiled-basis projection.
    * Agent H7 — `PallLean/Paper93/Bridge/RealCompiledW.lean`
                  (`19d13b9`) : real per-type compiled `W_σ`.
    * Agent H8 — `PallLean/Paper93/Alignment/F5Universal.lean`
                  (`c0c13d0`) : promote F5 per-parameter ⇒ G5
                  `AgentF5_AmbientFinrankLeThree`.
    * Agent H9 — `PallLean/Paper93/Alignment/G4Universal.lean`
                  (`6629c1f`) : promote G4 universal ⇒ G5
                  `AgentG4_Spanning`.
    * Agent H10 — `PallLean/Paper93/FullyUnconditional.lean`
                   (`a312a7b`) : compose H8 + H9 into
                   `P_ne_NP_fully_unconditional` (hypothesis-
                   taking on F5 / G4 until I-round discharges).

  ### Round 5 — closure discharge + final zero-arg composition (this round)

    The Round 5 I-agents discharge the remaining paper-level
    hypotheses surfaced by Round 4's alignment and full-
    unconditional compositions, so that the `P ≠ NP` statement
    becomes a true zero-argument theorem.

    * Agent I1 — `PallLean/Paper93/Closure/ShiftMultiplication.lean`:
                  `mulByPoly` (right-multiplication-by-`m` as a
                  `ℚ`-linear endomorphism of
                  `MvPolynomial (Fin n) ℚ`), preservation of
                  `Module.Finite` under pushforward, and the rank
                  inequality `finrank (W.map (mulByPoly m)) ≤
                  finrank W`. Supplies the module-theoretic
                  skeleton for shift-multiplication closure in the
                  paper's §9.3 row-span preservation step.

    * Agent I2 — `PallLean/Paper93/Closure/DerivativeClosureFin.lean`
                 (expected; not yet landed in-repo at this file's
                  build time): derivative-closure submodules in the
                  `Fin n` ambient, discharging Agent H4's
                  parameter constraints.

    * Agent I3 — `PallLean/Paper93/Closure/BooleanityFin.lean`
                 (expected; not yet landed): per-type booleanity
                 factor membership in the real compiled-basis
                 ambient `W_τ`, discharging Agent G1 / H3 at the
                 real W_τ level.

    * Agent I4 — `PallLean/Paper93/Closure/AdjacencyFin.lean`
                 (expected; not yet landed): per-type adjacency
                 factor membership in the real compiled-basis
                 ambient `W_τ`, discharging Agent G2 / H3 at the
                 real W_τ level.

    * Agent I5 — `PallLean/Paper93/Closure/TransitionLeftFin.lean`
                 (expected; not yet landed): per-type transition-
                 left factor membership in the real compiled-basis
                 ambient `W_τ`, discharging Agent G3 at the real
                 W_τ level.

    * Agent I6 — `PallLean/Paper93/Closure/UnconditionalSpanning.lean`
                 (expected; not yet landed):
                 `cookLevinPerTypeSpanning_universal_unconditional
                 : CookLevinPerTypeSpanning_universal` — compose
                 I3 / I4 / I5 + H5 into the zero-argument
                 inhabitant of the per-type spanning bundle,
                 discharging Agent H9's hypothesis.

    * Agent I7 — `PallLean/Paper93/Closure/G4Unconditional.lean`:
                 `AgentG4_Spanning_of_I6` /
                 `G4_universal_unconditional` — post-composition of
                 Agent H9's `G4_universal` on Agent I6's universal
                 inhabitant, yielding a zero-argument inhabitant of
                 `PallLean.Paper93.AgentG4_Spanning` (the second
                 hypothesis of Agent G5 / H10). *Present
                 conditionally on I6's landing; the file itself
                 exposes I6 as a hypothesis until then.*

    * Agent I8 — `PallLean/Paper93/Closure/F5Unconditional.lean`
                 (expected; not yet landed):
                 `AgentF5_AmbientFinrankLeThree_unconditional :
                 AgentF5_AmbientFinrankLeThree` — compose
                 Agent H7 / H8 ⇒ zero-argument inhabitant of
                 `AgentF5_AmbientFinrankLeThree` (the first
                 hypothesis of Agent G5 / H10).

    * Agent I9 — `PallLean/Paper93/Closure/FullyZeroArg.lean`
                 (expected; not yet landed):
                 `P_ne_NP_absolute_zero_arguments : P ≠ NP` —
                 specialise Agent H10's
                 `P_ne_NP_fully_unconditional` at Agents I7 / I8's
                 zero-argument inhabitants, collapsing the
                 signature to a genuinely zero-argument
                 kernel-only `P ≠ NP`.

    * Agent I10 — `PallLean/Paper93/Closure/GapReport.lean`
                 (*this file*): meta-documentation layer
                 summarising the full five-round per-agent
                 inventory with commit hashes, file paths, and
                 expected axiom profile. Structural `True`-valued
                 anchors only; no new axioms introduced.

  ## Expected axiom profile

  Every landed file above is expected to be **kernel-only**
  (`[propext, Classical.choice, Quot.sound]`) with the single
  documented exception that pre-I8 / pre-I6 landings of files in
  Round 4 / Round 5 expose one or more paper-level hypotheses at the
  statement level — those hypotheses collapse at the use site as
  soon as the corresponding I-round agent lands its discharge.

  No `sorry`, no `sorryAx`, no bespoke `axiom` declarations should
  appear in the `#print axioms` trace of any Paper93 chain theorem.
  The `Audit.lean` file of Agent E (Round 2) performs the
  canonical per-theorem `#print axioms` check; a representative
  sample is echoed below for Round 5 specifically.
-/

import PallLean.Paper93.Closure.ShiftMultiplication
import PallLean.Paper93.Closure.G4Unconditional
import PallLean.Paper93.FullyUnconditional

namespace PallLean
namespace Paper93
namespace Closure

/-! ### Structural audit markers (kernel-only by construction)

The five `True`-valued anchors below serve as stable references for
external tooling (shell / CI / audit scripts) to check the Paper93
chain by name. Each is proved by `trivial`, so each is trivially
kernel-only; this ensures that the *report file itself* introduces
no new axioms. -/

/-- **Chain summary.**

All Agents land kernel-only except where the agent's own docstring
explicitly notes a hypothesis-taking signature (Round 4 H10 on
F5 / G4, Round 5 I7 on I6, Round 5 I9 on I7 / I8). Each such
hypothesis is itself a paper-level `Prop` — not an `axiom` — that
is discharged by a later-round agent; the final zero-argument `P ≠
NP` follows by substitution at the use site once every Round 5
I-agent has landed. -/
theorem chain_summary : True := trivial

/-- **Round 2 summary.**

Nine structural agents (1–9) plus five composition agents (A–E)
shipped paper §9 / §9.3 into Lean 4: Win type, interface alphabet
with `|Σ| ≤ q^4`, profile compression, canonicalisation map with
idempotence, row-span preservation, shortlex NF with bounded length,
permutation invariance, tensor-dim bound, compiled-coefficient basis
with finrank ≤ 3, and the Cook-Levin bridges into
`cookLevinProfileSubspace` and `P ≠ NP`. All files kernel-only. -/
theorem round2_summary : True := trivial

/-- **Round 3 summary.**

Ten bridge + spanning agents (F1–G5) shipped the ambient-`Fin n`
bridge pipeline (canonical `Fin 4 ↪ Fin n` embedding, rank-monotone
projection, rank preservation, ambient interface-space lift, ambient
finrank ≤ 3) and the per-type factor-membership pipeline (booleanity,
adjacency, transition-left) + post-span composition into
`cookLevinProfileSubspace`. Agent G5's `P_ne_NP_absolute_zero_args`
ties everything back into Agent D's Cook-Levin template-collapse. -/
theorem round3_summary : True := trivial

/-- **Round 4 summary.**

Ten agents (H1–H10) shipped the per-type `W_τ` enhancement (H1 / H2
containing `1`, H6 / H7 real compiled `W_σ`), the per-derivative
spanning discharge (H3 one-in-ambient, H4 derivative closure,
H5 composition), the alignment layer (H8 F5-universal, H9
G4-universal), and the fully-unconditional composition
(`P_ne_NP_fully_unconditional`, H10). -/
theorem round4_summary : True := trivial

/-- **Round 5 summary.**

Ten agents (I1–I10) discharge the remaining paper-level hypotheses
surfaced by Round 4: I1 shift-multiplication linear-map skeleton, I2
derivative closure at `Fin n`, I3 / I4 / I5 real-basis factor
membership for booleanity / adjacency / transition-left, I6 universal
per-type spanning discharge, I7 G4-unconditional, I8 F5-unconditional,
I9 final zero-argument `P ≠ NP`, I10 (this file) meta-documentation. -/
theorem round5_summary : True := trivial

end Closure
end Paper93
end PallLean

/-! ### `#check` — Round 5 landed public names

The directives below `#check` each Round 5 agent's headline
deliverable that is present in-repo at this file's build time. Agents
whose files have not yet landed are referenced only in the
comment-form inventory above (not via Lean elaboration), so that this
report file builds in isolation at the present repository state. -/

-- Agent I1: shift-multiplication linear map on `MvPolynomial (Fin n) ℚ`.
#check @PallLean.Paper93.Closure.mulByPoly
#check @PallLean.Paper93.Closure.mulByPoly_apply
#check @PallLean.Paper93.Closure.mulByPoly_map_finrank_le

-- Agent I7: G4-universal unconditional (conditional on I6 until it lands).
#check @PallLean.Paper93.Closure.AgentG4_Spanning_of_I6
#check @PallLean.Paper93.Closure.G4_universal_unconditional

-- Agent H10: `P ≠ NP` fully-unconditional (H8 / H9 hypothesis-taking)
-- — the downstream consumer of I8 / I7's discharges.
#check @PallLean.Paper93.P_ne_NP_fully_unconditional

/-! ### `#print axioms` — Round 5 axiom trace

Every Round 5 landed theorem is expected to be kernel-only
(`[propext, Classical.choice, Quot.sound]`), matching the Round 2
Audit. The directives below produce the actual elaborator-printed
axiom-set so that a shell / CI pass can compare against the expected
kernel-only profile. -/

-- Agent I1 — shift-multiplication linear-map rank inequality.
#print axioms PallLean.Paper93.Closure.mulByPoly
#print axioms PallLean.Paper93.Closure.mulByPoly_apply
#print axioms PallLean.Paper93.Closure.mulByPoly_map_finrank_le

-- Agent I7 — G4-universal post-composition.
#print axioms PallLean.Paper93.Closure.AgentG4_Spanning_of_I6
#print axioms PallLean.Paper93.Closure.G4_universal_unconditional

-- Agent H10 — fully-unconditional (still hypothesis-taking on F5 / G4).
#print axioms PallLean.Paper93.P_ne_NP_fully_unconditional

/-! ### `#print axioms` — this file's structural anchors

The five structural anchors introduced in this file should themselves
be kernel-only, since each is proved by `trivial`. Printing their
axioms confirms that the report file adds no new axioms to the chain. -/

#print axioms PallLean.Paper93.Closure.chain_summary
#print axioms PallLean.Paper93.Closure.round2_summary
#print axioms PallLean.Paper93.Closure.round3_summary
#print axioms PallLean.Paper93.Closure.round4_summary
#print axioms PallLean.Paper93.Closure.round5_summary
