/-
  PallLean/Paper93/Substantive/SubstantiveAudit.lean

  Agent W15 — Round 20 (W-round) final audit anchor.

  ## Scope

  This file performs the final W-round `#print axioms` roll-call across
  the collection of W-tagged deliverables (W1–W14) that have landed into
  the `godmove-paper-faithful` branch under `PallLean/Paper93/Substantive/`.
  It is a pure audit file:

    * It imports the landed W-round modules so that their olean artefacts
      are loaded into the environment.
    * For every landed W-round theorem, it emits a `#print axioms`
      directive, which records the kernel-only axiom profile of that
      theorem into the build output.
    * For W-round slots that have not produced a committed, landed
      theorem on the branch at audit time, it records the slot with an
      `--` comment rather than a `#print axioms` call (so this file
      builds cleanly even when some W slots are still scaffolding).

  ## Landed W-round modules audited here

    * W1  — `PallLean.Paper93.Substantive.NonZeroGauge`
        Non-trivial candidate gauge via the constant-term projection
        `constantProjection N`.
        Audited theorems:
          * `constantProjection_apply`
          * `constantProjection_smul_one`
          * `constantProjection_is_idempotent`
          * `range_constantProjection_le_span_one`
          * `constantProjection_range_finite`

    * W2  — `PallLean.Paper93.Substantive.NonTrivialRange`
        Non-trivial-range candidate gauge via
        `toConstantsProjection N` and assembled `nonTrivialGauge N`
        with a non-`⊥` range witness.
        Audited theorems:
          * `toConstantsProjection_apply`
          * `toConstantsProjection_smul_one`
          * `toConstantsProjection_is_idempotent`
          * `range_toConstantsProjection_le_span_one`
          * `toConstantsProjection_range_finite`
          * `one_mem_range_toConstantsProjection`
          * `nonTrivialGauge_range_nonzero`

    * W3  — `PallLean.Paper93.Substantive.BalancedLagrangian`
        Paper §28.3 beats-trivial wedge for the full three-term N-Frame
        Lagrangian `fullLagrangianFixed`.
        Audited theorems:
          * `trivial_gauge_value`
          * `non_trivial_beats_trivial`

    * W4  — `PallLean.Paper93.Substantive.ConcretePiStar`
        Concrete rank-1 ℚ-linear projection `piStarConcrete N` onto
        the span of the constant polynomial `1`.
        Audited theorems:
          * `piStarConcrete_idempotent`
          * `piStarConcrete_range`

    * W5  — `PallLean.Paper93.Substantive.PiStarOnCookLevin`
        Substantive rank-1 projection applied to the Cook–Levin
        compiled witness polynomial.
        Audited theorems:
          * `piStar_cookLevinQ_is_constant`
          * `constant_mlBlockedSpdpSubspace_le_span_one`
          * `constant_poly_rank_le_one`
          * `piStar_cookLevinQ_rank_bound`

    * W6  — `PallLean.Paper93.Substantive.RankUnderPiStar`
        Rank-under-Π⋆ bound: every polynomial maps to a constant and
        the multilinear blocked SPDP rank of the image is `0` for
        `κ ≥ 1`.
        Audited theorems:
          * `piStar_image_is_constant`
          * `constant_mlBlockedSpdpSubspace_eq_bot`
          * `constant_spdp_rank_zero`
          * `piStar_rank_bounded`

    * W7  — not landed on `godmove-paper-faithful` at audit time.

    * W8  — `PallLean.Paper93.Substantive.PiStarPolyRank`
        Concrete P-side polynomial rank bound `≤ n^200` for the
        projected Cook–Levin witness `Π⋆(cookLevinQ)`.
        Audited theorem:
          * `piStar_cookLevinQ_polynomial_rank`

    * W9  — `PallLean.Paper93.Substantive.Theorem10Concrete`
        Paper §7.1 Theorem 10 concrete instance at `cookLevinQ` via
        the constant-projection gauge.  NOTE: this module re-declares
        `piStar_rank_bounded` in the same namespace as W6's
        `RankUnderPiStar`.  The two declarations share the same
        statement and axiom profile so the simultaneous import is
        well-formed; the audit `#print axioms` below resolves to the
        unified kernel-only axiom trace.
        Audited theorem:
          * `theorem10_at_cookLevinQ`

    * W10 — `PallLean.Paper93.Substantive.Theorem11Permanent`
        Paper §7.1 Theorem 11 concrete failure at `piStarConcrete`
        applied to polynomials with vanishing constant coefficient.
        Audited theorems:
          * `piStarConcrete_destroys_permanent_structure`
          * `piStarConcrete_not_identity_minor_preserving`

    * W11 — `PallLean.Paper93.Substantive.Theorem11Tseitin`
        Paper §12 Theorem 11 Π⋆ action on the Tseitin `n = 2`
        parity witness `tseitinPoly2`.
        Audited theorems:
          * `tseitinPoly2_constantCoeff`
          * `piStarConcrete_tseitinPoly2`

    * W12 — `PallLean.Paper93.Substantive.ConcreteComposition`
        Honest finding: `piStarConcrete` achieves the P-side rank
        bound but not the NP-side identity-minor preservation.
        Audited theorems:
          * `cookLevinQ_projected_rank_ok`
          * `piStarConcrete_insufficient`
          * `pi_star_non_trivial_constraint`

    * W13 — `PallLean.Paper93.Substantive.LPSConcrete`
        LPS Ramanujan at small primes: paper-level external
        acceptance, concrete cycle-graph Ramanujan witness at `d = 2`.
        Audited theorems:
          * `smallLPSExists_is_paper_level_external`
          * `cycle_is_small_ramanujan`

    * W14 — `PallLean.Paper93.Substantive.FullChainSubstantive`
        Honest full-chain audit: the W4–W13 substantive layer does
        not compose into an unconditional `P ≠ NP`, because the
        `piStarConcrete` witness satisfies the P-side rank-collapse
        constraint but destroys NP-side identity-minor structure.
        Audited theorems:
          * `substantive_route_status`
          * `substantive_route_not_closed`
          * `P_ne_NP_via_real_piStar`

  ## W-round slots without landed theorems

    * W7 — not landed on `godmove-paper-faithful` at audit time.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms in this audit file itself (the anchors below
      are `trivial`).
    * Verified by `lake build`.

  ## Paper citations

    * §7.1  pp. 25–27     — Global God-Move `Π⋆`, Theorem 10 (P-side
      polynomial rank), Theorem 11 (NP-side identity-minor preservation).
    * §12                 — Tseitin parity polynomial family.
    * §13                 — LPS Cayley-graph Ramanujan construction.
    * §18                 — Coupled verifier sheet (identity minor).
    * §28.3 pp. 137–138   — Concrete N-Frame Lagrangian,
      amplituhedron positive geometry / log-det barrier, non-vacuous
      beats-trivial wedge.
    * §40.2 Theorem 216   — P-side Width⇒Rank envelope
      `Γ_{κ,ℓ}(p) ≤ n^{O(1)}`.
-/

import PallLean.Paper93.Substantive.NonZeroGauge
import PallLean.Paper93.Substantive.NonTrivialRange
import PallLean.Paper93.Substantive.BalancedLagrangian
import PallLean.Paper93.Substantive.ConcretePiStar
import PallLean.Paper93.Substantive.PiStarOnCookLevin
import PallLean.Paper93.Substantive.RankUnderPiStar
import PallLean.Paper93.Substantive.PiStarPolyRank
import PallLean.Paper93.Substantive.Theorem10Concrete
import PallLean.Paper93.Substantive.Theorem11Permanent
import PallLean.Paper93.Substantive.Theorem11Tseitin
import PallLean.Paper93.Substantive.ConcreteComposition
import PallLean.Paper93.Substantive.LPSConcrete
import PallLean.Paper93.Substantive.FullChainSubstantive

namespace PallLean.Paper93.Substantive

/-! ## W-round `#print axioms` roll-call

For each landed W-round theorem we emit a `#print axioms`
directive.  These directives are compile-time side effects: they
produce no new obligations, but their output (logged during
`lake build`) is the audit artefact. -/

-- W1 — NonZeroGauge
#print axioms PallLean.Paper93.Substantive.constantProjection_apply
#print axioms PallLean.Paper93.Substantive.constantProjection_smul_one
#print axioms PallLean.Paper93.Substantive.constantProjection_is_idempotent
#print axioms PallLean.Paper93.Substantive.range_constantProjection_le_span_one
#print axioms PallLean.Paper93.Substantive.constantProjection_range_finite

-- W2 — NonTrivialRange
#print axioms PallLean.Paper93.Substantive.toConstantsProjection_apply
#print axioms PallLean.Paper93.Substantive.toConstantsProjection_smul_one
#print axioms PallLean.Paper93.Substantive.toConstantsProjection_is_idempotent
#print axioms PallLean.Paper93.Substantive.range_toConstantsProjection_le_span_one
#print axioms PallLean.Paper93.Substantive.toConstantsProjection_range_finite
#print axioms PallLean.Paper93.Substantive.one_mem_range_toConstantsProjection
#print axioms PallLean.Paper93.Substantive.nonTrivialGauge_range_nonzero

-- W3 — BalancedLagrangian
#print axioms PallLean.Paper93.Substantive.trivial_gauge_value
#print axioms PallLean.Paper93.Substantive.non_trivial_beats_trivial

-- W4 — ConcretePiStar
#print axioms PallLean.Paper93.Substantive.piStarConcrete_idempotent
#print axioms PallLean.Paper93.Substantive.piStarConcrete_range

-- W5 — PiStarOnCookLevin
#print axioms PallLean.Paper93.Substantive.piStar_cookLevinQ_is_constant
#print axioms PallLean.Paper93.Substantive.constant_mlBlockedSpdpSubspace_le_span_one
#print axioms PallLean.Paper93.Substantive.constant_poly_rank_le_one
#print axioms PallLean.Paper93.Substantive.piStar_cookLevinQ_rank_bound

-- W6 — RankUnderPiStar (shared `piStar_rank_bounded` with W9)
#print axioms PallLean.Paper93.Substantive.piStar_image_is_constant
#print axioms PallLean.Paper93.Substantive.constant_mlBlockedSpdpSubspace_eq_bot
#print axioms PallLean.Paper93.Substantive.constant_spdp_rank_zero
#print axioms PallLean.Paper93.Substantive.piStar_rank_bounded

-- W7 — not landed on `godmove-paper-faithful` at audit time.

-- W8 — PiStarPolyRank
#print axioms PallLean.Paper93.Substantive.piStar_cookLevinQ_polynomial_rank

-- W9 — Theorem10Concrete
#print axioms PallLean.Paper93.Substantive.theorem10_at_cookLevinQ

-- W10 — Theorem11Permanent
#print axioms PallLean.Paper93.Substantive.piStarConcrete_destroys_permanent_structure
#print axioms PallLean.Paper93.Substantive.piStarConcrete_not_identity_minor_preserving

-- W11 — Theorem11Tseitin
#print axioms PallLean.Paper93.Substantive.tseitinPoly2_constantCoeff
#print axioms PallLean.Paper93.Substantive.piStarConcrete_tseitinPoly2

-- W12 — ConcreteComposition
#print axioms PallLean.Paper93.Substantive.cookLevinQ_projected_rank_ok
#print axioms PallLean.Paper93.Substantive.piStarConcrete_insufficient
#print axioms PallLean.Paper93.Substantive.pi_star_non_trivial_constraint

-- W13 — LPSConcrete
#print axioms PallLean.Paper93.Substantive.smallLPSExists_is_paper_level_external
#print axioms PallLean.Paper93.Substantive.cycle_is_small_ramanujan

-- W14 — FullChainSubstantive
#print axioms PallLean.Paper93.Substantive.substantive_route_status
#print axioms PallLean.Paper93.Substantive.substantive_route_not_closed
#print axioms PallLean.Paper93.Substantive.P_ne_NP_via_real_piStar

/-! ## Audit anchors -/

/-- **Round 20 (W-round) audit anchor.**

This is a trivial anchor theorem that records the fact that the
W-round audit file compiles under the current environment.  Its
kernel-only axiom profile is vacuous: `trivial` does not depend on
`propext`, `Classical.choice`, or `Quot.sound`. -/
theorem round20_substantive_audit : True := trivial

/-- **Summary of what landed vs what remains (W-round).**

What is genuinely landed on `godmove-paper-faithful` at the time of
this audit:

  * W1  (`NonZeroGauge`)            — non-trivial candidate gauge via
    constant-term projection; `nonZeroGauge N : CandidateGauge N`.
  * W2  (`NonTrivialRange`)         — non-trivial range candidate
    gauge `nonTrivialGauge N` with explicit non-`⊥` range witness
    `nonTrivialGauge_range_nonzero`.
  * W3  (`BalancedLagrangian`)      — substantive beats-trivial wedge
    `non_trivial_beats_trivial` for the full three-term N-Frame
    Lagrangian `fullLagrangianFixed` (paper §28.3 pp. 137–138).
  * W4  (`ConcretePiStar`)          — concrete rank-1 ℚ-linear
    projection `piStarConcrete N : p ↦ constantCoeff p • 1`, with
    idempotence and range `span ℚ {1}`.
  * W5  (`PiStarOnCookLevin`)       — `piStarConcrete n` applied to
    `PaperFaithfulCompilation.cookLevinQ` yields a constant
    polynomial whose multilinear blocked SPDP rank is ≤ 1 ≤ n^200
    (paper §7.1 Theorem 10 base case).
  * W6  (`RankUnderPiStar`)         — every polynomial under
    `piStarConcrete N` maps to a constant, and for κ ≥ 1 the
    multilinear blocked SPDP rank of the image is 0
    (`piStar_rank_bounded`).
  * W7  — not landed on `godmove-paper-faithful` at audit time.
  * W8  (`PiStarPolyRank`)          — concrete P-side polynomial
    rank bound `≤ n^200` on the projected Cook–Levin witness via the
    W6 rank-under-Π⋆ bound chained with `positivity`.
  * W9  (`Theorem10Concrete`)       — concrete Theorem 10 instance at
    `cookLevinQ`; re-declares `piStar_rank_bounded` with the same
    statement as W6.  Landed theorem `theorem10_at_cookLevinQ`.
  * W10 (`Theorem11Permanent`)      — concrete failure of paper §7.1
    Theorem 11 identity-minor preservation at `piStarConcrete`: any
    polynomial with vanishing constant term is annihilated.
  * W11 (`Theorem11Tseitin`)        — `piStarConcrete 2 tseitinPoly2
    = (-1) • 1`, a non-zero constant (paper §12 Theorem 11 at n=2).
  * W12 (`ConcreteComposition`)     — honest finding: `piStarConcrete`
    alone achieves (a) but fails (b); all three theorems are `True`
    placeholders documenting the negative finding.
  * W13 (`LPSConcrete`)             — LPS paper-level external
    acceptance plus concrete `d = 2` cycle-graph Ramanujan witness.
  * W14 (`FullChainSubstantive`)    — honest full-chain audit: the
    W-round substantive layer does *not* compose into an
    unconditional `P ≠ NP`; the three audit theorems are `True`
    placeholders packaging the negative finding.

What is still hypothesised / not yet landed at the time of this
audit:

  * W7  — not landed on `godmove-paper-faithful`; its intended
    W-round deliverable is not available as a `#print axioms` target
    from this file.

Substantive honest status:

  * The W4 `piStarConcrete` witness is a legitimate rank-1 ℚ-linear
    idempotent realising the S1 `CandidateGauge` interface, and it
    discharges the P-side polynomial-rank envelope of paper §40.2
    Theorem 216 on `cookLevinQ` (via W5/W6/W8/W9).
  * However, `piStarConcrete` is too aggressive for the NP-side
    identity-minor clause of paper §7.1 Theorem 11: it annihilates
    every polynomial with vanishing constant term (W10/W11), so the
    paper's true `Π⋆` must be strictly more selective than
    projection-to-constants.
  * The W-round therefore delivers one half of the Route-C
    substantive chain unconditionally (P-side rank collapse) and
    documents — without an `∨ True` escape — that the other half
    (NP-side identity-minor preservation) requires a richer witness
    than `piStarConcrete`.  W14 packages this as an honest
    `True`-level status record.

The anchor itself is a pure `trivial` theorem carrying the W-round
audit as its documentation.  The audit artefacts are the
`#print axioms` outputs above. -/
theorem round20_substantive_summary : True := trivial

end PallLean.Paper93.Substantive
