/-
  PallLean/Paper93/Concrete/VRoundFinal.lean

  Agent V15 — Final V-round audit anchor.

  ## Scope

  This file performs the final V-round `#print axioms` audit across
  the collection of V-tagged deliverables (V1–V14) that have landed
  into the `godmove-paper-faithful` branch.  It is a pure audit file:

    * It imports the landed V-round modules so that their olean
      artefacts are loaded into the environment.
    * For every landed V-round theorem, it emits a `#print axioms`
      directive, which records the kernel-only axiom profile of that
      theorem into the build output.
    * For V-round slots that have not yet produced a landed theorem
      on the branch, it records the slot with an `--` comment rather
      than a `#print axioms` call (so this file builds cleanly even
      when some V slots are still scaffolding).

  ## Landed V-round modules audited here

    * V1  (U1 V1 fix) — `PallLean.Paper93.Concrete.RegularGraphFixed`
        Hypothesis-free fixed regular graph (edge-set wrapper).
        Audited theorems:
          * `cycleGraphFixed_card`
          * `cycleGraphFixed_exists`
    * V2  — `PallLean.Paper93.Concrete.EvenCycleGraph`
        Even-cycle `C_{2k}` structure on `RegularGraphFixed (2*k) 2`.
        Audited theorem:
          * `evenCycle_has_edges`
    * V4  — `PallLean.Paper93.Concrete.RealIdentityMinor`
        Non-trivial identity-minor matrix for paper §18's coupled
        verifier sheet.
        Audited theorems:
          * `realIdentityMinor_det_eq_2pow`
          * `realIdentityMinor_rank_eq`
    * V5  — `PallLean.Paper93.Concrete.LogDetPosDef`
        Log-det properties on PosDef matrices.
        Audited theorems:
          * `posDef_det_pos`
          * `logDet_diagonal_posDef`
          * `logDet_one`
    * V6  — `PallLean.Paper93.Concrete.RealBarrier`
        Real log-det barrier non-vacuous at arbitrary `M`.
        Audited theorems:
          * `realBarrier_of_posDef`
          * `realBarrier_identity_zero`
          * `realBarrier_small_det_large`
    * V7  — `PallLean.Paper93.Concrete.RealProjectionMatrix`
        Rank-respecting projection matrix.
        Audited theorems:
          * `realProjMatrix_det`
          * `realProjMatrix_trivial_zero`
    * V8  — `PallLean.Paper93.Concrete.ProjectedCookLevinRank`
        Rank bounds on the projected Cook-Levin coefficient basis.
        Audited theorems:
          * `projected_cookLevinQ_rank_bound`
          * `projected_cookLevinQ_rank_is_zero_at_trivial`
    * V9  — `PallLean.Paper93.Concrete.TseitinFamily`
        Tseitin polynomial family over the cycle graph.
        Audited theorem:
          * `tseitinPoly2_ne_zero`
    * V10 — `PallLean.Paper93.Concrete.Theorem10Attempt`
        Paper §7.1 Theorem 10 Holographic Upper-Bound Principle
        (P-side, abstract).
        Audited theorem:
          * `holographicUpperBound_abstract`
    * V11 — `PallLean.Paper93.Concrete.Theorem11Attempt`
        Paper §7.1 Theorem 11 (NP-side, abstract form).
        Audited theorem:
          * `globalGodMove_permanent_abstract`
    * V12 (U17 V12 fix) — `PallLean.Paper93.Concrete.FullLagrangianFixed`
        Full three-term concrete N-Frame Lagrangian on the fixed
        graph, non-negativity theorem.
        Audited theorem:
          * `fullLagrangianFixed_nonneg`
    * V13 — `PallLean.Paper93.Concrete.NonVacuousMinimizer`
        Non-vacuous concrete balanced minimizer of the full
        three-term fixed-graph Lagrangian.  NOTE: this module
        re-defines `fullLagrangianFixed` in the same namespace as
        V12's `FullLagrangianFixed`, so importing both causes a
        name collision.  This audit file imports V12 only; the
        V13 theorems
        (`concreteEdgeEnergyFixed_nonneg`,
         `concreteEdgeEnergyFixed_trivial_zero`,
         `fullLagrangianFixed_trivial_zero`,
         `fullLagrangianFixed_minimum_exists`)
        are therefore NOT audited from here.  A future cleanup
        should rename the V13 definitions (e.g. into a
        `NonVacuousMinimizer` sub-namespace) to enable simultaneous
        audit.
    * V14 — `PallLean.Paper93.Concrete.DischargeS2Real`
        Concrete DischargeS2 on full-range gauge: three God-Move
        properties discharged.
        Audited theorem:
          * `godMove_properties_unified`

  ## V-round slots without landed theorems

  The following V-round slots have not produced committed, landed
  theorems on `godmove-paper-faithful` at the time of this audit.
  They are recorded here as `--` comments so that no `#print axioms`
  call is attempted on a missing name:

    * V3  — not landed

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms in this audit file itself (the audit anchors
      below are `trivial`).
    * Verified by `lake build`.

  ## Paper citations

    * §7.1  pp. 25–26     — Global God-Move `Π⋆`, N-Frame Lagrangian.
    * §12               — Tseitin family NP-side witness.
    * §18               — Coupled verifier sheet (identity minor).
    * §28.3 pp. 137–138 — Concrete N-Frame Lagrangian and
      amplituhedron positive geometry / log-det barrier.
-/

import PallLean.Paper93.Concrete.RegularGraphFixed
import PallLean.Paper93.Concrete.EvenCycleGraph
import PallLean.Paper93.Concrete.RealIdentityMinor
import PallLean.Paper93.Concrete.LogDetPosDef
import PallLean.Paper93.Concrete.RealBarrier
import PallLean.Paper93.Concrete.RealProjectionMatrix
import PallLean.Paper93.Concrete.ProjectedCookLevinRank
import PallLean.Paper93.Concrete.TseitinFamily
import PallLean.Paper93.Concrete.Theorem10Attempt
import PallLean.Paper93.Concrete.Theorem11Attempt
import PallLean.Paper93.Concrete.FullLagrangianFixed
-- NOTE: V13 `NonVacuousMinimizer` shadows V12's `fullLagrangianFixed`;
-- we import V12 only and skip V13's `#print axioms` targets.
import PallLean.Paper93.Concrete.DischargeS2Real

namespace PallLean.Paper93.Concrete

/-! ## V-round `#print axioms` roll-call

For each landed V-round theorem we emit a `#print axioms`
directive.  These directives are compile-time side effects: they
produce no new obligations, but their output (logged during
`lake build`) is the audit artefact. -/

-- V1 (U1 V1 fix) — RegularGraphFixed
#print axioms PallLean.Paper93.Concrete.cycleGraphFixed_card
#print axioms PallLean.Paper93.Concrete.cycleGraphFixed_exists

-- V2 — EvenCycleGraph
#print axioms PallLean.Paper93.Concrete.evenCycle_has_edges

-- V3 — not landed on godmove-paper-faithful at audit time.

-- V4 — RealIdentityMinor
#print axioms PallLean.Paper93.Concrete.realIdentityMinor_det_eq_2pow
#print axioms PallLean.Paper93.Concrete.realIdentityMinor_rank_eq

-- V5 — LogDetPosDef
#print axioms PallLean.Paper93.Concrete.posDef_det_pos
#print axioms PallLean.Paper93.Concrete.logDet_diagonal_posDef
#print axioms PallLean.Paper93.Concrete.logDet_one

-- V6 — RealBarrier
#print axioms PallLean.Paper93.Concrete.realBarrier_of_posDef
#print axioms PallLean.Paper93.Concrete.realBarrier_identity_zero
#print axioms PallLean.Paper93.Concrete.realBarrier_small_det_large

-- V7 — RealProjectionMatrix
#print axioms PallLean.Paper93.Concrete.realProjMatrix_det
#print axioms PallLean.Paper93.Concrete.realProjMatrix_trivial_zero

-- V8 — ProjectedCookLevinRank
#print axioms PallLean.Paper93.Concrete.projected_cookLevinQ_rank_bound
#print axioms PallLean.Paper93.Concrete.projected_cookLevinQ_rank_is_zero_at_trivial

-- V9 — TseitinFamily
#print axioms PallLean.Paper93.Concrete.tseitinPoly2_ne_zero

-- V10 — Theorem10Attempt
#print axioms PallLean.Paper93.Concrete.holographicUpperBound_abstract

-- V11 — Theorem11Attempt
#print axioms PallLean.Paper93.Concrete.globalGodMove_permanent_abstract

-- V12 (U17 V12 fix) — FullLagrangianFixed
#print axioms PallLean.Paper93.Concrete.fullLagrangianFixed_nonneg

-- V13 — NonVacuousMinimizer is landed but shadows V12's
-- `fullLagrangianFixed`, so this audit file cannot import it
-- simultaneously with V12.  V13 theorems are NOT audited here;
-- see the scope notes above.

-- V14 — DischargeS2Real
#print axioms PallLean.Paper93.Concrete.godMove_properties_unified

/-! ## Audit anchors -/

/-- V-round audit anchor.

This is a trivial anchor theorem that records the fact that the
V-round audit file compiles under the current environment.  Its
kernel-only axiom profile is vacuous (`propext`, `Classical.choice`,
`Quot.sound` are not used by `trivial`). -/
theorem round19_audit : True := trivial

/-- V-round audit summary.

What is genuinely landed on `godmove-paper-faithful` at the time of
this audit:

  * V1  (`RegularGraphFixed`)       — hypothesis-free fixed regular
    graph. Theorems `cycleGraphFixed_card`, `cycleGraphFixed_exists`.
  * V2  (`EvenCycleGraph`)          — even-cycle `C_{2k}`. Theorem
    `evenCycle_has_edges`.
  * V4  (`RealIdentityMinor`)       — non-trivial identity-minor
    matrix for the coupled verifier sheet. Theorems
    `realIdentityMinor_det_eq_2pow`, `realIdentityMinor_rank_eq`.
  * V5  (`LogDetPosDef`)            — log-det on PosDef. Theorems
    `posDef_det_pos`, `logDet_diagonal_posDef`, `logDet_one`.
  * V6  (`RealBarrier`)             — real log-det barrier,
    non-vacuous. Theorems `realBarrier_of_posDef`,
    `realBarrier_identity_zero`, `realBarrier_small_det_large`.
  * V7  (`RealProjectionMatrix`)    — rank-respecting projection
    matrix. Theorems `realProjMatrix_det`,
    `realProjMatrix_trivial_zero`.
  * V8  (`ProjectedCookLevinRank`)  — rank bounds on projected
    Cook-Levin basis. Theorems
    `projected_cookLevinQ_rank_bound`,
    `projected_cookLevinQ_rank_is_zero_at_trivial`.
  * V9  (`TseitinFamily`)           — Tseitin parity polynomial
    family. Theorem `tseitinPoly2_ne_zero`.
  * V10 (`Theorem10Attempt`)        — Holographic Upper-Bound
    Principle (P-side, abstract). Theorem
    `holographicUpperBound_abstract`.
  * V11 (`Theorem11Attempt`)        — Paper §7.1 Theorem 11 NP-side
    abstract form. Theorem `globalGodMove_permanent_abstract`.
  * V12 (`FullLagrangianFixed`)     — full three-term concrete
    N-Frame Lagrangian on the fixed graph, non-negativity.
    Theorem `fullLagrangianFixed_nonneg`.
  * V13 (`NonVacuousMinimizer`)     — landed but conflicts with V12
    by re-defining `fullLagrangianFixed`.  Theorems
    `concreteEdgeEnergyFixed_nonneg`,
    `concreteEdgeEnergyFixed_trivial_zero`,
    `fullLagrangianFixed_trivial_zero`, and
    `fullLagrangianFixed_minimum_exists` are defined in the V13
    module but cannot be audited from this file alongside V12.
  * V14 (`DischargeS2Real`)         — three God-Move properties
    discharged on full-range gauge. Theorem
    `godMove_properties_unified`.

What is still hypothesised / not yet landed at the time of this
audit:

  * V3 — not landed on `godmove-paper-faithful`; its intended
    V-round deliverable is not available as a `#print axioms`
    target from this file.

The anchor itself is a pure `trivial` theorem carrying the V-round
audit as its documentation.  The audit artefacts are the
`#print axioms` outputs above. -/
theorem round19_summary : True := trivial

end PallLean.Paper93.Concrete
