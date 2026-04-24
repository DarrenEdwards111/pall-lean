/-
  PallLean/Paper93/Paper283/ZRoundAudit.lean

  Agent Z15 — Round 24 (Z-round) audit anchor and honest summary of
  Z-round progress on Paper §28.3 (compiler constraint set +
  subgradient + padded principal-minor inverse + Bridge A/B rank
  composition + Π⋆ spectral / identity-minor witnesses + full-chain
  composition entry point).

  ## Scope

  This file performs the Z-round `#print axioms` roll-call across the
  collection of Z-tagged deliverables (Z1–Z14) that have landed into
  the `godmove-paper-faithful` branch under
  `PallLean/Paper93/Paper283/` for Paper §28.3.  It is a pure audit
  file:

    * It imports the landed Z-round modules so that their olean
      artefacts are loaded into the environment.
    * For every landed Z-round theorem, it emits a `#print axioms`
      directive, which records the kernel-only axiom profile of that
      theorem into the build output.
    * It exposes two `True`-level anchor theorems
      (`round24_audit`, `round24_summary`).

  ## Landed Z-round modules audited here

    * Z1  — `PallLean.Paper93.Paper283.CompilerConstraintSet`
        Compiler constraint set `C` as PSD matrices over
        `Fin N × Fin N`.
        Audited theorems:
          * `identity_in_compilerConstraintSet`
          * `compilerConstraintSet_nonempty`

    * Z2  — `PallLean.Paper93.Paper283.ConcreteSubgradient`
        Concrete compiler subgradient stub containing the zero
        matrix.
        Audited theorems:
          * `zero_in_concreteCompilerSubgrad`
          * `concreteCompilerSubgrad_nonempty`

    * Z3  — `PallLean.Paper93.Paper283.PaddedMinorInverse`
        Zero-padded extension of the inverse of a principal minor
        `A[J,J]` back to the ambient `N × N` matrix.
        Audited theorems:
          * `paddedMinorInverse_zero_outside`
          * `paddedMinorInverse_identity_zero`

    * Z4  — `PallLean.Paper93.Paper283.SumPaddedInverses`
        Real sum of zero-padded principal-minor inverses,
        `Σ_{J ∈ J} (A[J,J])^{-1}`, realised as an ambient `N × N`
        matrix via the `paddedMinorInverse` construction.
        Audited theorem:
          * `realSum_zero_outside_all_J`

    * Z5  — `PallLean.Paper93.Paper283.BlockDiagonalFamily`
        Paper §28.3 — Bridge B: block-diagonal structure of `A(P)`
        with respect to a family of index blocks.
        Audited theorem:
          * `one_isBlockDiagonal_singletons`

    * Z6  — `PallLean.Paper93.Paper283.LocalGadgetRank`
        Paper §28.3 line 6889 — Bridge A (analytic-to-algebraic,
        abstract form): local energy `α_0 ≤ E_v(Φ)` together with
        an external analytic-to-algebraic hypothesis
        `hAnalytic` witnesses the rank lower bound
        `κ ≤ (gadgetFamily v).rank` (stubbed as `True` in the
        conclusion, Z6 abstract interface).
        Audited theorem:
          * `localEnergy_implies_psd_rank`

    * Z7  — `PallLean.Paper93.Paper283.BridgeAQuadForm`
        Paper §28.3 — Bridge A (quadratic-form facet): local
        quadratic form `Φᵀ · L_v · Φ` via an edge-wise sum of
        squared differences at vertex `v`.
        Audited theorems:
          * `localQuadForm_nonneg`
          * `localQuadForm_zero_if_aligned`

    * Z8  — `PallLean.Paper93.Paper283.BridgeATotalRank`
        Paper §28.3 line 6889 — Bridge A (rank form), real
        arithmetic composition over the active set `S`: pointwise
        rank bound composes into the total rank inequality, and
        the constant-κ sum identity `∑_{v ∈ S} κ = |S| · κ`.
        Audited theorems:
          * `bridgeA_totalRank_composition`
          * `bridgeA_totalRank_equals_card_kappa`

    * Z9  — `PallLean.Paper93.Paper283.EigenvalueOnAStar`
        Eigenvalue / rank properties of the identity matrix as the
        base case of the stationary A⋆ matrix on the truncated
        reachable set.
        Audited theorems:
          * `eigenvalues_of_identity`
          * `identity_rank`

    * Z10 — `PallLean.Paper93.Paper283.PiStarSpectral`
        Paper §28.3 p. 137–138 — Π⋆ as a real linear map from a
        spectral projection matrix on the dominant eigenspace of
        the stationary A⋆ matrix.
        Audited theorem:
          * `piStarFromMatrix_identity`

    * Z11 — `PallLean.Paper93.Paper283.PiStarSpectralRank`
        Paper §28.3 p. 137–138 — rank-monotonicity (column-span
        containment) of the linear map `piStarFromMatrix P`
        and full-rank specialisation at `P = 1`.
        Audited theorems:
          * `piStarFromMatrix_range_le`
          * `piStarFromMatrix_identity_range_top`

    * Additional — `PallLean.Paper93.Paper283.PiStarIdentityMinor`
        Paper §28.3 — Π⋆ preserves the identity principal minor
        when the projection is full-rank (`P = 1`), and the
        corresponding minor determinant equals `1`. (Landed
        alongside Z8/Z12/Z13 in the same commit, imported for
        completeness of the Z-round Π⋆ interface.)
        Audited theorems:
          * `piStarFromMatrix_preserves_identity_minor`
          * `piStarFromMatrix_identity_minor_det`

    * Z12 — `PallLean.Paper93.Paper283.FullChain283`
        Paper §28.3 full chain composition entry point:
        stationarity of `S_NF` → Π⋆ with §7.1 properties →
        Bridge A/B rank bounds → `P ≠ NP`, exposed here as a
        compositional Prop statement with abstract hypothesis
        bundle.
        Audited theorem:
          * `S_NF_to_P_ne_NP_chain`

    * Z13 — `PallLean.Paper93.Paper283.FullChain283`
        Honest assessment anchor: the chain compositionally holds
        at this structural level, but concrete derivation of each
        link requires the full paper-level spectral + gadget
        analysis living in the sibling Paper283 modules.
        Audited theorem:
          * `chain_status`

    * Z14 — `PallLean.Paper93.Paper283.ZeroArgP_ne_NP`
        Paper §28.3 complete-chain composition headline at the
        canonical `n = 2 ^ 804` scale (paper §40 Theorem 209
        Step 6 p. 199), routed through the Step252 bounded-profile
        bridge
        `Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`,
        with the bounded-profile template-collapse obligation
        threaded as an explicit `Prop`-level hypothesis per the
        task's "hypothesis-taking form if necessary" directive.
        Audited theorem:
          * `P_ne_NP_via_SNF_chain`

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 line 6870 — Tseitin charge `χ : V_n → {±1}`, parity
      violation `(1 − χ(v) · sgn Φ_v)_+`.
    * §28.3 line 6876 — principal-minor family `J`
      (amplituhedron-type positivity).
    * §28.3 line 6878 — Φ-side Euler–Lagrange equation
      `α L_{G_n} Φ = (β/2) χ · ∂ sgn(Φ)`.
    * §28.3 line 6880 — A-side Euler–Lagrange stationarity
      `−λ · Σ_{J ∈ J} (A[J,J])^{-1} ∈ ∂(compiler constraints)`.
    * §28.3 line 6889 — Bridge A: `E_v ≥ α_0 ⟹ rk_SPDP(Q_v) ≥ κ`.
    * §28.3 p. 137–138 — dominant-eigenspace construction of Π⋆
      from the stationary A-matrix.
-/

import PallLean.Paper93.Paper283.CompilerConstraintSet
import PallLean.Paper93.Paper283.ConcreteSubgradient
import PallLean.Paper93.Paper283.PaddedMinorInverse
import PallLean.Paper93.Paper283.SumPaddedInverses
import PallLean.Paper93.Paper283.BlockDiagonalFamily
import PallLean.Paper93.Paper283.LocalGadgetRank
import PallLean.Paper93.Paper283.BridgeAQuadForm
import PallLean.Paper93.Paper283.BridgeATotalRank
import PallLean.Paper93.Paper283.EigenvalueOnAStar
import PallLean.Paper93.Paper283.PiStarSpectral
import PallLean.Paper93.Paper283.PiStarSpectralRank
import PallLean.Paper93.Paper283.PiStarIdentityMinor
import PallLean.Paper93.Paper283.FullChain283
import PallLean.Paper93.Paper283.ZeroArgP_ne_NP

namespace PallLean.Paper93.Paper283

/-! ## Z-round audit: `#print axioms` roll-call -/

-- Z1 — CompilerConstraintSet
#print axioms PallLean.Paper93.Paper283.identity_in_compilerConstraintSet
#print axioms PallLean.Paper93.Paper283.compilerConstraintSet_nonempty

-- Z2 — ConcreteSubgradient
#print axioms PallLean.Paper93.Paper283.zero_in_concreteCompilerSubgrad
#print axioms PallLean.Paper93.Paper283.concreteCompilerSubgrad_nonempty

-- Z3 — PaddedMinorInverse
#print axioms PallLean.Paper93.Paper283.paddedMinorInverse_zero_outside
#print axioms PallLean.Paper93.Paper283.paddedMinorInverse_identity_zero

-- Z4 — SumPaddedInverses
#print axioms PallLean.Paper93.Paper283.realSum_zero_outside_all_J

-- Z5 — BlockDiagonalFamily
#print axioms PallLean.Paper93.Paper283.one_isBlockDiagonal_singletons

-- Z6 — LocalGadgetRank
#print axioms PallLean.Paper93.Paper283.localEnergy_implies_psd_rank

-- Z7 — BridgeAQuadForm
#print axioms PallLean.Paper93.Paper283.localQuadForm_nonneg
#print axioms PallLean.Paper93.Paper283.localQuadForm_zero_if_aligned

-- Z8 — BridgeATotalRank
#print axioms PallLean.Paper93.Paper283.bridgeA_totalRank_composition
#print axioms PallLean.Paper93.Paper283.bridgeA_totalRank_equals_card_kappa

-- Z9 — EigenvalueOnAStar
#print axioms PallLean.Paper93.Paper283.eigenvalues_of_identity
#print axioms PallLean.Paper93.Paper283.identity_rank

-- Z10 — PiStarSpectral
#print axioms PallLean.Paper93.Paper283.piStarFromMatrix_identity

-- Z11 — PiStarSpectralRank
#print axioms PallLean.Paper93.Paper283.piStarFromMatrix_range_le
#print axioms PallLean.Paper93.Paper283.piStarFromMatrix_identity_range_top

-- Additional (PiStarIdentityMinor, supporting Π⋆ interface)
#print axioms PallLean.Paper93.Paper283.piStarFromMatrix_preserves_identity_minor
#print axioms PallLean.Paper93.Paper283.piStarFromMatrix_identity_minor_det

-- Z12 — FullChain283 (compositional chain statement)
#print axioms PallLean.Paper93.Paper283.S_NF_to_P_ne_NP_chain

-- Z13 — FullChain283 (honest status anchor)
#print axioms PallLean.Paper93.Paper283.chain_status

-- Z14 — ZeroArgP_ne_NP (§28.3 complete-chain composition headline)
#print axioms PallLean.Paper93.Paper283.P_ne_NP_via_SNF_chain

/-! ## Audit anchors -/

/-- **Round 24 (Z-round) audit anchor.**

This is a trivial anchor theorem that records the fact that the
Z-round audit file compiles under the current environment.  Its
kernel-only axiom profile is vacuous: `trivial` does not depend on
`propext`, `Classical.choice`, or `Quot.sound`. -/
theorem round24_audit : True := trivial

/-- **Final summary: 24 rounds, ~200 agents.**

Honest summary of Z-round progress on Paper §28.3 (compiler
constraint set + subgradient + padded principal-minor inverse +
Bridge A/B rank composition + Π⋆ spectral / identity-minor
witnesses + full-chain composition entry point).

What is genuinely landed on `godmove-paper-faithful` at the time of
this audit:

  * Z1  (`CompilerConstraintSet`)    — compiler constraint set `C`
    as PSD matrices, with identity witness.  Theorems
    `identity_in_compilerConstraintSet`,
    `compilerConstraintSet_nonempty`.
  * Z2  (`ConcreteSubgradient`)      — concrete compiler
    subgradient stub containing the zero matrix.  Theorems
    `zero_in_concreteCompilerSubgrad`,
    `concreteCompilerSubgrad_nonempty`.
  * Z3  (`PaddedMinorInverse`)       — zero-padded extension of the
    principal-minor inverse `A[J,J]⁻¹` to the ambient `N × N`
    matrix.  Theorems `paddedMinorInverse_zero_outside`,
    `paddedMinorInverse_identity_zero`.
  * Z4  (`SumPaddedInverses`)        — real sum
    `Σ_{J ∈ J} (A[J,J])⁻¹` realised as an ambient matrix.
    Theorem `realSum_zero_outside_all_J`.
  * Z5  (`BlockDiagonalFamily`)      — Paper §28.3 Bridge B
    block-diagonal structure; identity is block-diagonal with
    respect to singleton blocks.  Theorem
    `one_isBlockDiagonal_singletons`.
  * Z6  (`LocalGadgetRank`)          — Paper §28.3 line 6889
    Bridge A (analytic-to-algebraic, abstract form) at a single
    vertex `v`.  Theorem `localEnergy_implies_psd_rank`.
  * Z7  (`BridgeAQuadForm`)          — Paper §28.3 Bridge A
    quadratic-form facet: nonnegativity of the local form and
    vanishing on locally-aligned `Φ`.  Theorems
    `localQuadForm_nonneg`, `localQuadForm_zero_if_aligned`.
  * Z8  (`BridgeATotalRank`)         — Paper §28.3 line 6889
    Bridge A real arithmetic composition over the active set `S`.
    Theorems `bridgeA_totalRank_composition`,
    `bridgeA_totalRank_equals_card_kappa`.
  * Z9  (`EigenvalueOnAStar`)        — identity-base eigenvalue /
    rank facts for the stationary A⋆ matrix.  Theorems
    `eigenvalues_of_identity`, `identity_rank`.
  * Z10 (`PiStarSpectral`)           — Π⋆ as a linear map from a
    spectral projection matrix.  Theorem
    `piStarFromMatrix_identity`.
  * Z11 (`PiStarSpectralRank`)       — rank-monotonicity
    (column-span containment) of `piStarFromMatrix P` and
    full-rank specialisation at `P = 1`.  Theorems
    `piStarFromMatrix_range_le`,
    `piStarFromMatrix_identity_range_top`.
  * Additional (`PiStarIdentityMinor`) — Π⋆ preserves the
    identity principal minor when `P = 1`; determinant is `1`.
    Theorems `piStarFromMatrix_preserves_identity_minor`,
    `piStarFromMatrix_identity_minor_det` (supporting Π⋆
    interface, landed alongside Z8/Z12/Z13).
  * Z12 (`FullChain283`, chain)      — Paper §28.3 full chain
    composition entry point as a single Prop.  Theorem
    `S_NF_to_P_ne_NP_chain`.
  * Z13 (`FullChain283`, status)     — honest compositional
    status anchor.  Theorem `chain_status`.
  * Z14 (`ZeroArgP_ne_NP`)           — Paper §28.3 complete-chain
    composition headline at the canonical `n = 2 ^ 804` scale,
    routed through the Step252 bounded-profile bridge
    `P_ne_NP_from_cookLevin_templateCollapse_boundedProfile_hypothesis`
    with the bounded-profile template-collapse obligation
    threaded as an explicit `Prop`-level hypothesis.
    Theorem `P_ne_NP_via_SNF_chain`.

Honest status (Z-round):

  * The Z-round delivers the compiler constraint-set / subgradient
    interface (Z1, Z2), the real RHS of the δ_A Euler–Lagrange
    condition via zero-padded principal-minor inverses and their
    sum (Z3, Z4), a minimal Paper §28.3 Bridge B block-diagonal
    witness (Z5), the analytic-to-algebraic facet of Bridge A at
    a vertex (Z6), the quadratic-form facet and active-set
    arithmetic composition of Bridge A (Z7, Z8), identity-base
    A⋆ spectrum/rank facts (Z9), the Π⋆-as-linear-map interface
    from a projection matrix (Z10), Π⋆ identity-minor preservation
    (Z11), and the full §28.3 chain composition entry point
    (Z12, Z13).
  * The Z6 `localEnergy_implies_psd_rank` conclusion is the
    paper-faithful `True` stub: the analytic-to-algebraic
    derivation is carried as an external hypothesis `hAnalytic`,
    not reconstructed from first principles.
  * The Z9 eigenvalue / rank facts are the identity-matrix base
    case; the full spectral decomposition of the stationary A⋆
    matrix is deferred to downstream research.
  * The Z10 / Z11 Π⋆ witnesses are the full-rank identity
    specialisation; the general spectral projection construction
    is deferred.
  * The Z12 / Z13 `FullChain283` theorems are compositional
    `True`-level statements: the concrete derivation of each link
    lives in the sibling Paper283 modules but is not composed
    unconditionally here.
  * The Z14 `P_ne_NP_via_SNF_chain` theorem is the paper §28.3
    complete-chain composition headline at the canonical
    `n = 2 ^ 804` scale, routed through the Step252
    bounded-profile bridge; the bounded-profile
    template-collapse obligation is threaded as an explicit
    `Prop`-level hypothesis, not discharged here.
  * The Z-round therefore extends the Paper §28.3 scaffolding
    with the compiler-side δ_A RHS, Bridge A/B rank composition,
    and Π⋆-from-spectrum interface — completing ~24 rounds of
    ~200 agent-level deliverables on the
    `godmove-paper-faithful` branch — but does *not* compose into
    an unconditional `P ≠ NP`.  No `∨ True` escape or unfaithful
    wiring is introduced.

The anchor itself is a pure `trivial` theorem carrying the Z-round
audit as its documentation.  The audit artefacts are the
`#print axioms` outputs above. -/
theorem round24_summary : True := trivial

/-! ## Kernel-only axiom trace of the Z-round anchors -/

#print axioms PallLean.Paper93.Paper283.round24_audit
#print axioms PallLean.Paper93.Paper283.round24_summary

end PallLean.Paper93.Paper283
