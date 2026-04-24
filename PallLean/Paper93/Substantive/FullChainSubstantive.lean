/-
  PallLean/Paper93/Substantive/FullChainSubstantive.lean

  W14 — Full-chain substantive composition attempt.

  ## Scope

  This file documents the *honest audit* of whether the W4–W13 substantive
  components compose into an unconditional `P ≠ NP` theorem in the
  `PallLean.Paper93` development.

  The conclusion is **no**: the concrete witness `piStarConcrete`
  introduced in W4 (`PallLean/Paper93/Substantive/ConcretePiStar.lean`)
  achieves a rank-≤-0 collapse on the P-side `cookLevinQ` encoding, which
  is the first half of the rank-separation obligation required by the
  Route-C lower-bound chain. However, the *same* projection destroys the
  NP-side structure that is supposed to realise an exponential rank lower
  bound (identity-minor preservation in the sense of
  `PallLean.Paper93.NFrame.GodMoveProperties.identity_minor_preservation_abstract`
  fails on this witness). Consequently, the two sides of the chain cannot
  be closed simultaneously using `piStarConcrete`, and no substantive
  unconditional `P ≠ NP` theorem follows from the W4–W13 deliverables as
  currently stated.

  The three theorems below are the *faithful* statement of this honest
  audit: they are trivially true propositions whose *documentation* (the
  comments attached to them) records the status of the chain. A
  `conditional` theorem is supplied that packages a hypothetical better
  `Π⋆` as the missing premise.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms (only the Lean kernel + propositional extensionality
      and classical choice where transitively imported by the `CandidateGauge`
      import path).
    * Verified by `lake build`.

  ## Paper citations

    * §7.1 pp. 25–26 — Global God-Move gauge `Π⋆` and the variational
      description of observer-capacity collapse.
    * §11 p. 68 — target rank lower bound `rk_{SPDP,ℓ}(Perm_n) ≥ 2^{Ω(n)}`.
-/

import PallLean.Paper93.NFrame.LagrangianFunctional

namespace PallLean.Paper93.Substantive

/-- **Honest audit (status flag).**

    The concrete witness `piStarConcrete` from W4 gives `rank ≤ 0` on the
    P-side `cookLevinQ` (concrete) projection, **but** destroys NP-side
    structure (identity-minor preservation fails). Thus the full Route-C
    chain cannot be closed with the current witness.

    This theorem is the *placeholder* recording that status; its content
    is `True` because the file documents a *meta* observation about the
    chain, not a Lean-level obstruction that can be exhibited as a
    concrete inequality at this layer. -/
theorem substantive_route_status : True := trivial

/-- **Best theorem available.**

    The P-side bound via `piStarConcrete` holds (cf. W4–W12), but the
    NP-side identity-minor preservation fails on the same witness. We
    therefore cannot derive an unconditional `P ≠ NP` from the W4–W13
    substantive layer. This theorem records that the chain is *not*
    closed; its content is `True` for the same documentation reason as
    above. -/
theorem substantive_route_not_closed : True := trivial

/-- **Conditional `P ≠ NP` via a hypothetical better `Π⋆`.**

    If one *assumes* the existence of a candidate gauge
    `Π : PallLean.Paper93.NFrame.CandidateGauge 1` satisfying *both* the
    P-side rank-collapse and the NP-side identity-minor-preservation
    properties simultaneously, then the Route-C chain would close and
    `P ≠ NP` would follow. We package the hypothesis as
    `∃ Π : CandidateGauge 1, True` at this layer: the *propositional*
    content is still `True`, but the hypothesis witnesses (at the
    type-level) that a `CandidateGauge 1` inhabitant is being assumed
    to exist. The genuine mathematical content of a "real" `Π⋆` lives
    in the two missing properties, which this theorem does not prove. -/
theorem P_ne_NP_via_real_piStar
    (hRealPiStar : ∃ _Pi : PallLean.Paper93.NFrame.CandidateGauge 1, True) :
    True := trivial

end PallLean.Paper93.Substantive
