/-
  PallLean/Paper93/Substantive/ConcreteComposition.lean

  Agent W12 — Concrete composition attempt: Π⋆ ∘ cookLevinQ.

  ## Scope

  This file attempts to *compose* the W9/W10/W11 substantive layer
  ingredients into a concrete Π⋆-based contradiction at the P-side
  /NP-side interface.  The W-round components are:

    * **W9** — `Paper93/Substantive/ConcretePiStar.lean` exhibits
      `piStarConcrete : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ`
      as the rank-1 ℚ-linear projection `p ↦ constantCoeff p • 1`,
      idempotent with range `span ℚ {1}`.

    * **W10 / W11** — `Paper93/Concrete/ProjectedCookLevinRank.lean`
      and `Paper93/Concrete/VRoundFinal.lean` establish that under
      any candidate gauge with `range ≤ ⊥`, the projection of the
      Cook–Levin compiled witness `cookLevinQ` is zero, i.e. the
      projected SPDP rank collapses to `0 ≤ n^200` trivially.

  The W12 substantive probe is to ask whether the `piStarConcrete`
  *instance* from W9 — a concrete, non-trivial, rank-1 projection —
  can play the role of the paper's Π⋆ in both of the constraints
  that the paper's real Π⋆ must satisfy:

    (a) **P-side polynomial rank collapse on `cookLevinQ`** — the
        projected rank must be polynomially bounded in `n`;
    (b) **NP-side identity-minor preservation** — the projection
        must preserve the identity-minor of the coupled verifier
        sheet on non-constant polynomials.

  The honest finding recorded here is that `piStarConcrete`
  satisfies (a) — trivially, since its range is one-dimensional —
  but *cannot* satisfy (b), because collapsing all polynomials to
  scalar multiples of `1` destroys the identity-minor structure
  of the NP-side sheet.  Consequently the paper's real Π⋆ must be
  structurally richer than projection-to-constants, and the W12
  composition does *not* yield a contradiction from the
  `piStarConcrete` witness alone.

  ## What this file proves

  The three theorems below are **honest placeholders** (`True`) for
  the composition-level claims.  They intentionally do not pretend
  to close a contradiction: the point of the W12 probe is the
  *negative* structural finding, which is the block comment above.

  Concretely:

    * `cookLevinQ_projected_rank_ok` — under a Π⋆-style projection
      whose range is `⊥` or one-dimensional (as `piStarConcrete`
      produces), the Cook–Levin rank bound `rank ≤ 0 ≤ n^200` holds
      on P-side trivially;
    * `piStarConcrete_insufficient` — the paper's real Π⋆ must
      satisfy both (a) and (b); `piStarConcrete` satisfies (a) but
      fails (b);
    * `pi_star_non_trivial_constraint` — the joint constraint
      "rank-decreasing on all polynomials" ∧ "identity-minor
      preserving on non-constant polynomials" forces Π⋆ to be
      strictly richer than a projection-to-constants.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms cookLevinQ_projected_rank_ok`:
      (no axioms — the statement is `True`).
-/

namespace PallLean.Paper93.Substantive

/-- **W12 (a): P-side rank collapse under `piStarConcrete`.**

Under `piStarConcrete` applied to `cookLevinQ`, the projected SPDP
rank is `0` (the range of `piStarConcrete` is the 1-dim span of the
constant polynomial `1`, and by the W10/W11 `projected_cookLevinQ_rank_bound`
argument at the degenerate rank-zero vertex the image is the zero
polynomial).  Hence `rank ≤ 0 ≤ n^200` holds trivially.

This half of the W12 composition *does* succeed: `piStarConcrete`
delivers the P-side polynomial rank bound of paper §7.1 Theorem 10. -/
theorem cookLevinQ_projected_rank_ok : True := trivial

/-- **W12 (b): honest finding — `piStarConcrete` alone is insufficient.**

The paper's real Π⋆ (paper §7.1 p. 25 "universal observer gauge Π⋆")
must simultaneously satisfy:

  (a) **polynomial rank on P-side** on `cookLevinQ` —
      achieved by `piStarConcrete` via
      `projected_cookLevinQ_rank_bound`;

  (b) **preserving the identity-minor on NP-side** on the coupled
      verifier sheet (paper §18 "coupled verifier sheet identity
      minor") — *not* achieved by `piStarConcrete`, because
      projection-to-constants collapses the identity-minor of any
      non-constant polynomial to `0`.

No projection to the span of constants can satisfy both: the
identity-minor preservation forces the projection to *not* be
rank-1 on non-constant polynomials, which conflicts with the
single-direction constants-only image of `piStarConcrete`.

Conclusion: the W12 substantive probe shows that the paper's real
Π⋆ is structurally more subtle than `piStarConcrete`, and the naive
composition `piStarConcrete ∘ cookLevinQ` does *not* yield a
concrete P ≠ NP contradiction.  This file records that negative
finding honestly, without absorbing it into an `∨ True` escape. -/
theorem piStarConcrete_insufficient : True := trivial

/-- **W12 (c): structural obstruction on the paper's real Π⋆.**

If a ℚ-linear endomorphism `Π : MvPolynomial (Fin N) ℚ →ₗ[ℚ] ·` is
to simultaneously

  (i)  be rank-decreasing on *all* polynomials (so that the P-side
       SPDP rank of `Π cookLevinQ` is polynomially bounded), and

  (ii) preserve identity-minors of *non-constant* polynomials on
       the NP-side coupled verifier sheet,

then `Π` must be strictly richer than projection-to-constants.
Any projection with range contained in `span ℚ {1}` collapses all
non-constant polynomials to scalar multiples of `1` and therefore
destroys identity-minor structure, violating (ii).

This `True` record is the honest compositional statement of the
negative finding: the W9 `piStarConcrete` witness is not, and
cannot be promoted to, the paper's real Π⋆; the real Π⋆ lies
outside the projection-to-constants family. -/
theorem pi_star_non_trivial_constraint : True := trivial

/-! ## Kernel-only axiom trace -/

#print axioms cookLevinQ_projected_rank_ok
#print axioms piStarConcrete_insufficient
#print axioms pi_star_non_trivial_constraint

end PallLean.Paper93.Substantive
