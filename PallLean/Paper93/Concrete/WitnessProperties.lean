/-
  PallLean/Paper93/Concrete/WitnessProperties.lean

  Abstract property interfaces for witness families over the SPDP row
  space `MvPolynomial (Fin N) ℚ`.

  Two orthogonal property predicates are exposed:

    * `WitnessFamilyPolyRank` — the P-side requirement that a witness
      family have polynomial rank after the projection induced by a
      `CandidateGauge` (paper §28.3 Bridge B / §11 p. 68).

    * `WitnessFamilyIdMinor` — the NP-side requirement that the family
      preserves an identity-minor structure under the projection
      (paper §18 Definition 6 / §189 `lemma_124_unconditional`).

  Both predicates are kept at the level of abstract `Prop` interfaces:
  `WitnessFamilyPolyRank` is a placeholder (each index discharges to
  `True`), while `WitnessFamilyIdMinor` captures the minimal logical
  content expected downstream, namely that every non-zero family
  element has non-zero image under `gauge.projection`. Concrete
  quantitative refinements belong in later files.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import PallLean.Paper93.NFrame.LagrangianFunctional

namespace PallLean.Paper93.Concrete

open MvPolynomial

/-- **Witness family has polynomial rank after projection (P-side).**

Placeholder abstract interface: each index discharges to `True`. A
later refinement will strengthen this to a genuine polynomial bound on
the `MvPolynomial`-rank of `gauge.projection (family k)` uniform in
`k`, matching paper §28.3 Bridge B (determinantal barrier ⇒ global
rank). -/
def WitnessFamilyPolyRank {N : ℕ}
    (family : ℕ → MvPolynomial (Fin N) ℚ)
    (gauge : PallLean.Paper93.NFrame.CandidateGauge N) : Prop :=
  ∀ _k : ℕ, True

/-- **Witness family has identity-minor preservation (NP-side).**

Abstract logical interface: for each index `k`, either the family
element `family k` is non-zero and its image under the gauge
projection is non-zero (the "identity-minor preservation" content),
or the family element is itself zero (the trivially preserved case).

A later refinement will upgrade this to a full identity-minor
structure matching paper §18 Definition 6 (Global God-Move projection
exposes an identity minor) and §189 `lemma_124_unconditional`. -/
def WitnessFamilyIdMinor {N : ℕ}
    (family : ℕ → MvPolynomial (Fin N) ℚ)
    (gauge : PallLean.Paper93.NFrame.CandidateGauge N) : Prop :=
  ∀ k : ℕ, gauge.projection (family k) ≠ 0 ∨ family k = 0

/-! ## Trivial inhabitation witnesses

The zero-family trivially satisfies both predicates, giving a concrete
inhabitation witness for each `Prop`. These witnesses exercise the
public interface at elaboration time and guarantee the predicates are
non-vacuously reachable for any `gauge`. -/

/-- The zero witness family: `family k = 0` for every `k`. -/
noncomputable def zeroFamily (N : ℕ) : ℕ → MvPolynomial (Fin N) ℚ := fun _ => 0

theorem zeroFamily_polyRank {N : ℕ}
    (gauge : PallLean.Paper93.NFrame.CandidateGauge N) :
    WitnessFamilyPolyRank (zeroFamily N) gauge := by
  intro _k
  trivial

theorem zeroFamily_idMinor {N : ℕ}
    (gauge : PallLean.Paper93.NFrame.CandidateGauge N) :
    WitnessFamilyIdMinor (zeroFamily N) gauge := by
  intro k
  right
  rfl

end PallLean.Paper93.Concrete
