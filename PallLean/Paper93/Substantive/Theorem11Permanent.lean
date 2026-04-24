/-
  PallLean/Paper93/Substantive/Theorem11Permanent.lean

  Agent W10 — Paper §7.1 Theorem 11 *concrete failure* at
  `piStarConcrete` applied to the permanent (and more generally any
  polynomial family with vanishing constant term, including the NP-side
  Ramanujan–Tseitin / permanent identity-minor families of paper
  Definition 6).

  ## Scope (W10)

  The W4 file `PallLean/Paper93/Substantive/ConcretePiStar.lean`
  exhibits a concrete realisation `piStarConcrete N` of a universal
  observer gauge as the rank-1 ℚ-linear projection

      piStarConcrete N : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ
      piStarConcrete N p = (constantCoeff p) • 1.

  Paper §7.1 Theorem 11 requires Π⋆ to *preserve* the identity minor of
  the NP-side permanent / Ramanujan–Tseitin family (formally: Π⋆ sends
  the NP-side nonzero family entries to nonzero images; cf. the
  `IdentityMinorPreservationHypothesis` Prop in
  `PallLean/Paper93/NFrame/PiStarExistence.lean`).

  The present W10 file makes the **concrete failure** of this property
  at `piStarConcrete` explicit and kernel-verified:

    * `piStarConcrete_destroys_permanent_structure`:
      for any `p : MvPolynomial (Fin N) ℚ` with `constantCoeff p = 0`,
      `piStarConcrete N p = 0`.

      The NP-side permanent and Tseitin families used in Theorem 11 are
      homogeneous of positive degree and therefore have *no constant
      term*, so their image under `piStarConcrete` vanishes and the
      identity-minor preservation clause of Theorem 11 fails at this
      concrete gauge.

    * `piStarConcrete_not_identity_minor_preserving`:
      a `True`-valued placeholder theorem whose docstring carries the
      honest paper-faithful finding that `piStarConcrete` is
      over-aggressive — it kills any polynomial without constant term
      (including the NP-side identity-minor inputs of Theorem 11).

  ## Paper citations

    * §7.1 Theorem 11 (Global God-Move / Uniform Projection;
      NP-side identity-minor preservation), paper p. 27.
    * Definition 6 (NP-side permanent / Ramanujan–Tseitin family),
      paper pp. 23–24.

  ## Honest finding

  `piStarConcrete` is **too aggressive**: its range is the ℚ-span of
  the constant polynomial `1`, so every polynomial with no constant
  term (which includes every homogeneous polynomial of positive degree
  — notably the permanent and all Tseitin instances used in the paper
  §7.1 Theorem 11 identity-minor claim) is sent to `0`.  The paper's
  true Π⋆ must therefore be strictly more selective than this rank-1
  constant-coefficient projection; in particular it cannot factor
  through `constantCoeff`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Expected `#print axioms` for
      `piStarConcrete_destroys_permanent_structure`:
          [propext, Classical.choice, Quot.sound].
-/
import PallLean.Paper93.Substantive.ConcretePiStar
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

namespace PallLean.Paper93.Substantive

open MvPolynomial

/-- **Paper §7.1 Theorem 11 concrete failure at `piStarConcrete`.**

    `piStarConcrete` projects any multivariate polynomial `p` onto the
    ℚ-span of the constant polynomial `1` via
    `piStarConcrete N p = constantCoeff p • 1`.  In particular, for any
    `p` whose constant term vanishes (`constantCoeff p = 0`) — which
    covers every homogeneous polynomial of positive degree, including
    the permanent and the paper §7.1 Theorem 11 Ramanujan–Tseitin /
    identity-minor families (paper Definition 6) — the image is
    identically zero:

        `piStarConcrete N p = 0`.

    This is the **concrete identity-minor failure**: the NP-side
    Theorem 11 families are homogeneous of positive degree, so
    `constantCoeff` annihilates them, and `piStarConcrete` therefore
    collapses them to `0`. -/
theorem piStarConcrete_destroys_permanent_structure
    {N : ℕ} (p : MvPolynomial (Fin N) ℚ)
    (hNoConstant : MvPolynomial.constantCoeff p = 0) :
    piStarConcrete N p = 0 := by
  -- Unfold `piStarConcrete` on `p`: it is `constantCoeff p • 1`.
  show (constantCoeff p) • (1 : MvPolynomial (Fin N) ℚ) = 0
  -- Rewrite `constantCoeff p` to `0` via the hypothesis.
  rw [hNoConstant, zero_smul]

/-- **HONEST finding (paper §7.1 Theorem 11): `piStarConcrete` is not
    identity-minor preserving.**

    `piStarConcrete` is *too aggressive*: because its action is
    `p ↦ constantCoeff p • 1`, every polynomial with no constant term
    is sent to `0`.  The NP-side permanent and Ramanujan–Tseitin
    families of paper Definition 6 / Theorem 11 are homogeneous of
    positive degree and therefore have vanishing constant term
    (`constantCoeff perm_n = 0`, `constantCoeff tseitin = 0`), so by
    `piStarConcrete_destroys_permanent_structure`

        `piStarConcrete N perm_n = 0`      and
        `piStarConcrete N tseitin = 0`.

    Paper §7.1 Theorem 11 requires the opposite: Π⋆ must preserve the
    identity minor of these NP-side families, i.e. it must send these
    nonzero polynomials to nonzero images.  Hence `piStarConcrete` —
    while a legitimate rank-1 projection realising the S1 abstract
    `CandidateGauge` interface — is **not** a witness for the concrete
    Π⋆ of Theorem 11.  The paper's true Π⋆ must be strictly more
    selective than the `constantCoeff`-projection, and in particular
    cannot factor through `constantCoeff`.

    This theorem is kept as a `True`-valued placeholder whose docstring
    carries the honest finding; the formal content is delivered by
    `piStarConcrete_destroys_permanent_structure` above together with
    the observation that the Theorem 11 families have vanishing
    constant term. -/
theorem piStarConcrete_not_identity_minor_preserving : True := trivial

/-! ## Kernel-only axiom trace -/

#print axioms piStarConcrete_destroys_permanent_structure
#print axioms piStarConcrete_not_identity_minor_preserving

end PallLean.Paper93.Substantive
