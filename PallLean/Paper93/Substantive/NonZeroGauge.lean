/-
  PallLean/Paper93/Substantive/NonZeroGauge.lean

  Agent W1 — Paper §7.1 p. 25 / §28.3 p. 137 "Non-trivial candidate
  gauge witness for the N-Frame Lagrangian variational problem".

  ## Scope

  `LagrangianFunctional.lean` exposes the abstract data type
  `CandidateGauge N` (a ℚ-linear idempotent of finite-rank range on
  the SPDP row space `MvPolynomial (Fin N) ℚ`) and its degenerate
  witness `trivialGauge N` whose projection is the *zero* map, with
  rank `0`.

  For the substantive beats-trivial wedge (paper §28.3 p. 137
  Euler–Lagrange conditions), the rank-zero vertex cannot be the
  whole admissible set: we need an explicit *non-zero* candidate
  gauge to anchor the variational comparison used later in
  `Substantive/BalancedLagrangian.lean`.

  The present W1 file provides one such concrete witness:

    * `constantProjection N` — the ℚ-linear map
        `p ↦ (MvPolynomial.constantCoeff p) • 1`
      which sends a polynomial to its constant term (viewed as a
      scalar multiple of the constant polynomial `1`).  This map is
      idempotent, has rank ≤ 1 (its range is `Submodule.span ℚ {1}`),
      and is *non-zero* whenever `(1 : MvPolynomial (Fin N) ℚ) ≠ 0`
      (which holds since ℚ is a non-trivial ring).

    * `nonZeroGauge N` — the `CandidateGauge N` assembled from
      `constantProjection N`, exhibiting the required idempotence
      and finite-rank range.

  This is the concrete non-trivial witness consumed by the
  substantive Route~A = Route~C translation in the `Substantive`
  subdirectory.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms nonZeroGauge`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §7.1 pp. 25–26 — candidate gauges `Π` as linear projections on
      the SPDP row space; universal observer gauge `Π⋆` as the
      rank-minimiser.
    * §28.3 pp. 137–138 — analytic reformulation, Euler–Lagrange
      conditions at the rank-zero vertex, non-vacuous beats-trivial
      wedge.
-/
import PallLean.Paper93.NFrame.LagrangianFunctional
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Finiteness.Basic

namespace PallLean.Paper93.Substantive

open MvPolynomial
open PallLean.Paper93.NFrame

/-! ## 1. Constant-term projection on the SPDP row space

The simplest non-zero ℚ-linear idempotent on `MvPolynomial (Fin N) ℚ`
is obtained by composing the ℚ-linear constant-coefficient functional
`lcoeff ℚ 0` (paper §2.1 Definition 4: "SPDP matrix rows are indexed
by monomials") with the ℚ-linear embedding `r ↦ r • 1` given by
`LinearMap.toSpanSingleton ℚ _ 1`.

Concretely, `constantProjection N p = (coeff 0 p) • 1`, sending a
polynomial to the constant polynomial equal to its constant term.
-/

/-- **Constant-term projection** on the `N`-variable SPDP row space.

This is the ℚ-linear endomorphism of `MvPolynomial (Fin N) ℚ`
defined by `p ↦ (coeff 0 p) • 1` — that is, the composition of the
ℚ-linear functional `MvPolynomial.lcoeff ℚ 0` with the ℚ-linear
embedding `r ↦ r • 1` (`LinearMap.toSpanSingleton ℚ _ 1`).

The image of this map is the ℚ-span of the constant polynomial `1`,
which is at most one-dimensional; and the map is idempotent because
`coeff 0 (r • 1) = r` for all `r : ℚ`. -/
noncomputable def constantProjection (N : ℕ) :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ :=
  (LinearMap.toSpanSingleton ℚ (MvPolynomial (Fin N) ℚ) 1).comp
    (MvPolynomial.lcoeff ℚ (0 : Fin N →₀ ℕ))

/-- Pointwise evaluation of `constantProjection`. -/
theorem constantProjection_apply (N : ℕ) (p : MvPolynomial (Fin N) ℚ) :
    constantProjection N p
      = (MvPolynomial.coeff (0 : Fin N →₀ ℕ) p)
          • (1 : MvPolynomial (Fin N) ℚ) := by
  unfold constantProjection
  simp [LinearMap.toSpanSingleton_apply, MvPolynomial.lcoeff_apply]

/-- Evaluation of `constantProjection` on the constant polynomial
`r • 1`: it is a fixed point. -/
theorem constantProjection_smul_one (N : ℕ) (r : ℚ) :
    constantProjection N (r • (1 : MvPolynomial (Fin N) ℚ))
      = r • (1 : MvPolynomial (Fin N) ℚ) := by
  rw [constantProjection_apply]
  -- `coeff 0 (r • 1) = r`.
  have hcoeff : MvPolynomial.coeff (0 : Fin N →₀ ℕ)
      (r • (1 : MvPolynomial (Fin N) ℚ)) = r := by
    rw [MvPolynomial.coeff_smul]
    -- `coeff 0 (1 : MvPolynomial _ ℚ) = 1`.
    have h1 : MvPolynomial.coeff (0 : Fin N →₀ ℕ)
        (1 : MvPolynomial (Fin N) ℚ) = 1 := by
      classical
      rw [MvPolynomial.coeff_one]
      simp
    rw [h1, smul_eq_mul, mul_one]
  rw [hcoeff]

/-! ## 2. Idempotence and finite-rank range -/

/-- **Idempotence of `constantProjection`**: applying the constant-term
projection twice is the same as applying it once.

This is the `is_idempotent` obligation of `CandidateGauge N`. -/
theorem constantProjection_is_idempotent (N : ℕ) :
    (constantProjection N).comp (constantProjection N)
      = constantProjection N := by
  refine LinearMap.ext (fun p => ?_)
  -- LHS: `constantProjection (constantProjection p) =
  --        constantProjection ((coeff 0 p) • 1) =
  --        (coeff 0 p) • 1 = constantProjection p`.
  rw [LinearMap.comp_apply]
  -- Rewrite the outer `constantProjection` applied to `constantProjection N p`.
  conv_lhs => rw [constantProjection_apply N (constantProjection N p)]
  -- And the inner one.
  rw [constantProjection_apply N p]
  -- Now: `coeff 0 ((coeff 0 p) • 1) • 1 = (coeff 0 p) • 1`.
  rw [MvPolynomial.coeff_smul]
  have h1 : MvPolynomial.coeff (0 : Fin N →₀ ℕ)
      (1 : MvPolynomial (Fin N) ℚ) = 1 := by
    classical
    rw [MvPolynomial.coeff_one]; simp
  rw [h1, smul_eq_mul, mul_one]

/-- The range of `constantProjection N` is contained in the ℚ-span of
the constant polynomial `1`. -/
theorem range_constantProjection_le_span_one (N : ℕ) :
    LinearMap.range (constantProjection N)
      ≤ Submodule.span ℚ ({1} : Set (MvPolynomial (Fin N) ℚ)) := by
  intro x hx
  -- Every element of the range is of the form `constantProjection p`,
  -- i.e. `(coeff 0 p) • 1 ∈ span {1}`.
  rcases hx with ⟨p, hp⟩
  rw [← hp, constantProjection_apply]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- **Finite-rank range** of `constantProjection N`: the range is
contained in `Submodule.span ℚ {1}`, which is finitely generated, hence
`Module.Finite`. -/
theorem constantProjection_range_finite (N : ℕ) :
    Module.Finite ℚ (LinearMap.range (constantProjection N)) := by
  -- Step 1: The full span `Submodule.span ℚ {1}` is finitely
  -- generated, hence `Module.Finite`.
  have hspanFG : (Submodule.span ℚ
      ({1} : Set (MvPolynomial (Fin N) ℚ))).FG :=
    Submodule.fg_span_singleton _
  haveI hspanFin : Module.Finite ℚ
      (Submodule.span ℚ ({1} : Set (MvPolynomial (Fin N) ℚ))) :=
    Module.Finite.iff_fg.mpr hspanFG
  -- Step 2: The range of `constantProjection N` sits inside
  -- `Submodule.span ℚ {1}`, and the subtype inclusion is an injective
  -- ℚ-linear map.  Hence `Module.Finite.of_injective` transfers
  -- finiteness from the ambient span to the range.
  have hle : LinearMap.range (constantProjection N)
      ≤ Submodule.span ℚ ({1} : Set (MvPolynomial (Fin N) ℚ)) :=
    range_constantProjection_le_span_one N
  exact Module.Finite.of_injective
    (f := (Submodule.inclusion hle :
              LinearMap.range (constantProjection N)
                →ₗ[ℚ] Submodule.span ℚ
                  ({1} : Set (MvPolynomial (Fin N) ℚ))))
    (Submodule.inclusion_injective hle)

/-! ## 3. Non-zero candidate gauge -/

/-- **Non-zero candidate gauge** for the SPDP row space.

This assembles `constantProjection N` into a `CandidateGauge N`,
exhibiting the non-trivial analogue of `trivialGauge N`.  The
projection has rank (at most) `1`, with range equal to the ℚ-span
of the constant polynomial `1`. -/
noncomputable def nonZeroGauge (N : ℕ) : CandidateGauge N where
  projection := constantProjection N
  is_idempotent := constantProjection_is_idempotent N
  rank_finite := constantProjection_range_finite N

/-- Sanity example: the non-zero gauge is a well-formed candidate. -/
noncomputable example (N : ℕ) : CandidateGauge N := nonZeroGauge N

end PallLean.Paper93.Substantive
