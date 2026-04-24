/-
  PallLean/Paper93/Substantive/NonTrivialRange.lean

  Agent W2 — Paper §7.1 p. 25 / §28.3 p. 137 "Non-trivial-range
  candidate gauge for the N-Frame Lagrangian variational problem".

  ## Scope

  The structure `CandidateGauge N` (bundled in
  `PallLean/Paper93/NFrame/LagrangianFunctional.lean`) requires:

    1. a ℚ-linear projection on `MvPolynomial (Fin N) ℚ`;
    2. idempotence (`projection.comp projection = projection`);
    3. a *finite-rank* range (`Module.Finite ℚ (LinearMap.range projection)`).

  The bundled `trivialGauge N` has projection `0` and range `⊥`, which
  trivially satisfies the finite-rank clause (rank `0`) but has *zero*
  range.  For the paper-faithful Lagrangian analysis of §28.3 we need
  an *explicit* `CandidateGauge N` whose range is non-zero (i.e.\ the
  projection is not the zero map).  The naive idempotent
  `id : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ` fails the
  `rank_finite` clause because `MvPolynomial (Fin N) ℚ` is infinite
  dimensional over ℚ for any `N ≥ 0` (it has the countable free basis
  of monomials).

  The present W2 file constructs a candidate gauge with a *one*-
  dimensional range, whose projection lands in the ℚ-span of the
  constant polynomial `1`:

    * `toConstantsProjection N` — the ℚ-linear endomorphism of
      `MvPolynomial (Fin N) ℚ` defined by
      `p ↦ (MvPolynomial.constantCoeff p) • 1`.

    * `nonTrivialGauge N` — the `CandidateGauge N` assembled from
      `toConstantsProjection N`, with idempotence via
      `constantCoeff (r • 1) = r`, and finite-rank range via
      `LinearMap.range (toConstantsProjection N) ≤ Submodule.span ℚ {1}`
      (the ambient span being one-dimensional, hence finite).

    * `nonTrivialGauge_range_nonzero` — a witness that the range is
      not the bottom submodule: `(1 : MvPolynomial (Fin N) ℚ)` lies in
      the range, and `1 ≠ 0`, so the range is strictly above `⊥`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms nonTrivialGauge_range_nonzero`:
      [propext, Classical.choice, Quot.sound]

  ## Paper citations

    * §7.1 pp. 25–26 — candidate gauges as linear projections on the
      SPDP row space; universal observer gauge `Π⋆` as the
      rank-minimiser across admissible gauges.
    * §28.3 pp. 137–138 — analytic reformulation, non-vacuous wedge
      between the rank-zero vertex and positive-rank admissible
      candidates.
-/
import PallLean.Paper93.NFrame.LagrangianFunctional
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic

namespace PallLean.Paper93.Substantive

open MvPolynomial
open PallLean.Paper93.NFrame

/-! ## 1. Projection onto the ℚ-span of the constant polynomial `1`

The projection sends a polynomial to its constant-term scalar
multiple of `1`.  We realise it as the composition of the ℚ-linear
functional `MvPolynomial.lcoeff ℚ 0` (extracting the constant
coefficient) with the ℚ-linear embedding `r ↦ r • 1`
(`LinearMap.toSpanSingleton ℚ _ 1`).

Paper §2.1 Definition 4: "SPDP matrix rows are indexed by monomials"
— the monomial indexed by the zero exponent vector is the constant
polynomial `1`, so this projection factors every polynomial through
its *constant* row. -/

/-- **Projection to span{1} (the constants).**

`toConstantsProjection N : p ↦ (coeff 0 p) • 1`.

The comment in the W2 task description clarifies the intended
factorisation: `p ↦ constantCoeff p` (a ℚ-linear functional) followed
by `r ↦ r • 1` (the embedding `LinearMap.toSpanSingleton ℚ _ 1`).
We realise `p ↦ constantCoeff p` by the ℚ-linear map
`MvPolynomial.lcoeff ℚ 0`. -/
noncomputable def toConstantsProjection (N : ℕ) :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ :=
  (LinearMap.toSpanSingleton ℚ (MvPolynomial (Fin N) ℚ) 1).comp
    (MvPolynomial.lcoeff ℚ (0 : Fin N →₀ ℕ))

/-- Pointwise evaluation: `toConstantsProjection N p = (coeff 0 p) • 1`. -/
@[simp]
theorem toConstantsProjection_apply (N : ℕ) (p : MvPolynomial (Fin N) ℚ) :
    toConstantsProjection N p
      = (MvPolynomial.coeff (0 : Fin N →₀ ℕ) p)
          • (1 : MvPolynomial (Fin N) ℚ) := by
  unfold toConstantsProjection
  simp [LinearMap.toSpanSingleton_apply, MvPolynomial.lcoeff_apply]

/-- The constant coefficient of the polynomial `1` is `1`. -/
private theorem coeff_zero_one (N : ℕ) :
    MvPolynomial.coeff (0 : Fin N →₀ ℕ) (1 : MvPolynomial (Fin N) ℚ) = 1 := by
  classical
  rw [MvPolynomial.coeff_one]
  simp

/-- `toConstantsProjection` is a fixed point on scalar multiples of
`1`: applied to `r • 1`, it returns `r • 1`. -/
theorem toConstantsProjection_smul_one (N : ℕ) (r : ℚ) :
    toConstantsProjection N (r • (1 : MvPolynomial (Fin N) ℚ))
      = r • (1 : MvPolynomial (Fin N) ℚ) := by
  rw [toConstantsProjection_apply]
  have hcoeff : MvPolynomial.coeff (0 : Fin N →₀ ℕ)
      (r • (1 : MvPolynomial (Fin N) ℚ)) = r := by
    rw [MvPolynomial.coeff_smul, coeff_zero_one, smul_eq_mul, mul_one]
  rw [hcoeff]

/-! ## 2. Idempotence obligation

`projection.comp projection = projection` amounts to the fact that
applying the constant-coefficient extractor twice (through the
embedding `r • 1`) fixes scalar multiples of `1`. -/

/-- **Idempotence of `toConstantsProjection`.** -/
theorem toConstantsProjection_is_idempotent (N : ℕ) :
    (toConstantsProjection N).comp (toConstantsProjection N)
      = toConstantsProjection N := by
  refine LinearMap.ext (fun p => ?_)
  rw [LinearMap.comp_apply]
  -- Outer application.
  conv_lhs => rw [toConstantsProjection_apply N (toConstantsProjection N p)]
  -- Inner application.
  rw [toConstantsProjection_apply N p]
  -- Reduce `coeff 0 ((coeff 0 p) • 1) = coeff 0 p * 1 = coeff 0 p`.
  rw [MvPolynomial.coeff_smul, coeff_zero_one, smul_eq_mul, mul_one]

/-! ## 3. Finite-rank range obligation

The range is contained in `Submodule.span ℚ {1}` which is one-
dimensional; by `Module.Finite.of_injective` finiteness transfers
to the range via the inclusion. -/

/-- The range of `toConstantsProjection N` is contained in the ℚ-span
of the constant polynomial `1`. -/
theorem range_toConstantsProjection_le_span_one (N : ℕ) :
    LinearMap.range (toConstantsProjection N)
      ≤ Submodule.span ℚ ({1} : Set (MvPolynomial (Fin N) ℚ)) := by
  intro x hx
  rcases hx with ⟨p, hp⟩
  rw [← hp, toConstantsProjection_apply]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_singleton _))

/-- **Finite-rank range** of `toConstantsProjection N`. -/
theorem toConstantsProjection_range_finite (N : ℕ) :
    Module.Finite ℚ (LinearMap.range (toConstantsProjection N)) := by
  -- The ambient span `span ℚ {1}` is finitely generated, hence finite.
  have hspanFG : (Submodule.span ℚ
      ({1} : Set (MvPolynomial (Fin N) ℚ))).FG :=
    Submodule.fg_span_singleton _
  haveI hspanFin : Module.Finite ℚ
      (Submodule.span ℚ ({1} : Set (MvPolynomial (Fin N) ℚ))) :=
    Module.Finite.iff_fg.mpr hspanFG
  -- Transfer finiteness along the injective subtype inclusion
  -- `range (toConstantsProjection N) ↪ span ℚ {1}`.
  have hle : LinearMap.range (toConstantsProjection N)
      ≤ Submodule.span ℚ ({1} : Set (MvPolynomial (Fin N) ℚ)) :=
    range_toConstantsProjection_le_span_one N
  exact Module.Finite.of_injective
    (f := (Submodule.inclusion hle :
              LinearMap.range (toConstantsProjection N)
                →ₗ[ℚ] Submodule.span ℚ
                  ({1} : Set (MvPolynomial (Fin N) ℚ))))
    (Submodule.inclusion_injective hle)

/-! ## 4. Candidate gauge with non-trivial range -/

/-- **Candidate gauge with non-trivial range.**

Assembled from `toConstantsProjection N` together with the
idempotence and finite-rank proofs above.  Concretely, the gauge's
projection is `p ↦ (coeff 0 p) • 1`, and its range is the one-
dimensional ℚ-span of the constant polynomial `1`. -/
noncomputable def nonTrivialGauge (N : ℕ) :
    PallLean.Paper93.NFrame.CandidateGauge N where
  projection := toConstantsProjection N
  is_idempotent := toConstantsProjection_is_idempotent N
  rank_finite := toConstantsProjection_range_finite N

/-- The constant polynomial `1` is in the range of
`toConstantsProjection N`: it is the image of itself. -/
theorem one_mem_range_toConstantsProjection (N : ℕ) :
    (1 : MvPolynomial (Fin N) ℚ)
      ∈ LinearMap.range (toConstantsProjection N) := by
  refine ⟨(1 : MvPolynomial (Fin N) ℚ), ?_⟩
  rw [toConstantsProjection_apply, coeff_zero_one, one_smul]

/-- **Non-zero range witness** for `nonTrivialGauge N`.

Under any `N` (not just positive `N`), the range of the
`nonTrivialGauge N` projection is strictly above `⊥` — it contains
the non-zero constant polynomial `1`.  The hypothesis `0 < N` is
therefore not logically required by the proof, but we keep it in
the signature to match the W2 task specification. -/
theorem nonTrivialGauge_range_nonzero (N : ℕ) (_hN : 0 < N) :
    LinearMap.range (nonTrivialGauge N).projection ≠ ⊥ := by
  -- If the range were `⊥`, then the element `1`, which lies in the
  -- range, would equal `0` in `MvPolynomial (Fin N) ℚ`.  But `ℚ` is
  -- non-trivial, so `1 ≠ 0` in `MvPolynomial (Fin N) ℚ`.
  intro hbot
  have h1mem : (1 : MvPolynomial (Fin N) ℚ)
      ∈ LinearMap.range (nonTrivialGauge N).projection := by
    -- Unfold `nonTrivialGauge` to expose the underlying projection.
    show (1 : MvPolynomial (Fin N) ℚ)
        ∈ LinearMap.range (toConstantsProjection N)
    exact one_mem_range_toConstantsProjection N
  -- `hbot` says the range equals `⊥`, so `1 ∈ ⊥`, hence `1 = 0`.
  rw [hbot, Submodule.mem_bot] at h1mem
  exact (one_ne_zero (α := MvPolynomial (Fin N) ℚ)) h1mem

/-! ## 5. Kernel-only sanity examples -/

noncomputable example (N : ℕ) :
    PallLean.Paper93.NFrame.CandidateGauge N :=
  nonTrivialGauge N

example (N : ℕ) (hN : 0 < N) :
    LinearMap.range (nonTrivialGauge N).projection ≠ ⊥ :=
  nonTrivialGauge_range_nonzero N hN

end PallLean.Paper93.Substantive
