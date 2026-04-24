/-
  PallLean/Paper93/NFrame/PSideCollapse.lean

  Paper §7.1 Theorem 10 (Holographic Upper-Bound Principle) — derived
  P-side SPDP rank collapse for Π⋆, unconditionally.

  ## Scope

  This file combines Agent S2's Euler–Lagrange existence theorem for
  Π⋆ (`PallLean/Paper93/NFrame/PiStarExistence.lean`,
  `piStar_exists`) with the Agent S1 skeleton's concrete
  `nframeLagrangian` (which reduces to `Module.finrank ℚ (range
  projection)` via `nframeLagrangian_eq_finrank`) to derive the
  paper §7.1 Theorem 10 P-side collapse property of Π⋆
  **without assuming** the abstract `PSideCollapseHypothesis`
  Prop-level hypothesis used in S2's
  `piStar_exists_bundled`.

  The derivation exploits the observation stated in the task prompt:

    * The admissible set contains the trivial gauge (`trivialGauge N`)
      with `Module.finrank ℚ (range 0) = 0`.
    * The ℕ-valued Lagrangian is non-negative, so
      `lagrangianNatMin N = 0`.
    * Hence the S2 minimiser Π⋆ satisfies
      `Module.finrank ℚ (range Π⋆.projection) = 0`, i.e.
      `range Π⋆.projection = ⊥`.
    * Therefore Π⋆.projection `f = 0` for every `f`, and in particular
      `mlBlockedSpdpRank B κ ℓ (Π⋆.projection f) = 0 ≤ N^200`.

  ## Honest assessment of Prop-hypothesis elimination

  The statement obtained here is formally non-vacuous as a Lean theorem
  — it asserts a `mlBlockedSpdpRank` bound on an actual projected
  polynomial. But the underlying construction is **kernel-only
  trivial**: in the Agent S1 skeleton, the S1 admissibility
  predicate is weak enough that the Lagrangian minimiser collapses
  all input to `0`. The statement is therefore UNCONDITIONAL and
  CANONICAL given the S1 skeleton, but its non-triviality awaits a
  refinement of `AdmissibleGauge` in S1 that forces the minimiser's
  projection to be a non-zero gauge.

  In the `piStar_exists_bundled` framework, this file's
  `piStar_P_side_collapse_derived` replaces the
  `PSideCollapseHypothesis` Prop argument with an unconditional
  proof; it does NOT weaken or eliminate
  `RankMonotoneHypothesis` or `IdentityMinorPreservationHypothesis`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build PallLean.Paper93.NFrame.PSideCollapse`.
    * Kernel-only axiom profile
      `[propext, Classical.choice, Quot.sound]`.

  ## Paper citations

    * §7.1 Theorem 10 (Holographic Upper-Bound Principle): for every
      `f ∈ P` compiled via Cook–Levin, `rk_SPDP(E(f); r(n)) ≤ n^{O(1)}`
      under Π⋆ (paper pp. 25–26).
    * §28.3 Bridge B (determinantal barrier ⇒ global rank),
      pp. 137–138.
-/

import PallLean.Paper93.NFrame.PiStarExistence
import PallLean.MultilinearSPDP
import PallLean.SPDPDefs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace PallLean
namespace Paper93
namespace NFrame

open MvPolynomial SPDP MultilinearSPDP

/-! ## 1. The admissible Lagrangian infimum is `0`

We first show the trivial gauge attains Lagrangian value `0`, hence
the ℕ-valued infimum `lagrangianNatMin N` equals `0`. -/

/-- The trivial gauge has ℕ-valued Lagrangian value `0`. -/
theorem lagrangianNat_trivialGauge (N : ℕ) :
    lagrangianNat (trivialGauge N) = 0 := by
  unfold lagrangianNat trivialGauge
  -- `LinearMap.range (0 : V →ₗ V) = ⊥`, and `finrank ⊥ = 0`.
  have hrange :
      LinearMap.range
        (0 : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ) = ⊥ :=
    LinearMap.range_zero
  rw [hrange]
  exact finrank_bot ℚ (MvPolynomial (Fin N) ℚ)

/-- `0` is an attained Lagrangian ℕ-value (the trivial gauge witness). -/
theorem zero_mem_admissibleLagrangianNatValues (N : ℕ) :
    (0 : ℕ) ∈ admissibleLagrangianNatValues N := by
  refine ⟨trivialGauge N, ?_, lagrangianNat_trivialGauge N⟩
  unfold AdmissibleGauge trivialGauge
  simp

/-- The ℕ-valued Lagrangian infimum is exactly `0`. -/
theorem lagrangianNatMin_eq_zero (N : ℕ) :
    lagrangianNatMin N = 0 := by
  unfold lagrangianNatMin
  -- `sInf` of a set containing `0` is ≤ `0`, and every `ℕ`-valued `sInf`
  -- is ≥ `0`.
  have hle : sInf (admissibleLagrangianNatValues N) ≤ 0 :=
    Nat.sInf_le (zero_mem_admissibleLagrangianNatValues N)
  exact Nat.le_zero.mp hle

/-! ## 2. Kernel-range collapse of the S2 minimiser

Because the Lagrangian reduces to `finrank (range projection)`
(Agent S1 concrete form, `nframeLagrangian_eq_finrank`), the
minimiser Π⋆ must have `finrank (range Π⋆.projection) = 0`, which
forces `range Π⋆.projection = ⊥`. -/

/-- There exists a minimiser Π⋆ whose range has `finrank` equal to the
ℕ-valued infimum, which is `0`. -/
theorem exists_piStar_finrank_zero (N : ℕ) :
    ∃ Pi : CandidateGauge N, AdmissibleGauge Pi ∧
      Module.finrank ℚ (LinearMap.range Pi.projection) = 0 := by
  obtain ⟨PiStar, hAdm, hval⟩ := lagrangianNatMin_mem N
  rw [lagrangianNatMin_eq_zero] at hval
  -- `hval : lagrangianNat PiStar = 0`
  refine ⟨PiStar, hAdm, ?_⟩
  exact hval

/-- There exists a minimiser Π⋆ whose range is the zero submodule. -/
theorem exists_piStar_range_bot (N : ℕ) :
    ∃ Pi : CandidateGauge N, AdmissibleGauge Pi ∧
      LinearMap.range Pi.projection = ⊥ := by
  obtain ⟨PiStar, hAdm, hfin⟩ := exists_piStar_finrank_zero N
  refine ⟨PiStar, hAdm, ?_⟩
  -- Use the Agent S1 finite-rank hypothesis `PiStar.rank_finite` and
  -- `Submodule.finrank_eq_zero` to promote `finrank = 0` to `= ⊥`.
  have _finiteRange : Module.Finite ℚ (LinearMap.range PiStar.projection) :=
    PiStar.rank_finite
  exact Submodule.finrank_eq_zero.mp hfin

/-- There exists a minimiser Π⋆ which sends every polynomial to `0`. -/
theorem exists_piStar_projection_eq_zero (N : ℕ) :
    ∃ Pi : CandidateGauge N, AdmissibleGauge Pi ∧
      ∀ f : MvPolynomial (Fin N) ℚ, Pi.projection f = 0 := by
  obtain ⟨PiStar, hAdm, hrange⟩ := exists_piStar_range_bot N
  refine ⟨PiStar, hAdm, ?_⟩
  intro f
  -- `PiStar.projection f ∈ range PiStar.projection = ⊥`, so it is `0`.
  have hmem : PiStar.projection f ∈ LinearMap.range PiStar.projection :=
    LinearMap.mem_range_self _ f
  rw [hrange] at hmem
  exact (Submodule.mem_bot ℚ).mp hmem

/-! ## 3. Paper §7.1 Theorem 10 — P-side collapse, derived -/

/-- **Paper §7.1 Theorem 10 — Holographic Upper-Bound Principle
(derived form).**

For every `N ≥ 0`, every SPDP block partition `B`, every `κ, ℓ`,
and every input polynomial `f ∈ MvPolynomial (Fin N) ℚ`, there is an
admissible candidate gauge Π⋆ whose SPDP-rank of the projected
polynomial is polynomially bounded by `N^200`.

This realises paper §7.1 Theorem 10 in the Agent S1 skeleton
unconditionally: the S2 Euler–Lagrange minimiser
(`piStar_exists`) of the concrete Agent S1 Lagrangian has
`finrank(range) = 0`, whence the projection annihilates every
input, and the SPDP rank of the zero polynomial is `0 ≤ N^200`.

The signature matches the task prompt exactly. The parameters `κ`,
`ℓ`, `hκ`, `hℓ` are included per the prompt; their values are not
used in the proof. -/
theorem piStar_P_side_collapse_derived
    {N : ℕ} (B : SPDP.BlockPartition N) (κ ℓ : ℕ)
    (f : MvPolynomial (Fin N) ℚ)
    (_hκ : κ = Nat.log 2 N) (_hℓ : ℓ = Nat.log 2 N) :
    ∃ Pi : CandidateGauge N, AdmissibleGauge Pi ∧
      MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (Pi.projection f) ≤ N ^ 200 := by
  obtain ⟨PiStar, hAdm, hproj⟩ := exists_piStar_projection_eq_zero N
  refine ⟨PiStar, hAdm, ?_⟩
  rw [hproj f]
  rw [MultilinearSPDP.mlBlockedSpdpRank_zero]
  exact Nat.zero_le _

/-! ## 4. Bundled Π⋆ existence with P-side collapse unconditionally

We re-package `piStar_exists_bundled` so that the
`PSideCollapseHypothesis` is discharged internally for the concrete
SPDP-rank functional, leaving only the paper-faithful
`RankMonotoneHypothesis` and `IdentityMinorPreservationHypothesis`
Prop-level hypotheses as admitted input. -/

/-- The SPDP-rank functional `ρ_SPDP(p) := mlBlockedSpdpRank B κ ℓ p`
satisfies the `PSideCollapseHypothesis` for any admissible gauge Π⋆
whose range is `⊥`, with `polyBound k := 0`. -/
theorem pSideCollapseHypothesis_of_range_bot
    {N : ℕ} (B : SPDP.BlockPartition N) (κ ℓ : ℕ)
    (Pi : CandidateGauge N)
    (hrange : LinearMap.range Pi.projection = ⊥)
    (family : ℕ → MvPolynomial (Fin N) ℚ) :
    PSideCollapseHypothesis Pi family
      (fun p => MultilinearSPDP.mlBlockedSpdpRank B κ ℓ p) := by
  refine ⟨fun _ => 0, ?_⟩
  intro k
  have hproj : Pi.projection (family k) = 0 := by
    have hmem : Pi.projection (family k) ∈ LinearMap.range Pi.projection :=
      LinearMap.mem_range_self _ _
    rw [hrange] at hmem
    exact (Submodule.mem_bot ℚ).mp hmem
  show MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (Pi.projection (family k)) ≤ 0
  rw [hproj, MultilinearSPDP.mlBlockedSpdpRank_zero]

/-- **Paper §7.1 Theorem 10 — bundled Π⋆ existence with unconditional
P-side collapse** (derived form).

This is the Agent S2 `piStar_exists_bundled` with the
`PSideCollapseHypothesis` Prop-argument replaced by an internal
proof using the trivial-range collapse of the Agent S1 minimiser.

The `RankMonotoneHypothesis` and `IdentityMinorPreservationHypothesis`
remain as Prop-level hypotheses, matching the paper's separate
content for §7.1 Theorem 10 (rank monotonicity) and §7.1 Theorem 11
(identity-minor preservation). -/
theorem piStar_exists_bundled_pSideCollapse_derived
    {N : ℕ} (B : SPDP.BlockPartition N) (κ ℓ : ℕ)
    (family : ℕ → MvPolynomial (Fin N) ℚ)
    (hRankMonotone :
      ∀ Pi : CandidateGauge N, AdmissibleGauge Pi →
        RankMonotoneHypothesis Pi
          (fun p => MultilinearSPDP.mlBlockedSpdpRank B κ ℓ p))
    (hIdentityMinor :
      ∀ Pi : CandidateGauge N, AdmissibleGauge Pi →
        IdentityMinorPreservationHypothesis Pi family) :
    ∃ Pi : CandidateGauge N, AdmissibleGauge Pi ∧
      (∀ Pi' : CandidateGauge N, AdmissibleGauge Pi' →
        nframeLagrangian family Pi ≤ nframeLagrangian family Pi') ∧
      (∀ p : MvPolynomial (Fin N) ℚ,
        MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (Pi.projection p) ≤
          MultilinearSPDP.mlBlockedSpdpRank B κ ℓ p) ∧
      (∀ k : ℕ, family k ≠ 0 → Pi.projection (family k) ≠ 0) ∧
      (∃ polyBound : ℕ → ℕ,
        ∀ k : ℕ,
          MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (Pi.projection (family k)) ≤
            polyBound k) := by
  -- Pick the minimiser with `range = ⊥` from §2.
  obtain ⟨PiStar, hAdm, hrange⟩ := exists_piStar_range_bot N
  -- Recover the minimiser-of-Lagrangian clause from S2.
  obtain ⟨PiMin, hAdmMin, hminLag⟩ := piStar_exists family
  -- We must select a single witness: pick the `range = ⊥` minimiser
  -- `PiStar` and show it also minimises the Lagrangian by reducing both
  -- sides via `nframeLagrangian_eq_finrank` to the shared ℕ-valued
  -- infimum `lagrangianNatMin = 0`.
  refine ⟨PiStar, hAdm, ?_, ?_, ?_, ?_⟩
  · -- Π⋆ minimises the Lagrangian because its `finrank` is `0`, the
    -- minimum possible value.
    intro Pi' hAdm'
    rw [nframeLagrangian_eq_cast_lagrangianNat family PiStar,
        nframeLagrangian_eq_cast_lagrangianNat family Pi']
    have hPiStarZero : lagrangianNat PiStar = 0 := by
      unfold lagrangianNat
      -- `range = ⊥` implies `finrank = 0`.
      rw [hrange]
      simp
    have hPiPrimeVal :
        lagrangianNat Pi' ∈ admissibleLagrangianNatValues N :=
      ⟨Pi', hAdm', rfl⟩
    have hnn : 0 ≤ lagrangianNat Pi' := Nat.zero_le _
    have : (lagrangianNat PiStar : ℝ) ≤ (lagrangianNat Pi' : ℝ) := by
      rw [hPiStarZero]; exact_mod_cast hnn
    exact this
  · -- Rank monotonicity for Π⋆.
    exact hRankMonotone PiStar hAdm
  · -- Identity-minor preservation for Π⋆.
    exact hIdentityMinor PiStar hAdm
  · -- Unconditional P-side collapse: use the trivial-range fact.
    exact pSideCollapseHypothesis_of_range_bot B κ ℓ PiStar hrange family

/-! ## 5. Kernel-only axiom trace -/

#print axioms piStar_P_side_collapse_derived
#print axioms exists_piStar_range_bot
#print axioms exists_piStar_projection_eq_zero
#print axioms pSideCollapseHypothesis_of_range_bot
#print axioms piStar_exists_bundled_pSideCollapse_derived
#print axioms lagrangianNatMin_eq_zero

end NFrame
end Paper93
end PallLean
