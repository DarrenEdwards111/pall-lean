import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeDischargeSubgoals
import PallLean.PaperFaithfulCompilation

/-!
# Rank-monotone gauge criterion

This file isolates the linear-algebra core behind the existing gauge
rank-monotonicity proofs: it is enough to show that each SPDP subspace after
applying a gauge is contained in the linear image of the original SPDP
subspace.  The result is deliberately only a rank-monotonicity criterion; it
does not assert the P-side bound or NP identity-minor preservation fields.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

variable {N : Nat}

/-- Linear-map image containment gives the corresponding finrank inequality. -/
theorem finrank_le_of_submodule_le_map
    {V : Type*} [AddCommGroup V] [Module Rat V]
    (g : V →ₗ[Rat] V) (U W : Submodule Rat V)
    [Module.Finite Rat U] [Module.Finite Rat W]
    (hW : W ≤ Submodule.map g U) :
    Module.finrank Rat W ≤ Module.finrank Rat U := by
  calc
    Module.finrank Rat W ≤ Module.finrank Rat (Submodule.map g U) :=
      Submodule.finrank_mono hW
    _ ≤ Module.finrank Rat U :=
      Submodule.finrank_map_le g U

/-- The reusable SPDP-subspace image-containment criterion for a polynomial
endomorphism. -/
def SPDPSubspaceImageContainment
    (B : SPDP.BlockPartition N)
    (gauge : MvPolynomial (Fin N) Rat →ₗ[Rat] MvPolynomial (Fin N) Rat) :
    Prop :=
  ∀ (κ ℓ : Nat) (p : MvPolynomial (Fin N) Rat),
    mlBlockedSpdpSubspace B κ ℓ (gauge p) ≤
      Submodule.map gauge (mlBlockedSpdpSubspace B κ ℓ p)

/-- Generator-level form of the image-containment criterion.  This is the
shape used by concrete projection gauges: each projected SPDP generator must
be the gauge image of an original SPDP-span element. -/
theorem spdpSubspaceImageContainment_of_generator_image_mem
    (B : SPDP.BlockPartition N)
    (gauge : MvPolynomial (Fin N) Rat →ₗ[Rat] MvPolynomial (Fin N) Rat)
    (hgen :
      ∀ (κ ℓ : Nat) (p : MvPolynomial (Fin N) Rat)
        (S : List (Fin N)) (m : MvPolynomial (Fin N) Rat),
        S.length = κ →
        m.totalDegree ≤ ℓ →
        m.vars ⊆ S.toFinset →
        SPDP.isBlockAdmissible B S →
        mlProj (m * SPDP.iterDerivList S (gauge p)) ∈
          Submodule.map gauge (mlBlockedSpdpSubspace B κ ℓ p)) :
    SPDPSubspaceImageContainment B gauge := by
  intro κ ℓ p
  unfold mlBlockedSpdpSubspace
  rw [Submodule.span_le]
  rintro q ⟨S, m, hSlen, hmdeg, hmvars, hadm, hq⟩
  rw [hq]
  exact hgen κ ℓ p S m hSlen hmdeg hmvars hadm

/-- The SPDP-subspace image-containment criterion implies generic
`GaugeMonotonicity.IsRankMonotoneGauge`. -/
theorem isRankMonotoneGauge_of_spdpSubspaceImageContainment
    (B : SPDP.BlockPartition N)
    (gauge : MvPolynomial (Fin N) Rat →ₗ[Rat] MvPolynomial (Fin N) Rat)
    (hcontain : SPDPSubspaceImageContainment B gauge) :
    GaugeMonotonicity.IsRankMonotoneGauge B gauge := by
  intro κ ℓ p
  unfold mlBlockedSpdpRank
  exact finrank_le_of_submodule_le_map gauge
    (mlBlockedSpdpSubspace B κ ℓ p)
    (mlBlockedSpdpSubspace B κ ℓ (gauge p))
    (hcontain κ ℓ p)

/-- SAT-decider specialization of the SPDP-subspace image-containment
criterion. -/
def SATDeciderGaugeSPDPSubspaceImageContainment
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop :=
  SPDPSubspaceImageContainment
    (cook_levin_compilation M n hn2 htb hns).partition gauge

/-- SAT-decider rank monotonicity follows from the same image-containment
criterion. -/
theorem satDeciderGaugeRankMonotonicity_of_spdpSubspaceImageContainment
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hcontain :
      SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns gauge) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge :=
  isRankMonotoneGauge_of_spdpSubspaceImageContainment
    (cook_levin_compilation M n hn2 htb hns).partition gauge hcontain

/-- The existing `piZero` proof provides the stronger image-containment
statement, not just the final rank inequality. -/
theorem piZero_spdpSubspaceImageContainment
    (keep : Fin N → Prop) [DecidablePred keep]
    (B : SPDP.BlockPartition N) :
    SPDPSubspaceImageContainment B (PiStarConcrete.piZero keep) := by
  intro κ ℓ p q hq
  have hq' :=
    PiStarConcrete.mlBlockedSpdpSubspace_piSubst_factored
      keep (0 : Fin N → Rat) B κ ℓ p hq
  refine Submodule.span_le.mpr ?_ hq'
  rintro r ⟨S, m, hSlen, hmdeg, hmvars, hadm, hallkept, hr⟩
  have hm_kept : ∀ i ∈ m.vars, keep i := by
    intro i hi
    exact hallkept i (List.mem_toFinset.mp (hmvars hi))
  have hcomm :
      mlProj (m * PiStarConcrete.piZero keep (SPDP.iterDerivList S p)) =
        PiStarConcrete.piZero keep
          (mlProj (m * SPDP.iterDerivList S p)) :=
    PiStarConcrete.mlProj_mul_piZero_comm keep
      (PiStarConcrete.support_kept_of_vars_kept keep hm_kept)
      (SPDP.iterDerivList S p)
  rw [hr]
  show mlProj (m * PiStarConcrete.piSubst keep (0 : Fin N → Rat)
      (SPDP.iterDerivList S p)) ∈
    Submodule.map (PiStarConcrete.piZero keep)
      (mlBlockedSpdpSubspace B κ ℓ p)
  rw [show PiStarConcrete.piSubst keep (0 : Fin N → Rat)
      (SPDP.iterDerivList S p) =
        PiStarConcrete.piZero keep (SPDP.iterDerivList S p) from rfl]
  rw [hcomm]
  exact ⟨mlProj (m * SPDP.iterDerivList S p),
    Submodule.subset_span ⟨S, m, hSlen, hmdeg, hmvars, hadm, rfl⟩, rfl⟩

/-- Re-derivation of `piZero` rank monotonicity through the reusable
image-containment criterion. -/
theorem piZero_isRankMonotoneGauge_of_spdpSubspaceImageContainment
    (keep : Fin N → Prop) [DecidablePred keep]
    (B : SPDP.BlockPartition N) :
    GaugeMonotonicity.IsRankMonotoneGauge B (PiStarConcrete.piZero keep) :=
  isRankMonotoneGauge_of_spdpSubspaceImageContainment B
    (PiStarConcrete.piZero keep)
    (piZero_spdpSubspaceImageContainment keep B)

/-- `piPhi` also satisfies the stronger image-containment statement, by
specializing the `piZero` containment theorem to `keepU`. -/
theorem piPhi_spdpSubspaceImageContainment
    (σ : UVSplit) (B : SPDP.BlockPartition σ.total) :
    SPDPSubspaceImageContainment B (piPhi σ) := by
  unfold piPhi
  exact piZero_spdpSubspaceImageContainment (keepU σ) B

/-- Re-derivation of `piPhi` rank monotonicity through the reusable
image-containment criterion. -/
theorem piPhi_isRankMonotoneGauge_of_spdpSubspaceImageContainment
    (σ : UVSplit) (B : SPDP.BlockPartition σ.total) :
    GaugeMonotonicity.IsRankMonotoneGauge B (piPhi σ) :=
  isRankMonotoneGauge_of_spdpSubspaceImageContainment B (piPhi σ)
    (piPhi_spdpSubspaceImageContainment σ B)

/-- The complement of an idempotent projection is again an idempotent
projection.  This is only a structural fact; rank monotonicity for the
complement still needs the separate SPDP image-containment hypothesis below. -/
theorem complementProjection_isProjectionGauge_of_projection
    (gauge : MvPolynomial (Fin N) Rat →ₗ[Rat] MvPolynomial (Fin N) Rat)
    (hproj : GaugeMonotonicity.IsProjectionGauge gauge) :
    GaugeMonotonicity.IsProjectionGauge
      ((LinearMap.id : MvPolynomial (Fin N) Rat →ₗ[Rat]
        MvPolynomial (Fin N) Rat) - gauge) := by
  refine ⟨?_⟩
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [map_sub]
  rw [hproj.apply_apply]
  abel

/-- Complement projections become rank-monotone only after supplying the same
SPDP image-containment data for the complement map itself. -/
theorem complementProjection_isRankMonotoneGauge_of_spdpSubspaceImageContainment
    (B : SPDP.BlockPartition N)
    (gauge : MvPolynomial (Fin N) Rat →ₗ[Rat] MvPolynomial (Fin N) Rat)
    (hcontain : SPDPSubspaceImageContainment B
      ((LinearMap.id : MvPolynomial (Fin N) Rat →ₗ[Rat]
        MvPolynomial (Fin N) Rat) - gauge)) :
    GaugeMonotonicity.IsRankMonotoneGauge B
      ((LinearMap.id : MvPolynomial (Fin N) Rat →ₗ[Rat]
        MvPolynomial (Fin N) Rat) - gauge) :=
  isRankMonotoneGauge_of_spdpSubspaceImageContainment B
    ((LinearMap.id : MvPolynomial (Fin N) Rat →ₗ[Rat]
      MvPolynomial (Fin N) Rat) - gauge)
    hcontain

/-- Combined complement-projection package: idempotence transports from a
projection, while rank monotonicity is supplied by the extra SPDP containment. -/
theorem complementProjection_structure_and_rankMonotone_of_containment
    (B : SPDP.BlockPartition N)
    (gauge : MvPolynomial (Fin N) Rat →ₗ[Rat] MvPolynomial (Fin N) Rat)
    (hproj : GaugeMonotonicity.IsProjectionGauge gauge)
    (hcontain : SPDPSubspaceImageContainment B
      ((LinearMap.id : MvPolynomial (Fin N) Rat →ₗ[Rat]
        MvPolynomial (Fin N) Rat) - gauge)) :
    GaugeMonotonicity.IsProjectionGauge
        ((LinearMap.id : MvPolynomial (Fin N) Rat →ₗ[Rat]
          MvPolynomial (Fin N) Rat) - gauge) ∧
      GaugeMonotonicity.IsRankMonotoneGauge B
        ((LinearMap.id : MvPolynomial (Fin N) Rat →ₗ[Rat]
          MvPolynomial (Fin N) Rat) - gauge) :=
  ⟨complementProjection_isProjectionGauge_of_projection gauge hproj,
   complementProjection_isRankMonotoneGauge_of_spdpSubspaceImageContainment
    B gauge hcontain⟩

/-! ## Axiom audit anchors -/

#print axioms finrank_le_of_submodule_le_map
#print axioms spdpSubspaceImageContainment_of_generator_image_mem
#print axioms isRankMonotoneGauge_of_spdpSubspaceImageContainment
#print axioms satDeciderGaugeRankMonotonicity_of_spdpSubspaceImageContainment
#print axioms piZero_spdpSubspaceImageContainment
#print axioms piPhi_spdpSubspaceImageContainment
#print axioms complementProjection_structure_and_rankMonotone_of_containment

end PallLean.Paper93.DeepMath.PathB
