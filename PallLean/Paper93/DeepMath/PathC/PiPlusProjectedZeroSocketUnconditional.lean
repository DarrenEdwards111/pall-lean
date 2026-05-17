import PallLean.Paper93.DeepMath.PathC.PiPlusProjectedPayloadCloseout

/-!
# Unconditional projected zero-profile socket

This file discharges one projected zero-profile socket unconditionally: the zero
linear projection is idempotent, kills singleton shifts, and sends every
zero-profile shifted row to `0`, so the projected common span has empty basis.

This is useful but also diagnostic.  It shows that the current projected payload
interface is too weak unless the later Route-B bridge asks for a sufficiently
faithful quotient/projection.  No final P-side bound is claimed here.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- The zero linear projection at paper scale. -/
noncomputable def paperScaleZeroProjection :
    MvPolynomial (Fin (2 ^ 804)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (2 ^ 804)) ℚ :=
  0

/-- The zero projection is idempotent. -/
theorem paperScaleZeroProjection_idempotent :
    paperScaleZeroProjection.comp paperScaleZeroProjection =
      paperScaleZeroProjection := by
  ext q
  simp [paperScaleZeroProjection]

/-- The zero projection kills all singleton-shift rows for every paper-scale
Cook--Levin instance. -/
theorem paperScaleZeroProjection_killsSingleton
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    ZeroProfileProjectionKillsSingletonShifts
      (fun i =>
        (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
      paperScaleZeroProjection := by
  intro i
  change (0 : MvPolynomial (Fin (2 ^ 804)) ℚ) = 0
  rfl

/-- Unconditional projected zero-profile common span for the zero projection.
Every projected shifted row is `0`, so the empty span suffices. -/
theorem paperScaleZeroProjection_projectedZeroCommonSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
      M htb hns paperScaleZeroProjection := by
  classical
  refine ⟨∅, by simp, ?_⟩
  intro q hq
  rcases hq with ⟨row, _hrow, rfl⟩
  change (0 : MvPolynomial (Fin (2 ^ 804)) ℚ) ∈
    Submodule.span ℚ (↑(∅ : Finset (MvPolynomial (Fin (2 ^ 804)) ℚ)) :
      Set (MvPolynomial (Fin (2 ^ 804)) ℚ))
  exact Submodule.zero_mem _

/-- The three projection-side fields for a paper-scale projected payload are
unconditionally available for the zero projection.  This intentionally does not
construct a full payload, because the Pi+ transport, NP inclusion, active data,
and faithful Route-B bridge remain separate mathematical payloads. -/
structure PaperScaleZeroProjectionSocket
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Type where
  project :
    MvPolynomial (Fin (2 ^ 804)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (2 ^ 804)) ℚ
  project_eq : project = paperScaleZeroProjection
  project_idempotent : project.comp project = project
  killsSingleton :
    ZeroProfileProjectionKillsSingletonShifts
      (fun i =>
        (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
      project
  projected_zero_common_span :
    PaperScaleCookLevinOneWindowProjectedZeroHistogramShiftCommonSpan
      M htb hns project

/-- Inhabitant of the unconditional zero-projection socket. -/
noncomputable def paperScaleZeroProjectionSocket
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleZeroProjectionSocket M htb hns where
  project := paperScaleZeroProjection
  project_eq := rfl
  project_idempotent := paperScaleZeroProjection_idempotent
  killsSingleton := paperScaleZeroProjection_killsSingleton M htb hns
  projected_zero_common_span :=
    paperScaleZeroProjection_projectedZeroCommonSpan M htb hns

/-! ## Axiom audit anchors -/

#print axioms paperScaleZeroProjection_idempotent
#print axioms paperScaleZeroProjection_killsSingleton
#print axioms paperScaleZeroProjection_projectedZeroCommonSpan
#print axioms paperScaleZeroProjectionSocket

end PallLean.Paper93.DeepMath.PathC
