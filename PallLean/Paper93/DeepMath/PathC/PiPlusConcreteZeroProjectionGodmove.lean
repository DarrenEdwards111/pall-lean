import PallLean.Paper93.DeepMath.PathC.PiPlusRowPreservationSpanCriterion

/-!
# Concrete zero-projection godmove

The hard-coded singleton quotient projection uses an arbitrary
`Classical.choose` complement.  That is too opaque to prove unconditional
containment of its image in the concrete zero-profile `concreteW` chart.

This file takes the replacement route: use an explicit concrete projection with
known image.  The zero projection is idempotent, kills all singleton-shift rows,
and every projected zero-profile row is `0`, hence lands unconditionally in the
canonical zero-profile `concreteW` chart.

This does **not** claim the old chosen-complement projection has this property;
it supplies the concrete projected replacement requested by the corrected Route-C
socket.
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

/-- The explicit concrete replacement projection: project every row to zero. -/
noncomputable def zeroProfileConcreteZeroProjection (n : ℕ) :
    MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ :=
  0

@[simp] theorem zeroProfileConcreteZeroProjection_apply
    {n : ℕ} (q : MvPolynomial (Fin n) ℚ) :
    zeroProfileConcreteZeroProjection n q = 0 := rfl

/-- The concrete zero projection is idempotent. -/
theorem zeroProfileConcreteZeroProjection_idempotent (n : ℕ) :
    (zeroProfileConcreteZeroProjection n).comp
        (zeroProfileConcreteZeroProjection n) =
      zeroProfileConcreteZeroProjection n := by
  ext q
  simp [zeroProfileConcreteZeroProjection]

/-- The concrete zero projection kills singleton-shift rows. -/
theorem zeroProfileConcreteZeroProjection_killsSingletonShifts
    {n L : ℕ} (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    ZeroProfileProjectionKillsSingletonShifts factors
      (zeroProfileConcreteZeroProjection n) := by
  intro i
  simp [zeroProfileConcreteZeroProjection]

/-- Every concrete-zero-projected one-window zero-profile row lies in the
canonical zero-profile `concreteW` chart. -/
theorem cookLevinOneWindowConcreteZeroProjectionConcreteWRowPreservation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) :
    ∀ (S : List (Fin n)), S.length ≤ Nat.log 2 n + 1 →
      ∀ shift : MvPolynomial (Fin n) ℚ, shift.vars ⊆ S.toFinset →
        zeroProfileConcreteZeroProjection n
            (mlProj (shift *
              Finset.univ.prod
                (fun i => (cookLevinFactorList M n hn htb hns).get i))) ∈
          profileSubspace zeroProfileHistogram (concreteWCanonical n hn4) := by
  intro S hS shift hshift
  simp [zeroProfileConcreteZeroProjection]

/-- Concrete zero-projection row map into the singleton zero-profile
`concreteW` chart at the enlarged one-window radius. -/
noncomputable def cookLevinOneWindowConcreteZeroProjectionRowMap
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) :
    ZeroProfileConcreteNormalFormRowMap
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (zeroProfileConcreteZeroProjection n)
      (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
        (κ := Nat.log 2 n + 1) hn4) where
  rowNormalForm := fun _ _ _ _ => PUnit.unit
  projected_row_mem_profileSubspace := by
    intro S hS shift hshift
    have hmem :=
      cookLevinOneWindowConcreteZeroProjectionConcreteWRowPreservation
        M n hn htb hns hn4 S hS shift hshift
    simpa [zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW,
      zeroProfileConcreteNormalFormData_singletonZeroProfile,
      zeroProfileConcreteLocalChart_concreteW,
      zeroProfileConcreteLocalChart_of_submoduleFamily,
      concreteWCanonical] using hmem

/-- Concrete zero-projection common-span/type-budget closeout. -/
theorem zeroProfileProjectedCommonSpanWithBudget_concreteZeroProjection_oneWindow
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) :
    ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n + 1)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (zeroProfileConcreteZeroProjection n)
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  zeroProfileProjectedCommonSpanWithBudget_of_concreteRowMap
    (κ := Nat.log 2 n + 1)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (zeroProfileConcreteZeroProjection n)
    (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
      (κ := Nat.log 2 n + 1) hn4)
    (cookLevinOneWindowConcreteZeroProjectionRowMap
      M n hn htb hns hn4)

/-- Paper-scale concrete zero-projection row map. -/
noncomputable def paperScale_cookLevinOneWindowConcreteZeroProjectionRowMap
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    ZeroProfileConcreteNormalFormRowMap
      (fun i => (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
      (zeroProfileConcreteZeroProjection (2 ^ 804))
      (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
        (κ := Nat.log 2 (2 ^ 804) + 1) paperScale_two_pow_804_ge_four) :=
  cookLevinOneWindowConcreteZeroProjectionRowMap
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four

/-! ## Axiom audit anchors -/

#print axioms zeroProfileConcreteZeroProjection_idempotent
#print axioms zeroProfileConcreteZeroProjection_killsSingletonShifts
#print axioms cookLevinOneWindowConcreteZeroProjectionConcreteWRowPreservation
#print axioms cookLevinOneWindowConcreteZeroProjectionRowMap
#print axioms zeroProfileProjectedCommonSpanWithBudget_concreteZeroProjection_oneWindow
#print axioms paperScale_cookLevinOneWindowConcreteZeroProjectionRowMap

end PallLean.Paper93.DeepMath.PathC
