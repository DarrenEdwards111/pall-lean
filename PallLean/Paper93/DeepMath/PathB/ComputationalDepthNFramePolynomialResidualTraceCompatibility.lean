import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameInputBlindResidualTraceBarrier

/-!
# The residual information threshold is polynomially compatible

After copied input is discounted, a separated four-label cell requires an
`m`-bit residual.  That is an exact information lower bound, but it is only
linear in the continuation length.  It therefore does not by itself
contradict a polynomial trace or time budget.

This file proves the compatibility explicitly.  For every positive
continuation length `m`, every positive polynomial exponent `d`, every alleged
solver, and every redundant continuation code, choose the residual trace to
be the complete `m`-bit continuation label.  Its length is exactly `m`, hence
at most `m^d`; it is injective; the identity semantic cell factors through it
via an input-blind decoder; and it satisfies the radius-one four-label law.

Thus the preceding threshold can rule out sublinear residual information, but
not polynomial-time computation.  A genuine lower-bound route needs a
superpolynomial requirement on solver-generated residual structure, or a
separate theorem converting semantic preservation into superpolynomial work.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFramePolynomialResidualTraceCompatibility

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier

/-! ## Linear residuals fit every positive polynomial budget -/

/-- For positive `m` and positive exponent `d`, the linear residual length
`m` fits inside the polynomial bit budget `m^d`. -/
theorem linear_le_polynomial_budget
    {m d : Nat} (hm : 1 <= m) (hd : 1 <= d) :
    m <= m ^ d := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  rw [pow_succ]
  have hpow : 1 <= m ^ e := Nat.one_le_pow e m hm
  nlinarith

/-- The full-label residual admits an input-blind factorization of the
identity semantic cell. -/
theorem fullLabelCell_inputBlind_factorization (m : Nat) :
    CellMapFactorsThroughInputBlindResidual
      (fullLabelTrace m) (id : Assignment m -> Assignment m) := by
  apply (inputBlindResidual_iff_residual_factorization
    (fullLabelTrace m) (id : Assignment m -> Assignment m)).mpr
  exact fullLabelCell_factorsThrough_fullLabelTrace m

/-- Complete compatibility package: the exact threshold witness has
polynomial length, is injective, factors input-blindly, and satisfies the
four-label law for every code. -/
theorem exists_polynomialResidual_fourwise_package
    {m N d : Nat} (hm : 1 <= m) (hd : 1 <= d)
    (C : RedundantContinuationCode m N) :
    ∃ k : Nat, ∃ residual : Assignment m -> Assignment k,
      k <= m ^ d ∧
      Function.Injective residual ∧
      CellMapFactorsThroughInputBlindResidual residual
        (id : Assignment m -> Assignment m) ∧
      CellFourwiseRadiusCompatible C
        (id : Assignment m -> Assignment m) (R := 1) := by
  refine ⟨m, fullLabelTrace m,
    linear_le_polynomial_budget hm hd,
    fullLabelCell_injective m,
    fullLabelCell_inputBlind_factorization m, ?_⟩
  exact fullLabelCell_fourwise C

/-! ## Solver correctness adds nothing to this compatibility -/

/-- The polynomial residual package exists for every alleged solver; SAT
correctness is not used. -/
theorem correctnessForces_polynomialResidual_fourwise_package
    {U : MachineModel} (D : DecisionMachine U)
    {m N d : Nat} (hm : 1 <= m) (hd : 1 <= d)
    (C : RedundantContinuationCode m N) :
    DecidesSAT U D ->
      ∃ k : Nat, ∃ residual : Assignment m -> Assignment k,
        k <= m ^ d ∧
        Function.Injective residual ∧
        CellMapFactorsThroughInputBlindResidual residual
          (id : Assignment m -> Assignment m) ∧
        CellFourwiseRadiusCompatible C
          (id : Assignment m -> Assignment m) (R := 1) := by
  intro _
  exact exists_polynomialResidual_fourwise_package hm hd C

/-- Hence no universal theorem can rule out all polynomially bounded,
input-blind, fourwise residual packages: the full-label residual is an
explicit counterexample for every code. -/
theorem no_universal_polynomialResidual_obstruction
    {m N d : Nat} (hm : 1 <= m) (hd : 1 <= d)
    (C : RedundantContinuationCode m N) :
    ¬ (∀ k : Nat, ∀ residual : Assignment m -> Assignment k,
      k <= m ^ d ->
      CellMapFactorsThroughInputBlindResidual residual
        (id : Assignment m -> Assignment m) ->
      ¬ CellFourwiseRadiusCompatible C
        (id : Assignment m -> Assignment m) (R := 1)) := by
  intro hobstruct
  have hnot := hobstruct m (fullLabelTrace m)
    (linear_le_polynomial_budget hm hd)
    (fullLabelCell_inputBlind_factorization m)
  exact hnot (fullLabelCell_fourwise C)

end PallLean.Paper93.DeepMath.PathB.NFramePolynomialResidualTraceCompatibility

#print axioms PallLean.Paper93.DeepMath.PathB.NFramePolynomialResidualTraceCompatibility.linear_le_polynomial_budget
#print axioms PallLean.Paper93.DeepMath.PathB.NFramePolynomialResidualTraceCompatibility.fullLabelCell_inputBlind_factorization
#print axioms PallLean.Paper93.DeepMath.PathB.NFramePolynomialResidualTraceCompatibility.exists_polynomialResidual_fourwise_package
#print axioms PallLean.Paper93.DeepMath.PathB.NFramePolynomialResidualTraceCompatibility.correctnessForces_polynomialResidual_fourwise_package
#print axioms PallLean.Paper93.DeepMath.PathB.NFramePolynomialResidualTraceCompatibility.no_universal_polynomialResidual_obstruction
