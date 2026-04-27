import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteMultilinearResidual

/-!
# Projection-descent progress for the concrete multilinear tail

This file records the current Route B projection frontier for the concrete
multilinear-tail finite-row projection.

The broad multilinear tail makes every SPDP generator row a selected finite-row
output.  Consequently the paper-faithful projection-descent condition is
equivalent to the stronger-looking residual-generator-zero condition, and to
annihilation of every admissible generator on the arbitrary projection kernel.
The theorems below expose that equivalence directly at the projection-escape
surface, without adding an axiom or asserting the condition.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- For the concrete multilinear-tail finite-row projection, descent is
equivalent to generator annihilation on the projection kernel.

This is the kernel-form obstruction behind the residual-generator-zero
condition: the broad tail makes projected generator rows fixed, so all remaining
work is exactly the generator action on the arbitrary complement selected as
the kernel of the finite-row projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_kernelGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
        M n hn2 htb hns ↔
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns := by
  rw [
    routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_residualGenerator_zero,
    routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_iff_kernelGenerator_zero]

/-- Projection escape for the concrete multilinear-tail projection is exactly
failure of residual-generator-zero. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_residualGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns ↔
      ¬ RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
        M n hn2 htb hns := by
  calc
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns
        ↔ ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
          M n hn2 htb hns :=
      routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_projectionDescent
        M n hn2 htb hns
    _ ↔ ¬ RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
          M n hn2 htb hns :=
      not_congr
        (routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_residualGenerator_zero
          M n hn2 htb hns)

/-- Projection escape for the concrete multilinear-tail projection is exactly
failure of kernel-generator annihilation on the selected projection kernel. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_kernelGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns ↔
      ¬ RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns := by
  calc
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns
        ↔ ¬ RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
          M n hn2 htb hns :=
      routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_residualGenerator_zero
        M n hn2 htb hns
    _ ↔ ¬ RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
          M n hn2 htb hns :=
      not_congr
        (routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_iff_kernelGenerator_zero
          M n hn2 htb hns)

/-- Absence of concrete projection escape is exactly residual-generator-zero.

Thus the escape-free branch does not avoid the residual obstruction; for the
broad multilinear tail it is the same theorem. -/
theorem routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_residualGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns) ↔
      RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
        M n hn2 htb hns := by
  calc
    (¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns)
        ↔ RouteBRicherConcreteNPPrependedMultilinearProjectionDescent
          M n hn2 htb hns :=
      (routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_no_projectionEscapeWitness
        M n hn2 htb hns).symm
    _ ↔ RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
          M n hn2 htb hns :=
      routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_residualGenerator_zero
        M n hn2 htb hns

/-- Absence of concrete projection escape is exactly kernel-generator
annihilation on the selected projection kernel. -/
theorem routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_kernelGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    (¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns) ↔
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns := by
  calc
    (¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns)
        ↔ RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
          M n hn2 htb hns :=
      routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_residualGenerator_zero
        M n hn2 htb hns
    _ ↔ RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
          M n hn2 htb hns :=
      routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_iff_kernelGenerator_zero
        M n hn2 htb hns

/-- A kernel vector with nonzero multilinear part gives a concrete projection
escape witness.  This upgrades the residual no-go criterion to the actual
projection-descent frontier. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_kernel_mlProj_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      exists p : SATDeciderGaugeSpace M n hn2 htb hns,
        routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p = 0 ∧ mlProj p ≠ 0) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
      M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_residualGenerator_zero
    M n hn2 htb hns).mpr
    (routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_noGo_of_kernel_mlProj_ne_zero
      M n hn2 htb hns hbad)

/-- If the selected projection changes the multilinear part of some
polynomial, then the concrete multilinear-tail projection has an escape
witness. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_mlProj_projection_ne
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      exists p : SATDeciderGaugeSpace M n hn2 htb hns,
        mlProj
            (routeBRicherConcreteNPPrependedMultilinearProjection
              M n hn2 htb hns p) ≠
          mlProj p) :
    RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
      M n hn2 htb hns :=
  (routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_residualGenerator_zero
    M n hn2 htb hns).mpr
    (routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_noGo_of_mlProj_projection_ne
      M n hn2 htb hns hbad)

/-- If there is no concrete projection escape, the selected projection must
preserve the canonical multilinear part of every polynomial. -/
theorem routeBRicherConcreteNPPrependedMultilinear_mlProj_projection_eq_of_no_projectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    mlProj
        (routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p) =
      mlProj p :=
  routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_implies_mlProj_projection_eq
    M n hn2 htb hns
    ((routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_residualGenerator_zero
      M n hn2 htb hns).mp hno)
    p

/-- If there is no concrete projection escape, the kernel of the selected
projection must be contained in the kernel of `mlProj`. -/
theorem routeBRicherConcreteNPPrependedMultilinear_kernel_mlProj_zero_of_no_projectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness
        M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (hker :
      routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns p = 0) :
    mlProj p = 0 :=
  routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_implies_kernel_mlProj_zero
    M n hn2 htb hns
    ((routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_residualGenerator_zero
      M n hn2 htb hns).mp hno)
    p hker

/-! ## Axiom audit anchors -/

#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionDescent_iff_kernelGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_residualGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_iff_not_kernelGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_residualGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinear_no_projectionEscapeWitness_iff_kernelGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_kernel_mlProj_ne_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearProjectionEscapeWitness_of_mlProj_projection_ne
#print axioms routeBRicherConcreteNPPrependedMultilinear_mlProj_projection_eq_of_no_projectionEscapeWitness
#print axioms routeBRicherConcreteNPPrependedMultilinear_kernel_mlProj_zero_of_no_projectionEscapeWitness

end PallLean.Paper93.Paper283
