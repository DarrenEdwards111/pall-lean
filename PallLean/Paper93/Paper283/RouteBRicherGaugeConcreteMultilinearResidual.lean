import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteMultilinearTail
import PallLean.IterDerivHelpers

/-!
# Residual obstruction for the concrete multilinear-tail gauge

The concrete multilinear tail makes every Route B SPDP generator row land in
the selected finite row span.  Consequently the kernel-compatibility route is
not a free containment proof: it asks the whole projection-kernel residual to
be annihilated by every SPDP generator operator.

This file records that obstruction in kernel form and exposes two immediate
counterconditions for the current finite-row projection.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The residual-generator annihilation condition exposed by the concrete
multilinear-tail kernel-compatibility equivalence. -/
def RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBSPDPGeneratorRow M n hn2 htb hns
      (p -
        routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p)
      S shift = 0

/-- Kernel form of the same residual target: every SPDP generator operator
must vanish on every vector in the selected projection's kernel. -/
def RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBRicherConcreteNPPrependedMultilinearProjection
      M n hn2 htb hns p = 0 ->
    routeBSPDPGeneratorRow M n hn2 htb hns p S shift = 0

/-- The residual target is exactly the kernel-generator vanishing condition.

This is the checked form of the obstruction: closing residual annihilation for
the current finite-row projection is equivalent to proving that every vector
in its kernel has all Route B SPDP generator rows equal to zero. -/
theorem routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_iff_kernelGenerator_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
        M n hn2 htb hns ↔
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
        M n hn2 htb hns := by
  constructor
  · intro hzero spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm hker
    have hrow :=
      hzero spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
    simpa [hker] using hrow
  · intro hker spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
    let Pi :=
      routeBRicherConcreteNPPrependedMultilinearProjection M n hn2 htb hns
    have hPiPi : Pi (Pi p) = Pi p := by
      have hidem :=
        (routeBRicherConcreteNPPrependedMultilinearGauge
          M n hn2 htb hns).is_idempotent
      have happ := congrArg (fun L => L p) hidem
      simpa [Pi, routeBRicherConcreteNPPrependedMultilinearProjection,
        LinearMap.comp_apply] using happ
    have hresKer : Pi (p - Pi p) = 0 := by
      simp [Pi, map_sub, hPiPi]
    exact
      hker spdpKappa ell (p - Pi p) S shift
        hSlen hshiftDegree hshiftVars hadm hresKer

/-- Residual annihilation forces the selected projection to preserve the
canonical multilinear part of every polynomial. -/
theorem routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_implies_mlProj_projection_eq
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero :
      RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
        M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    mlProj
        (routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p) =
      mlProj p := by
  let Pi :=
    routeBRicherConcreteNPPrependedMultilinearProjection M n hn2 htb hns
  let L :=
    MultilinearSPDP.mlProjLinearMap
      (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat
  have hres : L (p - Pi p) = 0 := by
    have hrow :=
      hzero 0 0 p ([] : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (1 : SATDeciderGaugeSpace M n hn2 htb hns)
        (by simp) (by simp [MvPolynomial.totalDegree_one])
        (by simp [MvPolynomial.vars_one]) (by simp [SPDP.isBlockAdmissible])
    change mlProj (p - Pi p) = 0
    simpa [Pi, routeBSPDPGeneratorRow] using hrow
  have hsub : L p - L (Pi p) = 0 := by
    simpa [map_sub] using hres
  have heq : L p = L (Pi p) := sub_eq_zero.mp hsub
  simpa [L, Pi] using heq.symm

/-- In particular, residual annihilation forces the projection kernel to lie
inside the kernel of the canonical multilinear projection. -/
theorem routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_implies_kernel_mlProj_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero :
      RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
        M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (hker :
      routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns p = 0) :
    mlProj p = 0 := by
  have hkernel :=
    (routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_iff_kernelGenerator_zero
      M n hn2 htb hns).mp hzero
  have hrow :=
    hkernel 0 0 p ([] : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (1 : SATDeciderGaugeSpace M n hn2 htb hns)
      (by simp) (by simp [MvPolynomial.totalDegree_one])
      (by simp [MvPolynomial.vars_one]) (by simp [SPDP.isBlockAdmissible])
      hker
  simpa [routeBSPDPGeneratorRow] using hrow

/-- No-go criterion: a single projection-kernel vector with nonzero
multilinear part refutes residual-generator annihilation. -/
theorem routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_noGo_of_kernel_mlProj_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      exists p : SATDeciderGaugeSpace M n hn2 htb hns,
        routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p = 0 ∧ mlProj p ≠ 0) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
        M n hn2 htb hns := by
  rintro hzero
  rcases hbad with ⟨p, hker, hml⟩
  exact hml
    (routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_implies_kernel_mlProj_zero
      M n hn2 htb hns hzero p hker)

/-- No-go criterion: any polynomial whose multilinear part changes under the
selected finite-row projection refutes residual-generator annihilation. -/
theorem routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_noGo_of_mlProj_projection_ne
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      exists p : SATDeciderGaugeSpace M n hn2 htb hns,
        mlProj
            (routeBRicherConcreteNPPrependedMultilinearProjection
              M n hn2 htb hns p) ≠
          mlProj p) :
    ¬ RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
        M n hn2 htb hns := by
  rintro hzero
  rcases hbad with ⟨p, hbad⟩
  exact hbad
    (routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_implies_mlProj_projection_eq
      M n hn2 htb hns hzero p)

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherConcreteNPPrependedMultilinearResidualGeneratorZero
#print axioms RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZero
#print axioms routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_iff_kernelGenerator_zero
#print axioms routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_implies_mlProj_projection_eq
#print axioms routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_implies_kernel_mlProj_zero
#print axioms routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_noGo_of_kernel_mlProj_ne_zero
#print axioms routeBRicherConcreteNPPrependedMultilinear_residualGenerator_zero_noGo_of_mlProj_projection_ne

end PallLean.Paper93.Paper283
