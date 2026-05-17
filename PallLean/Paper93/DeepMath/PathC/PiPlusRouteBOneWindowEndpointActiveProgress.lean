import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedLocalWindowAssembly
import PallLean.Paper93.DeepMath.PathB.ActiveProfileEndpointAugmentedProgress

/-!
# Endpoint-augmented one-window active-data progress

The nonzero Route-B side now asks for
`CookLevinOneWindowPerTypeSpanningActiveData`.  This file proves the first
field, `factor_derivatives`, for the endpoint-augmented concrete row family at
the enlarged one-window radius `log₂ n + 1`.

The remaining active field is the genuinely hard local shift/`mlProj` closure;
we package it separately below.  This keeps the frontier honest while removing
all H3/H4 derivative plumbing from the active blocker.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Wiring (concreteW)
open PallLean.Paper93.Spanning
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec

/-- Public local copy of the standard induction: one-step derivative closure
implies closure under an arbitrary iterated derivative list. -/
theorem iterDerivList_mem_of_pderiv_mem_public
    {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hstep :
      ∀ (τ : ConstraintType) (i : Fin n) {p : MvPolynomial (Fin n) ℚ},
        p ∈ W τ → MvPolynomial.pderiv (R := ℚ) i p ∈ W τ)
    (τ : ConstraintType) (S : List (Fin n))
    {p : MvPolynomial (Fin n) ℚ}
    (hp : p ∈ W τ) :
    iterDerivList S p ∈ W τ := by
  induction S generalizing p with
  | nil =>
      simpa [iterDerivList] using hp
  | cons i rest ih =>
      simpa [iterDerivList] using ih (hstep τ i hp)

/-- Generic one-window derivative-membership discharge from H3 plus unrestricted
one-step derivative closure of the selected per-type family. -/
theorem cookLevinFactorDerivativeMemPerTypeOneWindow_of_factorMem_pderiv
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hFactor : CookLevinFactorMemPerType M n hn htb hns W)
    (hstep :
      ∀ (τ : ConstraintType) (i : Fin n) {p : MvPolynomial (Fin n) ℚ},
        p ∈ W τ → MvPolynomial.pderiv (R := ℚ) i p ∈ W τ) :
    CookLevinFactorDerivativeMemPerTypeOneWindow M n hn htb hns W := by
  intro i d _hd
  exact iterDerivList_mem_of_pderiv_mem_public W hstep
    (cookLevinConstraintType M n hn htb hns i) d (hFactor i)

/-- Endpoint-augmented concreteW discharges one-window factor-derivative
membership once its H3 factor membership is available. -/
theorem cookLevinFactorDerivativeMemPerTypeOneWindow_endpointAugmentedConcreteW_of_factorMem
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (endpointAugmentedConcreteW n hn4)) :
    CookLevinFactorDerivativeMemPerTypeOneWindow M n hn htb hns
      (endpointAugmentedConcreteW n hn4) :=
  cookLevinFactorDerivativeMemPerTypeOneWindow_of_factorMem_pderiv
    M n hn htb hns (endpointAugmentedConcreteW n hn4) hFactor
    (fun τ i {p} hp =>
      endpointAugmentedConcreteW_pderiv_mem n hn4 τ i (p := p) hp)

/-- Direct branch-shape data plus canonical-row transport discharges the
one-window factor-derivative field for endpoint-augmented concreteW. -/
theorem cookLevinFactorDerivativeMemPerTypeOneWindow_endpointAugmentedConcreteW_of_directBranchShapes_transport
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hTransport :
      CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4) :
    CookLevinFactorDerivativeMemPerTypeOneWindow M n hn htb hns
      (endpointAugmentedConcreteW n hn4) :=
  cookLevinFactorDerivativeMemPerTypeOneWindow_endpointAugmentedConcreteW_of_factorMem
    M n hn htb hns hn4
    (CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_directBranchShapes_transport
      M n hn htb hns hn4 hShape hTransport)

/-- The remaining local active closure for endpoint-augmented concreteW.  This
is the nonzero Route-B mathematical payload after the derivative field above is
proved. -/
def EndpointAugmentedOneWindowActiveShiftMlprojClosure
    (n : ℕ) (hn4 : n ≥ 4) : Prop :=
  ∀ bp : ActiveAdmissibleProfile (Nat.log 2 n + 1),
    bp.toHistogram ≠ zeroProfileHistogram →
      PerTypeShiftMlprojClosureAtOneWindowBoundedProfile
        (endpointAugmentedConcreteW n hn4)
        bp.toActiveBoundedProfile.toBoundedProfile

/-- Endpoint-augmented concreteW active data from concrete Cook-Levin H3 shape
witnesses and the remaining active shift/`mlProj` closure. -/
theorem cookLevinOneWindowPerTypeSpanningActiveData_endpointAugmentedConcreteW
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hTransport :
      CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4)
    (hShift : EndpointAugmentedOneWindowActiveShiftMlprojClosure n hn4) :
    CookLevinOneWindowPerTypeSpanningActiveData M n hn htb hns
      (endpointAugmentedConcreteW n hn4) where
  factor_derivatives :=
    cookLevinFactorDerivativeMemPerTypeOneWindow_endpointAugmentedConcreteW_of_directBranchShapes_transport
      M n hn htb hns hn4 hShape hTransport
  shift_mlproj_active := hShift

/-- Paper-scale specialization of the endpoint-augmented active data. -/
theorem paperScale_cookLevinOneWindowPerTypeSpanningActiveData_endpointAugmentedConcreteW
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hShape : CookLevinDirectBranchShapeWitnesses
      M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four)
    (hTransport :
      CookLevinConcreteWCanonicalRowTransport
        M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four)
    (hShift : EndpointAugmentedOneWindowActiveShiftMlprojClosure
      (2 ^ 804) paperScale_two_pow_804_ge_four) :
    CookLevinOneWindowPerTypeSpanningActiveData
      M (2 ^ 804) paperScale_ge_two htb hns
      (endpointAugmentedConcreteW (2 ^ 804) paperScale_two_pow_804_ge_four) :=
  cookLevinOneWindowPerTypeSpanningActiveData_endpointAugmentedConcreteW
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four
    hShape hTransport hShift

/-! ## Axiom audit anchors -/

#print axioms iterDerivList_mem_of_pderiv_mem_public
#print axioms cookLevinFactorDerivativeMemPerTypeOneWindow_of_factorMem_pderiv
#print axioms cookLevinFactorDerivativeMemPerTypeOneWindow_endpointAugmentedConcreteW_of_factorMem
#print axioms cookLevinFactorDerivativeMemPerTypeOneWindow_endpointAugmentedConcreteW_of_directBranchShapes_transport
#print axioms cookLevinOneWindowPerTypeSpanningActiveData_endpointAugmentedConcreteW
#print axioms paperScale_cookLevinOneWindowPerTypeSpanningActiveData_endpointAugmentedConcreteW

end PallLean.Paper93.DeepMath.PathC
