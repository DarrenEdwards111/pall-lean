import PallLean.Paper93.DeepMath.PathC.RouteBRouteCBridge

/-!
# Pi+ admissibility layer for the Route B/C bridge

This file starts the concrete Level-2 bridge attack in the smallest useful
slice: before proving that `Pi+` minimizes the N-frame/log-det Lagrangian, name
and package the exact admissibility/unit-preservation facts that such a proof
must use.

The key point is methodological: `Pi+` is an invertible block-local
Hadamard/Fourier transform, not a quotient.  Therefore the first bridge target
is an admissible *change of basis* with unit preservation and SPDP rank
invariance.  Once a future file proves the variational minimizer realization,
this package fills `PiPlusGaugeMinimizesNFrameLagrangian`, and hence the full
Route B ↔ Route C witness bridge.
-/

namespace PallLean.Paper93.DeepMath.PathC

open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open MultilinearSPDP

attribute [local instance] Classical.dec

/-- Unit preservation for a SAT-polynomial `Pi+` transform: the constant
polynomial is fixed.  This is intentionally separate from linear invertibility;
a linear equivalence need not preserve `1` unless it is the intended
polynomial-basis transform. -/
def PiPlusUnitPreserving
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  piP.gauge (1 : SATDeciderGaugeSpace M n hn2 htb hns) = 1

/-- Concrete admissibility package for the constructive `Pi+` side before the
variational minimizer proof.

This packages exactly the low-level facts we expect from the block-local
Hadamard/Fourier construction:

* block-local lift;
* unit preservation;
* trivial kernel/invertibility;
* SPDP rank invariance;
* the two final SAT-gauge fields used by Route C.
-/
structure PiPlusNFrameAdmissible
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop where
  block_local : piP.block_local_hadamard_lift
  unit_preserving : PiPlusUnitPreserving M n hn2 htb hns piP
  rank_invariant : PiPlusRankInvariant M n hn2 htb hns piP
  width_rank_p_side : PiPlusWidthRankPSide M n hn2 htb hns piP
  identity_minor_preservation : PiPlusIdentityMinorPreservation M n hn2 htb hns piP

/-- Admissibility includes the already-proved invertibility/trivial-kernel fact
for `Pi+`. -/
theorem piPlus_ker_eq_bot_of_admissible
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (_hadm : PiPlusNFrameAdmissible M n hn2 htb hns piP) :
    LinearMap.ker piP.gauge = ⊥ :=
  PiPlusSATTransform.gauge_ker_eq_bot piP

/-- Admissibility gives the rank-monotonicity field required by the global SAT
gauge socket. -/
theorem piPlus_rankMonotonicity_of_admissible
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hadm : PiPlusNFrameAdmissible M n hn2 htb hns piP) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns piP.gauge :=
  piPlus_rankMonotonicity_of_rankInvariant M n hn2 htb hns piP
    hadm.rank_invariant

/-- Admissibility is already enough to produce the Route-C constructive data for
this SAT-decider instance. -/
theorem piPlusConstructiveData_of_admissible
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hadm : PiPlusNFrameAdmissible M n hn2 htb hns piP) :
    PiPlusConstructiveSATGaugeData M n hn2 htb hns :=
  ⟨piP, hadm.block_local, hadm.rank_invariant,
    hadm.width_rank_p_side, hadm.identity_minor_preservation⟩

/-- Admissibility gives the explicit SAT-gauge subgoals directly. -/
theorem satDeciderGaugeSubgoals_of_piPlusAdmissible
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hadm : PiPlusNFrameAdmissible M n hn2 htb hns piP) :
    SATDeciderGaugeSubgoals M n hn2 htb hns piP.gauge :=
  ⟨piPlus_rankMonotonicity_of_admissible M n hn2 htb hns piP hadm,
    hadm.width_rank_p_side,
    hadm.identity_minor_preservation⟩

/-! ## Variational realization layer -/

/-- The still-open variational realization data after admissibility is known.

This is now the exact next mathematical target: prove that the admissible
constructive `Pi+` transform is realized by a Route-B log-det/N-frame minimizer
and induces the same SAT gauge. -/
structure PiPlusNFrameMinimizerRealization
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) where
  alpha : ℝ
  beta : ℝ
  lambdaCoeff : ℝ
  E : Finset (Fin n × Fin n)
  chi : Fin n → ℤ
  phi : Fin n → ℝ
  𝒥 : Finset (Finset (Fin n))
  AdmissibleMatrix : Matrix (Fin n) (Fin n) ℝ → Prop
  Astar : Matrix (Fin n) (Fin n) ℝ
  minimizer :
    IsLogDetNFrameMinimizer alpha beta lambdaCoeff E chi phi 𝒥
      AdmissibleMatrix Astar
  realizes_piPlus_gauge :
    MatrixGaugeRealizesSATGauge M n hn hn2 htb hns Astar 𝒥 piP.gauge

/-- Admissibility plus minimizer realization fills the named Level-2 bridge
`PiPlusGaugeMinimizesNFrameLagrangian`. -/
def piPlusGaugeMinimizesNFrameLagrangian_of_admissible_realization
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (_hadm : PiPlusNFrameAdmissible M n hn2 htb hns piP)
    (hreal : PiPlusNFrameMinimizerRealization M n hn hn2 htb hns piP) :
    PiPlusGaugeMinimizesNFrameLagrangian M n hn hn2 htb hns piP :=
  { alpha := hreal.alpha
    beta := hreal.beta
    lambdaCoeff := hreal.lambdaCoeff
    E := hreal.E
    chi := hreal.chi
    phi := hreal.phi
    𝒥 := hreal.𝒥
    Admissible := hreal.AdmissibleMatrix
    Astar := hreal.Astar
    minimizer := hreal.minimizer
    realizes_piPlus_gauge := hreal.realizes_piPlus_gauge }

/-- Admissibility plus minimizer realization gives the full witness-level B/C
bridge data. -/
def logDetBridgeData_of_admissible_realization
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hadm : PiPlusNFrameAdmissible M n hn2 htb hns piP)
    (hreal : PiPlusNFrameMinimizerRealization M n hn hn2 htb hns piP) :
    PiPlusLogDetMinimizerBridgeData M n hn hn2 htb hns :=
  logDetBridgeData_of_piPlusGauge_minimizes_nframeLagrangian
    M n hn hn2 htb hns piP
    hadm.block_local
    hadm.rank_invariant
    hadm.width_rank_p_side
    hadm.identity_minor_preservation
    (piPlusGaugeMinimizesNFrameLagrangian_of_admissible_realization
      M n hn hn2 htb hns piP hadm hreal)

/-- One instance of admissible-and-realized `Pi+` data.  This is a `Type`
(rather than a `Prop`) because it carries the actual transform witness. -/
structure PiPlusAdmissibleRealizedInstance
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  piP : PiPlusSATTransform M n hn2 htb hns
  admissible : PiPlusNFrameAdmissible M n hn2 htb hns piP
  realized : PiPlusNFrameMinimizerRealization M n hn hn2 htb hns piP

/-- Uniform admissibility plus uniform minimizer realization closes both routes
through the existing witness bridge. -/
def Step247UniformPiPlusAdmissibleAndRealized : Type :=
  ∀ (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    PiPlusAdmissibleRealizedInstance M n hn hn2 htb hns

/-- Uniform admissibility+realization inhabits the previous uniform witness
bridge surface. -/
theorem uniformLogDetMinimizerBridge_of_admissible_realized
    (h : Step247UniformPiPlusAdmissibleAndRealized) :
    Step247UniformPiPlusLogDetMinimizerBridgeData := by
  intro M n hn hn2 htb hns hdec
  let inst := h M n hn hn2 htb hns hdec
  exact ⟨logDetBridgeData_of_admissible_realization
    M n hn hn2 htb hns inst.piP inst.admissible inst.realized⟩

/-- Therefore the new admissibility+realization target is enough to obtain the
B/C route equivalence closeout. -/
theorem routeB_routeC_equivalence_of_admissible_realized
    (h : Step247UniformPiPlusAdmissibleAndRealized) :
    RouteBVariationalClosure ∧ RouteCFinalSocketClosure ∧
      (RouteBVariationalClosure ↔ RouteCFinalSocketClosure) :=
  routeB_routeC_equivalence_of_logDetMinimizerBridge
    (uniformLogDetMinimizerBridge_of_admissible_realized h)

/-! ## Axiom audit anchors -/

#print axioms piPlus_ker_eq_bot_of_admissible
#print axioms piPlus_rankMonotonicity_of_admissible
#print axioms piPlusConstructiveData_of_admissible
#print axioms satDeciderGaugeSubgoals_of_piPlusAdmissible
#print axioms piPlusGaugeMinimizesNFrameLagrangian_of_admissible_realization
#print axioms logDetBridgeData_of_admissible_realization
#print axioms uniformLogDetMinimizerBridge_of_admissible_realized
#print axioms routeB_routeC_equivalence_of_admissible_realized

end PallLean.Paper93.DeepMath.PathC
