import PallLean.Paper93.DeepMath.PathC.PiPlusConstructive
import PallLean.Paper93.DeepMath.PathB.GodMoveLift

/-!
# Route B ↔ Route C bridge equivalence

This file connects the two parallel closures without deleting either route.

* **Route B** remains the variational / N-frame / log-det / amplituhedron
  compressor surface.
* **Route C** remains the constructive `Pi+` / block-local Hadamard-Fourier /
  Width⇒Rank surface.

There are two layers here:

1. A **final-socket equivalence**: once both routes are expressed as ways to
   discharge the same SAT-decider gauge socket, the two closure propositions are
   equivalent.  This is useful API/plumbing, but it is not a new proof of the
   missing mathematics.
2. A **witness bridge surface**: the nontrivial theorem we actually want next,
   namely that the constructive `Pi+` transform is the same object as the
   log-det/N-frame minimizer and realizes the same SAT gauge.  Inhabiting this
   bridge would make Route B and Route C converge at witness level.
-/

namespace PallLean.Paper93.DeepMath.PathC

open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open MultilinearSPDP

attribute [local instance] Classical.dec

/-! ## Level 3 final-socket equivalence -/

/-- Route B closure surface: the variational/N-frame/log-det construction
produces the global God-Move compressor for SAT deciders. -/
abbrev RouteBVariationalClosure : Prop :=
  VariationalGodMoveCompressorForSatDeciders

/-- Route C closure surface at the shared final socket: construct, for every
paper-scale bounded SAT decider, a SAT gauge satisfying rank monotonicity,
P-side Width⇒Rank, and NP identity-minor preservation.

`Step247UniformPiPlusConstructiveData` is a stronger, explicitly `Pi+`-shaped
way to inhabit this socket. -/
abbrev RouteCFinalSocketClosure : Prop :=
  SATDeciderSpecificGaugeSubgoalDischarge

/-- Explicit uniform `Pi+` constructive data discharges the Route C final
socket. -/
theorem routeCFinalSocketClosure_of_uniformPiPlus
    (hPi : Step247UniformPiPlusConstructiveData) :
    RouteCFinalSocketClosure :=
  satDeciderSpecificGaugeSubgoalDischarge_of_uniformPiPlus hPi

/-- Route C's final socket gives the Route B variational closure surface,
because both are just presentations of the same global God-Move gauge frontier. -/
theorem routeBVariationalClosure_of_routeCFinalSocketClosure
    (hC : RouteCFinalSocketClosure) :
    RouteBVariationalClosure := by
  refine ⟨?_, ?_⟩
  · intro M n hn hn2 htb hns hdec
    trivial
  · exact globalAmplituhedronGaugeForSatDeciders_iff_subgoals.mpr hC

/-- Route B's variational closure gives Route C's final socket by splitting the
bundled global God-Move gauge into the three explicit SAT-gauge fields. -/
theorem routeCFinalSocketClosure_of_routeBVariationalClosure
    (hB : RouteBVariationalClosure) :
    RouteCFinalSocketClosure :=
  globalAmplituhedronGaugeForSatDeciders_iff_subgoals.mp hB.to_godMoveGauge

/-- Final-socket bridge equivalence: at the current logical boundary, Route B
and Route C close the same proposition once both are expressed as SAT-decider
God-Move gauge discharge. -/
theorem routeB_routeC_finalSocket_equivalence :
    RouteBVariationalClosure ↔ RouteCFinalSocketClosure := by
  constructor
  · exact routeCFinalSocketClosure_of_routeBVariationalClosure
  · exact routeBVariationalClosure_of_routeCFinalSocketClosure

/-- Stronger usable direction: explicit uniform `Pi+` data closes the Route B
variational compressor surface as well, via the shared final socket. -/
theorem routeBVariationalClosure_of_uniformPiPlus
    (hPi : Step247UniformPiPlusConstructiveData) :
    RouteBVariationalClosure :=
  routeBVariationalClosure_of_routeCFinalSocketClosure
    (routeCFinalSocketClosure_of_uniformPiPlus hPi)

/-! ## Level 2 witness bridge surface -/

/-- `Pi+` as a log-det/N-frame minimizer for one SAT-decider instance.

This is the named Level-2 bridge target: the constructive `Pi+` polynomial
transform is not merely another route to the final socket; it is realized by the
same matrix object selected by the Route-B variational problem.  The additional
`realizes_piPlus_gauge` field is the concrete matrix-to-polynomial identification
needed to transfer properties in both directions. -/
structure PiPlusGaugeMinimizesNFrameLagrangian
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
  Admissible : Matrix (Fin n) (Fin n) ℝ → Prop
  Astar : Matrix (Fin n) (Fin n) ℝ
  minimizer :
    IsLogDetNFrameMinimizer alpha beta lambdaCoeff E chi phi 𝒥 Admissible Astar
  realizes_piPlus_gauge :
    MatrixGaugeRealizesSATGauge M n hn hn2 htb hns Astar 𝒥 piP.gauge

/-- The Level-2 bridge immediately identifies `Pi+` with a Route-B minimizer. -/
theorem piPlusGauge_minimizes_nframeLagrangian
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (h : PiPlusGaugeMinimizesNFrameLagrangian M n hn hn2 htb hns piP) :
    IsLogDetNFrameMinimizer h.alpha h.beta h.lambdaCoeff h.E h.chi h.phi
      h.𝒥 h.Admissible h.Astar :=
  h.minimizer

/-- A Level-2 bridge transfers the Route-B minimizer realization into the Route-C
SAT-gauge subgoals for the same constructive `Pi+` map. -/
theorem satDeciderGaugeSubgoals_of_piPlusGauge_minimizes_nframeLagrangian
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (h : PiPlusGaugeMinimizesNFrameLagrangian M n hn hn2 htb hns piP) :
    SATDeciderGaugeSubgoals M n hn2 htb hns piP.gauge :=
  satDeciderGaugeSubgoals_of_matrixGaugeRealizesSATGauge
    M n hn hn2 htb hns h.Astar h.𝒥 piP.gauge h.realizes_piPlus_gauge

/-- Witness-level bridge data for one SAT-decider instance.

This is the nontrivial convergence theorem we want next: the constructive
`Pi+` transform is simultaneously

* a block-local Hadamard/Fourier SAT-polynomial transform with the Route C
  rank/P-side/NP-side fields; and
* the polynomial gauge realized by a log-det N-frame minimizer from Route B.

Unlike the final-socket equivalence above, inhabiting this structure would be
real mathematical progress: it identifies the Route B minimizer and the Route C
constructive `Pi+` witness as the same SAT gauge. -/
structure PiPlusLogDetMinimizerBridgeData
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  piP : PiPlusSATTransform M n hn2 htb hns
  block_local : piP.block_local_hadamard_lift
  rank_invariant : PiPlusRankInvariant M n hn2 htb hns piP
  width_rank_p_side : PiPlusWidthRankPSide M n hn2 htb hns piP
  identity_minor_preservation : PiPlusIdentityMinorPreservation M n hn2 htb hns piP
  alpha : ℝ
  beta : ℝ
  lambdaCoeff : ℝ
  E : Finset (Fin n × Fin n)
  chi : Fin n → ℤ
  phi : Fin n → ℝ
  𝒥 : Finset (Finset (Fin n))
  Admissible : Matrix (Fin n) (Fin n) ℝ → Prop
  Astar : Matrix (Fin n) (Fin n) ℝ
  minimizer : IsLogDetNFrameMinimizer alpha beta lambdaCoeff E chi phi 𝒥 Admissible Astar
  realizes_same_gauge :
    MatrixGaugeRealizesSATGauge M n hn hn2 htb hns Astar 𝒥 piP.gauge

/-- Conversely, if a `Pi+` transform has the Route-C fields and has been
identified with a Route-B minimizer, it gives the full witness-level B/C bridge
data used below. -/
def logDetBridgeData_of_piPlusGauge_minimizes_nframeLagrangian
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hlocal : piP.block_local_hadamard_lift)
    (hrank : PiPlusRankInvariant M n hn2 htb hns piP)
    (hp : PiPlusWidthRankPSide M n hn2 htb hns piP)
    (hnp : PiPlusIdentityMinorPreservation M n hn2 htb hns piP)
    (hmin : PiPlusGaugeMinimizesNFrameLagrangian M n hn hn2 htb hns piP) :
    PiPlusLogDetMinimizerBridgeData M n hn hn2 htb hns := by
  exact
    { piP := piP
      block_local := hlocal
      rank_invariant := hrank
      width_rank_p_side := hp
      identity_minor_preservation := hnp
      alpha := hmin.alpha
      beta := hmin.beta
      lambdaCoeff := hmin.lambdaCoeff
      E := hmin.E
      chi := hmin.chi
      phi := hmin.phi
      𝒥 := hmin.𝒥
      Admissible := hmin.Admissible
      Astar := hmin.Astar
      minimizer := hmin.minimizer
      realizes_same_gauge := hmin.realizes_piPlus_gauge }

/-- The witness bridge forgets to ordinary Route C constructive data. -/
theorem piPlusConstructiveData_of_logDetBridgeData
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : PiPlusLogDetMinimizerBridgeData M n hn hn2 htb hns) :
    PiPlusConstructiveSATGaugeData M n hn2 htb hns := by
  exact ⟨h.piP, h.block_local, h.rank_invariant,
    h.width_rank_p_side, h.identity_minor_preservation⟩

/-- The witness bridge also forgets to the explicit SAT-gauge subgoals, using
its matrix-to-SAT realization field. -/
theorem satDeciderGaugeSubgoals_of_logDetBridgeData
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : PiPlusLogDetMinimizerBridgeData M n hn hn2 htb hns) :
    SATDeciderGaugeSubgoals M n hn2 htb hns h.piP.gauge :=
  satDeciderGaugeSubgoals_of_matrixGaugeRealizesSATGauge
    M n hn hn2 htb hns h.Astar h.𝒥 h.piP.gauge h.realizes_same_gauge

/-- Uniform witness-level Route B/Route C bridge. -/
def Step247UniformPiPlusLogDetMinimizerBridgeData : Prop :=
  ∀ (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    Nonempty (PiPlusLogDetMinimizerBridgeData M n hn hn2 htb hns)

/-- A uniform witness bridge yields explicit uniform `Pi+` constructive data. -/
theorem uniformPiPlus_of_logDetMinimizerBridge
    (hBridge : Step247UniformPiPlusLogDetMinimizerBridgeData) :
    Step247UniformPiPlusConstructiveData := by
  intro M n hn hn2 htb hns hdec
  rcases hBridge M n hn hn2 htb hns hdec with ⟨h⟩
  exact piPlusConstructiveData_of_logDetBridgeData M n hn hn2 htb hns h

/-- A uniform witness bridge yields the Route C final socket directly. -/
theorem routeCFinalSocketClosure_of_logDetMinimizerBridge
    (hBridge : Step247UniformPiPlusLogDetMinimizerBridgeData) :
    RouteCFinalSocketClosure :=
  routeCFinalSocketClosure_of_uniformPiPlus
    (uniformPiPlus_of_logDetMinimizerBridge hBridge)

/-- A uniform witness bridge yields the Route B variational closure. -/
theorem routeBVariationalClosure_of_logDetMinimizerBridge
    (hBridge : Step247UniformPiPlusLogDetMinimizerBridgeData) :
    RouteBVariationalClosure :=
  routeBVariationalClosure_of_routeCFinalSocketClosure
    (routeCFinalSocketClosure_of_logDetMinimizerBridge hBridge)

/-- The witness bridge closes both named routes and records their final-socket
equivalence in one theorem. -/
theorem routeB_routeC_equivalence_of_logDetMinimizerBridge
    (hBridge : Step247UniformPiPlusLogDetMinimizerBridgeData) :
    RouteBVariationalClosure ∧ RouteCFinalSocketClosure ∧
      (RouteBVariationalClosure ↔ RouteCFinalSocketClosure) := by
  exact ⟨routeBVariationalClosure_of_logDetMinimizerBridge hBridge,
    routeCFinalSocketClosure_of_logDetMinimizerBridge hBridge,
    routeB_routeC_finalSocket_equivalence⟩

/-! ## Axiom audit anchors -/

#print axioms routeCFinalSocketClosure_of_uniformPiPlus
#print axioms routeBVariationalClosure_of_routeCFinalSocketClosure
#print axioms routeCFinalSocketClosure_of_routeBVariationalClosure
#print axioms routeB_routeC_finalSocket_equivalence
#print axioms routeBVariationalClosure_of_uniformPiPlus
#print axioms piPlusGauge_minimizes_nframeLagrangian
#print axioms satDeciderGaugeSubgoals_of_piPlusGauge_minimizes_nframeLagrangian
#print axioms piPlusConstructiveData_of_logDetBridgeData
#print axioms satDeciderGaugeSubgoals_of_logDetBridgeData
#print axioms uniformPiPlus_of_logDetMinimizerBridge
#print axioms routeB_routeC_equivalence_of_logDetMinimizerBridge

end PallLean.Paper93.DeepMath.PathC
