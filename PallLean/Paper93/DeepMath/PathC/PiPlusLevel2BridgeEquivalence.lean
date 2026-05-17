import PallLean.Paper93.DeepMath.PathC.PiPlusAdmissibility

/-!
# Level-2 Route B / Route C bridge equivalence

The route-level bridge was already bidirectional:

`RouteBVariationalClosure ↔ RouteCFinalSocketClosure`.

This file finishes the *structural* Level-2 bridge: the witness-level
`PiPlusLogDetMinimizerBridgeData` is equivalent to the concrete Route-C fields
plus the named Route-B minimizer realization
`PiPlusGaugeMinimizesNFrameLagrangian`.

This is not an unconditional proof that the concrete `Pi+` is the minimizer;
that remains the real variational theorem.  What is finished here is the bridge
plumbing: once either side supplies the Level-2 witness, Lean can move it both
ways without any extra informal interpretation.
-/

namespace PallLean.Paper93.DeepMath.PathC

open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- A witness-level log-det bridge gives the named `Pi+` minimizer property for
its carried transform. -/
def piPlusGaugeMinimizesNFrameLagrangian_of_logDetBridgeData
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : PiPlusLogDetMinimizerBridgeData M n hn hn2 htb hns) :
    PiPlusGaugeMinimizesNFrameLagrangian M n hn hn2 htb hns h.piP :=
  { alpha := h.alpha
    beta := h.beta
    lambdaCoeff := h.lambdaCoeff
    E := h.E
    chi := h.chi
    phi := h.phi
    𝒥 := h.𝒥
    Admissible := h.Admissible
    Astar := h.Astar
    minimizer := h.minimizer
    realizes_piPlus_gauge := h.realizes_same_gauge }

/-- Route-C fields plus the named Level-2 minimizer property are exactly enough
to build witness-level bridge data. -/
def logDetBridgeData_of_piPlusLevel2Fields
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hlocal : piP.block_local_hadamard_lift)
    (hrank : PiPlusRankInvariant M n hn2 htb hns piP)
    (hp : PiPlusWidthRankPSide M n hn2 htb hns piP)
    (hnp : PiPlusIdentityMinorPreservation M n hn2 htb hns piP)
    (hmin : PiPlusGaugeMinimizesNFrameLagrangian M n hn hn2 htb hns piP) :
    PiPlusLogDetMinimizerBridgeData M n hn hn2 htb hns :=
  logDetBridgeData_of_piPlusGauge_minimizes_nframeLagrangian
    M n hn hn2 htb hns piP hlocal hrank hp hnp hmin

/-- Instance-level Level-2 data, separated into the constructive Route-C fields
and the Route-B minimizer identification field. -/
def PiPlusLevel2BridgeFields
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ piP : PiPlusSATTransform M n hn2 htb hns,
    piP.block_local_hadamard_lift ∧
      PiPlusRankInvariant M n hn2 htb hns piP ∧
        PiPlusWidthRankPSide M n hn2 htb hns piP ∧
          PiPlusIdentityMinorPreservation M n hn2 htb hns piP ∧
            Nonempty (PiPlusGaugeMinimizesNFrameLagrangian M n hn hn2 htb hns piP)

/-- Instance-level equivalence between the bundled witness bridge and the
separated Level-2 fields. -/
theorem nonempty_logDetBridgeData_iff_piPlusLevel2BridgeFields
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Nonempty (PiPlusLogDetMinimizerBridgeData M n hn hn2 htb hns) ↔
      PiPlusLevel2BridgeFields M n hn hn2 htb hns := by
  constructor
  · intro hnon
    rcases hnon with ⟨h⟩
    exact ⟨h.piP, h.block_local, h.rank_invariant, h.width_rank_p_side,
      h.identity_minor_preservation,
      ⟨piPlusGaugeMinimizesNFrameLagrangian_of_logDetBridgeData
        M n hn hn2 htb hns h⟩⟩
  · intro hfields
    rcases hfields with
      ⟨piP, hlocal, hrank, hp, hnp, hmin⟩
    rcases hmin with ⟨hmin⟩
    exact ⟨logDetBridgeData_of_piPlusLevel2Fields
      M n hn hn2 htb hns piP hlocal hrank hp hnp hmin⟩

/-- Uniform Level-2 bridge fields for all bounded SAT-decider instances. -/
def Step247UniformPiPlusLevel2BridgeFields : Prop :=
  ∀ (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    PiPlusLevel2BridgeFields M n hn hn2 htb hns

/-- Uniform equivalence: the previous bundled witness bridge is exactly the
same data as the separated Level-2 bridge fields. -/
theorem uniformLogDetMinimizerBridge_iff_piPlusLevel2BridgeFields :
    Step247UniformPiPlusLogDetMinimizerBridgeData ↔
      Step247UniformPiPlusLevel2BridgeFields := by
  constructor
  · intro hBridge M n hn hn2 htb hns hdec
    exact (nonempty_logDetBridgeData_iff_piPlusLevel2BridgeFields
      M n hn hn2 htb hns).mp
      (hBridge M n hn hn2 htb hns hdec)
  · intro hFields M n hn hn2 htb hns hdec
    exact (nonempty_logDetBridgeData_iff_piPlusLevel2BridgeFields
      M n hn hn2 htb hns).mpr
      (hFields M n hn hn2 htb hns hdec)

/-- Therefore the separated Level-2 fields close both named routes through the
already-established witness bridge. -/
theorem routeB_routeC_equivalence_of_piPlusLevel2BridgeFields
    (h : Step247UniformPiPlusLevel2BridgeFields) :
    RouteBVariationalClosure ∧ RouteCFinalSocketClosure ∧
      (RouteBVariationalClosure ↔ RouteCFinalSocketClosure) :=
  routeB_routeC_equivalence_of_logDetMinimizerBridge
    ((uniformLogDetMinimizerBridge_iff_piPlusLevel2BridgeFields).mpr h)

/-! ## Axiom audit anchors -/

#print axioms piPlusGaugeMinimizesNFrameLagrangian_of_logDetBridgeData
#print axioms logDetBridgeData_of_piPlusLevel2Fields
#print axioms nonempty_logDetBridgeData_iff_piPlusLevel2BridgeFields
#print axioms uniformLogDetMinimizerBridge_iff_piPlusLevel2BridgeFields
#print axioms routeB_routeC_equivalence_of_piPlusLevel2BridgeFields

end PallLean.Paper93.DeepMath.PathC
