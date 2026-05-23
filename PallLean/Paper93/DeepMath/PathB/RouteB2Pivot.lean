import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget
import PallLean.Paper93.DeepMath.PathB.RouteBTransportSeamClosure

/-!
# Route B2 Rank-Sandwich Obstruction

This module isolates the post-obstruction Route-B2 rank-sandwich shape:
- avoid same-object rank sandwich,
- use a new NP witness object and a distinct P envelope object,
- connect them by one-way transport monotonicity.

The honest conclusion is obstructional: at paper scale, the conjunction of an
NP lower bound, rank-non-increasing transport, and a P-side upper bound is
arithmetically impossible. A paper-faithful use of this file is therefore:
derive such a sandwich from a hypothetical bounded SAT decider, then close by
contradiction. The sandwich itself is not a constructive target.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.Paper283

/-- Route B2 rank observables.  A real proof must instantiate these fields with
concrete rank/complexity measures, not postulate global observables. -/
structure RouteB2RankData where
  ΓNP : Type → Nat
  ΓP : Type → Nat

/-- NP-side hardness witness object (must be instance-sensitive). -/
abbrev HardNPWitnessObject (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Type :=
  MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat

/-- P-side envelope object from deterministic/local compilation. -/
abbrev PEnvelopeObject (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Type :=
  MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat

/-- One-way transport: NP witness -> P envelope observable, carrying the
rank-non-increasing inequality needed for the sandwich. -/
abbrev RouteB2Transport
    (D : RouteB2RankData)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (_T : HardNPWitnessObject M n hn2 htb hns →
      PEnvelopeObject M n hn2 htb hns),
    D.ΓNP (HardNPWitnessObject M n hn2 htb hns) ≤
      D.ΓP (PEnvelopeObject M n hn2 htb hns)

/-- The remaining hard Route B2 bounds.  This record replaces the previous
global bound axioms with explicit proof obligations. -/
structure RouteB2BoundObligations (D : RouteB2RankData) : Prop where
  p_side_upper_bound :
    ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      D.ΓP (PEnvelopeObject M n hn2 htb hns) ≤ n ^ 200
  np_side_lower_bound :
    ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
      (_hdec : DecidesSAT M),
      n ^ (Nat.log 2 n) ≤ D.ΓNP (HardNPWitnessObject M n hn2 htb hns)

/-- Extract the rank inequality carried by the one-way Route B2 transport. -/
theorem routeB2_transport_monotone
    (D : RouteB2RankData)
    (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hT : RouteB2Transport D M n hn2 htb hns) :
    D.ΓNP (HardNPWitnessObject M n hn2 htb hns) ≤
      D.ΓP (PEnvelopeObject M n hn2 htb hns) := by
  rcases hT with ⟨_T, hmono⟩
  exact hmono

/-- Route B2 assembly interface: the forbidden rank-sandwich obligations for a
single SAT-decider instance. -/
structure RouteB2InstancePackage
    (D : RouteB2RankData)
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) : Prop where
  transport : RouteB2Transport D M n hn2 htb hns
  p_upper : D.ΓP (PEnvelopeObject M n hn2 htb hns) ≤ n ^ 200
  np_lower :
    n ^ (Nat.log 2 n) ≤ D.ΓNP (HardNPWitnessObject M n hn2 htb hns)
  monotone : D.ΓNP (HardNPWitnessObject M n hn2 htb hns) ≤
    D.ΓP (PEnvelopeObject M n hn2 htb hns)

/-- Explicit obstruction-facing name for the impossible per-instance sandwich. -/
abbrev RouteB2RankSandwich := RouteB2InstancePackage

/-- Uniform extractor: every hypothetical bounded SAT decider instance is sent
to the forbidden Route B2 rank sandwich.  This is the paper-faithful way to use
the obstruction: derive the sandwich from `DecidesSAT M`, then contradict it. -/
abbrev RouteB2UniformPackage (D : RouteB2RankData) : Prop :=
  ∀ (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M),
    RouteB2InstancePackage D M n hn hn2 htb hns hdec

/-- Obstruction-facing alias for the uniform decider-to-sandwich extractor. -/
abbrev RouteB2DeciderForcesRankSandwich := RouteB2UniformPackage

/-- Build the per-instance package from explicit Route B2 bound obligations
plus an explicit one-way transport. -/
theorem routeB2_instancePackage_of_transport
    (D : RouteB2RankData) (hBounds : RouteB2BoundObligations D)
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (hT : RouteB2Transport D M n hn2 htb hns) :
    RouteB2InstancePackage D M n hn hn2 htb hns hdec where
  transport := hT
  p_upper := hBounds.p_side_upper_bound M n hn hn2 htb hns
  np_lower := hBounds.np_side_lower_bound M n hn hn2 htb hns hdec
  monotone := routeB2_transport_monotone D M n hn hn2 htb hns hT

/-- Uniform transport closes the current Route B2 package, relative to the
explicit P-side and NP-side bound obligations above. -/
theorem routeB2UniformPackage_of_uniform_transport
    (D : RouteB2RankData) (hBounds : RouteB2BoundObligations D)
    (hT :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteB2Transport D M n hn2 htb hns) :
    RouteB2UniformPackage D := by
  intro M n hn hn2 htb hns hdec
  exact routeB2_instancePackage_of_transport D hBounds M n hn hn2 htb hns hdec
    (hT M n hn hn2 htb hns hdec)

/-- The Route B2 rank sandwich is arithmetically impossible at paper scale. -/
theorem routeB2_instance_rank_sandwich_false
    (D : RouteB2RankData)
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (hPkg : RouteB2InstancePackage D M n hn hn2 htb hns hdec) :
    False := by
  have hchain : n ^ (Nat.log 2 n) ≤ n ^ 200 :=
    le_trans hPkg.np_lower (le_trans hPkg.monotone hPkg.p_upper)
  have hlog : 804 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn
  have h201 : 201 ≤ Nat.log 2 n := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) h201) hchain
  exact absurd hcontra
    (not_le_of_gt
      (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))

/-- Headline obstruction: no per-instance Route B2 rank sandwich can exist at
paper scale. -/
theorem routeB2_rankSandwich_obstruction
    (D : RouteB2RankData)
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ¬ RouteB2RankSandwich D M n hn hn2 htb hns hdec := by
  intro hPkg
  exact routeB2_instance_rank_sandwich_false D M n hn hn2 htb hns hdec hPkg

/-- Paper-faithful closure form: if every hypothetical bounded SAT decider
instance yields the forbidden rank sandwich, then no such bounded SAT decider
exists. -/
theorem routeB2_noBoundedSATDeciderAtPaperScale
    (D : RouteB2RankData) (hU : RouteB2DeciderForcesRankSandwich D) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact routeB2_instance_rank_sandwich_false D M n hn hn2 htb hns hdec
    (hU M n hn hn2 htb hns hdec)

/-- Route B2 closure from explicit rank data, bound obligations, and uniform
transport. -/
theorem routeB2_noBoundedSATDeciderAtPaperScale_of_bounds_and_transport
    (D : RouteB2RankData) (hBounds : RouteB2BoundObligations D)
    (hT :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteB2Transport D M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  routeB2_noBoundedSATDeciderAtPaperScale D
    (routeB2UniformPackage_of_uniform_transport D hBounds hT)

/-- Final Route B2 contradiction form. -/
theorem routeB2_not_PeqNP
    (D : RouteB2RankData) (hU : RouteB2DeciderForcesRankSandwich D) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (routeB2_noBoundedSATDeciderAtPaperScale D hU)

/-- Final Route B2 contradiction from explicit remaining obligations. -/
theorem routeB2_not_PeqNP_of_bounds_and_transport
    (D : RouteB2RankData) (hBounds : RouteB2BoundObligations D)
    (hT :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteB2Transport D M n hn2 htb hns) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (routeB2_noBoundedSATDeciderAtPaperScale_of_bounds_and_transport
      D hBounds hT)

#print axioms routeB2_rankSandwich_obstruction
#print axioms routeB2_not_PeqNP
#print axioms routeB2_not_PeqNP_of_bounds_and_transport

end PallLean.Paper93.DeepMath.PathB
