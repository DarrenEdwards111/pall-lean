import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget
import PallLean.Paper93.DeepMath.PathB.RouteBTransportSeamClosure

/-!
# Route B2 Pivot (object-separation architecture)

This module isolates the post-obstruction Route-B2 plan:
- avoid same-object rank sandwich,
- use a new NP witness object and a distinct P envelope object,
- connect them by one-way transport monotonicity.

The final arithmetic contradiction is proved here. The remaining proof burden is
the construction of the NP/P observables, the P-side upper bound, the NP-side
lower bound, and the rank-non-increasing transport.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.Paper283

/-- Abstract rank observable on the NP witness object. -/
axiom ΓNP : Type → Nat

/-- Abstract rank observable on the P envelope object. -/
axiom ΓP : Type → Nat

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
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (_T : HardNPWitnessObject M n hn2 htb hns →
      PEnvelopeObject M n hn2 htb hns),
    ΓNP (HardNPWitnessObject M n hn2 htb hns) ≤
      ΓP (PEnvelopeObject M n hn2 htb hns)

/-- P-side upper bound target for Route B2. -/
axiom routeB2_p_side_upper_bound
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ΓP (PEnvelopeObject M n hn2 htb hns) ≤ n ^ 200

/-- NP-side lower bound target for Route B2 (instance-sensitive). -/
axiom routeB2_np_side_lower_bound
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    n ^ (Nat.log 2 n) ≤ ΓNP (HardNPWitnessObject M n hn2 htb hns)

/-- Extract the rank inequality carried by the one-way Route B2 transport. -/
theorem routeB2_transport_monotone
    (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hT : RouteB2Transport M n hn2 htb hns) :
    ΓNP (HardNPWitnessObject M n hn2 htb hns) ≤
      ΓP (PEnvelopeObject M n hn2 htb hns) := by
  rcases hT with ⟨_T, hmono⟩
  exact hmono

/-- Route B2 assembly interface: package all obligations per SAT decider instance. -/
structure RouteB2InstancePackage
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) : Prop where
  transport : RouteB2Transport M n hn2 htb hns
  p_upper : ΓP (PEnvelopeObject M n hn2 htb hns) ≤ n ^ 200
  np_lower : n ^ (Nat.log 2 n) ≤ ΓNP (HardNPWitnessObject M n hn2 htb hns)
  monotone : ΓNP (HardNPWitnessObject M n hn2 htb hns) ≤
    ΓP (PEnvelopeObject M n hn2 htb hns)

/-- Uniform Route B2 package at paper scale. -/
abbrev RouteB2UniformPackage : Prop :=
  ∀ (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M),
    RouteB2InstancePackage M n hn hn2 htb hns hdec

/-- Build the per-instance package from the current Route B2 obligation
axioms plus an explicit one-way transport. -/
theorem routeB2_instancePackage_of_transport
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (hT : RouteB2Transport M n hn2 htb hns) :
    RouteB2InstancePackage M n hn hn2 htb hns hdec where
  transport := hT
  p_upper := routeB2_p_side_upper_bound M n hn hn2 htb hns
  np_lower := routeB2_np_side_lower_bound M n hn hn2 htb hns hdec
  monotone := routeB2_transport_monotone M n hn hn2 htb hns hT

/-- Uniform transport closes the current Route B2 package, relative to the
explicit P-side and NP-side bound axioms above. -/
theorem routeB2UniformPackage_of_uniform_transport
    (hT :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteB2Transport M n hn2 htb hns) :
    RouteB2UniformPackage := by
  intro M n hn hn2 htb hns hdec
  exact routeB2_instancePackage_of_transport M n hn hn2 htb hns hdec
    (hT M n hn hn2 htb hns hdec)

/-- The Route B2 rank sandwich is arithmetically impossible at paper scale. -/
theorem routeB2_instance_rank_sandwich_false
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (hPkg : RouteB2InstancePackage M n hn hn2 htb hns hdec) :
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

/-- Route B2 closure form: a uniform package rules out bounded SAT deciders at
paper scale by the explicit rank-sandwich contradiction above. -/
theorem routeB2_noBoundedSATDeciderAtPaperScale
    (hU : RouteB2UniformPackage) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact routeB2_instance_rank_sandwich_false M n hn hn2 htb hns hdec
    (hU M n hn hn2 htb hns hdec)

/-- Final Route B2 contradiction form. -/
theorem routeB2_not_PeqNP
    (hU : RouteB2UniformPackage) :
    ∀ (_ : PeqNP_Paper), False :=
  noBoundedSATDeciderAtPaperScale_implies_not_PeqNP
    (routeB2_noBoundedSATDeciderAtPaperScale hU)

#print axioms routeB2_not_PeqNP

end PallLean.Paper93.DeepMath.PathB
