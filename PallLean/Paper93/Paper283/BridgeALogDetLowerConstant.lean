import PallLean.Paper93.Paper283.BridgeALogDetLower

/-!
# Constant-floor constructors for Bridge A lower log-det

This module records kernel-only algebra around the Bridge A lower-logdet
interface.  It does not prove the analytic local barrier estimate.  Instead it
discharges useful subcases where that analytic input has already been reduced
to a constant local contribution or to simple rank-rate side conditions.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- A constant local lower-logdet floor gives the active-contribution
hypothesis package as soon as the constant floor is at least `delta` and its
active-set total is bounded by the global `logDet`. -/
theorem bridgeA_activeLogDetLowerHypotheses_of_constant_floor {N d : Nat}
    (alpha beta alpha0 delta logDet localFloor : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (hdelta : delta <= localFloor)
    (hglobal :
      localFloor *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <= logDet) :
    BridgeAActiveLogDetLowerHypotheses
      alpha beta alpha0 delta logDet G chi Phi
      (fun _ : Fin N => localFloor) := by
  classical
  refine ⟨?_, ?_⟩
  · intro v hv
    exact hdelta
  · have hsum :
        (∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
          (fun _ : Fin N => localFloor) v) =
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) * localFloor := by
      simp
    calc
      (∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        (fun _ : Fin N => localFloor) v)
          =
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) * localFloor := hsum
      _ =
        localFloor *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) := by
        ring
      _ <= logDet := hglobal

/-- Constant active local contribution subcase of the Bridge A lower-logdet
estimate. -/
theorem bridgeA_logDet_lower_from_constant_active_contribution {N d : Nat}
    (alpha beta alpha0 delta logDet localFloor : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (hdelta : delta <= localFloor)
    (hglobal :
      localFloor *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <= logDet) :
    delta *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) <= logDet := by
  exact bridgeA_logDet_lower_from_active_contributions
    alpha beta alpha0 delta logDet G chi Phi
    (fun _ : Fin N => localFloor)
    (bridgeA_activeLogDetLowerHypotheses_of_constant_floor
      alpha beta alpha0 delta logDet localFloor G chi Phi hdelta hglobal)

/-- If a nonnegative constant local floor is budgeted over all `N` vertices,
then it is budgeted over the Bridge A active set. -/
theorem bridgeA_logDet_lower_from_uniform_vertex_budget {N d : Nat}
    (alpha beta alpha0 delta logDet localFloor : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (hfloor_nonneg : 0 <= localFloor)
    (hdelta : delta <= localFloor)
    (hglobal : localFloor * (N : Real) <= logDet) :
    delta *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) <= logDet := by
  classical
  have hcard_nat :
      (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card <= N := by
    simpa using
      (Finset.card_le_univ
        (s := activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi))
  have hcard_real :
      ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
        Real) <= (N : Real) := by
    exact_mod_cast hcard_nat
  have hactive_budget :
      localFloor *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <= logDet := by
    exact le_trans
      (mul_le_mul_of_nonneg_left hcard_real hfloor_nonneg)
      hglobal
  exact bridgeA_logDet_lower_from_constant_active_contribution
    alpha beta alpha0 delta logDet localFloor G chi Phi hdelta hactive_budget

/-- A unit-rate floor is a simpler sufficient condition for the rank-logdet
side condition `delta <= rankLogRate * kappa`, provided `1 <= kappa`. -/
theorem bridgeA_rankLogDetLowerHypotheses_of_unit_rate_floor {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : ∀ v : Fin N, LocalGadget N v)
    (rankLogRate logDet delta : Real)
    (hrate_nonneg : 0 <= rankLogRate)
    (hkappa : 1 <= kappa)
    (hdelta_rate : delta <= rankLogRate)
    (hglobal :
      rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (gadgetFamily v).rank) : Real) <= logDet) :
    BridgeARankLogDetLowerHypotheses
      alpha beta alpha0 kappa G chi Phi gadgetFamily
      rankLogRate logDet delta := by
  refine ⟨hrate_nonneg, ?_, hglobal⟩
  have hkappa_real : (1 : Real) <= (kappa : Real) := by
    exact_mod_cast hkappa
  have hrate_mul_one :
      rankLogRate * (1 : Real) <= rankLogRate * (kappa : Real) :=
    mul_le_mul_of_nonneg_left hkappa_real hrate_nonneg
  calc
    delta <= rankLogRate := hdelta_rate
    _ = rankLogRate * (1 : Real) := by ring
    _ <= rankLogRate * (kappa : Real) := hrate_mul_one

/-! ## Axiom audit anchors -/

#print axioms bridgeA_activeLogDetLowerHypotheses_of_constant_floor
#print axioms bridgeA_logDet_lower_from_constant_active_contribution
#print axioms bridgeA_logDet_lower_from_uniform_vertex_budget
#print axioms bridgeA_rankLogDetLowerHypotheses_of_unit_rate_floor

end PallLean.Paper93.Paper283
