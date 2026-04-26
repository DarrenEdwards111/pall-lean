import PallLean.Paper93.Paper283.RouteBRicherGaugeSpectralWindowBudget
import PallLean.Paper93.Paper283.BridgeACompilerLocalPolynomial
import PallLean.Paper93.Paper283.RouteBBridgeAConcreteSpectralFloor
import PallLean.Paper93.Paper283.BridgeAComposition
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetIsHermitian
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Concrete spectral-window budget for the compiled gadget

This file packages the three hypotheses of
`RouteBRicherGaugeSpectralWindowBudget` as a concrete kernel-only
constructor for the compiled-gadget matrix `compiledGadget α n` with
window `S := Finset.univ` and floor `lambdaFloor := α`.

The three obligations are discharged as follows:

1. `lambdaFloor_nonneg`: `0 ≤ α` follows from the strict positivity
   hypothesis `0 < α`.
2. `eigenvalue_floor`: every Hermitian eigenvalue of `compiledGadget α n`
   is at least `α`. This is the existing kernel theorem
   `compiledGadget_eigenvalue_floor` from
   `RouteBBridgeAConcreteSpectralFloor`.
3. `spectral_floor_budget`: setting
   `rankLogRate := Real.log (1 + θ * α) / (κ * gadgetN)`, the LHS reduces
   exactly to `(activeSet.card : Real) * Real.log (1 + θ * α)`, which is
   bounded by the RHS `(N : Real) * Real.log (1 + θ * α)` because
   `activeSet ⊆ Finset.univ` and `Real.log (1 + θ * α) ≥ 0` (since
   `θ * α ≥ 0`).

The pocket-rank identification
`(cookLevinPocketLocalGadgetFamily N α κ gadgetN v).rank = κ * gadgetN`
comes from `BridgeACompilerLocalPolynomial`, and the Hermitian /
PosSemidef witnesses for `compiledGadget α n` come from `PathB`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

/-- Auxiliary computation: the per-vertex pocket rank for the
Cook-Levin family is the constant `κ * gadgetN`, so the active-set sum
is `activeSet.card * (κ * gadgetN)`. -/
private theorem cookLevinPocket_activeSet_rank_sum_eq
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (hgadgetN : 1 <= gadgetN) :
    ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank) : Real)
      =
      ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card : Real)
        * ((kappa * gadgetN : Nat) : Real) := by
  classical
  have hpoint :
      ∀ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank : Real)
          = ((kappa * gadgetN : Nat) : Real) := by
    intro v _
    have h := bridgeA_cookLevinPocketLocalGadget_rank_eq_kappa_mul_gadgetN
      (N := N) alpha kappa gadgetN v halpha hgadgetN
    exact_mod_cast (by rw [h] : ((cookLevinPocketLocalGadgetFamily N alpha kappa
      gadgetN v).rank : Real) = ((kappa * gadgetN : Nat) : Real))
  -- Rewrite the Nat-valued sum cast into a Real sum, then pull the
  -- constant out.
  -- The Nat-valued sum cast into Real distributes over the finite sum
  -- (definitional equality via `Nat.cast_sum`).
  have hpush :
      ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
          (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank) : Real)
        =
        ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
          ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank : Real) :=
    rfl
  rw [hpush, Finset.sum_congr rfl hpoint, Finset.sum_const]
  simp [nsmul_eq_mul, mul_comm]

/-- Helper: `Real.log (1 + θ * α) ≥ 0` when `θ > 0` and `α > 0`. -/
private theorem log_one_add_theta_alpha_nonneg
    {theta alpha : Real} (htheta : 0 < theta) (halpha : 0 < alpha) :
    0 <= Real.log (1 + theta * alpha) := by
  have hpos : 0 < theta * alpha := mul_pos htheta halpha
  have hone : (1 : Real) <= 1 + theta * alpha := by linarith
  exact Real.log_nonneg hone

/-- **Concrete spectral-window budget for the compiled gadget on the full
window.**

Given `0 < α`, `0 < θ`, `1 ≤ κ`, `1 ≤ gadgetN`, the package
`RouteBRicherGaugeSpectralWindowBudget` is satisfied for the
compiled-gadget matrix `compiledGadget α n`, the window `S := Finset.univ`,
the floor `lambdaFloor := α`, and the rate
`rankLogRate := Real.log (1 + θ * α) / (κ * gadgetN)`.

The three hypotheses are discharged from existing kernel facts:
* `lambdaFloor_nonneg` from `halpha.le`.
* `eigenvalue_floor` from `compiledGadget_eigenvalue_floor`.
* `spectral_floor_budget` by direct algebra on the rank identity
  `(cookLevinPocketLocalGadgetFamily N α κ gadgetN v).rank = κ * gadgetN`
  and `activeSet.card ≤ N`.

The PosSemidef witness for `compiledGadget α n` is supplied by
`compiledGadget_posSemidef_of_positive_coupling`, and the Hermitian
witness inside the eigenvalue floor proof comes via
`Matrix.PosSemidef.1` (the underlying `IsHermitian`). -/
theorem spectralWindowBudget_compiledGadget_univ
    {N d : Nat}
    (alpha beta alpha0 theta : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (htheta : 0 < theta)
    (hkappa : 1 <= kappa) (hgadgetN : 1 <= gadgetN) :
    RouteBRicherGaugeSpectralWindowBudget
      (N := N) (d := d)
      alpha beta alpha0 kappa gadgetN G chi Phi
      theta
      (Real.log (1 + theta * alpha) / ((kappa * gadgetN : Nat) : Real))
      alpha
      (compiledGadget alpha N)
      (compiledGadget_posSemidef_of_positive_coupling alpha halpha)
      Finset.univ where
  lambdaFloor_nonneg := halpha.le
  eigenvalue_floor := by
    intro i _hi
    exact compiledGadget_eigenvalue_floor (N := N) alpha halpha
      (compiledGadget_posSemidef_of_positive_coupling alpha halpha) i
  spectral_floor_budget := by
    classical
    -- Abbreviations
    set L : Real := Real.log (1 + theta * alpha) with hL_def
    set kg : Nat := kappa * gadgetN with hkg_def
    -- κ * gadgetN ≥ 1, so its real cast is positive.
    have hkg_pos_nat : 1 <= kg := by
      rw [hkg_def]
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero
          (Nat.one_le_iff_ne_zero.mp hkappa)
          (Nat.one_le_iff_ne_zero.mp hgadgetN))
    have hkg_pos : (0 : Real) < (kg : Real) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hkg_pos_nat
    have hkg_ne : (kg : Real) ≠ 0 := ne_of_gt hkg_pos
    -- log(1 + θ*α) ≥ 0
    have hL_nonneg : 0 <= L := by
      rw [hL_def]
      exact log_one_add_theta_alpha_nonneg htheta halpha
    -- Sum identity
    have hsum_eq :
        ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank) : Real)
          =
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card : Real)
            * (kg : Real) := by
      rw [hkg_def]
      exact cookLevinPocket_activeSet_rank_sum_eq
        alpha beta alpha0 kappa gadgetN G chi Phi halpha hgadgetN
    -- LHS = (L/kg) * (activeSet.card * kg) = L * activeSet.card
    rw [hsum_eq]
    -- Goal: (L / kg) * (activeSet.card * kg) ≤ univ.card * L
    have hcard_le :
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card : Real)
          ≤ ((Finset.univ : Finset (Fin N)).card : Real) := by
      have h := activeSet_card_le (N := N) (d := d) alpha beta alpha0 G chi Phi
      have hN : (Finset.univ : Finset (Fin N)).card = N := by
        simp [Finset.card_univ]
      rw [hN]
      exact_mod_cast h
    -- Algebraic simplification
    have hLHS :
        L / (kg : Real) *
            (((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card : Real)
              * (kg : Real))
          =
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card : Real)
            * L := by
      field_simp
    rw [hLHS]
    -- Goal: activeSet.card * L ≤ univ.card * L
    exact mul_le_mul_of_nonneg_right hcard_le hL_nonneg

/-! ## Axiom audit anchor -/

#print axioms spectralWindowBudget_compiledGadget_univ

end PallLean.Paper93.Paper283
