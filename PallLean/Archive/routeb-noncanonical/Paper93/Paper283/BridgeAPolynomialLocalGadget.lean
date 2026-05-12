import PallLean.Paper93.Paper283.BridgeASquareHelperExact

/-!
# Polynomial-bearing Bridge A local gadgets

`LocalGadget` is intentionally minimal: it stores only a natural-number rank.
That is enough for the existing active-set budget, but it cannot express the
paper-level statement that a compiler-local polynomial `Q_v` has large SPDP
rank.

This file adds a narrow adapter layer that keeps the old rank-only interface
intact while exposing the polynomial payload needed by a genuine Route B
Bridge A proof:

* local SPDP variable space;
* local partition;
* local polynomial `Q_v`;
* the energy-triggered SPDP rank lower bound for that polynomial.

The square-helper instance below is still an adapter candidate, not a theorem
that the full Cook-Levin compiler emits `squareHelperQ` literally.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP

/-- Polynomial-bearing version of a per-vertex Bridge A local gadget.

Unlike `LocalGadget`, this structure carries the local polynomial itself and
the energy-to-SPDP-rank implication for that polynomial. -/
structure BridgeAPolynomialLocalGadget {N d : Nat}
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) : Type where
  spdpVars : Nat
  partition : SPDP.BlockPartition spdpVars
  Qv : MvPolynomial (Fin spdpVars) Rat
  energy_to_spdpRank :
    alpha0 <= localEnergy alpha beta G chi Phi v ->
      kappa <= mlBlockedSpdpRank partition kappa kappa Qv

namespace BridgeAPolynomialLocalGadget

/-- Forget the polynomial payload and retain only the rank number expected by
the existing `LocalGadget` active-set interface. -/
noncomputable def toLocalGadget {N d : Nat}
    {alpha beta alpha0 : Real} {kappa : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real} {v : Fin N}
    (Q : BridgeAPolynomialLocalGadget
      alpha beta alpha0 kappa G chi Phi v) :
    LocalGadget N v where
  rank := mlBlockedSpdpRank Q.partition kappa kappa Q.Qv

/-- The polynomial-bearing gadget immediately supplies the old rank-only
Bridge A hypothesis after forgetting to `LocalGadget`. -/
theorem toLocalGadget_rank_lower_bound {N d : Nat}
    {alpha beta alpha0 : Real} {kappa : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real} {v : Fin N}
    (Q : BridgeAPolynomialLocalGadget
      alpha beta alpha0 kappa G chi Phi v)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <= (Q.toLocalGadget).rank := by
  exact Q.energy_to_spdpRank hE

/-- Convert a family of polynomial-bearing gadgets into the rank-only
`hGadgetRank` hypothesis used by `bridgeA_activeSet_rank_budget`. -/
theorem family_to_hGadgetRank {N d : Nat}
    {alpha beta alpha0 : Real} {kappa : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real}
    (Q :
      forall v : Fin N,
        BridgeAPolynomialLocalGadget
          alpha beta alpha0 kappa G chi Phi v) :
    forall v : Fin N,
      alpha0 <= localEnergy alpha beta G chi Phi v ->
        kappa <= ((Q v).toLocalGadget).rank := by
  intro v hE
  exact (Q v).toLocalGadget_rank_lower_bound hE

/-- Direct SPDP-rank lower bound from a polynomial-bearing local gadget. -/
theorem spdpRank_lower_bound {N d : Nat}
    {alpha beta alpha0 : Real} {kappa : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real} {v : Fin N}
    (Q : BridgeAPolynomialLocalGadget
      alpha beta alpha0 kappa G chi Phi v)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <= mlBlockedSpdpRank Q.partition kappa kappa Q.Qv :=
  Q.energy_to_spdpRank hE

end BridgeAPolynomialLocalGadget

namespace BridgeAGeneralizedNonzeroWitness

/-- The exact square-helper polynomial as a polynomial-bearing Bridge A local
gadget.  This is a non-vacuous polynomial witness for the adapter interface,
not a literal compiler-output theorem. -/
noncomputable def squareHelper_polynomialLocalGadget
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN) :
    BridgeAPolynomialLocalGadget
      alpha beta alpha0 kappa G chi Phi v where
  spdpVars := squareHelperVarCount kappa gadgetN
  partition := discretePartition (squareHelperVarCount kappa gadgetN)
  Qv := squareHelperQ kappa gadgetN
  energy_to_spdpRank := by
    intro hE
    exact
      squareHelper_perVertex_spdpRank_lower_bound
        alpha beta alpha0 kappa gadgetN G chi Phi v
        halpha hgadgetN hE

/-- Family-level square-helper polynomial-bearing gadget. -/
noncomputable def squareHelper_polynomialLocalGadgetFamily
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN) :
    forall v : Fin N,
      BridgeAPolynomialLocalGadget
        alpha beta alpha0 kappa G chi Phi v :=
  fun v =>
    squareHelper_polynomialLocalGadget
      alpha beta alpha0 kappa gadgetN G chi Phi v halpha hgadgetN

/-- Pointwise SPDP-rank lower bound from the polynomial-bearing square-helper
gadget. -/
theorem squareHelper_polynomialLocalGadget_spdpRank_lower_bound
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <=
      mlBlockedSpdpRank
        (discretePartition (squareHelperVarCount kappa gadgetN))
        kappa kappa (squareHelperQ kappa gadgetN) := by
  exact
    (squareHelper_polynomialLocalGadget
      alpha beta alpha0 kappa gadgetN G chi Phi v halpha hgadgetN).energy_to_spdpRank hE

end BridgeAGeneralizedNonzeroWitness

/-! ## Axiom audit anchors -/

#print axioms BridgeAPolynomialLocalGadget.toLocalGadget
#print axioms BridgeAPolynomialLocalGadget.toLocalGadget_rank_lower_bound
#print axioms BridgeAPolynomialLocalGadget.family_to_hGadgetRank
#print axioms BridgeAPolynomialLocalGadget.spdpRank_lower_bound
#print axioms BridgeAGeneralizedNonzeroWitness.squareHelper_polynomialLocalGadget
#print axioms BridgeAGeneralizedNonzeroWitness.squareHelper_polynomialLocalGadgetFamily
#print axioms BridgeAGeneralizedNonzeroWitness.squareHelper_polynomialLocalGadget_spdpRank_lower_bound

end PallLean.Paper93.Paper283
