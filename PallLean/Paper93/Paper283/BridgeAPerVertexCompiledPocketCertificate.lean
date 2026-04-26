import PallLean.MultilinearSPDP
import PallLean.Paper93.Paper283.BridgeAConcreteGadget

/-!
# Bridge A per-vertex compiled pocket certificate

This file records the kernel-checked per-vertex Bridge A reduction available
for the compiler-owned pocket gadget currently exposed in Paper283:
`cookLevinPocketLocalGadgetFamily`.

The existing object is a `LocalGadget` and carries only a natural-number
`rank`.  The file therefore proves the rank implication at that checked
surface, and separately names the exact realization data still missing for a
fully polynomial statement about a compiler-produced local gadget `Q_v`:
the local variable space, the local SPDP partition, the polynomial `Q_v`, and
the equality identifying its `mlBlockedSpdpRank` with the rank of the checked
Cook-Levin pocket gadget.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP

/-- The per-vertex Bridge A rank implication for the checked Cook-Levin pocket
local gadget family.

The analytic hypothesis `hE` is retained because it is the paper-faithful
Bridge A trigger.  With the current repository data, the checked pocket gadget
rank lower bound is uniform in `v`; the missing compiler layer is the
identification of this rank with the SPDP rank of the actual local polynomial
`Q_v`. -/
theorem bridgeA_perVertex_cookLevinPocket_rank_lower_bound {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN)
    (_hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <= ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v).rank :=
  cookLevinPocketLocalGadget_rank_kappa alpha kappa gadgetN v halpha hgadgetN

/-- A reduced per-vertex certificate at the closest existing compiled-gadget
surface: the checked `cookLevinPocketLocalGadgetFamily` rank field.

This is not yet a polynomial `Q_v` certificate.  It is the exact per-vertex
Bridge A payload that can be checked today from the available Cook-Levin pocket
rank theorem. -/
structure BridgeAPerVertexCookLevinPocketRankCertificate {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) : Prop where
  energy_floor : alpha0 <= localEnergy alpha beta G chi Phi v
  rank_lower_bound :
    kappa <= ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v).rank

/-- Build the per-vertex checked pocket-rank certificate from the paper
Bridge A energy trigger and the existing Cook-Levin pocket rank theorem. -/
theorem bridgeA_perVertex_cookLevinPocketRankCertificate {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    BridgeAPerVertexCookLevinPocketRankCertificate
      alpha beta alpha0 kappa gadgetN G chi Phi v where
  energy_floor := hE
  rank_lower_bound :=
    bridgeA_perVertex_cookLevinPocket_rank_lower_bound
      alpha beta alpha0 kappa gadgetN G chi Phi v halpha hgadgetN hE

/-- Exact missing realization data for upgrading the checked pocket-rank
certificate to a statement about the SPDP rank of the compiler-produced local
polynomial `Q_v`.

The repository currently exposes `cookLevinPocketLocalGadgetFamily` only as a
rank-carrying `LocalGadget`.  A fully paper-faithful per-vertex Bridge A proof
needs these fields from the compiler:

* the local SPDP variable space `spdpVars`;
* the local block partition `partition`;
* the local polynomial `Qv`;
* the equality identifying the polynomial's blocked SPDP rank with the checked
  Cook-Levin pocket gadget rank. -/
structure BridgeAPerVertexCompilerSPDPData {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) : Type where
  spdpVars : Nat
  partition : SPDP.BlockPartition spdpVars
  Qv : MvPolynomial (Fin spdpVars) Rat
  rank_eq_pocket :
    mlBlockedSpdpRank partition kappa kappa Qv =
      ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v).rank

/-- If the compiler supplies the missing per-vertex SPDP realization data, the
checked pocket rank theorem becomes the desired local SPDP rank lower bound for
`Q_v`. -/
theorem bridgeA_perVertex_spdpRank_lower_bound_of_compilerData {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v)
    (data :
      BridgeAPerVertexCompilerSPDPData
        alpha beta alpha0 kappa gadgetN G chi Phi v) :
    kappa <= mlBlockedSpdpRank data.partition kappa kappa data.Qv := by
  have hpocket :
      kappa <= ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v).rank :=
    bridgeA_perVertex_cookLevinPocket_rank_lower_bound
      alpha beta alpha0 kappa gadgetN G chi Phi v halpha hgadgetN hE
  simpa [data.rank_eq_pocket] using hpocket

/-- Family-level form of the missing compiler realization data, for use by
active-set or summation arguments. -/
structure BridgeACompilerSPDPFamilyData {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) : Type where
  spdpVars : Fin N -> Nat
  partition : ∀ v : Fin N, SPDP.BlockPartition (spdpVars v)
  Qv : ∀ v : Fin N, MvPolynomial (Fin (spdpVars v)) Rat
  rank_eq_pocket :
    ∀ v : Fin N,
      mlBlockedSpdpRank (partition v) kappa kappa (Qv v) =
        ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v).rank

/-- The family-level compiler realization specializes to the per-vertex SPDP
rank lower bound. -/
theorem bridgeA_family_spdpRank_lower_bound {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN)
    (data :
      BridgeACompilerSPDPFamilyData
        alpha beta alpha0 kappa gadgetN G chi Phi)
    (v : Fin N)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <= mlBlockedSpdpRank (data.partition v) kappa kappa (data.Qv v) := by
  have hpocket :
      kappa <= ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v).rank :=
    bridgeA_perVertex_cookLevinPocket_rank_lower_bound
      alpha beta alpha0 kappa gadgetN G chi Phi v halpha hgadgetN hE
  simpa [data.rank_eq_pocket v] using hpocket

/-! ## Axiom audit anchors -/

#print axioms bridgeA_perVertex_cookLevinPocket_rank_lower_bound
#print axioms bridgeA_perVertex_cookLevinPocketRankCertificate
#print axioms BridgeAPerVertexCompilerSPDPData
#print axioms bridgeA_perVertex_spdpRank_lower_bound_of_compilerData
#print axioms BridgeACompilerSPDPFamilyData
#print axioms bridgeA_family_spdpRank_lower_bound

end PallLean.Paper93.Paper283
