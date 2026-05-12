import PallLean.Paper93.Paper283.BridgeAPerVertexCompiledPocketCertificate
import PallLean.Paper93.DeepMath.BridgeB.PocketFamilyRank
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetRankPos

/-!
# Bridge A compiler local polynomial frontier

This file makes the current polynomial-facing Bridge A frontier explicit.

The existing Paper283 Cook-Levin pocket local gadget
`cookLevinPocketLocalGadgetFamily` is rank-carrying: it exposes the natural
number `(pocketFamily alpha kappa gadgetN).rank`, not a compiler-owned
polynomial `Q_v`.  Consequently the general `BridgeAPerVertexCompilerSPDPData`
and `BridgeACompilerSPDPFamilyData` constructions reduce exactly to the
missing theorem that an actual local polynomial has multilinear blocked SPDP
rank equal to that pocket rank.

There is one exact instantiation available from the current definitions:
the zero-pocket case `kappa = 0`, with the actual polynomial `Q_v = 0`.
For arbitrary `kappa`, the final section names the sharp rank-equality subgoal
needed to upgrade any concrete polynomial candidate to the existing compiler
SPDP data structures.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP

/-! ## Matrix-side rank normalization -/

/-- The checked matrix-side pocket family has exact rank `kappa * gadgetN`
whenever the coupling is positive and the local gadget has at least one
coordinate.  This removes one layer of opacity from the remaining compiler
polynomial target: the missing polynomial theorem can be stated as
`mlBlockedSpdpRank ... Q_v = kappa * gadgetN`. -/
theorem bridgeA_pocketFamily_rank_eq_kappa_mul_gadgetN
    (alpha : Real) (kappa gadgetN : Nat)
    (halpha : 0 < alpha) (hgadgetN : 1 <= gadgetN) :
    (PallLean.Paper93.DeepMath.BridgeB.pocketFamily alpha kappa gadgetN).rank =
      kappa * gadgetN := by
  rw [PallLean.Paper93.DeepMath.BridgeB.pocketFamily_rank]
  rw [PallLean.Paper93.DeepMath.PathB.compiledGadget_rank_full
    alpha gadgetN halpha hgadgetN]

/-- The Paper283 Cook-Levin pocket wrapper has the same exact normalized rank
as the underlying checked matrix pocket family. -/
theorem bridgeA_cookLevinPocketLocalGadget_rank_eq_kappa_mul_gadgetN {N : Nat}
    (alpha : Real) (kappa gadgetN : Nat) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 1 <= gadgetN) :
    ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v).rank =
      kappa * gadgetN := by
  simpa [cookLevinPocketLocalGadgetFamily, cookLevinPocketLocalGadget] using
    bridgeA_pocketFamily_rank_eq_kappa_mul_gadgetN
      alpha kappa gadgetN halpha hgadgetN

/-- The same normalized rank statement under the stronger `2 <= gadgetN`
condition used by most Bridge A interfaces. -/
theorem bridgeA_cookLevinPocketLocalGadget_rank_eq_kappa_mul_gadgetN_of_two
    {N : Nat} (alpha : Real) (kappa gadgetN : Nat) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN) :
    ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v).rank =
      kappa * gadgetN := by
  exact bridgeA_cookLevinPocketLocalGadget_rank_eq_kappa_mul_gadgetN
    alpha kappa gadgetN v halpha (by omega)

/-- A one-block partition on the empty local variable space. -/
noncomputable def bridgeAZeroPocketPartition : SPDP.BlockPartition 0 where
  numBlocks := 1
  assign := fun i => Fin.elim0 i

/-- The actual local polynomial used by the exact zero-pocket instantiation. -/
noncomputable def bridgeAZeroPocketPolynomial : MvPolynomial (Fin 0) Rat :=
  0

/-- In the zero-pocket case, the zero polynomial has exactly the checked
Cook-Levin pocket rank. -/
theorem bridgeA_zeroPocketPolynomial_rank_eq_pocket {N : Nat}
    (alpha : Real) (gadgetN : Nat) (v : Fin N) :
    mlBlockedSpdpRank bridgeAZeroPocketPartition 0 0
        bridgeAZeroPocketPolynomial =
      ((cookLevinPocketLocalGadgetFamily N alpha 0 gadgetN) v).rank := by
  rw [bridgeAZeroPocketPolynomial, mlBlockedSpdpRank_zero]
  simp [cookLevinPocketLocalGadgetFamily, cookLevinPocketLocalGadget,
    PallLean.Paper93.DeepMath.BridgeB.pocketFamily_rank]

/-- Exact per-vertex compiler SPDP data in the only currently available
polynomial-realized equality case: `kappa = 0`, `Q_v = 0`. -/
noncomputable def bridgeA_zeroPocket_perVertexCompilerSPDPData {N d : Nat}
    (alpha beta alpha0 : Real) (gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) :
    BridgeAPerVertexCompilerSPDPData
      alpha beta alpha0 0 gadgetN G chi Phi v where
  spdpVars := 0
  partition := bridgeAZeroPocketPartition
  Qv := bridgeAZeroPocketPolynomial
  rank_eq_pocket :=
    bridgeA_zeroPocketPolynomial_rank_eq_pocket alpha gadgetN v

/-- Exact family-level compiler SPDP data for the zero-pocket polynomial
realization. -/
noncomputable def bridgeA_zeroPocket_compilerSPDPFamilyData {N d : Nat}
    (alpha beta alpha0 : Real) (gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) :
    BridgeACompilerSPDPFamilyData
      alpha beta alpha0 0 gadgetN G chi Phi where
  spdpVars := fun _ => 0
  partition := fun _ => bridgeAZeroPocketPartition
  Qv := fun _ => bridgeAZeroPocketPolynomial
  rank_eq_pocket := fun v =>
    bridgeA_zeroPocketPolynomial_rank_eq_pocket alpha gadgetN v

/-! ## General polynomial frontier -/

/-- A concrete per-vertex local polynomial candidate, separated from the rank
equality theorem that is not currently exposed by the compiler. -/
structure BridgeAPerVertexLocalPolynomial {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) : Type where
  spdpVars : Nat
  partition : SPDP.BlockPartition spdpVars
  Qv : MvPolynomial (Fin spdpVars) Rat

/-- The exact remaining subgoal for a per-vertex polynomial candidate to become
`BridgeAPerVertexCompilerSPDPData`. -/
def BridgeAPerVertexLocalPolynomial.rankEqPocket {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real} {v : Fin N}
    (Q : BridgeAPerVertexLocalPolynomial
      alpha beta alpha0 kappa gadgetN G chi Phi v) : Prop :=
  mlBlockedSpdpRank Q.partition kappa kappa Q.Qv =
    ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v).rank

/-- The reduced per-vertex theorem: once the single rank equality is supplied
for an actual polynomial `Q_v`, it is exactly the existing compiler SPDP data. -/
noncomputable def bridgeA_perVertexCompilerSPDPData_of_localPolynomial
    {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real} {v : Fin N}
    (Q : BridgeAPerVertexLocalPolynomial
      alpha beta alpha0 kappa gadgetN G chi Phi v)
    (hrank : Q.rankEqPocket) :
    BridgeAPerVertexCompilerSPDPData
      alpha beta alpha0 kappa gadgetN G chi Phi v where
  spdpVars := Q.spdpVars
  partition := Q.partition
  Qv := Q.Qv
  rank_eq_pocket := hrank

/-! ## Normalized polynomial-rank target -/

/-- A concrete per-vertex local polynomial candidate with the rank target
already normalized to the exact matrix-side value `kappa * gadgetN`.

This is the sharper non-vacuous target after the matrix rank normalization
above.  It is still not a construction of the compiler's `Q_v`; it is the
smallest data package needed from that construction. -/
structure BridgeAPerVertexLocalPolynomialNormalized {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) : Type where
  spdpVars : Nat
  partition : SPDP.BlockPartition spdpVars
  Qv : MvPolynomial (Fin spdpVars) Rat
  rank_eq_normalized :
    mlBlockedSpdpRank partition kappa kappa Qv = kappa * gadgetN

/-- A normalized per-vertex local polynomial candidate upgrades to the exact
compiler SPDP data once the matrix-side pocket rank is normalized. -/
noncomputable def bridgeA_perVertexCompilerSPDPData_of_normalizedLocalPolynomial
    {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real} {v : Fin N}
    (Q : BridgeAPerVertexLocalPolynomialNormalized
      alpha beta alpha0 kappa gadgetN G chi Phi v)
    (halpha : 0 < alpha) (hgadgetN : 1 <= gadgetN) :
    BridgeAPerVertexCompilerSPDPData
      alpha beta alpha0 kappa gadgetN G chi Phi v where
  spdpVars := Q.spdpVars
  partition := Q.partition
  Qv := Q.Qv
  rank_eq_pocket := by
    rw [Q.rank_eq_normalized]
    rw [bridgeA_cookLevinPocketLocalGadget_rank_eq_kappa_mul_gadgetN
      alpha kappa gadgetN v halpha hgadgetN]

/-- Direct Bridge A SPDP-rank consequence of a normalized concrete local
polynomial.  This is the form the final compiler-local `Q_v` construction
should feed to the Route B transport layer. -/
theorem bridgeA_perVertex_spdpRank_lower_bound_of_normalizedLocalPolynomial
    {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real} {v : Fin N}
    (Q : BridgeAPerVertexLocalPolynomialNormalized
      alpha beta alpha0 kappa gadgetN G chi Phi v)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <= mlBlockedSpdpRank Q.partition kappa kappa Q.Qv := by
  exact bridgeA_perVertex_spdpRank_lower_bound_of_compilerData
    alpha beta alpha0 kappa gadgetN G chi Phi v halpha hgadgetN hE
    (bridgeA_perVertexCompilerSPDPData_of_normalizedLocalPolynomial
      Q halpha (by omega))

/-- Family-level concrete local polynomial candidates. -/
structure BridgeACompilerLocalPolynomialFamily {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) : Type where
  spdpVars : Fin N -> Nat
  partition : forall v : Fin N, SPDP.BlockPartition (spdpVars v)
  Qv : forall v : Fin N, MvPolynomial (Fin (spdpVars v)) Rat

/-- The exact remaining family-level subgoal: every concrete local polynomial
must have blocked SPDP rank equal to the checked Cook-Levin pocket rank at the
same vertex. -/
def BridgeACompilerLocalPolynomialFamily.rankEqPocket {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real}
    (Q : BridgeACompilerLocalPolynomialFamily
      alpha beta alpha0 kappa gadgetN G chi Phi) : Prop :=
  forall v : Fin N,
    mlBlockedSpdpRank (Q.partition v) kappa kappa (Q.Qv v) =
      ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v).rank

/-- The reduced family theorem: a concrete polynomial family plus exactly the
rank-equality subgoal yields the repository's existing compiler SPDP family
data. -/
noncomputable def bridgeA_compilerSPDPFamilyData_of_localPolynomialFamily
    {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real}
    (Q : BridgeACompilerLocalPolynomialFamily
      alpha beta alpha0 kappa gadgetN G chi Phi)
    (hrank : Q.rankEqPocket) :
    BridgeACompilerSPDPFamilyData
      alpha beta alpha0 kappa gadgetN G chi Phi where
  spdpVars := Q.spdpVars
  partition := Q.partition
  Qv := Q.Qv
  rank_eq_pocket := hrank

/-- Family-level concrete local polynomial candidates with the exact normalized
rank target `kappa * gadgetN` at every vertex. -/
structure BridgeACompilerLocalPolynomialFamilyNormalized {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) : Type where
  spdpVars : Fin N -> Nat
  partition : forall v : Fin N, SPDP.BlockPartition (spdpVars v)
  Qv : forall v : Fin N, MvPolynomial (Fin (spdpVars v)) Rat
  rank_eq_normalized :
    forall v : Fin N,
      mlBlockedSpdpRank (partition v) kappa kappa (Qv v) = kappa * gadgetN

/-- The normalized family target upgrades to the existing compiler SPDP family
data using the checked matrix-side pocket rank formula. -/
noncomputable def bridgeA_compilerSPDPFamilyData_of_normalizedLocalPolynomialFamily
    {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real}
    (Q : BridgeACompilerLocalPolynomialFamilyNormalized
      alpha beta alpha0 kappa gadgetN G chi Phi)
    (halpha : 0 < alpha) (hgadgetN : 1 <= gadgetN) :
    BridgeACompilerSPDPFamilyData
      alpha beta alpha0 kappa gadgetN G chi Phi where
  spdpVars := Q.spdpVars
  partition := Q.partition
  Qv := Q.Qv
  rank_eq_pocket := by
    intro v
    rw [Q.rank_eq_normalized v]
    rw [bridgeA_cookLevinPocketLocalGadget_rank_eq_kappa_mul_gadgetN
      alpha kappa gadgetN v halpha hgadgetN]

/-- Family-level direct Bridge A SPDP-rank consequence of normalized concrete
local polynomial data. -/
theorem bridgeA_family_spdpRank_lower_bound_of_normalizedLocalPolynomialFamily
    {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real}
    (Q : BridgeACompilerLocalPolynomialFamilyNormalized
      alpha beta alpha0 kappa gadgetN G chi Phi)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN)
    (v : Fin N)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <= mlBlockedSpdpRank (Q.partition v) kappa kappa (Q.Qv v) := by
  exact bridgeA_family_spdpRank_lower_bound
    alpha beta alpha0 kappa gadgetN G chi Phi halpha hgadgetN
    (bridgeA_compilerSPDPFamilyData_of_normalizedLocalPolynomialFamily
      Q halpha (by omega))
    v hE

/-! ## Axiom audit anchors -/

#print axioms bridgeA_zeroPocketPolynomial_rank_eq_pocket
#print axioms bridgeA_zeroPocket_perVertexCompilerSPDPData
#print axioms bridgeA_zeroPocket_compilerSPDPFamilyData
#print axioms bridgeA_pocketFamily_rank_eq_kappa_mul_gadgetN
#print axioms bridgeA_cookLevinPocketLocalGadget_rank_eq_kappa_mul_gadgetN
#print axioms bridgeA_perVertexCompilerSPDPData_of_localPolynomial
#print axioms bridgeA_compilerSPDPFamilyData_of_localPolynomialFamily
#print axioms bridgeA_perVertexCompilerSPDPData_of_normalizedLocalPolynomial
#print axioms bridgeA_compilerSPDPFamilyData_of_normalizedLocalPolynomialFamily
#print axioms bridgeA_perVertex_spdpRank_lower_bound_of_normalizedLocalPolynomial
#print axioms bridgeA_family_spdpRank_lower_bound_of_normalizedLocalPolynomialFamily

end PallLean.Paper93.Paper283
