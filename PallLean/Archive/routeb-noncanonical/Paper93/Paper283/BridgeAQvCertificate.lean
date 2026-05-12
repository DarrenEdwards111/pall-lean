import PallLean.Paper93.Paper283.BridgeASquareHelperExact

/-!
# Explicit Bridge A `Q_v` certificates

This file adds a polynomial-facing Bridge A certificate surface:

`alpha0 <= E_v(Phi) -> kappa <= mlBlockedSpdpRank partition kappa kappa Qv`.

The currently exposed Cook-Levin pocket object is still the rank-carrying
`LocalGadget` / `pocketFamily` surface.  The structures below separate the
literal polynomial data `(spdpVars, partition, Qv)` from the additional
identification needed to connect that polynomial to the checked pocket rank.

The square-helper instantiation is an exact certificate for the concrete
polynomial `squareHelperQ`.  It is also identified with the currently exposed
Cook-Levin pocket rank through the normalized rank equality
`mlBlockedSpdpRank ... squareHelperQ = kappa * gadgetN`.  This is not a claim
that the full Cook-Levin compiler has been refactored to emit `squareHelperQ`
as its literal local output.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP

/-- A per-vertex polynomial `Q_v` certificate for the Bridge A rank conclusion.

This is the direct kernel surface for the paper statement at one vertex: after
the local energy trigger is supplied, the named polynomial has blocked SPDP
rank at least `kappa`. -/
structure BridgeAPerVertexQvCertificate {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) : Type where
  spdpVars : Nat
  partition : SPDP.BlockPartition spdpVars
  Qv : MvPolynomial (Fin spdpVars) Rat
  spdpRank_lower_bound :
    alpha0 <= localEnergy alpha beta G chi Phi v ->
      kappa <= mlBlockedSpdpRank partition kappa kappa Qv

/-- Consume a per-vertex `Q_v` certificate to obtain the Bridge A SPDP-rank
implication. -/
theorem bridgeA_qv_spdpRank_lower_bound {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real} {v : Fin N}
    (cert :
      BridgeAPerVertexQvCertificate
        alpha beta alpha0 kappa gadgetN G chi Phi v)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <= mlBlockedSpdpRank cert.partition kappa kappa cert.Qv :=
  cert.spdpRank_lower_bound hE

/-- The exact data needed to identify a named polynomial `Q_v` with the
currently exposed Cook-Levin pocket rank at the same vertex. -/
structure BridgeAPerVertexQvPocketIdentification {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) : Type where
  spdpVars : Nat
  partition : SPDP.BlockPartition spdpVars
  Qv : MvPolynomial (Fin spdpVars) Rat
  rank_eq_pocket :
    mlBlockedSpdpRank partition kappa kappa Qv =
      ((cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN) v).rank

/-- A `Q_v`/pocket rank identification is exactly the older compiler-SPDP data
surface, with the polynomial fields made explicit. -/
noncomputable def bridgeA_perVertexCompilerSPDPData_of_qvPocketIdentification
    {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real} {v : Fin N}
    (data :
      BridgeAPerVertexQvPocketIdentification
        alpha beta alpha0 kappa gadgetN G chi Phi v) :
    BridgeAPerVertexCompilerSPDPData
      alpha beta alpha0 kappa gadgetN G chi Phi v where
  spdpVars := data.spdpVars
  partition := data.partition
  Qv := data.Qv
  rank_eq_pocket := data.rank_eq_pocket

/-- From an explicit `Q_v`/pocket identification, the checked Cook-Levin pocket
rank theorem gives the desired Bridge A SPDP-rank implication for that
polynomial. -/
theorem bridgeA_qv_spdpRank_lower_bound_of_pocketIdentification {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN)
    (data :
      BridgeAPerVertexQvPocketIdentification
        alpha beta alpha0 kappa gadgetN G chi Phi v)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <= mlBlockedSpdpRank data.partition kappa kappa data.Qv :=
  bridgeA_perVertex_spdpRank_lower_bound_of_compilerData
    alpha beta alpha0 kappa gadgetN G chi Phi v halpha hgadgetN hE
    (bridgeA_perVertexCompilerSPDPData_of_qvPocketIdentification data)

/-- A normalized polynomial identification: the blocked SPDP rank of `Q_v` is
the exact matrix-side target `kappa * gadgetN`. -/
structure BridgeAPerVertexQvNormalizedIdentification {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) : Type where
  spdpVars : Nat
  partition : SPDP.BlockPartition spdpVars
  Qv : MvPolynomial (Fin spdpVars) Rat
  rank_eq_normalized :
    mlBlockedSpdpRank partition kappa kappa Qv = kappa * gadgetN

/-- A normalized polynomial rank equality already implies the Bridge A
rank-lower-bound conclusion when the local gadget has at least two
coordinates.  The energy hypothesis is the Bridge A trigger; this numerical
consequence uses only the exact rank equality. -/
theorem bridgeA_qv_spdpRank_lower_bound_of_normalizedIdentification
    {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real} {v : Fin N}
    (data :
      BridgeAPerVertexQvNormalizedIdentification
        alpha beta alpha0 kappa gadgetN G chi Phi v)
    (hgadgetN : 2 <= gadgetN)
    (_hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <= mlBlockedSpdpRank data.partition kappa kappa data.Qv := by
  rw [data.rank_eq_normalized]
  exact Nat.le_mul_of_pos_right kappa (by omega)

/-- Build the direct `Q_v` certificate from a normalized polynomial
identification. -/
noncomputable def bridgeA_qvCertificate_of_normalizedIdentification
    {N d : Nat}
    {alpha beta alpha0 : Real} {kappa gadgetN : Nat}
    {G : PallLean.Paper93.Concrete.RegularGraphFixed N d}
    {chi : TseitinCharge N} {Phi : Fin N -> Real} {v : Fin N}
    (data :
      BridgeAPerVertexQvNormalizedIdentification
        alpha beta alpha0 kappa gadgetN G chi Phi v)
    (hgadgetN : 2 <= gadgetN) :
    BridgeAPerVertexQvCertificate
      alpha beta alpha0 kappa gadgetN G chi Phi v where
  spdpVars := data.spdpVars
  partition := data.partition
  Qv := data.Qv
  spdpRank_lower_bound :=
    bridgeA_qv_spdpRank_lower_bound_of_normalizedIdentification
      data hgadgetN

/-! ## Exact square-helper instantiation -/

namespace BridgeAGeneralizedNonzeroWitness

/-- The square-helper polynomial as an explicit normalized `Q_v`
identification. -/
noncomputable def squareHelper_qvNormalizedIdentification
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) :
    BridgeAPerVertexQvNormalizedIdentification
      alpha beta alpha0 kappa gadgetN G chi Phi v where
  spdpVars := squareHelperVarCount kappa gadgetN
  partition := discretePartition (squareHelperVarCount kappa gadgetN)
  Qv := squareHelperQ kappa gadgetN
  rank_eq_normalized := squareHelperExactRankTarget_closed kappa gadgetN

/-- The square-helper polynomial as a direct Bridge A `Q_v` certificate. -/
noncomputable def squareHelper_qvCertificate
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (hgadgetN : 2 <= gadgetN) :
    BridgeAPerVertexQvCertificate
      alpha beta alpha0 kappa gadgetN G chi Phi v :=
  bridgeA_qvCertificate_of_normalizedIdentification
    (squareHelper_qvNormalizedIdentification
      alpha beta alpha0 kappa gadgetN G chi Phi v)
    hgadgetN

/-- Pointwise Bridge A rank implication for the explicit square-helper
polynomial `Q_v = squareHelperQ kappa gadgetN`. -/
theorem squareHelper_qv_spdpRank_lower_bound
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (hgadgetN : 2 <= gadgetN)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <=
      mlBlockedSpdpRank
        (discretePartition (squareHelperVarCount kappa gadgetN))
        kappa kappa (squareHelperQ kappa gadgetN) := by
  exact
    bridgeA_qv_spdpRank_lower_bound
      (squareHelper_qvCertificate
        alpha beta alpha0 kappa gadgetN G chi Phi v hgadgetN)
      hE

/-- The square-helper polynomial identified with the currently exposed
Cook-Levin pocket rank.  This is a rank identification for the candidate
polynomial, not a literal compiler-output theorem. -/
noncomputable def squareHelper_qvPocketIdentification
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 1 <= gadgetN) :
    BridgeAPerVertexQvPocketIdentification
      alpha beta alpha0 kappa gadgetN G chi Phi v where
  spdpVars := squareHelperVarCount kappa gadgetN
  partition := discretePartition (squareHelperVarCount kappa gadgetN)
  Qv := squareHelperQ kappa gadgetN
  rank_eq_pocket := by
    rw [squareHelperExactRankTarget_closed kappa gadgetN]
    rw [bridgeA_cookLevinPocketLocalGadget_rank_eq_kappa_mul_gadgetN
      alpha kappa gadgetN v halpha hgadgetN]

/-- The same square-helper Bridge A implication routed through the explicit
`Q_v`/pocket-rank identification surface. -/
theorem squareHelper_qv_spdpRank_lower_bound_via_pocketIdentification
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
    bridgeA_qv_spdpRank_lower_bound_of_pocketIdentification
      alpha beta alpha0 kappa gadgetN G chi Phi v halpha hgadgetN
      (squareHelper_qvPocketIdentification
        alpha beta alpha0 kappa gadgetN G chi Phi v halpha (by omega))
      hE

/-! ## Axiom audit anchors -/

#print axioms bridgeA_qv_spdpRank_lower_bound
#print axioms bridgeA_perVertexCompilerSPDPData_of_qvPocketIdentification
#print axioms bridgeA_qv_spdpRank_lower_bound_of_pocketIdentification
#print axioms bridgeA_qv_spdpRank_lower_bound_of_normalizedIdentification
#print axioms bridgeA_qvCertificate_of_normalizedIdentification
#print axioms squareHelper_qvNormalizedIdentification
#print axioms squareHelper_qvCertificate
#print axioms squareHelper_qv_spdpRank_lower_bound
#print axioms squareHelper_qvPocketIdentification
#print axioms squareHelper_qv_spdpRank_lower_bound_via_pocketIdentification

end BridgeAGeneralizedNonzeroWitness

end PallLean.Paper93.Paper283
