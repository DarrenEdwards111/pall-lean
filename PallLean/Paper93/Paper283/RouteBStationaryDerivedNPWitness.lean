import PallLean.Paper93.Paper283.RouteBRicherGaugeReducedCertificate
import PallLean.Paper93.Paper283.PiStarFromStationarity
import PallLean.Paper93.DeepMath.PathB.EulerLagrangeStationarity

/-!
# Stationarity-derived Route B NP witnesses

This file separates the genuinely independent Route B NP-side target from the
older concrete Cook-Levin/Lemma 124 witness.

The existing Route B finite-row machinery already accepts an arbitrary coupled
sheet `Q` carrying a `SourceIdentityMinorLowerBound`.  The missing independent
Route B move is stricter: `Q` should be produced from an `S_NF` stationary
point, and its identity-minor lower bound should be proved for that derived
polynomial rather than imported from the flat compiled Cook-Levin witness.

The definitions below make that target explicit:

* `RouteBStationaryNFPoint` records the current paper §28.3 stationarity data;
* `RouteBStationaryDerivedSourceWitness` records a polynomial extractor from
  stationary data to a coupled sheet and requires a fresh source lower bound
  for the extracted sheet;
* the fixed-embed and finite-row constructors wire such a witness into the
  existing Route B transport package without mentioning the concrete
  `routeBRicherConcreteNPWitnessQ` or Lemma 124 constructor.

This is still not a construction of the final independent witness.  It is the
checked interface that the real stationary-polynomial construction and its new
identity-minor proof must inhabit.
-/

namespace PallLean.Paper93.Paper283

open Matrix
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GraphSpectral
open PallLean.Paper93.DeepMath.LPS

attribute [local instance] Classical.dec

/-- Route B normal-form stationary data in the current Paper283 vocabulary.

The `StationaryPhi` and `StationaryA` predicates are the active §28.3
interfaces.  Today they are still intentionally weak/stub-like; this structure
is nevertheless the right owner for a future stationary-polynomial extractor.
-/
structure RouteBStationaryNFPoint {N d : Nat}
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) : Type where
  Phi : Fin N -> Real
  A : Matrix (Fin N) (Fin N) Real
  stationary_phi : StationaryPhi (N := N) (d := d) alpha beta G chi Phi
  stationary_A : StationaryA lam A

/-- The current stationarity predicates still imply the active admissible-gauge
existence wrapper.  This theorem deliberately exposes that the present
`PiStarFromStationarity` file supplies only an admissible gauge, not yet a
stationarity-derived polynomial witness. -/
theorem routeBStationaryNFPoint_admissibleGauge_exists {N d : Nat}
    (alpha beta lam : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hlam : 0 < lam)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (point : RouteBStationaryNFPoint alpha beta lam G chi) :
    ∃ PiStar : PallLean.Paper93.NFrame.CandidateGauge N,
      PallLean.Paper93.NFrame.AdmissibleGauge PiStar :=
  piStar_exists_from_stationarity
    alpha beta lam halpha hbeta hlam G chi point.Phi point.A
    point.stationary_phi point.stationary_A

/-- The kinetic-only stationary datum from the round-1
`EulerLagrangeStationarity` file.  This is the algebraic first-variation part
of `S_NF`, separate from the nonsmooth sign and log-det terms. -/
structure RouteBKineticStationaryPoint (alpha : Real) (N : Nat) : Type where
  Phi : Fin N -> Real
  gradient_zero : ∀ i, kineticTerm_partialDeriv alpha N i Phi = 0

/-- Round-1 Euler-Lagrange stationarity gives the expected Laplacian-kernel
condition for the kinetic term. -/
theorem routeBKineticStationaryPoint_laplacian_kernel
    (alpha : Real) (N : Nat) (halpha : alpha ≠ 0)
    (point : RouteBKineticStationaryPoint alpha N) :
    (laplacian (completeAdj N)).mulVec point.Phi = 0 :=
  (kineticTerm_grad_zero_iff_kernel alpha N halpha point.Phi).1
    point.gradient_zero

/-- A polynomial extractor from §28.3 stationary data to the SAT-decider
coupled sheet.  The independent Route B theorem still needs an actual
definition of this map. -/
abbrev RouteBStationaryCoupledSheetExtractor {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) : Type :=
  RouteBStationaryNFPoint alpha beta lam G chi ->
    CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns)

/-- A source-side NP witness genuinely owned by Route B stationarity.

The field `non_flat_compiled_witness` prevents this certificate from being the
old flat identity sanity case in disguise: the embedded stationary sheet is
required not to be the raw Cook-Levin `compiledPoly`.  The lower-bound field is
the new independent identity-minor theorem that remains to be proved for the
chosen stationary extractor. -/
structure RouteBStationaryDerivedSourceWitness {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi) : Type where
  point : RouteBStationaryNFPoint alpha beta lam G chi
  Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns)
  derived_eq : extractor point = Q
  non_flat_compiled_witness :
    CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q ≠
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
  independent_source_lower_bound :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) Q

/-- The stationary-derived witness exposes the source lower bound for the
actual extractor output. -/
theorem routeBStationaryDerivedSourceWitness_lower_bound_for_extractor {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    (w :
      RouteBStationaryDerivedSourceWitness M n hn2 htb hns
        alpha beta lam G chi extractor) :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) (extractor w.point) := by
  rw [w.derived_eq]
  exact w.independent_source_lower_bound

/-- Fixed-embed certificate whose source obstruction is explicitly derived
from Route B stationary data, not from the concrete Lemma 124 witness. -/
structure RouteBStationaryDerivedNPFixedEmbedCertificate {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Type where
  source :
    RouteBStationaryDerivedSourceWitness M n hn2 htb hns
      alpha beta lam G chi extractor
  fixed_embed :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) source.Q) =
      CoupledSheetPoly.embed
        (flatCookLevinUVSplit M n hn2 htb hns) source.Q
  extracts_compiled :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) source.Q)

/-- Forgetting the stationarity provenance gives the existing fixed-embed
Route B NP certificate.  The source lower bound used here is the
stationarity-derived one carried by the certificate. -/
noncomputable def routeBNPIdentityMinorFixedEmbedCertificate_of_stationaryDerived
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (cert :
      RouteBStationaryDerivedNPFixedEmbedCertificate M n hn2 htb hns
        alpha beta lam G chi extractor Pi) :
    RouteBNPIdentityMinorFixedEmbedCertificate M n hn2 htb hns Pi where
  Q := cert.source.Q
  fixed_embed := cert.fixed_embed
  extracts_compiled := cert.extracts_compiled
  source_lower_bound := cert.source.independent_source_lower_bound

/-- A stationarity-derived fixed-embed certificate supplies the projected
NP identity-minor field required by Route B. -/
theorem routeBSATProjectedNPIdentityMinorLowerBound_of_stationaryDerived
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (cert :
      RouteBStationaryDerivedNPFixedEmbedCertificate M n hn2 htb hns
        alpha beta lam G chi extractor Pi) :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_certificate
    M n hn2 htb hns Pi
    (routeBNPIdentityMinorFixedEmbedCertificate_of_stationaryDerived
      M n hn2 htb hns alpha beta lam G chi extractor Pi cert)

/-- Primitive transport constructor for the independent Route B NP source. -/
theorem routeBFunctorialTransportCertificate_of_stationaryDerivedNP
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (himage :
      SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi))
    (hpside :
      RouteBSATUnprojectedPSideRankBound M n hn2 htb hns)
    (cert :
      RouteBStationaryDerivedNPFixedEmbedCertificate M n hn2 htb hns
        alpha beta lam G chi extractor Pi) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns Pi :=
  routeBFunctorialTransportCertificate_of_npIdentityMinorFixedEmbedCertificate
    M n hn2 htb hns Pi himage hpside
    (routeBNPIdentityMinorFixedEmbedCertificate_of_stationaryDerived
      M n hn2 htb hns alpha beta lam G chi extractor Pi cert)

/-- Finite-row Route B constructor using a stationarity-derived source witness.

This is the finite-span analogue of the existing concrete one-row constructor,
but its NP source is the extracted stationary polynomial `source.Q` and its
lower bound is `source.independent_source_lower_bound`. -/
theorem routeBRicherFiniteRowsCandidateGauge_transportCertificate_of_stationaryDerived
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (source :
      RouteBStationaryDerivedSourceWitness M n hn2 htb hns
        alpha beta lam G chi extractor)
    (i : Fin m)
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns)
          source.Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) source.Q)) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) :=
  routeBRicherFiniteRowsCandidateGauge_transportCertificate
    M n hn2 htb hns rows hcontain cover source.Q i hrow hextract
    source.independent_source_lower_bound

/-! ## Axiom audit anchors -/

#print axioms routeBStationaryNFPoint_admissibleGauge_exists
#print axioms routeBKineticStationaryPoint_laplacian_kernel
#print axioms routeBStationaryDerivedSourceWitness_lower_bound_for_extractor
#print axioms routeBNPIdentityMinorFixedEmbedCertificate_of_stationaryDerived
#print axioms routeBSATProjectedNPIdentityMinorLowerBound_of_stationaryDerived
#print axioms routeBFunctorialTransportCertificate_of_stationaryDerivedNP
#print axioms routeBRicherFiniteRowsCandidateGauge_transportCertificate_of_stationaryDerived

end PallLean.Paper93.Paper283
