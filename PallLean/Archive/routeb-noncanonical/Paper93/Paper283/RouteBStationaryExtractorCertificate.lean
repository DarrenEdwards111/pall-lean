import PallLean.Paper93.Paper283.RouteBStationaryDerivedNPWitness
import PallLean.Paper93.Paper283.RouteBIndependentSourceLowerBound

/-!
# Stationary extractor certificate surface

The current §28.3 stationary point interface provides `Phi`, `A`, and the
active `StationaryPhi`/`StationaryA` predicates.  That is not enough data to
define the independent Route B source polynomial: no existing stationarity file
constructs a coupled sheet, proves that it is not the flat `compiledPoly`, or
transports the Tseitin identity-minor lower bound to that sheet.

This module records the honest closure surface.  A future stationary
polynomial construction must supply the fields below; once it does, the
standard `RouteBStationaryDerivedSourceWitness` follows without using the
concrete Cook-Levin/Lemma124 source witness.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- Exact data still missing from the current stationary files for an
independent Route B source polynomial.

The `identity_minor_bridge` field is intentionally the independent
Tseitin-to-coupled-sheet bridge, not a raw invocation of the compiled-polynomial
lower bound.  It expands to the generic Tseitin formula/packing, the arithmetic
target comparison, and the rank transport to the chosen stationary sheet. -/
structure RouteBStationaryExtractorClosureCertificate {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) : Type where
  extractor :
    RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
      alpha beta lam G chi
  point : RouteBStationaryNFPoint alpha beta lam G chi
  Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns)
  derived_eq : extractor point = Q
  non_flat_compiled_witness :
    CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q ≠
      compiledPoly (cook_levin_compilation M n hn2 htb hns)
  identity_minor_bridge :
    GenericTseitinIdentityMinorToCoupledSheetBridge n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) Q

/-- The closure certificate supplies the independent source lower bound for
the named stationary sheet. -/
theorem sourceIdentityMinorLowerBound_of_stationaryExtractorClosure
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (cert :
      RouteBStationaryExtractorClosureCertificate M n hn2 htb hns
        alpha beta lam G chi) :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) cert.Q :=
  sourceIdentityMinorLowerBound_of_genericTseitinBridge
    n (flatCookLevinUVSplit M n hn2 htb hns)
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n) cert.Q
    cert.identity_minor_bridge

/-- The same lower bound, rewritten onto the actual extractor output. -/
theorem sourceIdentityMinorLowerBound_for_stationaryExtractorOutput
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (cert :
      RouteBStationaryExtractorClosureCertificate M n hn2 htb hns
        alpha beta lam G chi) :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) (cert.extractor cert.point) := by
  rw [cert.derived_eq]
  exact
    sourceIdentityMinorLowerBound_of_stationaryExtractorClosure
      M n hn2 htb hns alpha beta lam G chi cert

/-- Once the exact closure fields are supplied, they assemble into the existing
stationarity-derived Route B source witness.  This constructor is only a
transport step; it does not manufacture the extractor or its lower bound. -/
noncomputable def routeBStationaryDerivedSourceWitness_of_extractorClosure
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (cert :
      RouteBStationaryExtractorClosureCertificate M n hn2 htb hns
        alpha beta lam G chi) :
    RouteBStationaryDerivedSourceWitness M n hn2 htb hns
      alpha beta lam G chi cert.extractor where
  point := cert.point
  Q := cert.Q
  derived_eq := cert.derived_eq
  non_flat_compiled_witness := cert.non_flat_compiled_witness
  independent_source_lower_bound :=
    sourceIdentityMinorLowerBound_of_stationaryExtractorClosure
      M n hn2 htb hns alpha beta lam G chi cert

/-! ## Axiom audit anchors -/

#print axioms sourceIdentityMinorLowerBound_of_stationaryExtractorClosure
#print axioms sourceIdentityMinorLowerBound_for_stationaryExtractorOutput
#print axioms routeBStationaryDerivedSourceWitness_of_extractorClosure

end PallLean.Paper93.Paper283
