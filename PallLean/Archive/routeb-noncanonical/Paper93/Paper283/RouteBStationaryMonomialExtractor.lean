import PallLean.Paper93.Paper283.RouteBStationaryIndependentAssembly
import PallLean.Paper93.Paper283.RouteBMonomialProductNonFlat

/-!
# Stationary monomial-product extractor

This module packages the already-proved monomial-product source witness as a
stationarity-derived extractor target.  The extractor is the current honest
stationary interface map: the available `RouteBStationaryNFPoint` fields do not
yet determine rational coefficients, so the extracted sheet is the fixed
spaced monomial product from `RouteBMonomialProductSourceWitness`.

The source lower bound is proved by the monomial-product theorem, and exact
non-flatness against the raw compiled Cook-Levin polynomial is discharged by a
coefficient comparison.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

namespace RouteBStationaryMonomialExtractor

/-- The stationary monomial extractor output, named at the Route B stationary
surface. -/
noncomputable def stationarySpacedMonomialQ
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns) :=
  RouteBMonomialProductSourceWitness.spacedMonomialProduct M n hn2 htb hns

/-- A stationary-data extractor whose output is the spaced monomial product. -/
noncomputable def stationarySpacedMonomialExtractor {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) :
    RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
      alpha beta lam G chi :=
  fun _point => stationarySpacedMonomialQ M n hn2 htb hns

/-- The extractor is definitionally the monomial-product source witness. -/
theorem stationarySpacedMonomialExtractor_derived_eq {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (point : RouteBStationaryNFPoint alpha beta lam G chi) :
    stationarySpacedMonomialExtractor M n hn2 htb hns alpha beta lam G chi point =
      RouteBMonomialProductSourceWitness.spacedMonomialProduct
        M n hn2 htb hns := by
  rfl

/-- The precise remaining non-flatness field for the stationary monomial
extractor. -/
def StationarySpacedMonomialNonFlat
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns)
      (stationarySpacedMonomialQ M n hn2 htb hns) ≠
    compiledPoly (cook_levin_compilation M n hn2 htb hns)

/-- The independently proved monomial-product source is genuinely not the raw
Cook-Levin compiled polynomial. -/
theorem stationarySpacedMonomialNonFlat
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    StationarySpacedMonomialNonFlat M n hn2 htb hns := by
  simpa [StationarySpacedMonomialNonFlat, stationarySpacedMonomialQ] using
    RouteBMonomialProductNonFlat.embed_spacedMonomialProduct_ne_compiledPoly
      M n hn2 htb hns

/-- The source lower bound for the stationary monomial extractor output. -/
theorem sourceIdentityMinorLowerBound_stationarySpacedMonomialQ
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (stationarySpacedMonomialQ M n hn2 htb hns) := by
  simpa [
    stationarySpacedMonomialQ,
    RouteBMonomialProductSourceWitness.flatSplit,
    RouteBMonomialProductSourceWitness.cookPartition
  ] using
    RouteBMonomialProductSourceWitness.sourceIdentityMinorLowerBound_spacedMonomialProduct
      M n hn2 htb hns

/-- The same lower bound, rewritten onto the extractor output at any
stationary point. -/
theorem sourceIdentityMinorLowerBound_stationarySpacedMonomialExtractor {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (point : RouteBStationaryNFPoint alpha beta lam G chi) :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (stationarySpacedMonomialExtractor
        M n hn2 htb hns alpha beta lam G chi point) := by
  rw [stationarySpacedMonomialExtractor_derived_eq
    M n hn2 htb hns alpha beta lam G chi point]
  exact sourceIdentityMinorLowerBound_stationarySpacedMonomialQ M n hn2 htb hns

/-- The closure certificate for the stationary monomial extractor.  Under the
current stationary API, a point is the only data still needed; the
monomial-product lower bound and non-flatness are proved separately. -/
structure StationarySpacedMonomialExtractorCertificate {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) : Type where
  point : RouteBStationaryNFPoint alpha beta lam G chi

/-- Convert the stationary monomial extractor certificate to the existing
monomial-product stationary source certificate. -/
noncomputable def stationaryMonomialProductCertificate
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (cert :
      StationarySpacedMonomialExtractorCertificate
        M n hn2 htb hns alpha beta lam G chi) :
    RouteBStationaryMonomialProductCertificate M n hn2 htb hns
      alpha beta lam G chi
      (stationarySpacedMonomialExtractor
        M n hn2 htb hns alpha beta lam G chi) where
  point := cert.point
  derived_eq :=
    stationarySpacedMonomialExtractor_derived_eq
      M n hn2 htb hns alpha beta lam G chi cert.point
  non_flat_compiled_witness := by
    simpa [StationarySpacedMonomialNonFlat, stationarySpacedMonomialQ] using
      stationarySpacedMonomialNonFlat M n hn2 htb hns

/-- The stationary monomial extractor gives a full
`RouteBStationaryDerivedSourceWitness` once the exact non-flatness field is
supplied.  Its lower bound is the proved
`sourceIdentityMinorLowerBound_spacedMonomialProduct`, not Lemma 124. -/
noncomputable def stationarySpacedMonomialDerivedSourceWitness
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (cert :
      StationarySpacedMonomialExtractorCertificate
        M n hn2 htb hns alpha beta lam G chi) :
    RouteBStationaryDerivedSourceWitness M n hn2 htb hns
      alpha beta lam G chi
      (stationarySpacedMonomialExtractor
        M n hn2 htb hns alpha beta lam G chi) :=
  routeBStationaryDerivedSourceWitness_of_monomialProduct
    M n hn2 htb hns alpha beta lam G chi
    (stationarySpacedMonomialExtractor
      M n hn2 htb hns alpha beta lam G chi)
    (stationaryMonomialProductCertificate
      M n hn2 htb hns alpha beta lam G chi cert)

/-! ## Axiom audit anchors -/

#print axioms stationarySpacedMonomialExtractor_derived_eq
#print axioms stationarySpacedMonomialNonFlat
#print axioms sourceIdentityMinorLowerBound_stationarySpacedMonomialQ
#print axioms sourceIdentityMinorLowerBound_stationarySpacedMonomialExtractor
#print axioms stationaryMonomialProductCertificate
#print axioms stationarySpacedMonomialDerivedSourceWitness

end RouteBStationaryMonomialExtractor
end PallLean.Paper93.Paper283
