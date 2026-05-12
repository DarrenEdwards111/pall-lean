import PallLean.Paper93.Paper283.RouteBStationaryDerivedNPWitness
import PallLean.Paper93.Paper283.RouteBIndependentSourceLowerBound
import PallLean.Paper93.Paper283.RouteBMonomialProductSourceWitness

/-!
# Assembling independent source lower bounds into stationary Route B witnesses

`RouteBStationaryDerivedNPWitness` isolates the desired independent Route B
source witness:

  stationary point -> derived coupled sheet `Q` -> source identity-minor lower
  bound for `Q`.

`RouteBIndependentSourceLowerBound` isolates the generic Tseitin/identity-minor
bridge that can provide the source lower bound without using the concrete
Cook-Levin Lemma 124 witness.

This file connects the two surfaces.  Once a concrete stationary extractor and
generic-to-coupled-sheet bridge are supplied for its output, the result is an
actual `RouteBStationaryDerivedSourceWitness` that can be consumed by the
Route B transport constructors.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- Certificate that a stationary extractor output has an independent
identity-minor lower bound, phrased at the exact flat Cook-Levin source
surface used by Route B. -/
structure RouteBStationaryIndependentSourceCertificate {N d : Nat}
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
  independent_certificate :
    IndependentCoupledSheetSourceLowerBoundCertificate n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) Q

/-- The independent source certificate gives the source lower bound for the
stationarity-derived polynomial. -/
theorem sourceIdentityMinorLowerBound_of_stationaryIndependentCertificate
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    (cert :
      RouteBStationaryIndependentSourceCertificate M n hn2 htb hns
        alpha beta lam G chi extractor) :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) cert.Q :=
  sourceIdentityMinorLowerBound_of_independentCertificate
    n (flatCookLevinUVSplit M n hn2 htb hns)
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n) cert.Q
    cert.independent_certificate

/-- Turn an independent stationary source certificate into the exact
`RouteBStationaryDerivedSourceWitness` consumed by the Route B NP transport
surface. -/
noncomputable def routeBStationaryDerivedSourceWitness_of_independentCertificate
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    (cert :
      RouteBStationaryIndependentSourceCertificate M n hn2 htb hns
        alpha beta lam G chi extractor) :
    RouteBStationaryDerivedSourceWitness M n hn2 htb hns
      alpha beta lam G chi extractor where
  point := cert.point
  Q := cert.Q
  derived_eq := cert.derived_eq
  non_flat_compiled_witness := cert.non_flat_compiled_witness
  independent_source_lower_bound :=
    sourceIdentityMinorLowerBound_of_stationaryIndependentCertificate
      M n hn2 htb hns alpha beta lam G chi extractor cert

/-- Direct lower-bound statement for the extractor output. -/
theorem sourceIdentityMinorLowerBound_for_extractor_of_stationaryIndependentCertificate
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    (cert :
      RouteBStationaryIndependentSourceCertificate M n hn2 htb hns
        alpha beta lam G chi extractor) :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) (extractor cert.point) := by
  rw [cert.derived_eq]
  exact
    sourceIdentityMinorLowerBound_of_stationaryIndependentCertificate
      M n hn2 htb hns alpha beta lam G chi extractor cert

/-! ## Axiom audit anchors -/

#print axioms sourceIdentityMinorLowerBound_of_stationaryIndependentCertificate
#print axioms routeBStationaryDerivedSourceWitness_of_independentCertificate
#print axioms sourceIdentityMinorLowerBound_for_extractor_of_stationaryIndependentCertificate

/-! ## Direct source-lower-bound certificates

The generic Tseitin bridge above is one way to supply the independent source
lower bound.  Some Route B candidates, such as the monomial-product source
witness, prove the source lower bound directly.  The next certificate keeps
that route available without forcing it through the generic Tseitin bridge.
-/

/-- Direct stationary source certificate: an extractor output plus an
independent source lower bound for that exact output. -/
structure RouteBStationaryDirectSourceCertificate {N d : Nat}
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
  source_lower_bound :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) Q

/-- A direct source certificate is already the stationary-derived source
witness expected by the Route B NP transport surface. -/
noncomputable def routeBStationaryDerivedSourceWitness_of_directCertificate
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    (cert :
      RouteBStationaryDirectSourceCertificate M n hn2 htb hns
        alpha beta lam G chi extractor) :
    RouteBStationaryDerivedSourceWitness M n hn2 htb hns
      alpha beta lam G chi extractor where
  point := cert.point
  Q := cert.Q
  derived_eq := cert.derived_eq
  non_flat_compiled_witness := cert.non_flat_compiled_witness
  independent_source_lower_bound := cert.source_lower_bound

/-- Direct lower-bound statement for a stationary extractor from a direct
source certificate. -/
theorem sourceIdentityMinorLowerBound_for_extractor_of_directCertificate
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    (cert :
      RouteBStationaryDirectSourceCertificate M n hn2 htb hns
        alpha beta lam G chi extractor) :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) (extractor cert.point) := by
  rw [cert.derived_eq]
  exact cert.source_lower_bound

/-! ## Monomial-product stationary source candidate

The spaced monomial product is a concrete non-compiled source candidate with
its source lower bound now proved in `RouteBMonomialProductSourceWitness`.  This
certificate says exactly what remains to make it stationary-derived: the
extractor must actually output that monomial at the chosen stationary point,
and the embedded monomial must be non-flat relative to the compiled polynomial.
-/

/-- Stationary certificate specialized to the monomial-product Route B source
candidate. -/
structure RouteBStationaryMonomialProductCertificate {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi) : Type where
  point : RouteBStationaryNFPoint alpha beta lam G chi
  derived_eq :
    extractor point =
      RouteBMonomialProductSourceWitness.spacedMonomialProduct M n hn2 htb hns
  non_flat_compiled_witness :
    CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns)
        (RouteBMonomialProductSourceWitness.spacedMonomialProduct
          M n hn2 htb hns) ≠
      compiledPoly (cook_levin_compilation M n hn2 htb hns)

/-- The monomial-product certificate supplies the direct source lower-bound
certificate for the stationary Route B witness surface. -/
noncomputable def routeBStationaryDirectSourceCertificate_of_monomialProduct
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    (cert :
      RouteBStationaryMonomialProductCertificate M n hn2 htb hns
        alpha beta lam G chi extractor) :
    RouteBStationaryDirectSourceCertificate M n hn2 htb hns
      alpha beta lam G chi extractor where
  point := cert.point
  Q := RouteBMonomialProductSourceWitness.spacedMonomialProduct M n hn2 htb hns
  derived_eq := cert.derived_eq
  non_flat_compiled_witness := cert.non_flat_compiled_witness
  source_lower_bound := by
    simpa [
      RouteBMonomialProductSourceWitness.flatSplit,
      RouteBMonomialProductSourceWitness.cookPartition
    ] using
      RouteBMonomialProductSourceWitness.sourceIdentityMinorLowerBound_spacedMonomialProduct
        M n hn2 htb hns

/-- The monomial-product certificate is directly consumable by the stationary
Route B source witness interface. -/
noncomputable def routeBStationaryDerivedSourceWitness_of_monomialProduct
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta lam : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N)
    (extractor :
      RouteBStationaryCoupledSheetExtractor M n hn2 htb hns
        alpha beta lam G chi)
    (cert :
      RouteBStationaryMonomialProductCertificate M n hn2 htb hns
        alpha beta lam G chi extractor) :
    RouteBStationaryDerivedSourceWitness M n hn2 htb hns
      alpha beta lam G chi extractor :=
  routeBStationaryDerivedSourceWitness_of_directCertificate
    M n hn2 htb hns alpha beta lam G chi extractor
    (routeBStationaryDirectSourceCertificate_of_monomialProduct
      M n hn2 htb hns alpha beta lam G chi extractor cert)

/-! ## Axiom audit anchors for direct and monomial routes -/

#print axioms routeBStationaryDerivedSourceWitness_of_directCertificate
#print axioms sourceIdentityMinorLowerBound_for_extractor_of_directCertificate
#print axioms routeBStationaryDirectSourceCertificate_of_monomialProduct
#print axioms routeBStationaryDerivedSourceWitness_of_monomialProduct

end PallLean.Paper93.Paper283
