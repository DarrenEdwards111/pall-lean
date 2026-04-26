import PallLean.Paper93.Paper283.RouteBRicherGaugeFiniteRowsConcreteAssembly
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPConcreteCoefficients

/-!
# Finite-row SPDP frontier for the corrected Route B gauge

This module packages the corrected finite-row SPDP containment route into
named obligations.  The SPDP generator check is deliberately split into two
independent pieces:

* finite-row closure: every projected generator is a linear combination of
  the selected finite rows;
* unprojected preimage: the same generator already belongs to the raw
  Cook--Levin SPDP subspace for the original polynomial.

The combined frontier is then converted back to the existing checked
finite-row assembly surface.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Finite-row closure for Route B SPDP generator rows.

This is only the row-span part of the corrected containment check: after the
finite-row candidate projection is applied to the base polynomial, every
resulting SPDP generator row must be expressible as a finite linear
combination of the selected rows. -/
structure RouteBRicherGaugeFiniteRowsSPDPClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Prop where
  finite_row_closure :
    forall (spdpKappa ell : Nat)
      (p : SATDeciderGaugeSpace M n hn2 htb hns)
      (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (shift : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = spdpKappa ->
      shift.totalDegree <= ell ->
      shift.vars <= S.toFinset ->
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S ->
      ∃ coeff : Fin m -> Rat,
        routeBSPDPGeneratorRow M n hn2 htb hns
            ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (routeBRicherFiniteRowsCandidateGauge
                M n hn2 htb hns rows)) p)
            S shift =
          Finset.univ.sum (fun j => coeff j • rows j)

/-- Row-closure formulation for the finite-row SPDP span check.

This is the concrete invariant-span condition on the selected rows.  It is
strictly a finite-row closure assertion; it does not include the separate
unprojected SPDP preimage condition. -/
structure RouteBRicherGaugeFiniteRowsSPDPRowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Prop where
  row_closure :
    forall (spdpKappa ell : Nat)
      (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (shift : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = spdpKappa ->
      shift.totalDegree <= ell ->
      shift.vars <= S.toFinset ->
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S ->
      forall i,
        routeBSPDPGeneratorRow M n hn2 htb hns (rows i) S shift
          ∈ finiteRowsSubmodule rows

/-- Unprojected preimage side of the Route B finite-row SPDP check.

This is separate from finite-row closure: the projected generator row must
already lie in the raw SPDP subspace of the original, unprojected polynomial. -/
structure RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Prop where
  unprojected_preimage :
    forall (spdpKappa ell : Nat)
      (p : SATDeciderGaugeSpace M n hn2 htb hns)
      (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (shift : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = spdpKappa ->
      shift.totalDegree <= ell ->
      shift.vars <= S.toFinset ->
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S ->
      routeBSPDPGeneratorRow M n hn2 htb hns
          ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
            (routeBRicherFiniteRowsCandidateGauge
              M n hn2 htb hns rows)) p)
          S shift
        ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          spdpKappa ell p

/-- Weaker and more natural image-preimage side of the Route B finite-row SPDP
check.

For image containment, the projected generator does not need to be an element
of the original unprojected SPDP subspace itself.  It is enough to exhibit an
unprojected SPDP row whose image under the selected projection is the projected
generator.  This is the direct witness demanded by `Submodule.map`. -/
structure RouteBRicherGaugeFiniteRowsSPDPMapPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Prop where
  map_preimage :
    forall (spdpKappa ell : Nat)
      (p : SATDeciderGaugeSpace M n hn2 htb hns)
      (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (shift : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = spdpKappa ->
      shift.totalDegree <= ell ->
      shift.vars <= S.toFinset ->
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S ->
      ∃ raw :
          SATDeciderGaugeSpace M n hn2 htb hns,
        raw ∈
          mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            spdpKappa ell p
        ∧
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge
            M n hn2 htb hns rows)) raw =
          routeBSPDPGeneratorRow M n hn2 htb hns
            ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (routeBRicherFiniteRowsCandidateGauge
                M n hn2 htb hns rows)) p)
            S shift

/-- Combined finite-row SPDP frontier for the corrected Route B containment
route.  The fields intentionally keep row-span closure and unprojected
preimage data independent. -/
structure RouteBRicherGaugeFiniteRowsSPDPFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Prop where
  closure :
    RouteBRicherGaugeFiniteRowsSPDPClosure M n hn2 htb hns rows
  preimage :
    RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns rows

/-- A direct unprojected-preimage membership proof gives the map-preimage
formulation by taking the projected generator itself as its own preimage. -/
theorem routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_unprojectedPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (closure :
      RouteBRicherGaugeFiniteRowsSPDPClosure M n hn2 htb hns rows)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage
        M n hn2 htb hns rows) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns rows := by
  constructor
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  let row :=
    routeBSPDPGeneratorRow M n hn2 htb hns
      ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge
          M n hn2 htb hns rows)) p)
      S shift
  have hmemSpan : row ∈ finiteRowsSubmodule rows := by
    rcases closure.finite_row_closure
        spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm with
      ⟨coeff, hcoeff⟩
    exact mem_finiteRowsSubmodule_of_linearCombination rows coeff hcoeff
  refine ⟨row, ?_, ?_⟩
  · exact
      preimage.unprojected_preimage
        spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  · exact
      routeBRicherFiniteRowsCandidateGauge_fixed_of_mem
        M n hn2 htb hns rows hmemSpan

/-- Finite-row row-closure gives the coefficient-level closure package used by
the corrected Route B SPDP frontier. -/
theorem routeBRicherGaugeFiniteRowsSPDPClosure_of_rowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPRowClosure M n hn2 htb hns rows) :
    RouteBRicherGaugeFiniteRowsSPDPClosure M n hn2 htb hns rows := by
  constructor
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  have hmem :
      routeBSPDPGeneratorRow M n hn2 htb hns
          ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
            (routeBRicherFiniteRowsCandidateGauge
              M n hn2 htb hns rows)) p)
          S shift
        ∈ finiteRowsSubmodule rows :=
    routeBSPDPGeneratorRow_projected_mem_finiteRowsSubmodule_of_rowClosure
      M n hn2 htb hns rows p S shift
      (rowClosure.row_closure
        spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm)
  exact
    (mem_finiteRowsSubmodule_iff_exists_linearCombination rows
      (routeBSPDPGeneratorRow M n hn2 htb hns
          ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
            (routeBRicherFiniteRowsCandidateGauge
              M n hn2 htb hns rows)) p)
          S shift)).mp hmem

/-- Row-closure plus unprojected preimage is exactly the corrected finite-row
SPDP frontier. -/
theorem routeBRicherGaugeFiniteRowsSPDPFrontier_of_rowClosure_preimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPRowClosure M n hn2 htb hns rows)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage
        M n hn2 htb hns rows) :
    RouteBRicherGaugeFiniteRowsSPDPFrontier M n hn2 htb hns rows where
  closure :=
    routeBRicherGaugeFiniteRowsSPDPClosure_of_rowClosure
      M n hn2 htb hns rows rowClosure
  preimage := preimage

/-- The named finite-row SPDP frontier reconstructs the checked
linear-combination generator obligation consumed by the existing containment
lemma. -/
theorem routeBRicherGaugeFiniteRowsSPDPFrontier_hgen
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (frontier :
      RouteBRicherGaugeFiniteRowsSPDPFrontier M n hn2 htb hns rows) :
    forall (spdpKappa ell : Nat)
      (p : SATDeciderGaugeSpace M n hn2 htb hns)
      (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (shift : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = spdpKappa ->
      shift.totalDegree <= ell ->
      shift.vars <= S.toFinset ->
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S ->
      ∃ coeff : Fin m -> Rat,
        routeBSPDPGeneratorRow M n hn2 htb hns
            ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (routeBRicherFiniteRowsCandidateGauge
                M n hn2 htb hns rows)) p)
            S shift =
          Finset.univ.sum (fun j => coeff j • rows j)
        ∧
        routeBSPDPGeneratorRow M n hn2 htb hns
            ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
              (routeBRicherFiniteRowsCandidateGauge
                M n hn2 htb hns rows)) p)
            S shift
          ∈
          mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            spdpKappa ell p := by
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  rcases frontier.closure.finite_row_closure
      spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm with
    ⟨coeff, hlinear⟩
  exact
    ⟨coeff, hlinear,
      frontier.preimage.unprojected_preimage
        spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm⟩

/-- The finite-row SPDP frontier gives the Route B SPDP subspace containment
field for the corresponding finite-row candidate gauge. -/
theorem routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_spdpFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (frontier :
      RouteBRicherGaugeFiniteRowsSPDPFrontier M n hn2 htb hns rows) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) := by
  exact
    routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_projectedGenerator_linearCombination
      M n hn2 htb hns rows
      (routeBRicherGaugeFiniteRowsSPDPFrontier_hgen
        M n hn2 htb hns rows frontier)

/-- The map-preimage formulation is enough for Route B SPDP subspace
containment.  This is weaker than asking each projected generator to already
belong to the unprojected subspace: it supplies exactly the preimage required
by `Submodule.map`. -/
theorem routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_mapPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns rows) :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) := by
  intro spdpKappa ell p
  apply Submodule.span_le.mpr
  rintro q ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, hq⟩
  rw [hq]
  rcases preimage.map_preimage
      spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm with
    ⟨raw, hraw, hmap⟩
  exact Submodule.mem_map.mpr ⟨raw, hraw, hmap⟩

/-- Concrete finite-row Route B assembly from the named SPDP frontier.

All scalar, spectral, row-count, P-window, and NP fixed-row assumptions are
the same as the finite-row concrete assembly; the SPDP input is now the
frontier that separates finite-row closure from unprojected preimage. -/
theorem routeBPerInstanceCertificate_of_finiteRowsSPDPFrontier_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hN : 1 <= N) (hrowCount : m <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (frontier :
      RouteBRicherGaugeFiniteRowsSPDPFrontier M n hn2 htb hns rows)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (i : Fin m)
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  exact
    routeBPerInstanceCertificate_of_finiteRowsCompiledGadget_linearCombination_deltaEqRateKappa
      (N := N) (d := d)
      M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
      rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      (routeBRicherGaugeFiniteRowsSPDPFrontier_hgen
        M n hn2 htb hns rows frontier)
      cover Q i hrow hextract hsource

/-- Concrete finite-row Route B assembly from the map-preimage SPDP field.

This is the preferred SPDP surface for a nontrivial projection: the projected
rows only have to be images of unprojected rows, not members of the
unprojected subspace themselves. -/
theorem routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hN : 1 <= N) (hrowCount : m <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns rows)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (i : Fin m)
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  exact
    routeBPerInstanceCertificate_of_finiteRowsCompiledGadget_deltaEqRateKappa
      (N := N) (d := d)
      M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
      rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      (routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_mapPreimage
        M n hn2 htb hns rows preimage)
      cover Q i hrow hextract hsource

/-- Concrete finite-row Route B assembly with the SPDP side reduced to
selected-row closure plus the unprojected preimage condition. -/
theorem routeBPerInstanceCertificate_of_finiteRowsSPDPRowClosure_deltaEqRateKappa
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hN : 1 <= N) (hrowCount : m <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPRowClosure M n hn2 htb hns rows)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage
        M n hn2 htb hns rows)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (i : Fin m)
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  exact
    routeBPerInstanceCertificate_of_finiteRowsSPDPFrontier_deltaEqRateKappa
      (N := N) (d := d)
      M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
      rows hN hrowCount heta htheta halpha halpha0 hkappa hgadgetN
      (routeBRicherGaugeFiniteRowsSPDPFrontier_of_rowClosure_preimage
        M n hn2 htb hns rows rowClosure preimage)
      cover Q i hrow hextract hsource

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherGaugeFiniteRowsSPDPClosure
#print axioms RouteBRicherGaugeFiniteRowsSPDPRowClosure
#print axioms RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage
#print axioms RouteBRicherGaugeFiniteRowsSPDPMapPreimage
#print axioms RouteBRicherGaugeFiniteRowsSPDPFrontier
#print axioms routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_unprojectedPreimage
#print axioms routeBRicherGaugeFiniteRowsSPDPClosure_of_rowClosure
#print axioms routeBRicherGaugeFiniteRowsSPDPFrontier_of_rowClosure_preimage
#print axioms routeBRicherGaugeFiniteRowsSPDPFrontier_hgen
#print axioms routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_spdpFrontier
#print axioms routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_mapPreimage
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPFrontier_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPRowClosure_deltaEqRateKappa

end PallLean.Paper93.Paper283
