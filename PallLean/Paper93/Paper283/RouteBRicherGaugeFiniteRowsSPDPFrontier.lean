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

/-! ## Log-window-only finite-row SPDP consumers -/

/-- Log-window row-closure formulation for the finite-row SPDP span check.

Unlike `RouteBRicherGaugeFiniteRowsSPDPRowClosure`, this only speaks about
queries whose derivative list and shift degree are explicitly inside the
canonical `Nat.log 2 n` window.  It is not a claim that every admissible query
is log-windowed. -/
structure RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure
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
      spdpKappa <= Nat.log 2 n ->
      ell <= Nat.log 2 n ->
      shift.vars <= S.toFinset ->
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S ->
      forall i,
        routeBSPDPGeneratorRow M n hn2 htb hns (rows i) S shift
          ∈ finiteRowsSubmodule rows

/-- Log-window coefficient-level finite-row closure for projected Route B
SPDP generator rows. -/
structure RouteBRicherGaugeFiniteRowsSPDPLogWindowClosure
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
      spdpKappa <= Nat.log 2 n ->
      ell <= Nat.log 2 n ->
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

/-- Log-window unprojected-preimage side of the finite-row SPDP check. -/
structure RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
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
      spdpKappa <= Nat.log 2 n ->
      ell <= Nat.log 2 n ->
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

/-- Log-window image-preimage side of the finite-row SPDP check. -/
structure RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage
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
      spdpKappa <= Nat.log 2 n ->
      ell <= Nat.log 2 n ->
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

/-- Combined log-window finite-row SPDP frontier. -/
structure RouteBRicherGaugeFiniteRowsSPDPLogWindowFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Prop where
  closure :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowClosure M n hn2 htb hns rows
  preimage :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
      M n hn2 htb hns rows

/-- Log-window row-closure gives log-window coefficient-level closure. -/
theorem routeBRicherGaugeFiniteRowsSPDPLogWindowClosure_of_rowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure
        M n hn2 htb hns rows) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowClosure
      M n hn2 htb hns rows := by
  constructor
  intro spdpKappa ell p S shift
    hSlen hshiftDegree hSlog hellLog hshiftVars hadm
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
        spdpKappa ell S shift
        hSlen hshiftDegree hSlog hellLog hshiftVars hadm)
  exact
    (mem_finiteRowsSubmodule_iff_exists_linearCombination rows
      (routeBSPDPGeneratorRow M n hn2 htb hns
          ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
            (routeBRicherFiniteRowsCandidateGauge
              M n hn2 htb hns rows)) p)
          S shift)).mp hmem

/-- Log-window row-closure plus log-window unprojected preimage gives the
log-window map-preimage formulation. -/
theorem routeBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage_of_rowClosure_unprojectedPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure
        M n hn2 htb hns rows)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
        M n hn2 htb hns rows) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage
      M n hn2 htb hns rows := by
  constructor
  intro spdpKappa ell p S shift
    hSlen hshiftDegree hSlog hellLog hshiftVars hadm
  let row :=
    routeBSPDPGeneratorRow M n hn2 htb hns
      ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge
          M n hn2 htb hns rows)) p)
      S shift
  have hmemSpan : row ∈ finiteRowsSubmodule rows :=
    routeBSPDPGeneratorRow_projected_mem_finiteRowsSubmodule_of_rowClosure
      M n hn2 htb hns rows p S shift
      (rowClosure.row_closure
        spdpKappa ell S shift
        hSlen hshiftDegree hSlog hellLog hshiftVars hadm)
  refine ⟨row, ?_, ?_⟩
  · exact
      preimage.unprojected_preimage
        spdpKappa ell p S shift
        hSlen hshiftDegree hSlog hellLog hshiftVars hadm
  · exact
      routeBRicherFiniteRowsCandidateGauge_fixed_of_mem
        M n hn2 htb hns rows hmemSpan

/-- Row-closure plus unprojected preimage is exactly the log-window finite-row
SPDP frontier. -/
theorem routeBRicherGaugeFiniteRowsSPDPLogWindowFrontier_of_rowClosure_preimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure
        M n hn2 htb hns rows)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
        M n hn2 htb hns rows) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowFrontier
      M n hn2 htb hns rows where
  closure :=
    routeBRicherGaugeFiniteRowsSPDPLogWindowClosure_of_rowClosure
      M n hn2 htb hns rows rowClosure
  preimage := preimage

/-- The log-window frontier reconstructs the checked generator obligation, but
only for explicitly log-windowed SPDP queries. -/
theorem routeBRicherGaugeFiniteRowsSPDPLogWindowFrontier_hgen
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (frontier :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowFrontier
        M n hn2 htb hns rows) :
    forall (spdpKappa ell : Nat)
      (p : SATDeciderGaugeSpace M n hn2 htb hns)
      (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (shift : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = spdpKappa ->
      shift.totalDegree <= ell ->
      spdpKappa <= Nat.log 2 n ->
      ell <= Nat.log 2 n ->
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
  intro spdpKappa ell p S shift
    hSlen hshiftDegree hSlog hellLog hshiftVars hadm
  rcases frontier.closure.finite_row_closure
      spdpKappa ell p S shift
      hSlen hshiftDegree hSlog hellLog hshiftVars hadm with
    ⟨coeff, hlinear⟩
  exact
    ⟨coeff, hlinear,
      frontier.preimage.unprojected_preimage
        spdpKappa ell p S shift
        hSlen hshiftDegree hSlog hellLog hshiftVars hadm⟩

/-- Log-window SPDP subspace containment for a richer candidate.

This is the true P-window consumer: it only asks for containment at the
canonical profile `(Nat.log 2 n, Nat.log 2 n)`. -/
def RouteBRicherGaugeSPDPLogWindowSubspaceContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Prop :=
  forall (p : MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat),
    mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) p) <=
      Submodule.map
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
        (mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n) p)

/-- Log-window map-preimage gives log-window subspace containment for a
finite-row candidate. -/
theorem routeBRicherFiniteRowsCandidateGauge_spdpLogWindowSubspaceContainment_of_logWindowMapPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage
        M n hn2 htb hns rows) :
    RouteBRicherGaugeSPDPLogWindowSubspaceContainment M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) := by
  intro p
  apply Submodule.span_le.mpr
  rintro q ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, hq⟩
  rw [hq]
  rcases preimage.map_preimage
      (Nat.log 2 n) (Nat.log 2 n) p S shift
      hSlen hshiftDegree le_rfl le_rfl hshiftVars hadm with
    ⟨raw, hraw, hmap⟩
  exact Submodule.mem_map.mpr ⟨raw, hraw, hmap⟩

/-- Log-window subspace containment and an unprojected P-window finite-span
cover prove the projected P-side field, without any all-profile SPDP
containment claim. -/
theorem routeBRicherGauge_projectedPSideBound_of_logWindowSubspaceContainment_finiteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcontain :
      RouteBRicherGaugeSPDPLogWindowSubspaceContainment
        M n hn2 htb hns Pi)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) := by
  unfold SATDeciderGaugePSideBound mlBlockedSpdpRank
  let PiMap := routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
  let U := routeBRicherGaugeUnprojectedPWindowSubspace M n hn2 htb hns
  letI := cover.finite
  letI : Module.Finite Rat (Submodule.map PiMap cover.span) :=
    Module.Finite.map cover.span PiMap
  have htarget :
      mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (PiMap (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
        ≤ Submodule.map PiMap cover.span := by
    exact le_trans
      (hcontain (compiledPoly (cook_levin_compilation M n hn2 htb hns))
        : mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (PiMap (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
          ≤ Submodule.map PiMap U)
      (Submodule.map_mono cover.contains)
  calc
    Module.finrank Rat
        (mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (PiMap (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        ≤ Module.finrank Rat (Submodule.map PiMap cover.span) :=
          Submodule.finrank_mono htarget
    _ ≤ Module.finrank Rat cover.span :=
          Submodule.finrank_map_le _ _
    _ ≤ n ^ 200 := cover.rank_bound

/-- Finite-row log-window map-preimage and an unprojected P-window cover prove
the projected P-side field for the finite-row candidate. -/
theorem routeBRicherFiniteRowsCandidateGauge_projectedPSideBound_of_logWindowMapPreimage_finiteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage
        M n hn2 htb hns rows)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)) :=
  routeBRicherGauge_projectedPSideBound_of_logWindowSubspaceContainment_finiteSpanCover
    M n hn2 htb hns
    (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
    (routeBRicherFiniteRowsCandidateGauge_spdpLogWindowSubspaceContainment_of_logWindowMapPreimage
      M n hn2 htb hns rows preimage)
    cover

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

/-- Conversely, the finite-row SPDP subspace-containment field gives exactly
the map-preimage witnesses demanded by `Submodule.map`.

This identifies the corrected finite-row map-preimage target with the existing
Route B SPDP image-containment statement.  It does not use the stronger
unprojected-preimage formulation. -/
theorem routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_spdpSubspaceContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (contain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns rows := by
  constructor
  intro spdpKappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  let Pi :=
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
  have hrow_mem :
      routeBSPDPGeneratorRow M n hn2 htb hns (Pi p) S shift ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          spdpKappa ell (Pi p) :=
    Submodule.subset_span
      ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  have hmap_mem :
      routeBSPDPGeneratorRow M n hn2 htb hns (Pi p) S shift ∈
        Submodule.map Pi
          (mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            spdpKappa ell p) :=
    contain spdpKappa ell p hrow_mem
  rcases Submodule.mem_map.mp hmap_mem with ⟨raw, hraw, hraw_map⟩
  exact ⟨raw, hraw, hraw_map⟩

/-- For finite-row gauges, the map-preimage field is exactly the Route B SPDP
subspace-containment field. -/
theorem routeBRicherGaugeFiniteRowsSPDPMapPreimage_iff_spdpSubspaceContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns rows ↔
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) := by
  constructor
  · exact
      routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_mapPreimage
        M n hn2 htb hns rows
  · exact
      routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_spdpSubspaceContainment
        M n hn2 htb hns rows

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
#print axioms RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure
#print axioms RouteBRicherGaugeFiniteRowsSPDPLogWindowClosure
#print axioms RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
#print axioms RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage
#print axioms RouteBRicherGaugeFiniteRowsSPDPLogWindowFrontier
#print axioms routeBRicherGaugeFiniteRowsSPDPLogWindowClosure_of_rowClosure
#print axioms routeBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage_of_rowClosure_unprojectedPreimage
#print axioms routeBRicherGaugeFiniteRowsSPDPLogWindowFrontier_of_rowClosure_preimage
#print axioms routeBRicherGaugeFiniteRowsSPDPLogWindowFrontier_hgen
#print axioms RouteBRicherGaugeSPDPLogWindowSubspaceContainment
#print axioms routeBRicherFiniteRowsCandidateGauge_spdpLogWindowSubspaceContainment_of_logWindowMapPreimage
#print axioms routeBRicherGauge_projectedPSideBound_of_logWindowSubspaceContainment_finiteSpanCover
#print axioms routeBRicherFiniteRowsCandidateGauge_projectedPSideBound_of_logWindowMapPreimage_finiteSpanCover
#print axioms RouteBRicherGaugeFiniteRowsSPDPFrontier
#print axioms routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_unprojectedPreimage
#print axioms routeBRicherGaugeFiniteRowsSPDPClosure_of_rowClosure
#print axioms routeBRicherGaugeFiniteRowsSPDPFrontier_of_rowClosure_preimage
#print axioms routeBRicherGaugeFiniteRowsSPDPFrontier_hgen
#print axioms routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_spdpFrontier
#print axioms routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_mapPreimage
#print axioms routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_spdpSubspaceContainment
#print axioms routeBRicherGaugeFiniteRowsSPDPMapPreimage_iff_spdpSubspaceContainment
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPFrontier_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPMapPreimage_deltaEqRateKappa
#print axioms routeBPerInstanceCertificate_of_finiteRowsSPDPRowClosure_deltaEqRateKappa

end PallLean.Paper93.Paper283
