import PallLean.Paper93.Paper283.RouteBRicherGaugeCorrectedConcreteNPAssembly
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPConcreteScalarClosure

/-!
# Concrete prepended-row SPDP map-preimage reductions

This file specializes the checked finite-row SPDP map-preimage bridges to the
concrete Route B row family obtained by prepending the Cook-Levin NP witness.

There is no unconditional semantic proof here: the remaining content is still
the SPDP compatibility of the richer finite-row projection.  The reductions
below expose that content either as generator commutation, or as a row-level
closure plus unprojected-preimage package for the concrete prepended rows.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Row-level SPDP closure package for the concrete prepended row family.

The head row is the concrete Cook-Levin NP witness; the remaining rows are the
arbitrary richer-gauge tail.  Both sets of generator rows must land in the span
of the full prepended family. -/
structure RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Prop where
  concrete_row_closure :
    forall (spdpKappa ell : Nat)
      (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (shift : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = spdpKappa ->
      shift.totalDegree <= ell ->
      shift.vars <= S.toFinset ->
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S ->
      routeBSPDPGeneratorRow M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift
        ∈ finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
  tail_row_closure :
    forall (spdpKappa ell : Nat)
      (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (shift : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = spdpKappa ->
      shift.totalDegree <= ell ->
      shift.vars <= S.toFinset ->
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S ->
      forall i,
        routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift
          ∈ finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)

/-- The concrete head/tail row package is exactly the standard finite-row
row-closure obligation for `routeBRicherConcreteNPPrependedRows`. -/
theorem routeBRicherConcreteNPPrependedRows_spdpRowClosure_of_package
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail) :
    RouteBRicherGaugeFiniteRowsSPDPRowClosure M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) := by
  constructor
  intro spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm i
  refine Fin.cases ?zero ?succ i
  · simpa [routeBRicherConcreteNPPrependedRows] using
      pkg.concrete_row_closure
        spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm
  · intro j
    simpa [routeBRicherConcreteNPPrependedRows] using
      pkg.tail_row_closure
        spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm j

/-- The standard finite-row row-closure obligation for the concrete prepended
rows splits back into the concrete head-row and tail-row package. -/
theorem routeBRicherConcreteNPPrependedRows_package_of_spdpRowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPRowClosure M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
      M n hn2 htb hns tail := by
  constructor
  · intro spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm
    simpa [routeBRicherConcreteNPPrependedRows] using
      rowClosure.row_closure
        spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm
        (0 : Fin (m + 1))
  · intro spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm i
    simpa [routeBRicherConcreteNPPrependedRows] using
      rowClosure.row_closure
        spdpKappa ell S shift hSlen hshiftDegree hshiftVars hadm
        (Fin.succ i)

/-- For the concrete prepended rows, the package formulation is equivalent to
the ordinary finite-row row-closure formulation. -/
theorem routeBRicherConcreteNPPrependedRows_spdpRowClosure_iff_package
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPRowClosure M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) ↔
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail := by
  constructor
  · exact routeBRicherConcreteNPPrependedRows_package_of_spdpRowClosure
      M n hn2 htb hns tail
  · exact routeBRicherConcreteNPPrependedRows_spdpRowClosure_of_package
      M n hn2 htb hns tail

/-! ## Log-window concrete prepended-row consumers -/

/-- Log-window row-level SPDP closure package for the concrete prepended row
family.

This is the concrete head/tail version of
`RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure`: it only consumes
admissible queries carrying explicit `Nat.log 2 n` bounds. -/
structure RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    Prop where
  concrete_row_closure :
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
      routeBSPDPGeneratorRow M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift
        ∈ finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
  tail_row_closure :
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
        routeBSPDPGeneratorRow M n hn2 htb hns (tail i) S shift
          ∈ finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)

/-- The concrete log-window head/tail row package is exactly the standard
finite-row log-window row-closure obligation for the prepended row family. -/
theorem routeBRicherConcreteNPPrependedRows_spdpLogWindowRowClosure_of_package
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
        M n hn2 htb hns tail) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) := by
  constructor
  intro spdpKappa ell S shift
    hSlen hshiftDegree hSlog hellLog hshiftVars hadm i
  refine Fin.cases ?zero ?succ i
  · simpa [routeBRicherConcreteNPPrependedRows] using
      pkg.concrete_row_closure
        spdpKappa ell S shift
        hSlen hshiftDegree hSlog hellLog hshiftVars hadm
  · intro j
    simpa [routeBRicherConcreteNPPrependedRows] using
      pkg.tail_row_closure
        spdpKappa ell S shift
        hSlen hshiftDegree hSlog hellLog hshiftVars hadm j

/-- The standard finite-row log-window row-closure obligation for the concrete
prepended rows splits into the concrete head-row and tail-row package. -/
theorem routeBRicherConcreteNPPrependedRows_package_of_spdpLogWindowRowClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (rowClosure :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
      M n hn2 htb hns tail := by
  constructor
  · intro spdpKappa ell S shift
      hSlen hshiftDegree hSlog hellLog hshiftVars hadm
    simpa [routeBRicherConcreteNPPrependedRows] using
      rowClosure.row_closure
        spdpKappa ell S shift
        hSlen hshiftDegree hSlog hellLog hshiftVars hadm
        (0 : Fin (m + 1))
  · intro spdpKappa ell S shift
      hSlen hshiftDegree hSlog hellLog hshiftVars hadm i
    simpa [routeBRicherConcreteNPPrependedRows] using
      rowClosure.row_closure
        spdpKappa ell S shift
        hSlen hshiftDegree hSlog hellLog hshiftVars hadm
        (Fin.succ i)

/-- For concrete prepended rows, the log-window package formulation is
equivalent to the ordinary finite-row log-window row-closure formulation. -/
theorem routeBRicherConcreteNPPrependedRows_spdpLogWindowRowClosure_iff_package
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowRowClosure M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) ↔
      RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
        M n hn2 htb hns tail := by
  constructor
  · exact routeBRicherConcreteNPPrependedRows_package_of_spdpLogWindowRowClosure
      M n hn2 htb hns tail
  · exact routeBRicherConcreteNPPrependedRows_spdpLogWindowRowClosure_of_package
      M n hn2 htb hns tail

/-- Log-window row-level closure package for the concrete prepended rows gives
the coefficient-level finite-row log-window SPDP closure package. -/
theorem routeBRicherConcreteNPPrependedRows_spdpLogWindowClosure_of_rowClosurePackage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
        M n hn2 htb hns tail) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowClosure M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) :=
  routeBRicherGaugeFiniteRowsSPDPLogWindowClosure_of_rowClosure
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    (routeBRicherConcreteNPPrependedRows_spdpLogWindowRowClosure_of_package
      M n hn2 htb hns tail pkg)

/-- Concrete prepended-row log-window map-preimage from the head/tail
row-closure package and the log-window unprojected-preimage side. -/
theorem routeBRicherConcreteNPPrependedRows_spdpLogWindowMapPreimage_of_rowClosurePackage_unprojectedPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
        M n hn2 htb hns tail)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) :=
  routeBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage_of_rowClosure_unprojectedPreimage
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    (routeBRicherConcreteNPPrependedRows_spdpLogWindowRowClosure_of_package
      M n hn2 htb hns tail pkg)
    preimage

/-- Concrete prepended-row projected P-side bound from the log-window
map-preimage surface and an unprojected P-window cover. -/
theorem routeBRicherConcreteNPPrependedRows_projectedPSideBound_of_spdpLogWindowMapPreimage_finiteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowMapPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))) :=
  routeBRicherFiniteRowsCandidateGauge_projectedPSideBound_of_logWindowMapPreimage_finiteSpanCover
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    preimage cover

/-- Concrete prepended-row projected P-side bound from the log-window
head/tail row-closure package, log-window unprojected preimage, and an
unprojected P-window cover. -/
theorem routeBRicherConcreteNPPrependedRows_projectedPSideBound_of_logWindowRowClosurePackage_unprojectedPreimage_finiteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
        M n hn2 htb hns tail)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))) :=
  routeBRicherConcreteNPPrependedRows_projectedPSideBound_of_spdpLogWindowMapPreimage_finiteSpanCover
    M n hn2 htb hns tail
    (routeBRicherConcreteNPPrependedRows_spdpLogWindowMapPreimage_of_rowClosurePackage_unprojectedPreimage
      M n hn2 htb hns tail pkg preimage)
    cover

/-- Row-level closure package for the concrete prepended rows gives the
coefficient-level finite-row SPDP closure package. -/
theorem routeBRicherConcreteNPPrependedRows_spdpClosure_of_rowClosurePackage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail) :
    RouteBRicherGaugeFiniteRowsSPDPClosure M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) :=
  routeBRicherGaugeFiniteRowsSPDPClosure_of_rowClosure
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    (routeBRicherConcreteNPPrependedRows_spdpRowClosure_of_package
      M n hn2 htb hns tail pkg)

/-- Concrete prepended-row map-preimage from finite-row closure and the
unprojected-preimage side. -/
theorem routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_closure_unprojectedPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (closure :
      RouteBRicherGaugeFiniteRowsSPDPClosure M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) :=
  routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_unprojectedPreimage
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    closure preimage

/-- Concrete prepended-row map-preimage from the head/tail row-closure package
and the unprojected-preimage side. -/
theorem routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_rowClosurePackage_unprojectedPreimage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail)
    (preimage :
      RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) :=
  routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_closure_unprojectedPreimage
    M n hn2 htb hns tail
    (routeBRicherConcreteNPPrependedRows_spdpClosure_of_rowClosurePackage
      M n hn2 htb hns tail pkg)
    preimage

/-- Concrete prepended-row map-preimage from finite-row generator-row
commutation. -/
theorem routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_generatorRowCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcomm :
      RouteBRicherGaugeFiniteRowsSPDPGeneratorCommutation M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) :=
  routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorRowCommutation
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    hcomm

/-- Concrete prepended-row map-preimage from the general richer-gauge
generator commutation hypothesis. -/
theorem routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_generatorCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) :=
  routeBRicherGaugeFiniteRowsSPDPMapPreimage_of_generatorCommutation
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
    hcomm

/-- Concrete prepended-row map-preimage from finite-row closure plus the
kernel/complement compatibility needed to upgrade closure to commutation. -/
theorem routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_spdpClosure_kernelCompatibility
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (closure :
      RouteBRicherGaugeFiniteRowsSPDPClosure M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail))
    (hker :
      RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)) :
    RouteBRicherGaugeFiniteRowsSPDPMapPreimage M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) :=
  routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_generatorCommutation
    M n hn2 htb hns tail
    (routeBRicherGaugeGeneratorCommutation_of_spdpClosure_kernelCompatibility
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail)
      closure hker)

/-! ## Empty-tail reductions and obstruction -/

/-- With an empty tail, the concrete prepended row family is definitionally the
one-row concrete NP witness family. -/
theorem routeBRicherConcreteNPPrependedRows_empty_eq_witnessRows
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (tail : Fin 0 -> SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail =
      routeBRicherConcreteNPWitnessRows M n hn2 htb hns := by
  funext i
  fin_cases i
  rfl

/-- Empty-tail prepended unprojected-preimage is exactly the older one-row
concrete NP unprojected-preimage closure. -/
theorem routeBRicherConcreteNPPrependedRows_empty_unprojectedPreimage_iff_concreteNP
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (tail : Fin 0 -> SATDeciderGaugeSpace M n hn2 htb hns) :
    RouteBRicherGaugeFiniteRowsSPDPUnprojectedPreimage M n hn2 htb hns
        (routeBRicherConcreteNPPrependedRows M n hn2 htb hns tail) ↔
      RouteBRicherConcreteNPUnprojectedSPDPPreimageClosure
        M n hn2 htb hns := by
  constructor
  · intro preimage kappa ell p S shift hSlen hshiftDegree hshiftVars hadm
    have hrows :=
      routeBRicherConcreteNPPrependedRows_empty_eq_witnessRows
        M n hn2 htb hns tail
    simpa [hrows] using
      preimage.unprojected_preimage
        kappa ell p S shift hSlen hshiftDegree hshiftVars hadm
  · intro hpre
    constructor
    intro kappa ell p S shift hSlen hshiftDegree hshiftVars hadm
    have hrows :=
      routeBRicherConcreteNPPrependedRows_empty_eq_witnessRows
        M n hn2 htb hns tail
    simpa [hrows] using
      hpre kappa ell p S shift hSlen hshiftDegree hshiftVars hadm

/-- An empty-tail prepended row-closure package would imply the false
one-row scalar closure for the concrete Cook-Levin witness. -/
theorem routeBRicherConcreteNPWitnessScalarRowClosure_of_emptyPrependedRowsPackage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (tail : Fin 0 -> SATDeciderGaugeSpace M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail) :
    RouteBRicherConcreteNPWitnessScalarRowClosure M n hn2 htb hns := by
  intro kappa ell S shift hSlen hshiftDegree hshiftVars hadm
  have hrows :=
    routeBRicherConcreteNPPrependedRows_empty_eq_witnessRows
      M n hn2 htb hns tail
  have hmem :
      routeBSPDPGeneratorRow M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift
        ∈ finiteRowsSubmodule
            (routeBRicherConcreteNPWitnessRows M n hn2 htb hns) := by
    simpa [hrows] using
      pkg.concrete_row_closure
        kappa ell S shift hSlen hshiftDegree hshiftVars hadm
  exact
    (mem_finiteRowsSubmodule_one_iff_exists_scalar
      (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)
      (routeBSPDPGeneratorRow M n hn2 htb hns
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) S shift)).mp
      hmem

/-- Empty-tail prepended row-closure package would imply the refuted
`compiledPoly` scalar-row closure. -/
theorem routeBRicherConcreteNPCompiledPolyScalarRowClosure_of_emptyPrependedRowsPackage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (tail : Fin 0 -> SATDeciderGaugeSpace M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail) :
    RouteBRicherConcreteNPCompiledPolyScalarRowClosure M n hn2 htb hns :=
  (routeBRicherConcreteNPWitnessScalarRowClosure_iff_compiledPoly
    M n hn2 htb hns).mp
    (routeBRicherConcreteNPWitnessScalarRowClosure_of_emptyPrependedRowsPackage
      M n hn2 htb hns tail pkg)

/-- The empty-tail concrete prepended rows cannot satisfy the row-closure
package: that would be the impossible scalar closure of the single concrete
Cook-Levin witness row. -/
theorem not_routeBRicherConcreteNPPrependedRows_empty_spdpRowClosurePackage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (tail : Fin 0 -> SATDeciderGaugeSpace M n hn2 htb hns) :
    ¬ RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail := by
  intro pkg
  exact
    not_routeBRicherConcreteNPCompiledPolyScalarRowClosure M n hn2 htb hns
      (routeBRicherConcreteNPCompiledPolyScalarRowClosure_of_emptyPrependedRowsPackage
        M n hn2 htb hns tail pkg)

/-- Consequently, any genuine concrete prepended-row closure package needs at
least one tail row beyond the concrete NP head. -/
theorem routeBRicherConcreteNPPrependedRows_tail_nonempty_of_spdpRowClosurePackage
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (tail : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (pkg :
      RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
        M n hn2 htb hns tail) :
    0 < m := by
  by_contra hnot
  have hm : m = 0 := Nat.eq_zero_of_not_pos hnot
  subst m
  exact
    not_routeBRicherConcreteNPPrependedRows_empty_spdpRowClosurePackage
      M n hn2 htb hns tail pkg

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
#print axioms routeBRicherConcreteNPPrependedRows_spdpRowClosure_of_package
#print axioms routeBRicherConcreteNPPrependedRows_package_of_spdpRowClosure
#print axioms routeBRicherConcreteNPPrependedRows_spdpRowClosure_iff_package
#print axioms RouteBRicherConcreteNPPrependedRowsSPDPLogWindowRowClosurePackage
#print axioms routeBRicherConcreteNPPrependedRows_spdpLogWindowRowClosure_of_package
#print axioms routeBRicherConcreteNPPrependedRows_package_of_spdpLogWindowRowClosure
#print axioms routeBRicherConcreteNPPrependedRows_spdpLogWindowRowClosure_iff_package
#print axioms routeBRicherConcreteNPPrependedRows_spdpLogWindowClosure_of_rowClosurePackage
#print axioms routeBRicherConcreteNPPrependedRows_spdpLogWindowMapPreimage_of_rowClosurePackage_unprojectedPreimage
#print axioms routeBRicherConcreteNPPrependedRows_projectedPSideBound_of_spdpLogWindowMapPreimage_finiteSpanCover
#print axioms routeBRicherConcreteNPPrependedRows_projectedPSideBound_of_logWindowRowClosurePackage_unprojectedPreimage_finiteSpanCover
#print axioms routeBRicherConcreteNPPrependedRows_spdpClosure_of_rowClosurePackage
#print axioms routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_closure_unprojectedPreimage
#print axioms routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_rowClosurePackage_unprojectedPreimage
#print axioms routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_generatorRowCommutation
#print axioms routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_generatorCommutation
#print axioms routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_spdpClosure_kernelCompatibility
#print axioms routeBRicherConcreteNPPrependedRows_empty_eq_witnessRows
#print axioms routeBRicherConcreteNPPrependedRows_empty_unprojectedPreimage_iff_concreteNP
#print axioms routeBRicherConcreteNPWitnessScalarRowClosure_of_emptyPrependedRowsPackage
#print axioms routeBRicherConcreteNPCompiledPolyScalarRowClosure_of_emptyPrependedRowsPackage
#print axioms not_routeBRicherConcreteNPPrependedRows_empty_spdpRowClosurePackage
#print axioms routeBRicherConcreteNPPrependedRows_tail_nonempty_of_spdpRowClosurePackage

end PallLean.Paper93.Paper283
