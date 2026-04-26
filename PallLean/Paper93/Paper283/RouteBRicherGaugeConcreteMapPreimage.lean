import PallLean.Paper93.Paper283.RouteBRicherGaugeCorrectedConcreteNPAssembly

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

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherConcreteNPPrependedRowsSPDPRowClosurePackage
#print axioms routeBRicherConcreteNPPrependedRows_spdpRowClosure_of_package
#print axioms routeBRicherConcreteNPPrependedRows_spdpClosure_of_rowClosurePackage
#print axioms routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_closure_unprojectedPreimage
#print axioms routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_rowClosurePackage_unprojectedPreimage
#print axioms routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_generatorRowCommutation
#print axioms routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_generatorCommutation
#print axioms routeBRicherConcreteNPPrependedRows_spdpMapPreimage_of_spdpClosure_kernelCompatibility

end PallLean.Paper93.Paper283
