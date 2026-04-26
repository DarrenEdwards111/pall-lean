import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteMultilinearTail
import PallLean.Paper93.Paper283.BridgeAMlProjLinear

/-!
# No-go diagnostics for the concrete multilinear-tail Route B gauge

This file records what the kernel can prove about the current concrete
finite-row projection with the full multilinear monomial tail.

The key diagnostic is that the selected row span already contains every
`mlProj` output.  Therefore the finite-row projection fixes the whole
multilinear image, before any residual-annihilation hypothesis is used.
Residual annihilation for all generators only forces the residual to lie in the
kernel of `mlProj`.  Upgrading that to equality of the projection with the
identity is blocked unless one can also prove that every projected output is
itself fixed by `mlProj`; under that extra hypothesis the projection collapses
to the full multilinear projection.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

private abbrev ResidualAnnihilation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
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
      (p -
        routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p)
      S shift = 0

/-- The concrete multilinear-tail projection fixes every multilinear
projection.  This uses only the row-span definition: the tail contains all
multilinear monomials, so every `mlProj p` lies in the selected finite row
span. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjection_fixes_mlProj
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    routeBRicherConcreteNPPrependedMultilinearProjection M n hn2 htb hns
        (mlProj p) =
      mlProj p := by
  simpa [routeBRicherConcreteNPPrependedMultilinearProjection,
    routeBRicherConcreteNPPrependedMultilinearGauge] using
    routeBRicherFiniteRowsCandidateGauge_fixed_of_mem
      M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)
      (routeBRicherConcreteNPPrependedMultilinearRows_mlProj_mem
        M n hn2 htb hns p)

/-- Consequently, the projection is already the identity on every polynomial
fixed by `mlProj`.  This is unconditional and is the first sign that the full
multilinear tail is too broad for a nontrivial gauge. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjection_fixed_of_mlProj_eq
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (hp : mlProj p = p) :
    routeBRicherConcreteNPPrependedMultilinearProjection M n hn2 htb hns p =
      p := by
  simpa [hp] using
    routeBRicherConcreteNPPrependedMultilinearProjection_fixes_mlProj
      M n hn2 htb hns p

/-- Empty-derivative, constant-shift specialization of residual annihilation:
if residual annihilation holds for all generators, then every residual is
killed by the multilinear projection. -/
theorem routeBRicherConcreteNPPrependedMultilinearResidual_mlProj_eq_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero : ResidualAnnihilation M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    mlProj
      (p -
        routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p) = 0 := by
  have hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        ([] : List (Fin (RouteBCookLevinDim M n hn2 htb hns))) := by
    constructor
    · simp
    · intro b
      simp
  have h :=
    hzero 0 0 p
      ([] : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
      (1 : SATDeciderGaugeSpace M n hn2 htb hns)
      (by simp) (by simp) (by simp) hadm
  simpa [routeBSPDPGeneratorRow, SPDP.iterDerivList, mlProj_one] using h

/-- Residual annihilation forces agreement with the identity only after
applying `mlProj`.  This is the strongest unconditional consequence available
from the empty-generator diagnostic. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjection_mlProj_agrees
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero : ResidualAnnihilation M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    mlProj
        (routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p) =
      mlProj p := by
  have hres :=
    routeBRicherConcreteNPPrependedMultilinearResidual_mlProj_eq_zero
      M n hn2 htb hns hzero p
  have hsub :
      mlProj
        (p -
          routeBRicherConcreteNPPrependedMultilinearProjection
            M n hn2 htb hns p) =
        mlProj p -
          mlProj
            (routeBRicherConcreteNPPrependedMultilinearProjection
              M n hn2 htb hns p) := by
    change (mlProjHom ℚ)
        (p -
          routeBRicherConcreteNPPrependedMultilinearProjection
            M n hn2 htb hns p) =
      (mlProjHom ℚ) p -
        (mlProjHom ℚ)
          (routeBRicherConcreteNPPrependedMultilinearProjection
            M n hn2 htb hns p)
    exact map_sub _ p
      (routeBRicherConcreteNPPrependedMultilinearProjection
        M n hn2 htb hns p)
  rw [hsub] at hres
  exact (sub_eq_zero.mp hres).symm

/-- If one could additionally prove that every projected output is itself
multilinear, then residual annihilation would make the current projection
equal to the full multilinear projection.  This is the precise point where a
proof of literal identity is blocked: the current definitions expose no
kernel-checked proof of this extra hypothesis for the prepended NP row. -/
theorem routeBRicherConcreteNPPrependedMultilinearProjection_eq_mlProj_of_residual_and_projected_ml
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero : ResidualAnnihilation M n hn2 htb hns)
    (hprojected_ml :
      forall p : SATDeciderGaugeSpace M n hn2 htb hns,
        mlProj
          (routeBRicherConcreteNPPrependedMultilinearProjection
            M n hn2 htb hns p) =
        routeBRicherConcreteNPPrependedMultilinearProjection
          M n hn2 htb hns p) :
    routeBRicherConcreteNPPrependedMultilinearProjection M n hn2 htb hns =
      mlProjLinearMap (Fin (RouteBCookLevinDim M n hn2 htb hns)) ℚ := by
  apply LinearMap.ext
  intro p
  rw [← hprojected_ml p]
  exact routeBRicherConcreteNPPrependedMultilinearProjection_mlProj_agrees
    M n hn2 htb hns hzero p

/-- The existing kernel-compatibility theorem rephrased using the local
`ResidualAnnihilation` abbreviation.  This makes the no-go surface explicit:
for the full multilinear tail, compatibility is exactly the residual
annihilation condition studied above. -/
theorem routeBRicherConcreteNPPrependedMultilinearRows_kernelCompatibility_iff_noGoResidualAnnihilation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherGaugeFiniteRowsSPDPKernelCompatibility M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns) ↔
      ResidualAnnihilation M n hn2 htb hns := by
  simpa [ResidualAnnihilation] using
    routeBRicherConcreteNPPrependedMultilinearRows_kernelCompatibility_iff_residualGenerator_zero
      M n hn2 htb hns

/-! ## Axiom audit anchors -/

#print axioms routeBRicherConcreteNPPrependedMultilinearProjection_fixes_mlProj
#print axioms routeBRicherConcreteNPPrependedMultilinearProjection_fixed_of_mlProj_eq
#print axioms routeBRicherConcreteNPPrependedMultilinearResidual_mlProj_eq_zero
#print axioms routeBRicherConcreteNPPrependedMultilinearProjection_mlProj_agrees
#print axioms routeBRicherConcreteNPPrependedMultilinearProjection_eq_mlProj_of_residual_and_projected_ml
#print axioms routeBRicherConcreteNPPrependedMultilinearRows_kernelCompatibility_iff_noGoResidualAnnihilation

end PallLean.Paper93.Paper283
