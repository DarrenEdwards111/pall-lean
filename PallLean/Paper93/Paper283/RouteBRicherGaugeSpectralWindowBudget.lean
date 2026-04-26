import PallLean.Paper93.Paper283.RouteBRicherGaugeRankBudget

/-!
# Route B richer-gauge spectral-window budgets

This file isolates the spectral-window/floor/budget package consumed by
`routeBPerInstanceCertificate_of_richerFiniteRows_eigenvalueFloor`.

It does not prove a new analytic floor.  The point is to keep the real
spectral inputs explicit while giving the finite-row Route B constructor a
row-count surface for the matrix-rank side condition.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- The spectral-window part of the richer finite-row Route B certificate.

The fields are exactly the non-row spectral inputs needed by
`routeBPerInstanceCertificate_of_richerFiniteRows_eigenvalueFloor`: a
nonnegative common eigenvalue floor on the selected window, and the scalar
budget comparing the Bridge A active-rank side with that window. -/
structure RouteBRicherGaugeSpectralWindowBudget
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (theta rankLogRate lambdaFloor : Real)
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (S : Finset (Fin N)) : Prop where
  lambdaFloor_nonneg : 0 <= lambdaFloor
  eigenvalue_floor :
    forall i, i ∈ S -> lambdaFloor <= hA.1.eigenvalues i
  spectral_floor_budget :
    rankLogRate *
        ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
          (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank) :
          Real) <=
      (S.card : Real) * Real.log (1 + theta * lambdaFloor)

/-- Direct constructor for the packaged spectral-window budget. -/
theorem routeBRicherGaugeSpectralWindowBudget_of_eigenvalueFloorBudget
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {theta rankLogRate lambdaFloor : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (S : Finset (Fin N))
    (hlambdaFloor_nonneg : 0 <= lambdaFloor)
    (hfloor : forall i, i ∈ S -> lambdaFloor <= hA.1.eigenvalues i)
    (hbudget :
      rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank) :
            Real) <=
        (S.card : Real) * Real.log (1 + theta * lambdaFloor)) :
    RouteBRicherGaugeSpectralWindowBudget
      alpha beta alpha0 kappa gadgetN G chi Phi
      theta rankLogRate lambdaFloor A hA S where
  lambdaFloor_nonneg := hlambdaFloor_nonneg
  eigenvalue_floor := hfloor
  spectral_floor_budget := hbudget

/-- Full-window constructor from a uniform eigenvalue floor. -/
theorem routeBRicherGaugeSpectralWindowBudget_univ_of_uniform_eigenvalueFloor
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {theta rankLogRate lambdaFloor : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (hlambdaFloor_nonneg : 0 <= lambdaFloor)
    (hfloor : forall i, lambdaFloor <= hA.1.eigenvalues i)
    (hbudget :
      rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank) :
            Real) <=
        (N : Real) * Real.log (1 + theta * lambdaFloor)) :
    RouteBRicherGaugeSpectralWindowBudget
      alpha beta alpha0 kappa gadgetN G chi Phi
      theta rankLogRate lambdaFloor A hA Finset.univ := by
  refine
    routeBRicherGaugeSpectralWindowBudget_of_eigenvalueFloorBudget
      alpha beta alpha0 kappa gadgetN G chi Phi A hA Finset.univ
      hlambdaFloor_nonneg ?_ ?_
  · intro i _hi
    exact hfloor i
  · simpa using hbudget

/-- The row-count matrix-rank assumption supplies the real finrank inequality
needed by `routeBPerInstanceCertificate_of_richerFiniteRows_eigenvalueFloor`. -/
theorem routeBRicherGauge_rowSpan_rank_le_matrix_rank_of_rowCount_le
    {rowVarCount : Nat} {m : Nat}
    (rows : Fin m -> MvPolynomial (Fin rowVarCount) Rat)
    {rankA : Nat} (hrowRank : m <= rankA) :
    (Module.finrank Rat (finiteRowsSubmodule rows) : Real) <=
      (rankA : Real) := by
  exact_mod_cast
    le_trans (finiteRowsSubmodule_finrank_le_card rows) hrowRank

/-- A packaged spectral-window budget plus a row-count rank bound gives the
three spectral arguments and the row-rank argument in exactly the order needed
by `routeBPerInstanceCertificate_of_richerFiniteRows_eigenvalueFloor`.

This is intentionally only a hypothesis packer: it does not call the final
Route B certificate constructor, so it remains a kernel-only helper. -/
theorem routeBRicherGauge_eigenvalueFloor_args_of_spectralWindowBudget_rowCount
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {theta rankLogRate lambdaFloor : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (S : Finset (Fin N))
    {rowVarCount m : Nat}
    (rows : Fin m -> MvPolynomial (Fin rowVarCount) Rat)
    (hspectral :
      RouteBRicherGaugeSpectralWindowBudget
        alpha beta alpha0 kappa gadgetN G chi Phi
        theta rankLogRate lambdaFloor A hA S)
    (hrowRank : m <= A.rank) :
    (0 <= lambdaFloor) ∧
      (forall i, i ∈ S -> lambdaFloor <= hA.1.eigenvalues i) ∧
      (rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank) :
            Real) <=
        (S.card : Real) * Real.log (1 + theta * lambdaFloor)) ∧
      ((Module.finrank Rat (finiteRowsSubmodule rows) : Real) <=
        (A.rank : Real)) :=
  ⟨hspectral.lambdaFloor_nonneg,
    hspectral.eigenvalue_floor,
    hspectral.spectral_floor_budget,
    routeBRicherGauge_rowSpan_rank_le_matrix_rank_of_rowCount_le
      rows hrowRank⟩

/-! ## Axiom audit anchors -/

#print axioms routeBRicherGaugeSpectralWindowBudget_of_eigenvalueFloorBudget
#print axioms routeBRicherGaugeSpectralWindowBudget_univ_of_uniform_eigenvalueFloor
#print axioms routeBRicherGauge_rowSpan_rank_le_matrix_rank_of_rowCount_le
#print axioms routeBRicherGauge_eigenvalueFloor_args_of_spectralWindowBudget_rowCount

end PallLean.Paper93.Paper283
