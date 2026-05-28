import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMikoshiTseitinConcrete

/-!
# Restricted Mikoshi/Tseitin lower bound

This file proves the first deliberately restricted non-local Mikoshi/K^t lower
bound.

The model is intentionally narrow: a relational Mikoshi description carries an
explicit direction capacity, and it reconstructs a signed counterfactual
Tseitin boundary only when that capacity is at least the number of independent
parity-flip directions.  Inside this model, a direction/budget gap gives a
machine-checked no-short-description certificate.

This is **not** P-vs-NP.  It is the kind of restricted theorem the framework can
own: it proves the obstruction for a specified description model, and keeps the
dangerous unrestricted bridge separate.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Direction-capacity Mikoshi descriptions -/

/-- A restricted Mikoshi relational description whose semantic payload is an
explicit number of parity-flip directions it can reconstruct. -/
structure DirectionCapacityMikoshiDescription where
  relationalProgram : MikoshiRelationalProgramDescription
  directionCapacity : Nat

namespace DirectionCapacityMikoshiDescription

/-- Cost of a direction-capacity description: relational program size plus one
unit per represented independent direction. -/
def cost (D : DirectionCapacityMikoshiDescription) : Nat :=
  D.relationalProgram.cost + D.directionCapacity

theorem directionCapacity_le_cost
    (D : DirectionCapacityMikoshiDescription) :
    D.directionCapacity <= D.cost := by
  simp [cost, MikoshiRelationalProgramDescription.cost]

end DirectionCapacityMikoshiDescription

/-- Restricted description model: a description reconstructs the signed SAT
counterfactual boundary only if it has capacity for every direction.

This is the non-local combination-state assumption made explicit as a model,
not smuggled into the final theorem. -/
def directionCapacityMikoshiDescriptionModel
    (enc : SignedFormulaEncoding)
    (budget : Nat -> Nat) :
    MikoshiContextDescriptionModel enc where
  Description := DirectionCapacityMikoshiDescription
  descCost := DirectionCapacityMikoshiDescription.cost
  observerBudget := budget
  reconstructsSATBoundary := by
    intro _M _n C D
    exact C.directionCount <= D.directionCapacity

/-! ## No-short-description theorem inside the restricted model -/

/-- In the direction-capacity model, a budget smaller than the number of
directions prevents any in-budget description from reconstructing the boundary.
-/
theorem not_compressedByObserver_directionCapacityModel_of_budget_lt_directions
    {enc : SignedFormulaEncoding}
    {budget : Nat -> Nat}
    {M : DTM} {n scale : Nat}
    (C : SignedCounterfactualEKPDirectionCoverage enc M n)
    (hgap : budget scale < C.directionCount) :
    Not (MikoshiBoundaryCompressedByObserver
      (directionCapacityMikoshiDescriptionModel enc budget) C scale) := by
  rintro ⟨desc, hcost, hreconstructs⟩
  have hcap_le_cost :
      desc.directionCapacity <= DirectionCapacityMikoshiDescription.cost desc :=
    DirectionCapacityMikoshiDescription.directionCapacity_le_cost desc
  have hcap_le_budget :
      desc.directionCapacity <= budget scale :=
    le_trans hcap_le_cost hcost
  have hdir_le_budget :
      C.directionCount <= budget scale :=
    le_trans hreconstructs hcap_le_budget
  exact Nat.not_lt_of_ge hdir_le_budget hgap

/-- Direction/budget gap gives a concrete no-short-description certificate for
any signed counterfactual coverage object in the restricted direction-capacity
model. -/
def noShortMikoshiSATDescription_of_directionCapacityGap
    {enc : SignedFormulaEncoding}
    {budget : Nat -> Nat}
    {M : DTM} {n scale : Nat}
    (C : SignedCounterfactualEKPDirectionCoverage enc M n)
    (hfloor :
      ComplexityErasureLowerBound.independentBranchFloor scale <=
        C.directionCount)
    (hgap : budget scale < C.directionCount) :
    NoShortMikoshiSATDescription
      (directionCapacityMikoshiDescriptionModel enc budget) C where
  scale := scale
  directionFloor := hfloor
  witnessCost := C.directionCount
  observerBudget_lt_witnessCost := hgap
  no_compression :=
    not_compressedByObserver_directionCapacityModel_of_budget_lt_directions
      C hgap

/-- Direction/budget gap gives a no-short Mikoshi certificate for any signed
Tseitin parity-flip boundary in the restricted model. -/
def noShortSignedTseitinMikoshiDescription_of_directionCapacityGap
    {enc : SignedFormulaEncoding}
    {budget : Nat -> Nat}
    {M : DTM} {n scale : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n)
    (hfloor :
      ComplexityErasureLowerBound.independentBranchFloor scale <=
        T.coverage.directionCount)
    (hgap : budget scale < T.coverage.directionCount) :
    NoShortSignedTseitinMikoshiDescription
      (directionCapacityMikoshiDescriptionModel enc budget) T where
  certificate :=
    noShortMikoshiSATDescription_of_directionCapacityGap
      T.coverage hfloor hgap

/-- Any direction/budget gap in the restricted model yields an observer-K^t
certificate for the underlying decider. -/
theorem existsObserverKtCertificate_of_directionCapacityGap
    {enc : SignedFormulaEncoding}
    {budget : Nat -> Nat}
    {M : DTM} {n scale : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n)
    (hfloor :
      ComplexityErasureLowerBound.independentBranchFloor scale <=
        T.coverage.directionCount)
    (hgap : budget scale < T.coverage.directionCount) :
    exists Cert : ObserverKtBoundaryCertificate enc M, Cert.High :=
  (noShortSignedTseitinMikoshiDescription_of_directionCapacityGap
    T hfloor hgap).existsObserverKtCertificate

/-! ## Tiny concrete sanity instantiation -/

/-- Zero observer budget for the restricted direction-capacity model. -/
def zeroMikoshiBudget : Nat -> Nat :=
  fun _ => 0

/-- The concrete one-edge seed has no short direction-capacity Mikoshi
description under zero budget.

This is a sanity theorem, not an asymptotic expander lower bound: the one-edge
seed has real SAT/UNSAT semantics but not genuine expander-scale diversity. -/
def oneEdge_noShortSignedTseitinMikoshiDescription_zeroBudget
    (M : DTM)
    (hM : SignedDTMDecidesSAT signedThreeCNFEncoding M) :
    NoShortSignedTseitinMikoshiDescription
      (directionCapacityMikoshiDescriptionModel
        signedThreeCNFEncoding zeroMikoshiBudget)
      (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM) :=
  noShortSignedTseitinMikoshiDescription_of_directionCapacityGap
    (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM)
    (Nat.le_refl _)
    (by
      simpa [zeroMikoshiBudget] using
        signedOneEdgeTseitinDirectionCount_pos)

/-- The one-edge zero-budget restricted model yields an observer-K^t certificate
for every signed SAT decider.  This is intentionally only a restricted-model
sanity result. -/
theorem oneEdge_existsObserverKtCertificate_zeroBudget
    (M : DTM)
    (hM : SignedDTMDecidesSAT signedThreeCNFEncoding M) :
    exists Cert : ObserverKtBoundaryCertificate signedThreeCNFEncoding M,
      Cert.High :=
  NoShortSignedTseitinMikoshiDescription.existsObserverKtCertificate
    (oneEdge_noShortSignedTseitinMikoshiDescription_zeroBudget M hM)

/-! ## Kernel-only axiom trace -/

#print axioms DirectionCapacityMikoshiDescription.directionCapacity_le_cost
#print axioms not_compressedByObserver_directionCapacityModel_of_budget_lt_directions
#print axioms noShortMikoshiSATDescription_of_directionCapacityGap
#print axioms noShortSignedTseitinMikoshiDescription_of_directionCapacityGap
#print axioms existsObserverKtCertificate_of_directionCapacityGap
#print axioms oneEdge_noShortSignedTseitinMikoshiDescription_zeroBudget
#print axioms oneEdge_existsObserverKtCertificate_zeroBudget

end PallLean.Paper93.DeepMath.PathB
