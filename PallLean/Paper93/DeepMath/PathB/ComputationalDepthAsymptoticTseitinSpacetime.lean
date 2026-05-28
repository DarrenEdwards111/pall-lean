import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSpacetimeTseitinLowerBound

/-!
# Asymptotic signed Tseitin spacetime target

`ComputationalDepthSpacetimeTseitinLowerBound` reduced the local-physics
payload to a concrete communication statement:

* every signed-Tseitin direction must occupy a distinct local communication
  slot of any realization.

This file packages the asymptotic target around that reducer.  It introduces a
signed Tseitin expander-family surface, constructs signed counterfactual
coverage and parity-flip boundaries from any signed SAT decider, and records
the exact locality principle that remains to be proved for a genuine
expander/Mikoshi family.

Nothing here proves classical `P ≠ NP`; the load-bearing theorem is the
explicit `TseitinExpanderCommunicationPrinciple`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Signed Tseitin expander family at one scale -/

/-- A signed Tseitin/Mikoshi expander family at one input scale.

The SAT/UNSAT formulas and direction labels are concrete fields.  The graph
and expansion certificates are metadata for the future combinatorial theorem:
they are not used to assert the lower bound by definition. -/
structure SignedTseitinExpanderScale
    (enc : SignedFormulaEncoding) (n : Nat) : Type where
  hn : n >= 1
  directionCount : Nat
  directionCount_pos : 0 < directionCount
  direction_floor :
    Nat.choose (n / 3) (Nat.log 2 n) <= directionCount
  positiveInput : Fin directionCount -> Fin n -> Bool
  negativeInput : Fin directionCount -> Fin n -> Bool
  positiveFormula : Fin directionCount -> enc.Formula
  negativeFormula : Fin directionCount -> enc.Formula
  positive_encoded :
    forall d : Fin directionCount,
      enc.Encodes (positiveInput d) (positiveFormula d)
  negative_encoded :
    forall d : Fin directionCount,
      enc.Encodes (negativeInput d) (negativeFormula d)
  positive_satisfiable :
    forall d : Fin directionCount,
      enc.Satisfiable (positiveFormula d)
  negative_unsatisfiable :
    forall d : Fin directionCount,
      Not (enc.Satisfiable (negativeFormula d))
  directionOf :
    Fin directionCount -> SignedCounterfactualEKPDirection enc n
  direction_injective :
    Function.Injective directionOf
  parityFlipCoordinate : Fin directionCount -> Nat
  parityFlipCoordinate_injective :
    Function.Injective parityFlipCoordinate
  expanderVertices : Nat
  expanderEdges : Nat
  mikoshiContextNodes : Nat
  expansionCertificate : Prop
  expansionCertificate_cert : expansionCertificate

namespace SignedTseitinExpanderScale

/-- A signed SAT decider turns the semantic expander scale into signed
counterfactual EKP coverage. -/
def toCoverage
    {enc : SignedFormulaEncoding} {n : Nat}
    (S : SignedTseitinExpanderScale enc n)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M) :
    SignedCounterfactualEKPDirectionCoverage enc M n where
  hn := S.hn
  directionCount := S.directionCount
  directionCount_pos := S.directionCount_pos
  direction_floor := S.direction_floor
  positiveInput := S.positiveInput
  negativeInput := S.negativeInput
  positiveFormula := S.positiveFormula
  negativeFormula := S.negativeFormula
  positive_encoded := S.positive_encoded
  negative_encoded := S.negative_encoded
  positive_satisfiable := S.positive_satisfiable
  negative_unsatisfiable := S.negative_unsatisfiable
  positive_accepts := by
    intro d
    exact
      (hM S.hn (S.positiveInput d) (S.positiveFormula d)
        (S.positive_encoded d)).2 (S.positive_satisfiable d)
  negative_not_accepts := by
    intro d hacc
    have hs :
        enc.Satisfiable (S.negativeFormula d) :=
      (hM S.hn (S.negativeInput d) (S.negativeFormula d)
        (S.negative_encoded d)).1 hacc
    exact S.negative_unsatisfiable d hs
  directionOf := S.directionOf
  direction_injective := S.direction_injective

/-- A signed SAT decider turns an expander scale into the parity-flip boundary
used by the Mikoshi/spacetime observer files. -/
def toParityFlipBoundary
    {enc : SignedFormulaEncoding} {n : Nat}
    (S : SignedTseitinExpanderScale enc n)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M) :
    SignedTseitinParityFlipBoundary enc M n where
  coverage := S.toCoverage M hM
  parityFlipCoordinate := S.parityFlipCoordinate
  parityFlipCoordinate_injective := S.parityFlipCoordinate_injective
  positive_even_charge := S.positive_satisfiable
  negative_odd_charge := S.negative_unsatisfiable

/-- The generated boundary has exactly the scale's direction count. -/
theorem toParityFlipBoundary_directionCount
    {enc : SignedFormulaEncoding} {n : Nat}
    (S : SignedTseitinExpanderScale enc n)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M) :
    (S.toParityFlipBoundary M hM).coverage.directionCount =
      S.directionCount :=
  rfl

end SignedTseitinExpanderScale

/-! ## Asymptotic family and locality payload -/

/-- An asymptotic signed Tseitin/Mikoshi expander family. -/
structure AsymptoticSignedTseitinExpanderFamily
    (enc : SignedFormulaEncoding) : Type where
  scale : forall n : Nat, n >= 1 -> SignedTseitinExpanderScale enc n
  unboundedDirections : Prop
  unboundedDirections_cert : unboundedDirections
  expanderFamilyCertificate : Prop
  expanderFamilyCertificate_cert : expanderFamilyCertificate

namespace AsymptoticSignedTseitinExpanderFamily

/-- Boundary at scale `n` for a signed SAT decider. -/
def boundaryAt
    {enc : SignedFormulaEncoding}
    (F : AsymptoticSignedTseitinExpanderFamily enc)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M)
    (n : Nat)
    (hn : n >= 1) :
    SignedTseitinParityFlipBoundary enc M n :=
  (F.scale n hn).toParityFlipBoundary M hM

/-- Direction count at scale `n`. -/
def directionCountAt
    {enc : SignedFormulaEncoding}
    (F : AsymptoticSignedTseitinExpanderFamily enc)
    (n : Nat)
    (hn : n >= 1) : Nat :=
  (F.scale n hn).directionCount

end AsymptoticSignedTseitinExpanderFamily

/-- Locality theorem target for an asymptotic signed Tseitin/Mikoshi expander
family.

This is the remaining hard combinatorial/physical theorem.  It says that for
the canonical expander family, every physical realization of the induced
counterfactual boundary must communicate the independent parity-flip
directions through distinct local bandwidth slots. -/
structure TseitinExpanderCommunicationPrinciple
    {enc : SignedFormulaEncoding}
    (F : AsymptoticSignedTseitinExpanderFamily enc) : Type where
  communicatesDirections :
    forall (M : DTM) (hM : SignedDTMDecidesSAT enc M)
      (n : Nat) (hn : n >= 1),
        EveryRealizationCommunicatesDirections
          (F.boundaryAt M hM n hn)

/-- The communication principle gives the reducer payload at every scale. -/
def everyRealizationCommunicatesDirections_of_expanderPrinciple
    {enc : SignedFormulaEncoding}
    {F : AsymptoticSignedTseitinExpanderFamily enc}
    (H : TseitinExpanderCommunicationPrinciple F)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M)
    (n : Nat)
    (hn : n >= 1) :
    EveryRealizationCommunicatesDirections
      (F.boundaryAt M hM n hn) :=
  H.communicatesDirections M hM n hn

/-- Asymptotic signed Tseitin/Mikoshi spacetime observer boundary at any scale
whose direction count exceeds the P-class observer's local lightcone. -/
theorem spacetimeObserverBoundaryAt_of_asymptoticTseitinLightconeGap
    {enc : SignedFormulaEncoding}
    (F : AsymptoticSignedTseitinExpanderFamily enc)
    (H : TseitinExpanderCommunicationPrinciple F)
    (P : PClassLocalPhysicalObserver)
    (N : NPClassNonlocalBoundaryObserver)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M)
    (n : Nat)
    (hn : n >= 1)
    (hgap :
      P.observer.budget.localityLightconeLimit <
        F.directionCountAt n hn) :
    SpacetimeObserverBoundaryAt P N (F.boundaryAt M hM n hn) := by
  have hgap' :
      P.observer.budget.localityLightconeLimit <
        (F.boundaryAt M hM n hn).coverage.directionCount := by
    simpa [AsymptoticSignedTseitinExpanderFamily.boundaryAt,
      AsymptoticSignedTseitinExpanderFamily.directionCountAt,
      SignedTseitinExpanderScale.toParityFlipBoundary,
      SignedTseitinExpanderScale.toCoverage] using hgap
  exact
    spacetimeObserverBoundaryAt_of_directionCommunicationGap
      P N (F.boundaryAt M hM n hn)
      (H.communicatesDirections M hM n hn) hgap'

/-! ## Kernel-only axiom trace -/

#print axioms SignedTseitinExpanderScale.toCoverage
#print axioms SignedTseitinExpanderScale.toParityFlipBoundary
#print axioms everyRealizationCommunicatesDirections_of_expanderPrinciple
#print axioms spacetimeObserverBoundaryAt_of_asymptoticTseitinLightconeGap

end PallLean.Paper93.DeepMath.PathB
