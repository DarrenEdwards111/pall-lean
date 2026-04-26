import PallLean.Paper93.Paper283.RouteBRicherGaugePWindowConcreteDischarge

/-!
# Sharper concreteW reduction for the Route B P-window cover

This module is a small wrapper layer over the existing concrete P-window
discharge.  It consumes the already-proved I1/I2/I3-to-I5 composition and
exposes the current smallest canonical `concreteW` frontier for the
unprojected P-window finite-span cover:

* direct branch-shape witnesses for the compiled Cook-Levin factors;
* canonical-row transport from direct rows to `Fin.castLEEmb`;
* H4 derivative closure for canonical `concreteW`;
* the composed concrete I5 shift/mlProj closure package.

The canonical H4 input remains explicit: the PathB concreteW files currently
record the endpoint-variable obstruction to proving H4 for unaugmented
canonical `concreteW`.
-/

namespace PallLean.Paper93.Paper283

open TuringMachine (DTM)
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW)
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Direct branch shapes plus canonical-row transport close the concreteW H3
factor-membership component.  Together with H4 and the already-composed
concrete I5 shift/mlProj package, this gives concreteW row embeddings. -/
theorem CookLevinPerTypeRowEmbeddings_concreteW_of_directBranchShapes_transport_H4_I5
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hTransport : CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4)
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI5 : ConcreteWShiftMlprojClosure n hn4) :
    PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
      M n hn htb hns hn4 :=
  CookLevinPerTypeRowEmbeddings_concreteW_of_H3_H4_I5
    M n hn htb hns hn4
    (CookLevinFactorMemPerType_concreteW_of_directBranchShapes_transport
      M n hn htb hns hn4 hShape hTransport)
    hDeriv
    (by
      simpa [ConcreteWShiftMlprojClosure, concreteWCanonical] using hI5)

/-- The same row-embedding reduction, with I5 discharged from the concrete
I1/I2/I3 component interfaces by the existing composition theorem. -/
theorem CookLevinPerTypeRowEmbeddings_concreteW_of_directBranchShapes_transport_H4_I123
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hTransport : CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4)
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
      M n hn htb hns hn4 :=
  CookLevinPerTypeRowEmbeddings_concreteW_of_directBranchShapes_transport_H4_I5
    M n hn htb hns hn4 hShape hTransport hDeriv
    (concreteW_shiftMlprojClosure_of_components n hn4 hI1 hI2 hI3)

/-- Direct branch shapes plus canonical-row transport, H4, and the composed
concrete I5 package are enough to build the richer-gauge unprojected
P-window finite-span cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_directBranchShapes_transport_H4_I5
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hTransport : CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4)
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI5 : ConcreteWShiftMlprojClosure n hn4) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_concreteW_rowEmbeddings
    M n hn htb hns hn4
    (CookLevinPerTypeRowEmbeddings_concreteW_of_directBranchShapes_transport_H4_I5
      M n hn htb hns hn4 hShape hTransport hDeriv hI5)

/-- Convenience surface retaining the concrete I1/I2/I3 inputs but consuming
their proved composition before entering the P-window cover. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_directBranchShapes_transport_H4_I123_components
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hTransport : CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4)
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_directBranchShapes_transport_H4_I5
    M n hn htb hns hn4 hShape hTransport hDeriv
    (concreteW_shiftMlprojClosure_of_components n hn4 hI1 hI2 hI3)

/-! ## Axiom audit anchors -/

#print axioms CookLevinPerTypeRowEmbeddings_concreteW_of_directBranchShapes_transport_H4_I5
#print axioms CookLevinPerTypeRowEmbeddings_concreteW_of_directBranchShapes_transport_H4_I123
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_directBranchShapes_transport_H4_I5
#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_directBranchShapes_transport_H4_I123_components

end PallLean.Paper93.Paper283
