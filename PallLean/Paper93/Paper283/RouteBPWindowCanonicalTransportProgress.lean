import PallLean.Paper93.Paper283.RouteBRicherGaugePWindowConcreteWReduction

/-!
# P-window canonical-row transport progress

This file isolates a checked reduction for the H3 canonical-row transport
blocker used by the richer-gauge P-window cover.  The direct branch witnesses
already put each compiled factor in some row-indexed `concreteW`; the remaining
obstruction is row alignment for the booleanity and adjacency branches.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring

attribute [local instance] Classical.dec

/-- Direct branch witnesses are aligned with the canonical row slots.

For booleanity this says the direct variable is canonical slot `0`; for
adjacency it says the direct ordered pair is canonical slots `0,1`.  The
transition-left branch is already canonical in `CookLevinDirectBranchShapeWitnesses`.
-/
def CookLevinDirectBranchCanonicalRowAlignment
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4) :
    Prop :=
  (forall (i : Fin (cookLevinFactorList M n hn htb hns).length) (v : Fin n),
      cookLevinConstraintType M n hn htb hns i = ConstraintType.booleanity ->
      (cookLevinFactorList M n hn htb hns).get i =
        (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) Rat) ->
      v = (Fin.castLEEmb hn4) (0 : Fin 4)) /\
  (forall (i : Fin (cookLevinFactorList M n hn htb hns).length)
      (a b : Fin n),
      a ≠ b ->
      cookLevinConstraintType M n hn htb hns i = ConstraintType.adjacency ->
      (cookLevinFactorList M n hn htb hns).get i =
        (1 - MvPolynomial.X a * MvPolynomial.X b :
          MvPolynomial (Fin n) Rat) ->
      a = (Fin.castLEEmb hn4) (0 : Fin 4) /\
        b = (Fin.castLEEmb hn4) (1 : Fin 4))

/-- Direct branch shapes plus canonical slot alignment discharge the exact
canonical-row transport blocker for H3. -/
theorem CookLevinConcreteWCanonicalRowTransport_of_directBranchShapes_canonicalRowAlignment
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hAlign :
      CookLevinDirectBranchCanonicalRowAlignment M n hn htb hns hn4) :
    CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4 := by
  classical
  intro i _sigma _hmem
  rcases hAlign with ⟨hBoolAlign, hAdjAlign⟩
  rcases hShape i with hBool | hAdj | hLeft
  · rcases hBool with ⟨v, hType, hFactor⟩
    have hv : v = (Fin.castLEEmb hn4) (0 : Fin 4) :=
      hBoolAlign i v hType hFactor
    rw [hType, hFactor, hv]
    exact canonical_booleanity_factor_mem_concreteW n hn4
  · rcases hAdj with ⟨a, b, hab, hType, hFactor⟩
    rcases hAdjAlign i a b hab hType hFactor with ⟨ha, hb⟩
    rw [hType, hFactor, ha, hb]
    exact canonical_adjacency_factor_mem_concreteW n hn4
  · rcases hLeft with ⟨hType, hFactor⟩
    rw [hType, hFactor]
    exact canonical_transitionLeft_factor_mem_concreteW n hn4

/-- The same alignment reduction stated directly as the concrete H3
factor-membership theorem. -/
theorem CookLevinFactorMemPerType_concreteW_of_directBranchShapes_canonicalRowAlignment
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hAlign :
      CookLevinDirectBranchCanonicalRowAlignment M n hn htb hns hn4) :
    CookLevinFactorMemPerType M n hn htb hns
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) :=
  CookLevinFactorMemPerType_concreteW_of_directBranchShapes_transport
    M n hn htb hns hn4 hShape
    (CookLevinConcreteWCanonicalRowTransport_of_directBranchShapes_canonicalRowAlignment
      M n hn htb hns hn4 hShape hAlign)

/-! ## Axiom audit anchors -/

#print axioms CookLevinConcreteWCanonicalRowTransport_of_directBranchShapes_canonicalRowAlignment
#print axioms CookLevinFactorMemPerType_concreteW_of_directBranchShapes_canonicalRowAlignment

end PallLean.Paper93.DeepMath.PathB

namespace PallLean.Paper93.Paper283

open TuringMachine (DTM)
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW)
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- P-window cover wrapper with the H3 canonical-row transport discharged from
direct branch shapes plus canonical row-slot alignment. -/
noncomputable def routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_directBranchShapes_canonicalRowAlignment_H4_I5
    (M : DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hAlign :
      CookLevinDirectBranchCanonicalRowAlignment M n hn htb hns hn4)
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI5 : ConcreteWShiftMlprojClosure n hn4) :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn htb hns :=
  routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_directBranchShapes_transport_H4_I5
    M n hn htb hns hn4 hShape
    (CookLevinConcreteWCanonicalRowTransport_of_directBranchShapes_canonicalRowAlignment
      M n hn htb hns hn4 hShape hAlign)
    hDeriv hI5

/-! ## Axiom audit anchors -/

#print axioms routeBRicherGauge_unprojectedPWindowFiniteSpanCover_of_directBranchShapes_canonicalRowAlignment_H4_I5

end PallLean.Paper93.Paper283
