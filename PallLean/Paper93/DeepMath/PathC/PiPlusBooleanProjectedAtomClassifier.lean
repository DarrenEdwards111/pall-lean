import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedTransitionAtom

/-!
# Local atom classifier for Boolean-projected Pi+

This file synthesizes the three local atom discharges now available:

* mixed Booleanity atom, same block: `X(i,false) * X(i,true)`;
* adjacency atom, distinct blocks: `1 - X(i,false) * X(j,false)`;
* transition atom, distinct blocks with coefficient: `1 - c • X(i,false) * X(j,false)`.

The common target is the paper one-window local row certificate: after raw `Pi+`,
Boolean normalization, and inverse pullback, the atom is a source SPDP row with
at most one extra derivative and zero extra multiplier degree.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- The three local Cook--Levin atom shapes handled unconditionally by the
Boolean-projected `Pi+` row calculus. -/
inductive BlockPiPlusBooleanProjectedLocalAtom
    {ι : Type*} :
    MvPolynomial (ι × Bool) ℚ → Prop
  | mixed (i : ι) :
      BlockPiPlusBooleanProjectedLocalAtom
        (((X (i, false)) * (X (i, true))) : MvPolynomial (ι × Bool) ℚ)
  | adjacency (i j : ι) (hij : i ≠ j) :
      BlockPiPlusBooleanProjectedLocalAtom (blockAdjacencyAtomFF i j)
  | transition (c : ℚ) (i j : ι) (hij : i ≠ j) :
      BlockPiPlusBooleanProjectedLocalAtom (blockTransitionAtomFF c i j)

/-- Unified one-window local certificate: every classified local atom has a
Boolean-projected `Pi+` pullback that is a source row with `(extraK,extraL) ≤
(1,0)`.  This is the local case-split seam needed before assembling the
Cook--Levin factored product. -/
theorem blockPiPlusBooleanProjectedLocalAtom_oneZeroRowCertificate
    {ι : Type*}
    {p : MvPolynomial (ι × Bool) ℚ}
    (hatom : BlockPiPlusBooleanProjectedLocalAtom (ι := ι) p) :
    BlockPiPlusBooleanProjectedOneZeroRowCertificate p := by
  classical
  cases hatom with
  | mixed i =>
      exact blockPiPlusBooleanProjectedOneZeroRowCertificate_mixed i
  | adjacency i j hij =>
      refine ⟨[], 1, by simp, by simp, ?_⟩
      exact blockPiPlus_booleanProjected_adjacencyAtomFF_pullback_zeroDerivativeRow
        (hij := hij)
  | transition c i j hij =>
      refine ⟨[], 1, by simp, by simp, ?_⟩
      exact blockPiPlus_booleanProjected_transitionAtomFF_pullback_zeroDerivativeRow
        (hij := hij) c

/-- Mixed atom constructor immediately supplies the unified one-window
certificate. -/
theorem blockPiPlusBooleanProjectedLocalAtom_mixed_oneZero
    {ι : Type*} (i : ι) :
    BlockPiPlusBooleanProjectedOneZeroRowCertificate
      (((X (i, false)) * (X (i, true))) : MvPolynomial (ι × Bool) ℚ) :=
  blockPiPlusBooleanProjectedLocalAtom_oneZeroRowCertificate
    (BlockPiPlusBooleanProjectedLocalAtom.mixed (ι := ι) i)

/-- Adjacency atom constructor immediately supplies the unified one-window
certificate. -/
theorem blockPiPlusBooleanProjectedLocalAtom_adjacency_oneZero
    {ι : Type*} {i j : ι} (hij : i ≠ j) :
    BlockPiPlusBooleanProjectedOneZeroRowCertificate (blockAdjacencyAtomFF i j) :=
  blockPiPlusBooleanProjectedLocalAtom_oneZeroRowCertificate
    (BlockPiPlusBooleanProjectedLocalAtom.adjacency (ι := ι) i j hij)

/-- Transition atom constructor immediately supplies the unified one-window
certificate. -/
theorem blockPiPlusBooleanProjectedLocalAtom_transition_oneZero
    {ι : Type*} {i j : ι} (hij : i ≠ j) (c : ℚ) :
    BlockPiPlusBooleanProjectedOneZeroRowCertificate (blockTransitionAtomFF c i j) :=
  blockPiPlusBooleanProjectedLocalAtom_oneZeroRowCertificate
    (BlockPiPlusBooleanProjectedLocalAtom.transition (ι := ι) c i j hij)

/-- Local atom closeout package: a finite case split over the three currently
implemented atom classes gives the paper one-window certificate. -/
def BlockPiPlusBooleanProjectedLocalAtomClassifierClosed
    {ι : Type*} : Prop :=
  ∀ {p : MvPolynomial (ι × Bool) ℚ},
    BlockPiPlusBooleanProjectedLocalAtom (ι := ι) p →
      BlockPiPlusBooleanProjectedOneZeroRowCertificate p

/-- The local atom classifier is closed unconditionally. -/
theorem blockPiPlusBooleanProjectedLocalAtomClassifierClosed_unconditional
    {ι : Type*} :
    BlockPiPlusBooleanProjectedLocalAtomClassifierClosed (ι := ι) := by
  intro p hp
  exact blockPiPlusBooleanProjectedLocalAtom_oneZeroRowCertificate hp

/-! ## Axiom audit anchors -/

#print axioms blockPiPlusBooleanProjectedLocalAtom_oneZeroRowCertificate
#print axioms blockPiPlusBooleanProjectedLocalAtom_mixed_oneZero
#print axioms blockPiPlusBooleanProjectedLocalAtom_adjacency_oneZero
#print axioms blockPiPlusBooleanProjectedLocalAtom_transition_oneZero
#print axioms blockPiPlusBooleanProjectedLocalAtomClassifierClosed_unconditional

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
