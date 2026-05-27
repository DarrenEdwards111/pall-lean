import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEKPSemanticForceAudit

/-!
# Counterfactual EKP semantic force

`ComputationalDepthEKPSemanticForceAudit` rules out the run-indexed reading of
EKP: paper-scale directions cannot inject into one polynomial-length DTM run.

This file records the surviving workaround shape.  An EKP direction is not a
time in one run; it is an intervention pair in the global correctness surface
of a SAT decider:

* a positive encoded input/formula that the machine accepts;
* a negative encoded input/formula that the machine does not accept;
* an injective direction label attached to that pair.

The sheet essentiality bridge is correspondingly narrowed.  We no longer ask
an arbitrary instrumented sheet to become essential from bare non-local
coverage.  Instead, the sheet must bind the counterfactual SAT/UNSAT switches:
the full compiled object accepts the positive side, while deleting/collapsing
the sheet loses the negative-side separation.

This is an interface layer.  It proves the wiring theorem and the removable
sheet guard, but it does not assert that the counterfactual coverage or sheet
binding theorem has been proved from Cook--Levin semantics.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open InstrumentedSheetAudit

/-! ## Counterfactual directions -/

/-- A lightweight EKP direction label at length `n`.  The mathematical content
is not the label itself; it is the injective assignment of labels to
SAT/UNSAT intervention pairs in `CounterfactualEKPDirectionCoverage`. -/
structure CounterfactualEKPDirection
    (_enc : ThreeCNFEncoding) (_n : Nat) where
  tag : Nat

/-- Counterfactual/interventional EKP coverage.

The directions are witnessed across the decider's global input-output surface,
not inside one execution trace.  This is why the run-indexed time-window bound
from `ComputationalDepthEKPSemanticForceAudit` does not apply directly.
-/
structure CounterfactualEKPDirectionCoverage
    (enc : ThreeCNFEncoding) (M : TuringMachine.DTM) (n : Nat) : Type where
  hn : n >= 1
  directionCount : Nat
  directionCount_pos : 0 < directionCount
  direction_floor :
    Nat.choose (n / 3) (Nat.log 2 n) <= directionCount
  positiveInput : Fin directionCount -> Fin n -> Bool
  negativeInput : Fin directionCount -> Fin n -> Bool
  positiveFormula : Fin directionCount -> ThreeCNF
  negativeFormula : Fin directionCount -> ThreeCNF
  positive_encoded :
    forall d : Fin directionCount,
      enc.Encodes (positiveInput d) (positiveFormula d)
  negative_encoded :
    forall d : Fin directionCount,
      enc.Encodes (negativeInput d) (negativeFormula d)
  positive_satisfiable :
    forall d : Fin directionCount,
      (positiveFormula d).IsSatisfiable
  negative_unsatisfiable :
    forall d : Fin directionCount,
      Not (negativeFormula d).IsSatisfiable
  positive_accepts :
    forall d : Fin directionCount,
      TuringMachine.accepts M n hn (positiveInput d)
  negative_not_accepts :
    forall d : Fin directionCount,
      Not (TuringMachine.accepts M n hn (negativeInput d))
  directionOf :
    Fin directionCount -> CounterfactualEKPDirection enc n
  direction_injective : Function.Injective directionOf

namespace CounterfactualEKPDirectionCoverage

/-- A canonical first direction, available because the coverage object carries
`directionCount_pos`. -/
def first
    {enc : ThreeCNFEncoding} {M : TuringMachine.DTM} {n : Nat}
    (C : CounterfactualEKPDirectionCoverage enc M n) :
    Fin C.directionCount :=
  ⟨0, C.directionCount_pos⟩

end CounterfactualEKPDirectionCoverage

/-- Fixed-scale counterfactual EKP force: every encoded SAT-deciding DTM has a
counterfactual intervention family at length `n`. -/
def CounterfactualEKPBoundaryVisibleAt
    (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  forall M : TuringMachine.DTM,
    DTMDecidesSATWithEncoding enc M ->
      Nonempty (CounterfactualEKPDirectionCoverage enc M n)

/-- Paper-scale counterfactual EKP force. -/
def CounterfactualClassicalSATDeciderForcesEKPBoundary
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 804 /\
    4 * (c + 1) <= Nat.log 2 n /\
    CounterfactualEKPBoundaryVisibleAt enc n

/-! ## Sheet binding -/

/-- The narrowed sheet-binding predicate for counterfactual EKP.

The acceptance predicate is still explicit, but it is no longer arbitrary
semantic slack: the fields say how it is forced by the actual intervention
pairs.  This is the intended replacement for the too-broad
`NonLocalEKPToTheorem207Essentiality` socket.
-/
structure SheetBindsCounterfactualSwitches
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
    (C : CounterfactualEKPDirectionCoverage enc M n) : Type where
  Accepts :
    MvPolynomial
      (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ ->
      Prop
  full_accepts_positive :
    forall d : Fin C.directionCount,
      TuringMachine.accepts M n C.hn (C.positiveInput d) ->
        Accepts S.extraction.paperCompiledPoly
  deleted_rejects_negative :
    forall d : Fin C.directionCount,
      Not (TuringMachine.accepts M n C.hn (C.negativeInput d)) ->
        Not (Accepts S.extraction.coupledSheet)
  sheetDirection : Fin C.directionCount -> Nat
  sheetDirection_injective : Function.Injective sheetDirection

/-- Counterfactual sheet binding implies ordinary Theorem-207 essentiality.

The proof uses one actual intervention pair from the counterfactual family.
The hard work is not here; it is proving `SheetBindsCounterfactualSwitches`
from the canonical Cook--Levin/Theorem-207 sheet semantics. -/
theorem theorem207SheetEssentialForAcceptance_of_counterfactualBinding
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (B : SheetBindsCounterfactualSwitches S C) :
    Theorem207SheetEssentialForAcceptance B.Accepts S := by
  let d := C.first
  exact ⟨
    B.full_accepts_positive d (C.positive_accepts d),
    B.deleted_rejects_negative d (C.negative_not_accepts d)
  ⟩

/-- Counterfactual EKP coverage and sheet binding produce the classical
semantic-force package. -/
theorem theorem207ClassicalSemanticForce_of_counterfactualEKP
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
    (C : CounterfactualEKPDirectionCoverage enc M n)
    (B : SheetBindsCounterfactualSwitches S C) :
    Nonempty (Theorem207ClassicalSemanticForce M n hn hn2 htb hns) := by
  exact ⟨{
    instrumented := S
    Accepts := B.Accepts
    essential := theorem207SheetEssentialForAcceptance_of_counterfactualBinding B
  }⟩

/-- The hard counterfactual bridge target: every relevant instrumented
Theorem-207 sheet must bind the counterfactual switches. -/
structure CounterfactualEKPToTheorem207Essentiality
    (enc : ThreeCNFEncoding) : Type where
  bind :
    forall {M : TuringMachine.DTM} {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
      (C : CounterfactualEKPDirectionCoverage enc M n),
        Nonempty (SheetBindsCounterfactualSwitches S C)

/-- The counterfactual bridge is a narrowed version of the earlier non-local
EKP-to-essentiality bridge. -/
def nonLocalEKPToTheorem207Essentiality_of_counterfactual
    (enc : ThreeCNFEncoding)
    (H : CounterfactualEKPToTheorem207Essentiality enc)
    (forget :
      forall {M : TuringMachine.DTM} {n : Nat},
        Nonempty (NonLocalEKPDirectionCoverage enc M n) ->
          Nonempty (CounterfactualEKPDirectionCoverage enc M n)) :
    NonLocalEKPToTheorem207Essentiality enc where
  bridge := by
    intro M n hn hn2 htb hns S Hcov
    rcases forget Hcov with ⟨C⟩
    rcases H.bind S C with ⟨B⟩
    exact ⟨B.Accepts,
      theorem207SheetEssentialForAcceptance_of_counterfactualBinding B⟩

/-! ## Paper-scale composition -/

/-- Paper-scale Theorem-207 semantic force follows from counterfactual EKP
coverage plus the counterfactual sheet-binding theorem. -/
theorem paperScaleTheorem207ClassicalSemanticForce_of_counterfactualEKP
    (enc : ThreeCNFEncoding)
    (Hcov : CounterfactualClassicalSATDeciderForcesEKPBoundary enc)
    (Hbind : CounterfactualEKPToTheorem207Essentiality enc) :
    PaperScaleTheorem207ClassicalSemanticForce enc := by
  intro c
  rcases Hcov c with ⟨n, hn804, hlog, Hat⟩
  have hn2 : n >= 2 :=
    le_trans
      (by
        have hpow : 2 ^ 1 <= 2 ^ 804 :=
          Nat.pow_le_pow_right (by norm_num : 1 <= 2) (by norm_num : 1 <= 804)
        simpa using hpow)
      hn804
  refine ⟨n, hn804, hn2, hlog, ?_⟩
  intro M hM htb hns S
  rcases Hat M hM with ⟨C⟩
  rcases Hbind.bind S C with ⟨B⟩
  exact ⟨{
    instrumented := S
    Accepts := B.Accepts
    essential := theorem207SheetEssentialForAcceptance_of_counterfactualBinding B
  }, rfl⟩

/-! ## Removable-sheet guard -/

/-- A removable/static sheet cannot bind a counterfactual EKP family. -/
theorem not_counterfactualBinding_of_removableSheet
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (Hremovable : Theorem207SheetRemovable S) :
    Not (Nonempty (SheetBindsCounterfactualSwitches S C)) := by
  intro hB
  rcases hB with ⟨B⟩
  exact Hremovable B.Accepts
    (theorem207SheetEssentialForAcceptance_of_counterfactualBinding B)

/-- Consequently, a global counterfactual bridge is impossible if it is asked
to bind a removable sheet for some counterfactual coverage family. -/
theorem not_counterfactualBridge_of_removableSheet
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
    (C : CounterfactualEKPDirectionCoverage enc M n)
    (Hremovable : Theorem207SheetRemovable S) :
    Not (Nonempty (CounterfactualEKPToTheorem207Essentiality enc)) := by
  intro hH
  rcases hH with ⟨H⟩
  rcases H.bind S C with ⟨B⟩
  exact Hremovable B.Accepts
    (theorem207SheetEssentialForAcceptance_of_counterfactualBinding B)

/-! ## Kernel-only axiom trace -/

#print axioms theorem207SheetEssentialForAcceptance_of_counterfactualBinding
#print axioms theorem207ClassicalSemanticForce_of_counterfactualEKP
#print axioms nonLocalEKPToTheorem207Essentiality_of_counterfactual
#print axioms paperScaleTheorem207ClassicalSemanticForce_of_counterfactualEKP
#print axioms not_counterfactualBinding_of_removableSheet
#print axioms not_counterfactualBridge_of_removableSheet

end PallLean.Paper93.DeepMath.PathB
