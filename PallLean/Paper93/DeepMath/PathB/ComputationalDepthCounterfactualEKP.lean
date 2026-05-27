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

/-! ## Actual intervention-pair semantics -/

/-- The part of counterfactual sheet binding that is forced by actual
positive/negative intervention runs alone.

This deliberately does not mention rank, minors, essentiality, or the
Theorem-207 polynomials.  It is the "observable" pair layer: the full decider
accepts the positive side, and it does not accept the negative side. -/
structure ActualCounterfactualPairFacts
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    (C : CounterfactualEKPDirectionCoverage enc M n) : Type where
  FullPositive : Fin C.directionCount -> Prop
  DeletedNegative : Fin C.directionCount -> Prop
  full_from_positive_run :
    forall d : Fin C.directionCount,
      TuringMachine.accepts M n C.hn (C.positiveInput d) ->
        FullPositive d
  deleted_from_negative_run :
    forall d : Fin C.directionCount,
      Not (TuringMachine.accepts M n C.hn (C.negativeInput d)) ->
        DeletedNegative d

namespace ActualCounterfactualPairFacts

/-- The canonical actual-pair facts already contained in a counterfactual EKP
coverage object.  This is the part that is genuinely obtained from actual
input pairs with no sheet/rank assumption. -/
def ofCoverage
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    (C : CounterfactualEKPDirectionCoverage enc M n) :
    ActualCounterfactualPairFacts C where
  FullPositive := fun d =>
    TuringMachine.accepts M n C.hn (C.positiveInput d)
  DeletedNegative := fun d =>
    Not (TuringMachine.accepts M n C.hn (C.negativeInput d))
  full_from_positive_run := fun _ h => h
  deleted_from_negative_run := fun _ h => h

end ActualCounterfactualPairFacts

/-- The missing Cook--Levin/Theorem-207 interpretation layer.

It is narrower than `SheetBindsCounterfactualSwitches`: the only allowed source
of full/deleted behavior is a family of actual intervention-pair facts.  The
remaining theorem is therefore no longer "assume essentiality"; it is "prove
that these actual pair facts are interpreted by the full/deleted Theorem-207
polynomials." -/
structure ActualPairPolynomialSemantics
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (P : ActualCounterfactualPairFacts C) : Type where
  Accepts :
    MvPolynomial
      (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ ->
      Prop
  full_poly_accepts_of_pair :
    forall d : Fin C.directionCount,
      P.FullPositive d ->
        Accepts S.extraction.paperCompiledPoly
  deleted_poly_rejects_of_pair :
    forall d : Fin C.directionCount,
      P.DeletedNegative d ->
        Not (Accepts S.extraction.coupledSheet)
  sheetDirection : Fin C.directionCount -> Nat
  sheetDirection_injective : Function.Injective sheetDirection

/-- Actual intervention-pair semantics, once interpreted by the full/deleted
Theorem-207 polynomials, yields the earlier sheet-binding predicate.

This theorem is the test result: actual pairs alone provide the pair facts, but
binding the sheet still requires a polynomial-semantics bridge. -/
def SheetBindsCounterfactualSwitches.ofActualPairPolynomialSemantics
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (P : ActualCounterfactualPairFacts C)
    (Hpoly : ActualPairPolynomialSemantics (S := S) P) :
    SheetBindsCounterfactualSwitches S C where
  Accepts := Hpoly.Accepts
  full_accepts_positive := fun d hrun =>
    Hpoly.full_poly_accepts_of_pair d (P.full_from_positive_run d hrun)
  deleted_rejects_negative := fun d hrun =>
    Hpoly.deleted_poly_rejects_of_pair d (P.deleted_from_negative_run d hrun)
  sheetDirection := Hpoly.sheetDirection
  sheetDirection_injective := Hpoly.sheetDirection_injective

/-- The same bridge, using the canonical pair facts already present in the
counterfactual coverage object. -/
def SheetBindsCounterfactualSwitches.ofCoveragePolynomialSemantics
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    (Hpoly :
      ActualPairPolynomialSemantics (S := S)
        (ActualCounterfactualPairFacts.ofCoverage C)) :
    SheetBindsCounterfactualSwitches S C :=
  SheetBindsCounterfactualSwitches.ofActualPairPolynomialSemantics
    (ActualCounterfactualPairFacts.ofCoverage C) Hpoly

/-- Pair-fact polynomial semantics is enough to produce ordinary
Theorem-207 essentiality. -/
theorem theorem207SheetEssentialForAcceptance_of_actualPairPolynomialSemantics
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {S : InstrumentedTheorem207Sheet M n hn hn2 htb hns}
    {C : CounterfactualEKPDirectionCoverage enc M n}
    {P : ActualCounterfactualPairFacts C}
    (Hpoly : ActualPairPolynomialSemantics (S := S) P) :
    Theorem207SheetEssentialForAcceptance Hpoly.Accepts S := by
  let d := C.first
  exact ⟨
    Hpoly.full_poly_accepts_of_pair d
      (P.full_from_positive_run d (C.positive_accepts d)),
    Hpoly.deleted_poly_rejects_of_pair d
      (P.deleted_from_negative_run d (C.negative_not_accepts d))
  ⟩

/-- The concrete hard target after the actual-pair refinement: every
instrumented sheet must interpret the actual intervention-pair facts through
its full/deleted polynomials. -/
structure ActualPairsToTheorem207PolynomialSemantics
    (enc : ThreeCNFEncoding) : Type where
  interpret :
    forall {M : TuringMachine.DTM} {n : Nat}
      {hn : n >= 2 ^ 804} {hn2 : n >= 2}
      {htb : M.timeBound <= 4} {hns : M.numStates <= n}
      (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns)
      (C : CounterfactualEKPDirectionCoverage enc M n),
        Nonempty
          (ActualPairPolynomialSemantics (S := S)
            (ActualCounterfactualPairFacts.ofCoverage C))

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

/-- Interpreting actual intervention pairs by the Theorem-207 polynomials is
strictly enough to recover the earlier counterfactual sheet-binding bridge. -/
def counterfactualBridge_of_actualPairPolynomialSemantics
    (enc : ThreeCNFEncoding)
    (H : ActualPairsToTheorem207PolynomialSemantics enc) :
    CounterfactualEKPToTheorem207Essentiality enc where
  bind := by
    intro M n hn hn2 htb hns S C
    rcases H.interpret S C with ⟨Hpoly⟩
    exact ⟨
      SheetBindsCounterfactualSwitches.ofCoveragePolynomialSemantics Hpoly
    ⟩

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

/-! ## Restricted-family local-edit witness surface -/

/-- A restricted Cook--Levin local-edit pair witness family.

This is the first concrete lemma-chain surface for counterfactual EKP:
for each direction we provide a positive/negative encoded pair linked by a
certified local edit, together with machine acceptance/rejection facts.

The hard theorem (not claimed here) is to construct this witness family from
canonical Cook--Levin reductions for a nontrivial SAT subfamily. -/
structure CookLevinLocalEditPairWitness
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
  directionOf : Fin directionCount -> CounterfactualEKPDirection enc n
  direction_injective : Function.Injective directionOf
  /-- Locality certificate placeholder: each pair differs by an admissible
  bounded local edit associated to the direction label. -/
  local_edit_witness : forall d : Fin directionCount, Prop

/-- Any restricted local-edit witness family induces a counterfactual EKP
coverage object. -/
def counterfactualCoverage_of_cookLevinLocalEditWitness
    {enc : ThreeCNFEncoding} {M : TuringMachine.DTM} {n : Nat}
    (W : CookLevinLocalEditPairWitness enc M n) :
    CounterfactualEKPDirectionCoverage enc M n where
  hn := W.hn
  directionCount := W.directionCount
  directionCount_pos := W.directionCount_pos
  direction_floor := W.direction_floor
  positiveInput := W.positiveInput
  negativeInput := W.negativeInput
  positiveFormula := W.positiveFormula
  negativeFormula := W.negativeFormula
  positive_encoded := W.positive_encoded
  negative_encoded := W.negative_encoded
  positive_satisfiable := W.positive_satisfiable
  negative_unsatisfiable := W.negative_unsatisfiable
  positive_accepts := W.positive_accepts
  negative_not_accepts := W.negative_not_accepts
  directionOf := W.directionOf
  direction_injective := W.direction_injective

/-- First concrete chain theorem:
restricted Cook--Levin local-edit pair witnesses are enough to obtain
counterfactual EKP boundary visibility at fixed scale. -/
theorem counterfactualEKPBoundaryVisibleAt_of_cookLevinLocalEditWitness
    (enc : ThreeCNFEncoding) (n : Nat)
    (Hw : forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        Nonempty (CookLevinLocalEditPairWitness enc M n)) :
    CounterfactualEKPBoundaryVisibleAt enc n := by
  intro M hM
  rcases Hw M hM with ⟨W⟩
  exact ⟨counterfactualCoverage_of_cookLevinLocalEditWitness W⟩

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
#print axioms theorem207SheetEssentialForAcceptance_of_actualPairPolynomialSemantics
#print axioms counterfactualBridge_of_actualPairPolynomialSemantics
#print axioms theorem207ClassicalSemanticForce_of_counterfactualEKP
#print axioms nonLocalEKPToTheorem207Essentiality_of_counterfactual
#print axioms paperScaleTheorem207ClassicalSemanticForce_of_counterfactualEKP
#print axioms not_counterfactualBinding_of_removableSheet
#print axioms not_counterfactualBridge_of_removableSheet

end PallLean.Paper93.DeepMath.PathB
