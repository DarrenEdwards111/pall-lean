import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniformFutureEvaluatorFrontier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCanonicalMachineTarget
import PallLean.Step4Compiler

/-!
# Universal-model cash-out to the textbook `P ≠ NP` statement

The Route-G audits now isolate the hard machine-level endpoint as
`¬ SATDecisionInP U`.  This file formalizes the remaining model/class bridge:
when does that endpoint imply the repository's textbook definitions
`Step4Compiler.P ≠ Step4Compiler.NP`?

The bridge records one concrete Boolean language representing CNF SAT, its
membership in textbook `NP`, its NP-completeness cash-out, and both directions
of compilation between a textbook P decider and the chosen machine model.
Under those explicit adequacy fields, polynomial SAT decision in `U` is
equivalent to textbook `P = NP`.  Consequently the absence of a uniform future
evaluator, the absence of a polynomial SAT decider in `U`, and textbook
`P ≠ NP` are equivalent.

This is closure plumbing, not the lower bound.  A future concrete universal
machine can discharge the encoding/compilation fields.  The remaining hard
field is still `¬ SATDecisionInP U`; no theorem below assumes or manufactures
it.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalModelPvsNPCashout

open SATDepthMachine
open UniformFutureEvaluatorFrontier

/-- Adequacy of a concrete machine model for textbook CNF-SAT complexity.

`satLanguage_in_NP` and `collapse_of_satLanguage_in_P` package the standard
NP-membership and NP-completeness facts for the selected bitstring encoding.
The two compiler fields state that polynomial decision is preserved and
reflected between that encoding and the machine model `U`. -/
structure UniversalCNFSATModelBridge (U : MachineModel) where
  satLanguage : Step4Compiler.Language
  satLanguage_in_NP : satLanguage ∈ Step4Compiler.NP
  collapse_of_satLanguage_in_P :
    satLanguage ∈ Step4Compiler.P → Step4Compiler.P = Step4Compiler.NP
  compile_textbookP_to_model :
    satLanguage ∈ Step4Compiler.P → SATDecisionInP U
  reflect_model_to_textbookP :
    SATDecisionInP U → satLanguage ∈ Step4Compiler.P

namespace UniversalCNFSATModelBridge

/-- A textbook collapse makes the selected SAT language polynomial and hence
produces a polynomial SAT decider in the concrete model. -/
theorem satDecisionInP_of_P_eq_NP
    {U : MachineModel} (B : UniversalCNFSATModelBridge U)
    (hEq : Step4Compiler.P = Step4Compiler.NP) :
    SATDecisionInP U := by
  apply B.compile_textbookP_to_model
  rw [hEq]
  exact B.satLanguage_in_NP

/-- Conversely, model-level polynomial SAT decision reflects to a textbook P
decider for the selected NP-complete language, forcing `P = NP`. -/
theorem P_eq_NP_of_satDecisionInP
    {U : MachineModel} (B : UniversalCNFSATModelBridge U)
    (hSAT : SATDecisionInP U) :
    Step4Compiler.P = Step4Compiler.NP :=
  B.collapse_of_satLanguage_in_P (B.reflect_model_to_textbookP hSAT)

/-- **Exact adequacy theorem.**  Once the concrete encoding and compiler are
verified, model-level polynomial SAT decision is exactly textbook collapse. -/
theorem satDecisionInP_iff_P_eq_NP
    {U : MachineModel} (B : UniversalCNFSATModelBridge U) :
    SATDecisionInP U ↔ Step4Compiler.P = Step4Compiler.NP := by
  constructor
  · exact B.P_eq_NP_of_satDecisionInP
  · exact B.satDecisionInP_of_P_eq_NP

/-- The hard machine lower bound cashes out exactly as textbook `P ≠ NP`. -/
theorem no_satDecisionInP_iff_P_ne_NP
    {U : MachineModel} (B : UniversalCNFSATModelBridge U) :
    (¬ SATDecisionInP U) ↔ Step4Compiler.P ≠ Step4Compiler.NP := by
  rw [B.satDecisionInP_iff_P_eq_NP]

/-- Combine the previous audit with model adequacy: uniform evaluation of all
genuine SAT future queries is exactly textbook collapse. -/
theorem uniformFutureEvaluator_iff_P_eq_NP
    {U : MachineModel} (B : UniversalCNFSATModelBridge U) :
    Nonempty (UniformFutureQueryEvaluator U) ↔
      Step4Compiler.P = Step4Compiler.NP :=
  (uniformFutureQueryEvaluator_iff_SATDecisionInP U).trans
    B.satDecisionInP_iff_P_eq_NP

/-- Negated form: the desired uniform evaluator lower bound is exactly the
textbook separation after the universal-model bridge is discharged. -/
theorem no_uniformFutureEvaluator_iff_P_ne_NP
    {U : MachineModel} (B : UniversalCNFSATModelBridge U) :
    (¬ Nonempty (UniformFutureQueryEvaluator U)) ↔
      Step4Compiler.P ≠ Step4Compiler.NP := by
  rw [B.uniformFutureEvaluator_iff_P_eq_NP]

end UniversalCNFSATModelBridge

/-! ## Canonical small-step specialization -/

/-- The same adequacy package specialized to a canonical oracle-free
small-step surface. -/
abbrev CanonicalCNFSATModelBridge (C : CanonicalMachineSurface) :=
  UniversalCNFSATModelBridge C.toMachineModel

/-- Canonical deep SAT search, model no-decider, no uniform evaluator, and
textbook `P ≠ NP` all coincide once universality/encoding adequacy is supplied. -/
theorem canonicalDeepSATSearch_iff_P_ne_NP
    (C : CanonicalMachineSurface) (B : CanonicalCNFSATModelBridge C) :
    CanonicalDeepSATSearch C ↔ Step4Compiler.P ≠ Step4Compiler.NP := by
  rw [canonicalDeepSATSearch_iff_no_decider C]
  exact B.no_satDecisionInP_iff_P_ne_NP

/-- Explicit final closure package.  The bridge is concrete-model engineering;
`machineLowerBound` is the unresolved general lower bound. -/
structure RouteGUniversalClosurePackage (C : CanonicalMachineSurface) where
  modelBridge : CanonicalCNFSATModelBridge C
  machineLowerBound : ¬ CanonicalSATDecisionInP C

/-- A complete closure package proves the textbook theorem. -/
theorem RouteGUniversalClosurePackage.P_ne_NP
    {C : CanonicalMachineSurface} (K : RouteGUniversalClosurePackage C) :
    Step4Compiler.P ≠ Step4Compiler.NP :=
  K.modelBridge.no_satDecisionInP_iff_P_ne_NP.mp K.machineLowerBound

/-- Equivalent depth form of the final closure package. -/
def routeGUniversalClosurePackageOfDeepSATSearch
    (C : CanonicalMachineSurface) (B : CanonicalCNFSATModelBridge C)
    (hdeep : CanonicalDeepSATSearch C) :
    RouteGUniversalClosurePackage C where
  modelBridge := B
  machineLowerBound := (canonicalDeepSATSearch_iff_no_decider C).mp hdeep

/-!
## Audit verdict

The textbook cash-out is now exact.  After a concrete universal CNF encoding
and two polynomial compiler directions are verified, any one of the following
is equivalent to the others:

* no polynomial SAT decider in the universal model;
* no polynomial uniform evaluator for genuine SAT future syntax;
* canonical deep SAT search;
* textbook `P ≠ NP`.

The model bridge itself does not prove the separation.  The only unresolved
mathematical input in `RouteGUniversalClosurePackage` is
`machineLowerBound : ¬ CanonicalSATDecisionInP C`.  Supplying that field for a
universal surface is precisely the open P-versus-NP lower bound.
-/

end PallLean.Paper93.DeepMath.PathB.UniversalModelPvsNPCashout

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalModelPvsNPCashout.UniversalCNFSATModelBridge.satDecisionInP_iff_P_eq_NP
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalModelPvsNPCashout.UniversalCNFSATModelBridge.no_satDecisionInP_iff_P_ne_NP
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalModelPvsNPCashout.UniversalCNFSATModelBridge.no_uniformFutureEvaluator_iff_P_ne_NP
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalModelPvsNPCashout.canonicalDeepSATSearch_iff_P_ne_NP
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalModelPvsNPCashout.RouteGUniversalClosurePackage.P_ne_NP
