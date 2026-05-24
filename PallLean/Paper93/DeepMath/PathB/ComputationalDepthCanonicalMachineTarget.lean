import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMachineCompiler

/-
# Canonical computational-depth machine target

`ComputationalDepthSemanticMachine.lean` closed the wiring over a permissive
semantic surface.  That is useful for checking the reduction, but it is too
loose to be the final lower-bound target: arbitrary functions can bake in SAT.

This file introduces the stricter target needed next.  A canonical surface has
an explicit small-step state space: search and decision outputs are obtained by

  init(code, φ) -> step^t -> readOutput.

The prefix-unit SAT decision-to-search compiler is then packaged over this
small-step surface.  No P-vs-NP lower bound is proved here.  The theorem at the
bottom says exactly what remains: proving canonical deep SAT search is
equivalent to ruling out canonical polynomial-time SAT decision.
-/

namespace SATDepthMachine

/-! ## Small-step execution core -/

/-- Iterate a deterministic step function for `t` steps. -/
def runFor {State : Type} (step : State -> State) :
    Nat -> State -> State
  | 0, s => s
  | t + 1, s => runFor step t (step s)

@[simp] theorem runFor_zero
    {State : Type} (step : State -> State) (s : State) :
    runFor step 0 s = s := rfl

theorem runFor_succ
    {State : Type} (step : State -> State) (t : Nat) (s : State) :
    runFor step (t + 1) s = runFor step t (step s) := rfl

/-- Search run induced by a small-step state machine. -/
def canonicalSearchRunOf
    {State : Type}
    (initSearch : Nat -> CNF -> State)
    (step : State -> State)
    (searchOutput : State -> Option RawAssignment)
    (searchRuntime : Nat -> CNF -> Nat)
    (code : Nat) (φ : CNF) :
    Option RawAssignment :=
  searchOutput (runFor step (searchRuntime code φ) (initSearch code φ))

/-- Decision run induced by a small-step state machine. -/
def canonicalDecisionRunOf
    {State : Type}
    (initDecision : Nat -> CNF -> State)
    (step : State -> State)
    (decisionOutput : State -> Bool)
    (decisionRuntime : Nat -> CNF -> Nat)
    (code : Nat) (φ : CNF) :
    Bool :=
  decisionOutput (runFor step (decisionRuntime code φ) (initDecision code φ))

/-! ## Canonical target surface -/

/-- A canonical non-oracle target for the computational-depth route.

The semantic behavior is not supplied directly as `CNF -> ...`; it is read from
states reached by bounded iteration of a fixed transition function.  The
`oracleFree` field is a named proof obligation for concrete instantiations:
future work has to certify that the chosen state syntax and transition function
do not contain SAT as a primitive oracle.

The compiler fields state that this small-step surface contains the standard
prefix-unit decision-to-search program with polynomial overhead. -/
structure CanonicalMachineSurface where
  State : Type
  initSearch : Nat -> CNF -> State
  initDecision : Nat -> CNF -> State
  step : State -> State
  searchOutput : State -> Option RawAssignment
  decisionOutput : State -> Bool
  searchRuntime : Nat -> CNF -> Nat
  decisionRuntime : Nat -> CNF -> Nat
  verifierCode : Nat -> Nat
  verifier_run :
    ∀ (code : Nat) (φ : CNF),
      canonicalDecisionRunOf initDecision step decisionOutput decisionRuntime
          (verifierCode code) φ =
        checkSearchOutput φ
          (canonicalSearchRunOf initSearch step searchOutput searchRuntime
            code φ)
  verifier_steps :
    ∀ (code : Nat) (φ : CNF),
      decisionRuntime (verifierCode code) φ = searchRuntime code φ
  compiledSearchCode : Nat -> Nat
  compiledSearchBudget : Nat -> Nat -> Nat
  compiledSearchPolyBudget :
    ∀ code : Nat, IsPolynomialBudget (compiledSearchBudget code)
  compiledSearch_steps_le :
    ∀ (decisionCode : Nat) (φ : CNF),
      searchRuntime (compiledSearchCode decisionCode) φ ≤
        compiledSearchBudget decisionCode φ.size
  compiledSearch_run_eq :
    ∀ (decisionCode : Nat) (φ : CNF),
      canonicalSearchRunOf initSearch step searchOutput searchRuntime
          (compiledSearchCode decisionCode) φ =
        some (searchFromPrefixOracle
          (prefixOracleOfSATDecider prefixUnitCNFReduction
            (fun ψ =>
              canonicalDecisionRunOf initDecision step decisionOutput
                decisionRuntime decisionCode ψ)) φ)
  oracleFree : Prop
  oracleFree_cert : oracleFree

/-- Search semantics induced by a canonical surface. -/
def CanonicalMachineSurface.searchRun
    (C : CanonicalMachineSurface) : Nat -> CNF -> Option RawAssignment :=
  canonicalSearchRunOf C.initSearch C.step C.searchOutput C.searchRuntime

/-- Decision semantics induced by a canonical surface. -/
def CanonicalMachineSurface.decisionRun
    (C : CanonicalMachineSurface) : Nat -> CNF -> Bool :=
  canonicalDecisionRunOf C.initDecision C.step C.decisionOutput
    C.decisionRuntime

/-- Every canonical surface gives a `MachineModel`. -/
def CanonicalMachineSurface.toMachineModel
    (C : CanonicalMachineSurface) : MachineModel where
  searchRun := C.searchRun
  searchSteps := C.searchRuntime
  decisionRun := C.decisionRun
  decisionSteps := C.decisionRuntime
  verifierCode := C.verifierCode
  verifier_run := C.verifier_run
  verifier_steps := C.verifier_steps

/-- The prefix-unit compiler over a canonical small-step surface. -/
def CanonicalMachineSurface.toPrefixUnitMachineCompiler
    (C : CanonicalMachineSurface) :
    PrefixUnitMachineCompiler C.toMachineModel where
  compileCode := fun D _hD => C.compiledSearchCode D.code
  budget := fun D _hD => C.compiledSearchBudget D.code
  polyBudget := fun D _hD => C.compiledSearchPolyBudget D.code
  steps_le_budget := by
    intro D _hD φ
    exact C.compiledSearch_steps_le D.code φ
  run_eq := by
    intro D _hD φ
    exact C.compiledSearch_run_eq D.code φ

/-! ## Canonical closure statements -/

/-- Canonical shallow/deep SAT search is measured in the induced machine model. -/
abbrev CanonicalDeepSATSearch (C : CanonicalMachineSurface) : Prop :=
  DeepSATSearch C.toMachineModel

/-- Canonical polynomial-time SAT decision is measured in the induced machine
model. -/
abbrev CanonicalSATDecisionInP (C : CanonicalMachineSurface) : Prop :=
  SATDecisionInP C.toMachineModel

/-- The named oracle-free proof obligation carried by a canonical surface. -/
abbrev CanonicalOracleFree (C : CanonicalMachineSurface) : Prop :=
  C.oracleFree

theorem canonicalOracleFree_cert
    (C : CanonicalMachineSurface) : CanonicalOracleFree C :=
  C.oracleFree_cert

/-- Once the canonical small-step surface supplies the prefix-unit compiler,
the remaining depth lower bound is exactly the no-SAT-decider statement for that
same canonical target. -/
theorem canonicalDeepSATSearch_iff_no_decider
    (C : CanonicalMachineSurface) :
    CanonicalDeepSATSearch C ↔ ¬ CanonicalSATDecisionInP C :=
  deepSATSearch_iff_no_decider_with_prefixUnitCompiler
    C.toPrefixUnitMachineCompiler

/-- Positive closure direction for the canonical target. -/
theorem canonicalNoDecider_of_deepSATSearch
    (C : CanonicalMachineSurface)
    (hdeep : CanonicalDeepSATSearch C) :
    ¬ CanonicalSATDecisionInP C :=
  (canonicalDeepSATSearch_iff_no_decider C).mp hdeep

/-- Guard theorem: if a canonical polynomial SAT decider exists, then the
canonical depth lower bound is false, by the compiled prefix-unit
self-reduction. -/
theorem not_canonicalDeepSATSearch_of_decider
    (C : CanonicalMachineSurface)
    (hdec : CanonicalSATDecisionInP C) :
    ¬ CanonicalDeepSATSearch C := by
  intro hdeep
  exact (canonicalNoDecider_of_deepSATSearch C hdeep) hdec

/-! ## Kernel-only axiom trace -/

#print axioms CanonicalMachineSurface.toMachineModel
#print axioms CanonicalMachineSurface.toPrefixUnitMachineCompiler
#print axioms canonicalDeepSATSearch_iff_no_decider
#print axioms canonicalNoDecider_of_deepSATSearch
#print axioms not_canonicalDeepSATSearch_of_decider

end SATDepthMachine
