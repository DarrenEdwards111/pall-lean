import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCanonicalMachineTarget
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

/-
# A concrete closed canonical surface

This file instantiates `CanonicalMachineSurface` with a small closed program
algebra.  The model has:

* a verifier decision tag;
* search behavior defined by the proved prefix-unit SAT decision-to-search
  self-reduction over the model's own decision behavior;
* no arbitrary `CNF -> Bool` or `CNF -> witness` semantic field.

This is a concrete canonical instantiation and discharges the compiler fields
for that instantiation.  It is intentionally not a universal machine model, so
it is not a P-vs-NP closure proof.  The remaining universal-machine/lower-bound
target is still separate.
-/

namespace SATDepthMachine

/-! ## Payload decrease for tagged verifier codes -/

theorem closed_right_lt_pair_of_left_pos {a b : Nat} (ha : 0 < a) :
    b < Nat.pair a b := by
  unfold Nat.pair
  by_cases h : a < b
  · rw [if_pos h]
    have hbpos : 0 < b := lt_trans ha h
    have hbmul : b ≤ b * b := Nat.le_mul_of_pos_right b hbpos
    exact lt_of_le_of_lt hbmul (Nat.lt_add_of_pos_right ha)
  · rw [if_neg h]
    have hpos : 0 < a * a + a := by nlinarith
    omega

theorem closed_unpair_right_lt_of_left_eq_pos
    {code tag : Nat}
    (hpos : 0 < tag)
    (htag : (Nat.unpair code).1 = tag) :
    (Nat.unpair code).2 < code := by
  calc
    (Nat.unpair code).2
        < Nat.pair tag (Nat.unpair code).2 :=
          closed_right_lt_pair_of_left_pos hpos
    _ = Nat.pair (Nat.unpair code).1 (Nat.unpair code).2 := by
          rw [htag]
    _ = code := Nat.pair_unpair code

/-! ## Closed program semantics -/

def closedVerifierTag : Nat := 2

def closedVerifierCode (searchCode : Nat) : Nat :=
  Nat.pair closedVerifierTag searchCode

/-- Decision semantics for the closed algebra.

The only nontrivial decision code is the verifier tag, which runs the search
behavior of the payload and checks the witness.  The search behavior itself is
inlined here to keep the recursion structurally decreasing on the payload code. -/
def closedDecisionRun : Nat -> CNF -> Bool :=
  WellFounded.fix (measure id).wf
    (fun code rec φ =>
      if htag : (Nat.unpair code).1 = closedVerifierTag then
        checkSearchOutput φ
          (some (searchFromPrefixOracle
            (prefixOracleOfSATDecider prefixUnitCNFReduction
              (fun ψ =>
                rec (Nat.unpair code).2
                  (closed_unpair_right_lt_of_left_eq_pos
                    (by decide) htag) ψ)) φ))
      else
        false)

/-- Search semantics for the closed algebra: bit-by-bit prefix self-reduction
against the closed decision semantics. -/
def closedSearchRun (code : Nat) (φ : CNF) : Option RawAssignment :=
  some (searchFromPrefixOracle
    (prefixOracleOfSATDecider prefixUnitCNFReduction
      (fun ψ => closedDecisionRun code ψ)) φ)

theorem closedSearchRun_eq_selfReduction
    (code : Nat) (φ : CNF) :
    closedSearchRun code φ =
      some (searchFromPrefixOracle
        (prefixOracleOfSATDecider prefixUnitCNFReduction
          (fun ψ => closedDecisionRun code ψ)) φ) := rfl

theorem closedDecisionRun_verifier
    (searchCode : Nat) (φ : CNF) :
    closedDecisionRun (closedVerifierCode searchCode) φ =
      checkSearchOutput φ (closedSearchRun searchCode φ) := by
  unfold closedDecisionRun closedSearchRun
  rw [WellFounded.fix_eq]
  simp [closedVerifierCode, closedVerifierTag, closedDecisionRun]

/-! ## Small-step state wrapper -/

inductive ClosedCanonicalState where
  | search (out : Option RawAssignment)
  | decision (out : Bool)
deriving Repr

def closedStep (s : ClosedCanonicalState) : ClosedCanonicalState := s

def closedSearchOutput : ClosedCanonicalState -> Option RawAssignment
  | ClosedCanonicalState.search out => out
  | ClosedCanonicalState.decision _ => none

def closedDecisionOutput : ClosedCanonicalState -> Bool
  | ClosedCanonicalState.search _ => false
  | ClosedCanonicalState.decision out => out

def closedInitSearch (code : Nat) (φ : CNF) : ClosedCanonicalState :=
  ClosedCanonicalState.search (closedSearchRun code φ)

def closedInitDecision (code : Nat) (φ : CNF) : ClosedCanonicalState :=
  ClosedCanonicalState.decision (closedDecisionRun code φ)

def closedSearchRuntime (_code : Nat) (φ : CNF) : Nat :=
  φ.size + 1

def closedDecisionRuntime (code : Nat) (φ : CNF) : Nat :=
  if (Nat.unpair code).1 = closedVerifierTag then
    closedSearchRuntime (Nat.unpair code).2 φ
  else
    0

theorem runFor_closedStep
    (t : Nat) (s : ClosedCanonicalState) :
    runFor closedStep t s = s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      simp [runFor_succ, closedStep, ih]

theorem canonicalSearchRun_closed
    (code : Nat) (φ : CNF) :
    canonicalSearchRunOf closedInitSearch closedStep closedSearchOutput
        closedSearchRuntime code φ =
      closedSearchRun code φ := by
  simp [canonicalSearchRunOf, closedInitSearch, closedSearchOutput,
    runFor_closedStep]

theorem canonicalDecisionRun_closed
    (code : Nat) (φ : CNF) :
    canonicalDecisionRunOf closedInitDecision closedStep closedDecisionOutput
        closedDecisionRuntime code φ =
      closedDecisionRun code φ := by
  simp [canonicalDecisionRunOf, closedInitDecision, closedDecisionOutput,
    runFor_closedStep]

theorem closedDecisionRuntime_verifier
    (searchCode : Nat) (φ : CNF) :
    closedDecisionRuntime (closedVerifierCode searchCode) φ =
      closedSearchRuntime searchCode φ := by
  simp [closedDecisionRuntime, closedVerifierCode, closedVerifierTag,
    closedSearchRuntime]

theorem closedCompiledBudget_poly
    (_code : Nat) :
    IsPolynomialBudget (fun n : Nat => n + 1) := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp

/-! ## Concrete canonical surface -/

/-- The concrete closed canonical surface.

`oracleFree` is represented here by a trivial certificate because this closed
algebra has no field that accepts an arbitrary SAT oracle.  Universality is not
claimed. -/
def closedCanonicalSurface : CanonicalMachineSurface where
  State := ClosedCanonicalState
  initSearch := closedInitSearch
  initDecision := closedInitDecision
  step := closedStep
  searchOutput := closedSearchOutput
  decisionOutput := closedDecisionOutput
  searchRuntime := closedSearchRuntime
  decisionRuntime := closedDecisionRuntime
  verifierCode := closedVerifierCode
  verifier_run := by
    intro code φ
    rw [canonicalDecisionRun_closed, canonicalSearchRun_closed,
      closedDecisionRun_verifier]
  verifier_steps := by
    intro code φ
    exact closedDecisionRuntime_verifier code φ
  compiledSearchCode := fun decisionCode => decisionCode
  compiledSearchBudget := fun _decisionCode n => n + 1
  compiledSearchPolyBudget := closedCompiledBudget_poly
  compiledSearch_steps_le := by
    intro decisionCode φ
    simp [closedSearchRuntime]
  compiledSearch_run_eq := by
    intro decisionCode φ
    rw [canonicalSearchRun_closed]
    rw [closedSearchRun_eq_selfReduction]
    simp [canonicalDecisionRun_closed]
  oracleFree := True
  oracleFree_cert := trivial

/-- The closure theorem specialized to the concrete closed canonical surface. -/
theorem closedCanonicalDeepSATSearch_iff_no_decider :
    CanonicalDeepSATSearch closedCanonicalSurface ↔
      ¬ CanonicalSATDecisionInP closedCanonicalSurface :=
  canonicalDeepSATSearch_iff_no_decider closedCanonicalSurface

/-- The lower-bound socket that remains for this concrete closed surface.  This
is not the final P-vs-NP target because `closedCanonicalSurface` is not a
universal machine model. -/
def ClosedCanonicalRemainingLowerBound : Prop :=
  CanonicalDeepSATSearch closedCanonicalSurface

theorem closedCanonicalNoDecider_of_remainingLowerBound
    (h : ClosedCanonicalRemainingLowerBound) :
    ¬ CanonicalSATDecisionInP closedCanonicalSurface :=
  (closedCanonicalDeepSATSearch_iff_no_decider).mp h

/-! ## Kernel-only axiom trace -/

#print axioms closedDecisionRun_verifier
#print axioms closedCanonicalSurface
#print axioms closedCanonicalDeepSATSearch_iff_no_decider
#print axioms closedCanonicalNoDecider_of_remainingLowerBound

end SATDepthMachine
