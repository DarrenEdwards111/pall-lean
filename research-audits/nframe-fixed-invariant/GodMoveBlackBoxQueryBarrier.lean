import GodMoveBooleanWireTable
import GodMoveDirectVerifierCircuit

/-!
# An adaptive scalar-query lower bound

A deterministic decision tree receives only the Boolean value of an unknown
function at each queried Boolean assignment. If it decides whether that
function is ever true, its all-zero-answer path must query every assignment.
For `n` Boolean inputs this requires at least `2^n` queries in the worst case.

The targets distinguishing an unqueried point from the zero function can be
realized by formulas with `n` unit clauses. Nevertheless, this is solely an
output-value oracle lower bound. The tree does not receive a circuit's syntax,
its internal wire values, or any other representation of the queried function.
It is not a lower bound for SAT computation, full-wire-row access, or the
repository's circuit-aware discovery algorithms.
-/

namespace GodMoveBlackBoxQueryBarrier

/-- Queries reveal one Boolean function value. Both adaptive continuations
are finite trees, and no circuit description is supplied to `run`. -/
inductive QueryTree (A : Type*) where
  | done (answer : Bool)
  | ask (point : A) (onFalse onTrue : QueryTree A)

def run {A : Type*} : QueryTree A → (A → Bool) → Bool
  | .done answer, _ => answer
  | .ask a no yes, f => if f a then run yes f else run no f

/-- The actual transcript points when every oracle response is false. -/
def zeroPath {A : Type*} : QueryTree A → List A
  | .done _ => []
  | .ask a no _ => a :: zeroPath no

/-- The number of queries on the longest branch of a finite tree. -/
def depth {A : Type*} : QueryTree A → ℕ
  | .done _ => 0
  | .ask _ no yes => 1 + max (depth no) (depth yes)

theorem zeroPath_length_le_depth {A : Type*} (t : QueryTree A) :
    (zeroPath t).length ≤ depth t := by
  induction t with
  | done => simp [zeroPath, depth]
  | ask a no yes ihno ihyes =>
    simp only [zeroPath, List.length_cons, depth]
    omega

/-- Matching all answers on the zero path reproduces that path's result,
even when later query choices depend on previous answers. -/
theorem run_eq_zero_of_zeroPath_false {A : Type*} (t : QueryTree A) (f : A → Bool)
    (hf : ∀ a ∈ zeroPath t, f a = false) : run t f = run t (fun _ => false) := by
  induction t with
  | done => rfl
  | ask a no yes ihno ihyes =>
    have ha := hf a (by simp [zeroPath])
    have hno : ∀ b ∈ zeroPath no, f b = false := by
      intro b hb
      exact hf b (by simp [zeroPath, hb])
    simpa [run, ha] using ihno hno

def singletonValue {A : Type*} [DecidableEq A] (a : A) : A → Bool :=
  fun x => decide (x = a)

/-- A true value hidden at an unqueried point is indistinguishable from the
zero function throughout the adaptive all-zero transcript. -/
theorem run_singleton_eq_zero_of_not_mem {A : Type*} [DecidableEq A]
    (t : QueryTree A) (a : A) (ha : a ∉ zeroPath t) :
    run t (singletonValue a) = run t (fun _ => false) := by
  apply run_eq_zero_of_zeroPath_false
  intro b hb
  have hba : b ≠ a := by
    intro heq
    exact ha (heq ▸ hb)
  simp [singletonValue, hba]

/-- Correctness for Boolean existence testing. This permits every Boolean
function as the unknown oracle; it imposes no circuit-inspection capability. -/
def DecidesExistence {A : Type*} (t : QueryTree A) : Prop :=
  ∀ f : A → Bool, run t f = true ↔ ∃ a, f a = true

/-- Only correctness on zero and on each singleton is needed for the bound. -/
theorem mem_zeroPath_of_distinguishes_singletons {A : Type*} [DecidableEq A]
    (t : QueryTree A) (hzero : run t (fun _ => false) = false)
    (hsingle : ∀ a, run t (singletonValue a) = true) (a : A) : a ∈ zeroPath t := by
  by_contra ha
  have heq := run_singleton_eq_zero_of_not_mem t a ha
  rw [hsingle, hzero] at heq
  contradiction

theorem every_point_mem_zeroPath {A : Type*} [DecidableEq A]
    (t : QueryTree A) (hcorrect : DecidesExistence t) (a : A) : a ∈ zeroPath t := by
  apply mem_zeroPath_of_distinguishes_singletons t
  · cases hz : run t (fun _ => false) with
    | false => rfl
    | true =>
      obtain ⟨b, hb⟩ := (hcorrect (fun _ => false)).mp hz
      contradiction
  · intro b
    exact (hcorrect (singletonValue b)).mpr ⟨b, by simp [singletonValue]⟩

theorem card_le_zeroPath_length {A : Type*} [Fintype A] [DecidableEq A]
    (t : QueryTree A) (hcorrect : DecidesExistence t) :
    Fintype.card A ≤ (zeroPath t).length := by
  have hcover : (Finset.univ : Finset A) ⊆ (zeroPath t).toFinset := by
    intro a _
    exact List.mem_toFinset.mpr (every_point_mem_zeroPath t hcorrect a)
  have hcard := Finset.card_le_card hcover
  have hc : Fintype.card A ≤ (zeroPath t).toFinset.card := by simpa using hcard
  exact hc.trans (List.toFinset_card_le (zeroPath t))

theorem card_le_depth {A : Type*} [Fintype A] [DecidableEq A]
    (t : QueryTree A) (hcorrect : DecidesExistence t) : Fintype.card A ≤ depth t :=
  (card_le_zeroPath_length t hcorrect).trans (zeroPath_length_le_depth t)

open GodMoveBooleanInterpolation GodMovePinnedSATQueries GodMoveDirectVerifierCircuit
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (output)

/-- Every exact deterministic scalar-query tester has an all-zero path of
at least `2^n` queries. This statement has no SAT machine as its subject. -/
theorem two_pow_le_zeroPath_length {n : ℕ} (t : QueryTree (Assignment n))
    (hcorrect : DecidesExistence t) : 2 ^ n ≤ (zeroPath t).length := by
  have h := card_le_zeroPath_length t hcorrect
  simpa [Assignment] using h

theorem two_pow_le_depth {n : ℕ} (t : QueryTree (Assignment n))
    (hcorrect : DecidesExistence t) : 2 ^ n ≤ depth t := by
  exact (two_pow_le_zeroPath_length t hcorrect).trans (zeroPath_length_le_depth t)

/-- The singleton oracle is the actual output of a direct verifier for the
unit clauses prescribing its one satisfying assignment. -/
theorem singletonValue_eq_unit_verifier {n : ℕ} (a b : Assignment n) :
    singletonValue a b = output (verifierCircuit n (assignmentUnits a)) b := by
  apply Bool.eq_iff_iff.mpr
  rw [verifierCircuit_computes]
  simp only [singletonValue, decide_eq_true_eq, eval_assignmentUnits_iff, extendAssignment_fin]
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

theorem assignmentUnits_length {n : ℕ} (a : Assignment n) :
    (assignmentUnits a).length = n := by simp [assignmentUnits]

/-- These oracle targets have linear gate count; their descriptions are
withheld by the query-tree model, so this is not circuit-aware hardness. -/
theorem unit_verifier_length_le {n : ℕ} (a : Assignment n) :
    (verifierCircuit n (assignmentUnits a)).length ≤ 5 * n + 1 := by
  have h := verifierCircuit_length_le n (assignmentUnits a)
  have harith : 3 * n + 2 * n + 1 = 5 * n + 1 := by omega
  simpa [assignmentUnits, List.map_map, Function.comp_def, harith] using h

/-- The same lower bound already holds when correctness is required only for
the zero output and the direct verifiers of unit-clause formulas. The tree
still receives their output values alone, with their descriptions withheld. -/
theorem two_pow_le_zeroPath_length_of_unit_tests {n : ℕ}
    (t : QueryTree (Assignment n)) (hzero : run t (fun _ => false) = false)
    (hunit : ∀ a : Assignment n,
      run t (output (verifierCircuit n (assignmentUnits a))) = true) :
    2 ^ n ≤ (zeroPath t).length := by
  have hsingle : ∀ a : Assignment n, run t (singletonValue a) = true := by
    intro a
    have heq : singletonValue a = output (verifierCircuit n (assignmentUnits a)) := by
      funext b
      exact singletonValue_eq_unit_verifier a b
    rw [heq]
    exact hunit a
  have hcover : (Finset.univ : Finset (Assignment n)) ⊆ (zeroPath t).toFinset := by
    intro a _
    exact List.mem_toFinset.mpr
      (mem_zeroPath_of_distinguishes_singletons t hzero hsingle a)
  have hcard : 2 ^ n ≤ (zeroPath t).toFinset.card := by
    simpa [Assignment] using Finset.card_le_card hcover
  exact hcard.trans (List.toFinset_card_le _)

end GodMoveBlackBoxQueryBarrier

#print axioms GodMoveBlackBoxQueryBarrier.run_eq_zero_of_zeroPath_false
#print axioms GodMoveBlackBoxQueryBarrier.run_singleton_eq_zero_of_not_mem
#print axioms GodMoveBlackBoxQueryBarrier.every_point_mem_zeroPath
#print axioms GodMoveBlackBoxQueryBarrier.two_pow_le_zeroPath_length
#print axioms GodMoveBlackBoxQueryBarrier.two_pow_le_depth
#print axioms GodMoveBlackBoxQueryBarrier.singletonValue_eq_unit_verifier
#print axioms GodMoveBlackBoxQueryBarrier.unit_verifier_length_le

#print axioms GodMoveBlackBoxQueryBarrier.two_pow_le_zeroPath_length_of_unit_tests
