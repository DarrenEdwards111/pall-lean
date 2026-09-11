import GodMoveMachineDiscoveryPrecision

/-!
# The actual SAT words emitted by adaptive discovery

These executable variants record the word at each actual `decideOut` call.
Erasing the log gives the existing discovery result and its exact call counter.
The log includes adaptive witness prefixes and coordinate scans, and stops at
the same early exits as the existing program. Recording a log is not asserted
to have zero host cost; this module isolates the invoked machine computations.
-/

namespace GodMoveDiscoveryClockTrace

open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveRationalRowBasis
open GodMoveResidualQueries GodMoveMachineRowFinder GodMoveMachineDiscovery
open GodMoveRationalMachineQuery GodMoveSignedBinary GodMoveMachineCircuitOracle
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine SeparationTarget

structure Traced (α : Type) where
  value : α
  words : List (List Bool)

def Traced.eraseCount {α : Type} (r : Traced α) : α × ℕ := (r.value, r.words.length)

/-- Exactly one machine call on the word stored in the singleton log. -/
def ask (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) : Traced Bool :=
  let w := circuitQuery c
  ⟨decideOut M w (T w.length), [w]⟩

@[simp] theorem ask_value (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    (ask M T c).value = circuitSAT M T c := rfl

@[simp] theorem ask_words (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    (ask M T c).words = [circuitQuery c] := rfl

def descend (M : Machine) (T : ℕ → ℕ) :
    (n : ℕ) → List (CGate n) → Traced (Assignment n)
  | 0, _ => ⟨fun i => Fin.elim0 i, []⟩
  | n + 1, c =>
      let q := ask M T (fixHead c false)
      let b := if q.value then false else true
      let rest := descend M T n (fixHead c b)
      ⟨Fin.cons b rest.value, q.words ++ rest.words⟩

@[simp] theorem descend_value (M : Machine) (T : ℕ → ℕ)
    (n : ℕ) (c : List (CGate n)) :
    (descend M T n c).value = (descendWithCount M T n c).1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [descend, ask_value, descendWithCount, ih]

@[simp] theorem descend_words_length (M : Machine) (T : ℕ → ℕ)
    (n : ℕ) (c : List (CGate n)) : (descend M T n c).words.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [descend, ask_words, List.length_append,
      List.length_singleton, ih]; omega

theorem descend_erase (M : Machine) (T : ℕ → ℕ) (n : ℕ) (c : List (CGate n)) :
    (descend M T n c).eraseCount = descendWithCount M T n c := by
  apply Prod.ext
  · exact descend_value M T n c
  · simp [Traced.eraseCount, descendWithCount_count]

def witness (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) : Traced (Option (Assignment n)) :=
  let q := ask M T c
  if q.value then
    let rest := descend M T n c
    ⟨some rest.value, q.words ++ rest.words⟩
  else ⟨none, q.words⟩

theorem witness_erase (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    (witness M T c).eraseCount = findWitnessWithCount M T c := by
  cases h : circuitSAT M T c <;>
    simp [witness, Traced.eraseCount, findWitnessWithCount, h,
      descendWithCount_count]

@[simp] theorem witness_value (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    (witness M T c).value = (findWitnessWithCount M T c).1 :=
  congrArg Prod.fst (witness_erase M T c)

@[simp] theorem witness_words_length (M : Machine) (T : ℕ → ℕ)
    {n : ℕ} (c : List (CGate n)) :
    (witness M T c).words.length = (findWitnessWithCount M T c).2 :=
  congrArg Prod.snd (witness_erase M T c)

def attempt (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (j : Fin c.length) :
    Traced (Option (Assignment n)) :=
  let q := residualCoefficients B j
  witness M T (rationalQuery c q (coefficientBits q))

theorem attempt_erase (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (j : Fin c.length) :
    (attempt M T c B j).eraseCount = rowAttempt M T c B j :=
  witness_erase M T _

@[simp] theorem attempt_value (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (j : Fin c.length) :
    (attempt M T c B j).value = (rowAttempt M T c B j).1 :=
  congrArg Prod.fst (attempt_erase M T c B j)

@[simp] theorem attempt_words_length (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (j : Fin c.length) :
    (attempt M T c B j).words.length = (rowAttempt M T c B j).2 :=
  congrArg Prod.snd (attempt_erase M T c B j)

def scan (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) :
    List (Fin c.length) → Traced (Option (Assignment n))
  | [] => ⟨none, []⟩
  | j :: js =>
      let q := attempt M T c B j
      match q.value with
      | some a => ⟨some a, q.words⟩
      | none =>
          let rest := scan M T c B js
          ⟨rest.value, q.words ++ rest.words⟩

theorem scan_erase (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (js : List (Fin c.length)) :
    (scan M T c B js).eraseCount = findIn M T c B js := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      cases h : (rowAttempt M T c B j).1 with
      | none =>
          have hv := congrArg Prod.fst ih
          have hl := congrArg Prod.snd ih
          simp only [Traced.eraseCount, scan, attempt_value, h, findIn,
            List.length_append, attempt_words_length] at *
          exact Prod.ext hv (congrArg (fun z => (rowAttempt M T c B j).2 + z) hl)
      | some a =>
          simp only [Traced.eraseCount, scan, attempt_value, h, findIn,
            attempt_words_length]

@[simp] theorem scan_value (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (js : List (Fin c.length)) :
    (scan M T c B js).value = (findIn M T c B js).1 :=
  congrArg Prod.fst (scan_erase M T c B js)

@[simp] theorem scan_words_length (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (js : List (Fin c.length)) :
    (scan M T c B js).words.length = (findIn M T c B js).2 :=
  congrArg Prod.snd (scan_erase M T c B js)

def row (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) : Traced (Option (Assignment n)) :=
  scan M T c B (List.ofFn (fun j : Fin c.length => j))

@[simp] theorem row_value (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) :
    (row M T c B).value = (findRowWithCount M T c B).1 := scan_value M T c B _

@[simp] theorem row_words_length (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) :
    (row M T c B).words.length = (findRowWithCount M T c B).2 := scan_words_length M T c B _

def discovery (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    ℕ → RowBasis c.length → Traced (List (Assignment n))
  | 0, _ => ⟨[], []⟩
  | fuel + 1, B =>
      let q := row M T c B
      match q.value with
      | none => ⟨[], q.words⟩
      | some a =>
          let rest := discovery M T c fuel (insert B (wireRow c a))
          ⟨a :: rest.value, q.words ++ rest.words⟩

@[simp] theorem discovery_value (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length) :
    (discovery M T c fuel B).value = (discover M T c fuel B).samples := by
  induction fuel generalizing B with
  | zero => rfl
  | succ fuel ih =>
      cases h : (findRowWithCount M T c B).1 <;>
        simp only [discovery, row_value, h, discover, ih]

@[simp] theorem discovery_words_length (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length) :
    (discovery M T c fuel B).words.length = (discover M T c fuel B).queries := by
  induction fuel generalizing B with
  | zero => rfl
  | succ fuel ih =>
      cases h : (findRowWithCount M T c B).1 <;>
        simp only [discovery, row_value, h, discover, List.length_append,
          row_words_length, ih]

def search (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) : Traced (List (Assignment n)) :=
  discovery M T c (c.length + 1) (empty c.length)

theorem search_erase (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    (search M T c).value = machineSamples M T c ∧
      (search M T c).words.length = (machineSearch M T c).queries :=
  ⟨discovery_value M T c _ _, discovery_words_length M T c _ _⟩

/-- The sum uses the length of each actual emitted word, retaining multiplicity. -/
def clockSum (T : ℕ → ℕ) (words : List (List Bool)) : ℕ :=
  (words.map (fun w => T w.length)).sum

def searchClock (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) : ℕ :=
  clockSum T (search M T c).words

theorem search_words_halt (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    ∀ w ∈ (search M T c).words, HaltsBy M w (T w.length) :=
  fun w _ => (hD w).1

end GodMoveDiscoveryClockTrace

#print axioms GodMoveDiscoveryClockTrace.descend_erase
#print axioms GodMoveDiscoveryClockTrace.witness_erase
#print axioms GodMoveDiscoveryClockTrace.attempt_erase
#print axioms GodMoveDiscoveryClockTrace.scan_erase
#print axioms GodMoveDiscoveryClockTrace.discovery_value
#print axioms GodMoveDiscoveryClockTrace.discovery_words_length
#print axioms GodMoveDiscoveryClockTrace.search_erase
#print axioms GodMoveDiscoveryClockTrace.search_words_halt
