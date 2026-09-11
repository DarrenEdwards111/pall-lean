import GodMoveCachedRowFinder
import GodMoveCachedMachineDiscovery
import GodMoveDiscoveryClockBudget

/-!
# The exact SAT query trace of cached discovery

The instrumented finder reads its coefficients from the materialized residual
matrix. Its trace agrees word for word with the original finder, including
adaptive witness prefixes and early termination. Cached insertion preserves
this equality through all subsequent discovery rounds.

Consequently the previous summed SAT-clock bound applies to the cached
algorithm's actual query words. Host arithmetic, allocation, encoding, and
integer implementation costs remain outside that clock sum.
-/

namespace GodMoveCachedDiscoveryTrace

open GodMoveBooleanInterpolation GodMoveBooleanWireTable
open GodMoveCachedDiscoveryBasis GodMoveCachedResidualMatrix
open GodMoveTrackedOrthogonalization (Row rowValue)
open GodMoveRationalMachineQuery GodMoveResidualQueries
open GodMoveDiscoveryClockTrace (Traced witness clockSum)
open GodMoveCachedMachineDiscovery (cachedWireRow cachedWireRow_value)
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine

/-- The matrix is supplied once; each attempted relation reads its stored row. -/
def scan (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n))
    (Q : Vector (Row c.length) c.length) :
    List (Fin c.length) → Traced (Option (Assignment n))
  | [] => ⟨none, []⟩
  | j :: js =>
      let q := rowValue Q[j]
      let attempt := witness M T (rationalQuery c q (coefficientBits q))
      match attempt.value with
      | some a => ⟨some a, attempt.words⟩
      | none =>
          let rest := scan M T c Q js
          ⟨rest.value, attempt.words ++ rest.words⟩

/-- Erasing the trace recovers the materialized finder's exact output and
SAT-call counter, for every stored matrix, before using any semantic identity. -/
theorem scan_erase (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n))
    (Q : Vector (Row c.length) c.length) (js : List (Fin c.length)) :
    (scan M T c Q js).eraseCount = GodMoveCachedRowFinder.findIn M T c Q js := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      cases h : (GodMoveMachineCircuitOracle.findWitnessWithCount M T
        (rationalQuery c (rowValue Q[j]) (coefficientBits (rowValue Q[j])))).1 with
      | none =>
          have hv := congrArg Prod.fst ih
          have hl := congrArg Prod.snd ih
          simp only [Traced.eraseCount, scan, GodMoveDiscoveryClockTrace.witness_value,
            GodMoveDiscoveryClockTrace.witness_words_length,
            rationalWitnessWithCount, h, GodMoveCachedRowFinder.findIn,
            List.length_append] at *
          exact Prod.ext hv (congrArg (fun z =>
            (rationalWitnessWithCount M T c (rowValue Q[j])
              (coefficientBits (rowValue Q[j]))).2 + z) hl)
      | some a =>
          simp only [Traced.eraseCount, scan, GodMoveDiscoveryClockTrace.witness_value,
            GodMoveDiscoveryClockTrace.witness_words_length,
            rationalWitnessWithCount, h, GodMoveCachedRowFinder.findIn]

theorem scan_eq_original (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n))
    (B : CachedBasis c.length) (Q : Vector (Row c.length) c.length)
    (hQ : ∀ j, rowValue Q[j] = residualCoefficients B.toRowBasis j)
    (js : List (Fin c.length)) :
    scan M T c Q js = GodMoveDiscoveryClockTrace.scan M T c B.toRowBasis js := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      simp only [scan, hQ, GodMoveDiscoveryClockTrace.scan,
        GodMoveDiscoveryClockTrace.attempt, ih]
      rfl

def row (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : CachedBasis c.length) : Traced (Option (Assignment n)) :=
  let Q := residualMatrix B
  scan M T c Q.value (List.ofFn (fun j : Fin c.length => j))

theorem row_erase (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : CachedBasis c.length) :
    (row M T c B).eraseCount = (GodMoveCachedRowFinder.findRowWithCount M T c B).value :=
  scan_erase M T c _ _

theorem row_eq_original (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : CachedBasis c.length) :
    row M T c B = GodMoveDiscoveryClockTrace.row M T c B.toRowBasis :=
  scan_eq_original M T c B _ (residualMatrix_row B) _

def discovery (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    ℕ → CachedBasis c.length → Traced (List (Assignment n))
  | 0, _ => ⟨[], []⟩
  | fuel + 1, B =>
      let q := row M T c B
      match q.value with
      | none => ⟨[], q.words⟩
      | some a =>
          let next := insert B (cachedWireRow c a)
          let rest := discovery M T c fuel next.value
          ⟨a :: rest.value, q.words ++ rest.words⟩

/-- Full trace equality is proved by the actual branch recursion, rather than
inferred from equality of outputs or call counts. -/
theorem discovery_eq_original (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (fuel : ℕ) (B : CachedBasis c.length) :
    discovery M T c fuel B = GodMoveDiscoveryClockTrace.discovery M T c fuel B.toRowBasis := by
  induction fuel generalizing B with
  | zero => rfl
  | succ fuel ih =>
      simp only [discovery, row_eq_original, GodMoveDiscoveryClockTrace.discovery,
        ih, insert_value, cachedWireRow_value]
      rfl

theorem discovery_erase (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (fuel : ℕ) (B : CachedBasis c.length) :
    (discovery M T c fuel B).value =
        (GodMoveCachedMachineDiscovery.discover M T c fuel B).value.samples ∧
      (discovery M T c fuel B).words.length =
        (GodMoveCachedMachineDiscovery.discover M T c fuel B).value.queries := by
  rw [discovery_eq_original, GodMoveCachedMachineDiscovery.discover_value]
  exact ⟨GodMoveDiscoveryClockTrace.discovery_value M T c fuel B.toRowBasis,
    GodMoveDiscoveryClockTrace.discovery_words_length M T c fuel B.toRowBasis⟩

def search (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) : Traced (List (Assignment n)) :=
  discovery M T c (c.length + 1) (empty c.length)

theorem search_eq_original (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) : search M T c = GodMoveDiscoveryClockTrace.search M T c := by
  simp only [search, discovery_eq_original, empty_value, GodMoveDiscoveryClockTrace.search]

theorem search_erase (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    (search M T c).value = GodMoveCachedMachineDiscovery.machineSamples M T c ∧
      (search M T c).words.length =
        (GodMoveCachedMachineDiscovery.machineSearch M T c).value.queries :=
  discovery_erase M T c _ _

def searchClock (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) : ℕ :=
  clockSum T (search M T c).words

theorem searchClock_eq_original (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) : searchClock M T c = GodMoveDiscoveryClockTrace.searchClock M T c := by
  rw [searchClock, search_eq_original]
  rfl

theorem searchClock_le_polynomial (M : Machine) (T : ℕ → ℕ) (C d : ℕ)
    (hT : ∀ m, T m ≤ C * (m + 1) ^ d) {n : ℕ} (c : List (CGate n)) :
    searchClock M T c ≤ (C * 500000000 ^ d) * (n + c.length + 1) ^ (16 * d + 3) := by
  rw [searchClock_eq_original]
  exact GodMoveDiscoveryClockBudget.searchClock_le_polynomial M T C d hT c

end GodMoveCachedDiscoveryTrace

#print axioms GodMoveCachedDiscoveryTrace.scan_erase
#print axioms GodMoveCachedDiscoveryTrace.scan_eq_original
#print axioms GodMoveCachedDiscoveryTrace.row_erase
#print axioms GodMoveCachedDiscoveryTrace.row_eq_original
#print axioms GodMoveCachedDiscoveryTrace.discovery_eq_original
#print axioms GodMoveCachedDiscoveryTrace.discovery_erase
#print axioms GodMoveCachedDiscoveryTrace.search_eq_original
#print axioms GodMoveCachedDiscoveryTrace.search_erase
#print axioms GodMoveCachedDiscoveryTrace.searchClock_eq_original
#print axioms GodMoveCachedDiscoveryTrace.searchClock_le_polynomial
