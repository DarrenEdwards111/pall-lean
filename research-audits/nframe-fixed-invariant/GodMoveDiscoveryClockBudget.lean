import GodMoveDiscoveryClockTrace

/-!
# Summing the actual SAT clocks used in discovery

The clock sum is over the exact executable query log, including all adaptive
witness prefixes, coordinate scans, and early termination. Query sizes follow
from the previously derived precision of the actual sampled states. A supplied
polynomial SAT clock therefore bounds the summed invoked machine clocks.

The result excludes host arithmetic, circuit construction, encoding, copying,
and interpreter overhead. It neither supplies a SAT decider nor bounds a
shifted partial derivative space.
-/

namespace GodMoveDiscoveryClockBudget

open GodMoveDiscoveryClockTrace GodMoveMachineDiscoveryPrecision
open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveRationalRowBasis
open GodMoveResidualQueries GodMoveMachineRowFinder GodMoveMachineDiscovery
open GodMoveRationalMachineQuery GodMoveSignedBinary GodMoveMachineCircuitOracle
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine SeparationTarget

def wordBudget (n s : ℕ) : ℕ :=
  100 * (n + queryGateBudget s (precisionBudget s) + 1) ^ 2

private theorem encodedBudget_mono {n m s t : ℕ} (hn : n ≤ m) (hs : s ≤ t) :
    100 * (n + s + 1) ^ 2 ≤ 100 * (m + t + 1) ^ 2 := by gcongr

/-- Every adaptive restriction is covered: specialization preserves the gate
count while removing one input coordinate. -/
theorem descend_word_length (M : Machine) (T : ℕ → ℕ)
    (n : ℕ) (c : List (CGate n)) :
    ∀ w ∈ (descend M T n c).words, w.length ≤ 100 * (n + c.length + 1) ^ 2 := by
  induction n with
  | zero => simp [descend]
  | succ n ih =>
      intro w hw
      simp only [descend, ask_words, List.singleton_append, List.mem_cons] at hw
      rcases hw with hw | hw
      · subst w
        exact (circuitQuery_length_le _).trans
          (encodedBudget_mono (Nat.le_succ n) (le_of_eq (fixHead_length c false)))
      · exact (ih _ w hw).trans
          (encodedBudget_mono (Nat.le_succ n) (le_of_eq (fixHead_length c _)))

theorem witness_word_length (M : Machine) (T : ℕ → ℕ)
    {n : ℕ} (c : List (CGate n)) :
    ∀ w ∈ (witness M T c).words, w.length ≤ 100 * (n + c.length + 1) ^ 2 := by
  intro w hw
  cases h : circuitSAT M T c with
  | false =>
      simp only [witness, ask_value, h, Bool.false_eq_true, ↓reduceIte,
        ask_words, List.mem_singleton] at hw
      subst w
      exact circuitQuery_length_le c
  | true =>
      simp only [witness, ask_value, h, ↓reduceIte, ask_words,
        List.singleton_append, List.mem_cons] at hw
      rcases hw with hw | hw
      · subst w; exact circuitQuery_length_le c
      · exact descend_word_length M T n c w hw

theorem attempt_word_length (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (hB : StatePrecision B)
    (j : Fin c.length) :
    ∀ w ∈ (attempt M T c B j).words, w.length ≤ wordBudget n c.length := by
  intro w hw
  exact (witness_word_length M T _ w hw).trans
    (encodedBudget_mono (le_refl n) (state_query_gates_le c B hB j))

theorem scan_word_length (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (hB : StatePrecision B)
    (js : List (Fin c.length)) :
    ∀ w ∈ (scan M T c B js).words, w.length ≤ wordBudget n c.length := by
  induction js with
  | nil => simp [GodMoveDiscoveryClockTrace.scan]
  | cons j js ih =>
      intro w hw
      cases h : (rowAttempt M T c B j).1 with
      | none =>
          simp only [GodMoveDiscoveryClockTrace.scan, attempt_value, h, List.mem_append] at hw
          exact hw.elim (attempt_word_length M T c B hB j w) (ih w)
      | some a =>
          simp only [GodMoveDiscoveryClockTrace.scan, attempt_value, h] at hw
          exact attempt_word_length M T c B hB j w hw

theorem row_word_length (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (hB : StatePrecision B) :
    ∀ w ∈ (row M T c B).words, w.length ≤ wordBudget n c.length :=
  scan_word_length M T c B hB _

theorem discovery_word_length (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (fuel : ℕ) (B : RowBasis c.length)
    (hB : DiscoveryPrecision M T c fuel B) :
    ∀ w ∈ (discovery M T c fuel B).words, w.length ≤ wordBudget n c.length := by
  induction fuel generalizing B with
  | zero => simp [discovery]
  | succ fuel ih =>
      intro w hw
      have hp := hB.1
      have hr := hB.2
      cases h : (findRowWithCount M T c B).1 with
      | none =>
          simp only [discovery, row_value, h] at hw
          exact row_word_length M T c B hp w hw
      | some a =>
          simp only [discovery, row_value, h, List.mem_append] at hw
          simp only [h] at hr
          exact hw.elim (row_word_length M T c B hp w)
            (ih (insert B (wireRow c a)) hr w)

theorem search_word_length (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) :
    ∀ w ∈ (search M T c).words, w.length ≤ wordBudget n c.length :=
  discovery_word_length M T c _ _ (machineSearch_precision M T c)

/-- Each summand is the supplied clock at that particular emitted word's
length. No maximum-clock premise is introduced. -/
theorem clockSum_le (T : ℕ → ℕ) (C d : ℕ)
    (hT : ∀ m, T m ≤ C * (m + 1) ^ d) (words : List (List Bool)) (b : ℕ)
    (hw : ∀ w ∈ words, w.length ≤ b) :
    clockSum T words ≤ words.length * (C * (b + 1) ^ d) := by
  induction words with
  | nil => simp [clockSum]
  | cons w ws ih =>
      have ht := (hT w.length).trans (Nat.mul_le_mul_left C
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hw w List.mem_cons_self) 1) d))
      have hr := ih (fun v hv => hw v (List.mem_cons_of_mem w hv))
      simp only [clockSum, List.map_cons, List.sum_cons, List.length_cons] at *
      nlinarith

/-- The exact traced SAT-clock sum for discovery is polynomial in the input
arity and circuit size whenever the supplied SAT clock has the stated bound. -/
theorem searchClock_le (M : Machine) (T : ℕ → ℕ) (C d : ℕ)
    (hT : ∀ m, T m ≤ C * (m + 1) ^ d) {n : ℕ} (c : List (CGate n)) :
    searchClock M T c ≤
      ((c.length + 1) * (c.length * (n + 1))) *
        (C * (wordBudget n c.length + 1) ^ d) := by
  apply (clockSum_le T C d hT _ _ (search_word_length M T c)).trans
  exact Nat.mul_le_mul_right _
    ((search_erase M T c).2.le.trans (machineSearch_queries_le M T c))

theorem queryGateBudget_le_polynomial (s : ℕ) :
    queryGateBudget s (precisionBudget s) ≤ 2048 * (s + 1) ^ 8 := by
  unfold queryGateBudget coefficientWidth precisionBudget
  ring_nf
  omega

theorem wordBudget_add_one_le_polynomial (n s : ℕ) :
    wordBudget n s + 1 ≤ 500000000 * (n + s + 1) ^ 16 := by
  let N := n + s + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hN8 : N ≤ N ^ 8 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right hN (by decide : 1 ≤ 8))
  have hn : n ≤ N ^ 8 := (by dsimp [N]; omega : n ≤ N).trans hN8
  have h1 : 1 ≤ N ^ 8 := hN.trans hN8
  have hs : s + 1 ≤ N := by dsimp [N]; omega
  have hg : queryGateBudget s (precisionBudget s) ≤ 2048 * N ^ 8 :=
    (queryGateBudget_le_polynomial s).trans
      (Nat.mul_le_mul_left 2048 (Nat.pow_le_pow_left hs 8))
  have hi : n + queryGateBudget s (precisionBudget s) + 1 ≤ 2050 * N ^ 8 := by omega
  have hp : 1 ≤ N ^ 16 := hN.trans (by
    simpa only [pow_one] using (Nat.pow_le_pow_right hN (by decide : 1 ≤ 16)))
  calc
    wordBudget n s + 1 ≤ 100 * (2050 * N ^ 8) ^ 2 + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hi 2)) 1
    _ = 420250000 * N ^ 16 + 1 := by ring
    _ ≤ 500000000 * N ^ 16 := by omega

/-- A single polynomial majorant for the summed clocks of all actual calls. -/
theorem searchClock_le_polynomial (M : Machine) (T : ℕ → ℕ) (C d : ℕ)
    (hT : ∀ m, T m ≤ C * (m + 1) ^ d) {n : ℕ} (c : List (CGate n)) :
    searchClock M T c ≤ (C * 500000000 ^ d) * (n + c.length + 1) ^ (16 * d + 3) := by
  let N := n + c.length + 1
  have hs : c.length + 1 ≤ N := by dsimp [N]; omega
  have hn : n + 1 ≤ N := by dsimp [N]; omega
  have hc : c.length ≤ N := by omega
  have hcalls : (c.length + 1) * (c.length * (n + 1)) ≤ N ^ 3 := by
    calc
      _ ≤ N * (N * N) := Nat.mul_le_mul hs (Nat.mul_le_mul hc hn)
      _ = _ := by ring
  calc
    searchClock M T c ≤ ((c.length + 1) * (c.length * (n + 1))) *
        (C * (wordBudget n c.length + 1) ^ d) := searchClock_le M T C d hT c
    _ ≤ N ^ 3 * (C * (500000000 * N ^ 16) ^ d) :=
      Nat.mul_le_mul hcalls (Nat.mul_le_mul_left C
        (Nat.pow_le_pow_left (wordBudget_add_one_le_polynomial n c.length) d))
    _ = (C * 500000000 ^ d) * N ^ (16 * d + 3) := by
      rw [mul_pow, ← pow_mul, pow_add]
      ring

theorem searchClock_polynomial (M : Machine) (T : ℕ → ℕ)
    (hT : PvsNPSeparatingInvariant.PolyBounded T) :
    ∃ C d : ℕ, ∀ (n : ℕ) (c : List (CGate n)),
      searchClock M T c ≤ C * (n + c.length + 1) ^ d := by
  obtain ⟨C, d, hT⟩ := hT
  exact ⟨C * 500000000 ^ d, 16 * d + 3,
    fun _ c => searchClock_le_polynomial M T C d hT c⟩

end GodMoveDiscoveryClockBudget

#print axioms GodMoveDiscoveryClockBudget.descend_word_length
#print axioms GodMoveDiscoveryClockBudget.witness_word_length
#print axioms GodMoveDiscoveryClockBudget.attempt_word_length
#print axioms GodMoveDiscoveryClockBudget.discovery_word_length
#print axioms GodMoveDiscoveryClockBudget.search_word_length
#print axioms GodMoveDiscoveryClockBudget.clockSum_le
#print axioms GodMoveDiscoveryClockBudget.searchClock_le
#print axioms GodMoveDiscoveryClockBudget.queryGateBudget_le_polynomial
#print axioms GodMoveDiscoveryClockBudget.wordBudget_add_one_le_polynomial
#print axioms GodMoveDiscoveryClockBudget.searchClock_le_polynomial
#print axioms GodMoveDiscoveryClockBudget.searchClock_polynomial
