import GodMoveResidualQueries
import GodMoveRationalMachineQuery

/-!
# Finding a new independent wire row using actual SAT-machine calls

For each residual coordinate, construct its explicit rational coefficient
row, compute a sufficient precision budget, compile its nonzero relation,
and run the supplied SAT machine through circuit witness self-reduction.
The first successful relation returns an actual Boolean assignment outside
the current rational row span. Exhausting the coordinate list proves every
Boolean wire row lies in that span.

This program uses no unrestricted predicate oracle and enumerates no Boolean
assignment table. Its correctness assumes that the supplied machine decides
SAT under its supplied clock. The counter bounds the number of SAT-machine
invocations. `GodMoveMachineDiscoveryPrecision` bounds coefficient bits and
query sizes on actual sampled states; total construction runtime is separate.
-/

namespace GodMoveMachineRowFinder

open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveRationalRowBasis
open GodMoveResidualQueries GodMoveRationalMachineQuery
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine SeparationTarget

def rowAttempt (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (j : Fin c.length) :
    Option (Assignment n) × ℕ :=
  let q := residualCoefficients B j
  rationalWitnessWithCount M T c q (coefficientBits q)

theorem rowAttempt_some (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (B : RowBasis c.length) (j : Fin c.length)
    (a : Assignment n) (ha : (rowAttempt M T c B j).1 = some a) :
    rationalWireValue c (residualCoefficients B j) a ≠ 0 :=
  rationalWitness_some M T hD c _ _ (coefficientBits_precision _) a ha

theorem rowAttempt_none_iff (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (B : RowBasis c.length) (j : Fin c.length) :
    (rowAttempt M T c B j).1 = none ↔
      ¬ ∃ a, rationalWireValue c (residualCoefficients B j) a ≠ 0 :=
  rationalWitness_none_iff M T hD c _ _ (coefficientBits_precision _)

theorem rowAttempt_queries_le (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (j : Fin c.length) :
    (rowAttempt M T c B j).2 ≤ n + 1 := rationalWitness_queries_le M T c _ _

def findIn (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) :
    List (Fin c.length) → Option (Assignment n) × ℕ
  | [] => (none, 0)
  | j :: js =>
      let attempt := rowAttempt M T c B j
      match attempt.1 with
      | some a => (some a, attempt.2)
      | none =>
          let rest := findIn M T c B js
          (rest.1, attempt.2 + rest.2)

theorem findIn_some (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (B : RowBasis c.length) (js : List (Fin c.length))
    (a : Assignment n) (ha : (findIn M T c B js).1 = some a) :
    ∃ j ∈ js, rationalWireValue c (residualCoefficients B j) a ≠ 0 := by
  induction js with
  | nil => simp [findIn] at ha
  | cons j js ih =>
      cases ht : (rowAttempt M T c B j).1 with
      | none =>
          have hrest : (findIn M T c B js).1 = some a := by
            simpa only [findIn, ht] using ha
          obtain ⟨k, hk, hvalue⟩ := ih hrest
          exact ⟨k, List.mem_cons_of_mem j hk, hvalue⟩
      | some b =>
          have he : b = a := Option.some.inj (by simpa only [findIn, ht] using ha)
          subst b
          exact ⟨j, List.mem_cons_self, rowAttempt_some M T hD c B j a ht⟩

theorem findIn_none_iff (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (B : RowBasis c.length) (js : List (Fin c.length)) :
    (findIn M T c B js).1 = none ↔
      ∀ j ∈ js, ¬ ∃ a, rationalWireValue c (residualCoefficients B j) a ≠ 0 := by
  induction js with
  | nil => simp [findIn]
  | cons j js ih =>
      cases ht : (rowAttempt M T c B j).1 with
      | none =>
          have hj := (rowAttempt_none_iff M T hD c B j).mp ht
          simpa only [findIn, ht, List.forall_mem_cons, hj, not_false_eq_true, true_and] using ih
      | some a =>
          have hj := rowAttempt_some M T hD c B j a ht
          simp only [findIn, ht, Option.some_ne_none, List.forall_mem_cons]
          constructor
          · intro h; exact h.elim
          · intro h
            exact h.1 ⟨a, hj⟩

theorem findIn_queries_le (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) (js : List (Fin c.length)) :
    (findIn M T c B js).2 ≤ js.length * (n + 1) := by
  induction js with
  | nil => simp [findIn]
  | cons j js ih =>
      have hq := rowAttempt_queries_le M T c B j
      cases ht : (rowAttempt M T c B j).1 with
      | none =>
          simp only [findIn, ht, List.length_cons]
          nlinarith
      | some a =>
          simp only [findIn, ht, List.length_cons]
          nlinarith

def findRowWithCount (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) : Option (Assignment n) × ℕ :=
  findIn M T c B (List.ofFn (fun j : Fin c.length => j))

theorem findRow_some_correct (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (B : RowBasis c.length) (a : Assignment n)
    (ha : (findRowWithCount M T c B).1 = some a) :
    accepts B (wireRow c a) = true := by
  obtain ⟨j, _, hj⟩ := findIn_some M T hD c B _ a ha
  exact (accepts_iff_exists_relation c B a).mpr ⟨j, hj⟩

theorem findRow_none_iff (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) (B : RowBasis c.length) :
    (findRowWithCount M T c B).1 = none ↔ ∀ a, accepts B (wireRow c a) = false := by
  rw [findRowWithCount, findIn_none_iff M T hD]
  constructor
  · intro h a
    cases ha : accepts B (wireRow c a) with
    | false => rfl
    | true =>
        obtain ⟨j, hj⟩ := (accepts_iff_exists_relation c B a).mp ha
        exact False.elim (h j (List.mem_ofFn.mpr ⟨j, rfl⟩) ⟨a, hj⟩)
  · intro h j _ hj
    obtain ⟨a, ha⟩ := hj
    have hyes := (accepts_iff_exists_relation c B a).mpr ⟨j, ha⟩
    rw [h a] at hyes
    exact Bool.noConfusion hyes

theorem findRow_queries_le (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (B : RowBasis c.length) :
    (findRowWithCount M T c B).2 ≤ c.length * (n + 1) := by
  simpa only [List.length_ofFn] using
    findIn_queries_le M T c B (List.ofFn (fun j : Fin c.length => j))

end GodMoveMachineRowFinder

#print axioms GodMoveMachineRowFinder.rowAttempt_some
#print axioms GodMoveMachineRowFinder.rowAttempt_none_iff
#print axioms GodMoveMachineRowFinder.findIn_some
#print axioms GodMoveMachineRowFinder.findIn_none_iff
#print axioms GodMoveMachineRowFinder.findIn_queries_le
#print axioms GodMoveMachineRowFinder.findRow_some_correct
#print axioms GodMoveMachineRowFinder.findRow_none_iff
#print axioms GodMoveMachineRowFinder.findRow_queries_le
