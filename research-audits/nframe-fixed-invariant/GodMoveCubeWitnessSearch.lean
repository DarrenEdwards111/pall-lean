import GodMoveBooleanWireTable

/-!
# Boolean-cube witness search from a decision oracle

The oracle decides whether a supplied Boolean predicate accepts some
assignment. After one existence query, witness search fixes each coordinate
to `false` when the corresponding restricted predicate is satisfiable, and
to `true` otherwise. The executable result carries its actual oracle-call
count: a rejected initial query uses one call, and an accepted query uses
exactly `n + 1` calls.

The oracle is an explicit argument. Neither its implementation nor the cost
of evaluating or encoding a predicate is supplied here. This construction
does not enumerate assignments or assert a polynomial-time SAT machine.
-/

namespace GodMoveCubeWitnessSearch

open GodMoveBooleanInterpolation

abbrev CubeOracle := (n : ℕ) → (Assignment n → Bool) → Bool

def OracleCorrect (O : CubeOracle) : Prop :=
  ∀ n (p : Assignment n → Bool), O n p = true ↔ ∃ a, p a = true

/-- Restrict the first coordinate without enumerating the remaining cube. -/
def restrictHead {n : ℕ} (p : Assignment (n + 1) → Bool) (b : Bool) :
    Assignment n → Bool := fun a => p (Fin.cons b a)

theorem exists_iff_head {n : ℕ} (p : Assignment (n + 1) → Bool) :
    (∃ a, p a = true) ↔
      (∃ a, restrictHead p false a = true) ∨ (∃ a, restrictHead p true a = true) := by
  constructor
  · rintro ⟨a, ha⟩
    have he := Fin.cons_self_tail a
    cases hb : a 0
    · left
      refine ⟨Fin.tail a, ?_⟩
      change p (Fin.cons false (Fin.tail a)) = true
      rw [show Fin.cons false (Fin.tail a) = a by simpa only [hb] using he]
      exact ha
    · right
      refine ⟨Fin.tail a, ?_⟩
      change p (Fin.cons true (Fin.tail a)) = true
      rw [show Fin.cons true (Fin.tail a) = a by simpa only [hb] using he]
      exact ha
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · exact ⟨Fin.cons false a, ha⟩
    · exact ⟨Fin.cons true a, ha⟩

/-- The caller has already established existence. Each recursive step makes
one decision query and records that call alongside the returned assignment. -/
def descendWithCount (O : CubeOracle) :
    (n : ℕ) → (Assignment n → Bool) → Assignment n × ℕ
  | 0, _ => (fun i => Fin.elim0 i, 0)
  | n + 1, p =>
      let b := if O n (restrictHead p false) then false else true
      let rest := descendWithCount O n (restrictHead p b)
      (Fin.cons b rest.1, rest.2 + 1)

theorem descendWithCount_count (O : CubeOracle) (n : ℕ) (p : Assignment n → Bool) :
    (descendWithCount O n p).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [descendWithCount]
      rw [ih]

theorem descendWithCount_correct (O : CubeOracle) (hO : OracleCorrect O)
    (n : ℕ) (p : Assignment n → Bool) (hex : ∃ a, p a = true) :
    p (descendWithCount O n p).1 = true := by
  induction n with
  | zero =>
      obtain ⟨a, ha⟩ := hex
      have he : (fun i => Fin.elim0 i : Assignment 0) = a := by
        funext i
        exact Fin.elim0 i
      simpa only [descendWithCount, he] using ha
  | succ n ih =>
      cases hq : O n (restrictHead p false) with
      | false =>
          have hn : ¬ ∃ a, restrictHead p false a = true := by
            intro h
            have hyes := (hO n (restrictHead p false)).mpr h
            simp [hq] at hyes
          have ht := (exists_iff_head p).mp hex |>.resolve_left hn
          simpa only [descendWithCount, hq, Bool.false_eq_true, ↓reduceIte, restrictHead]
            using ih (restrictHead p true) ht
      | true =>
          have hf := (hO n (restrictHead p false)).mp hq
          simpa only [descendWithCount, hq, ↓reduceIte, restrictHead]
            using ih (restrictHead p false) hf

/-- One initial existence query, followed by at most one query per coordinate. -/
def findWitnessWithCount (O : CubeOracle) {n : ℕ} (p : Assignment n → Bool) :
    Option (Assignment n) × ℕ :=
  if O n p then
    let found := descendWithCount O n p
    (some found.1, found.2 + 1)
  else (none, 1)

def findWitness (O : CubeOracle) {n : ℕ} (p : Assignment n → Bool) :
    Option (Assignment n) := (findWitnessWithCount O p).1

theorem findWitnessWithCount_fst (O : CubeOracle) {n : ℕ} (p : Assignment n → Bool) :
    (findWitnessWithCount O p).1 = findWitness O p := rfl

theorem findWitnessWithCount_count (O : CubeOracle) {n : ℕ} (p : Assignment n → Bool) :
    (findWitnessWithCount O p).2 = if O n p then n + 1 else 1 := by
  cases h : O n p <;> simp [findWitnessWithCount, descendWithCount_count, h]

theorem findWitnessWithCount_count_le (O : CubeOracle) {n : ℕ}
    (p : Assignment n → Bool) : (findWitnessWithCount O p).2 ≤ n + 1 := by
  rw [findWitnessWithCount_count]
  split <;> omega

theorem findWitness_some_correct (O : CubeOracle) (hO : OracleCorrect O)
    {n : ℕ} (p : Assignment n → Bool) (a : Assignment n)
    (ha : findWitness O p = some a) : p a = true := by
  unfold findWitness findWitnessWithCount at ha
  split at ha
  next hq =>
    have he : (descendWithCount O n p).1 = a := Option.some.inj ha
    rw [← he]
    exact descendWithCount_correct O hO n p ((hO n p).mp hq)
  next hq => simp at ha

theorem findWitness_none_iff (O : CubeOracle) (hO : OracleCorrect O)
    {n : ℕ} (p : Assignment n → Bool) :
    findWitness O p = none ↔ ¬ ∃ a, p a = true := by
  simp only [findWitness, findWitnessWithCount]
  split
  next hq => simp [(hO n p).mp hq]
  next hq =>
    have hn : ¬ ∃ a, p a = true := fun h => hq ((hO n p).mpr h)
    simp [hn]

theorem findWitness_exists_some_iff (O : CubeOracle) (hO : OracleCorrect O)
    {n : ℕ} (p : Assignment n → Bool) :
    (∃ a, findWitness O p = some a) ↔ ∃ a, p a = true := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, findWitness_some_correct O hO p a ha⟩
  · intro hex
    cases h : findWitness O p with
    | none => exact False.elim ((findWitness_none_iff O hO p).mp h hex)
    | some a => exact ⟨a, rfl⟩

end GodMoveCubeWitnessSearch

#print axioms GodMoveCubeWitnessSearch.exists_iff_head
#print axioms GodMoveCubeWitnessSearch.descendWithCount_count
#print axioms GodMoveCubeWitnessSearch.descendWithCount_correct
#print axioms GodMoveCubeWitnessSearch.findWitnessWithCount_count
#print axioms GodMoveCubeWitnessSearch.findWitnessWithCount_count_le
#print axioms GodMoveCubeWitnessSearch.findWitness_some_correct
#print axioms GodMoveCubeWitnessSearch.findWitness_none_iff
#print axioms GodMoveCubeWitnessSearch.findWitness_exists_some_iff
