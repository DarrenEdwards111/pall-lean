import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
# A bit-length fuel bound for the executed Euclidean algorithm

Each nonzero-divisor branch executes one natural remainder operation. The
returned counter records those invocations, and `finished` records whether the
algorithm reached a zero divisor before its fuel was exhausted. Two nonterminal
steps strictly halve the second operand, giving a linear bit-length fuel bound.

This counts invocations of `Nat.mod`, not the integer operations inside division
or a compiled machine's runtime. A division implementation can be coupled to
these calls using its own proved correctness and cost bounds.
-/

namespace GodMoveEuclideanBitIterations

structure EuclidResult where
  value : ℕ
  divisions : ℕ
  finished : Bool
  deriving DecidableEq, Repr

def euclid : ℕ → ℕ → ℕ → EuclidResult
  | 0, a, b => ⟨a, 0, decide (b = 0)⟩
  | fuel + 1, a, b =>
      if b = 0 then ⟨a, 0, true⟩ else
        let remainder := a % b
        let rest := euclid fuel b remainder
        ⟨rest.value, rest.divisions + 1, rest.finished⟩

@[simp] theorem euclid_zero (fuel a : ℕ) : euclid fuel a 0 = ⟨a, 0, true⟩ := by
  cases fuel <;> simp [euclid]

theorem euclid_step (fuel a b : ℕ) (hb : b ≠ 0) :
    euclid (fuel + 1) a b =
      ⟨(euclid fuel b (a % b)).value,
        (euclid fuel b (a % b)).divisions + 1,
        (euclid fuel b (a % b)).finished⟩ := by
  simp [euclid, hb]

theorem euclid_divisions_le (fuel a b : ℕ) : (euclid fuel a b).divisions ≤ fuel := by
  induction fuel generalizing a b with
  | zero => simp [euclid]
  | succ fuel ih =>
      by_cases hb : b = 0
      · simp [hb]
      · rw [euclid_step fuel a b hb]
        exact Nat.succ_le_succ (ih b (a % b))

/-- Strict halving after two Euclidean steps, provided the first remainder
does not already terminate the algorithm. -/
theorem twice_mod_lt (b r : ℕ) (hr : 0 < r) (hrb : r < b) : 2 * (b % r) < b := by
  by_cases hsmall : 2 * r ≤ b
  · have hmod := Nat.mod_lt b hr
    omega
  · have hsub : b - r < r := by omega
    rw [Nat.mod_eq_sub_mod (Nat.le_of_lt hrb), Nat.mod_eq_of_lt hsub]
    omega

theorem size_lt_of_twice_lt (a b : ℕ) (h : 2 * a < b) : a.size < b.size := by
  cases hs : b.size with
  | zero =>
      have hb : b = 0 := Nat.size_eq_zero.mp hs
      omega
  | succ k =>
      have hb := Nat.lt_size_self b
      rw [hs, pow_succ] at hb
      have ha : a < 2 ^ k := by nlinarith
      have hsize := Nat.size_le.mpr ha
      omega

theorem two_step_size_lt (a b : ℕ) (hb : b ≠ 0) (hr : a % b ≠ 0) :
    (b % (a % b)).size < b.size := by
  apply size_lt_of_twice_lt
  exact twice_mod_lt b (a % b) (Nat.pos_of_ne_zero hr)
    (Nat.mod_lt a (Nat.pos_of_ne_zero hb))

theorem gcd_step (a b : ℕ) : Nat.gcd a b = Nat.gcd b (a % b) := by
  rw [Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm (a % b) b]

/-- This proof reduces the fuel parameter by two only after proving that
the actual two-step remainder has lost a bit. -/
theorem euclid_correct_of_size_le (bits a b : ℕ) (hb : b.size ≤ bits) :
    (euclid (2 * bits + 1) a b).value = Nat.gcd a b ∧
      (euclid (2 * bits + 1) a b).finished = true := by
  induction bits generalizing a b with
  | zero =>
      have hb0 : b = 0 := Nat.size_eq_zero.mp (by omega)
      simp [hb0]
  | succ bits ih =>
      by_cases hb0 : b = 0
      · simp [hb0]
      · rw [show 2 * (bits + 1) + 1 = (2 * bits + 1 + 1) + 1 by omega,
          euclid_step (2 * bits + 1 + 1) a b hb0]
        by_cases hr : a % b = 0
        · rw [hr, euclid_zero]
          have hg : Nat.gcd a b = b := by rw [gcd_step a b, hr, Nat.gcd_zero_right]
          simp [hg]
        · rw [euclid_step (2 * bits + 1) b (a % b) hr]
          have hsmall : (b % (a % b)).size ≤ bits := by
            have h := two_step_size_lt a b hb0 hr
            omega
          have hrec := ih (a % b) (b % (a % b)) hsmall
          have hg : Nat.gcd a b = Nat.gcd (a % b) (b % (a % b)) :=
            (gcd_step a b).trans (gcd_step b (a % b))
          simpa only [hg] using hrec

/-- The numerical entry point has fuel determined by the actual divisor's
bit length, rather than by its magnitude. -/
def gcd (a b : ℕ) : EuclidResult := euclid (2 * b.size + 1) a b

theorem gcd_value (a b : ℕ) : (gcd a b).value = Nat.gcd a b :=
  (euclid_correct_of_size_le b.size a b le_rfl).1

theorem gcd_finished (a b : ℕ) : (gcd a b).finished = true :=
  (euclid_correct_of_size_le b.size a b le_rfl).2

theorem gcd_divisions_le (a b : ℕ) : (gcd a b).divisions ≤ 2 * b.size + 1 :=
  euclid_divisions_le _ _ _

/-- Actual operand pairs at the remainder invocations, in execution order. -/
def divisionInputs : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, _, _ => []
  | fuel + 1, a, b =>
      if b = 0 then [] else (a, b) :: divisionInputs fuel b (a % b)

theorem divisionInputs_length (fuel a b : ℕ) :
    (divisionInputs fuel a b).length = (euclid fuel a b).divisions := by
  induction fuel generalizing a b with
  | zero => rfl
  | succ fuel ih =>
      by_cases hb : b = 0
      · simp [divisionInputs, hb]
      · simp [divisionInputs, euclid, hb, ih]

theorem divisionInputs_bounds (fuel a b B : ℕ) (ha : a ≤ B) (hb : b ≤ B) :
    ∀ p ∈ divisionInputs fuel a b, p.1 ≤ B ∧ p.2 ≤ B ∧ 0 < p.2 := by
  induction fuel generalizing a b with
  | zero => simp [divisionInputs]
  | succ fuel ih =>
      by_cases hb0 : b = 0
      · simp [divisionInputs, hb0]
      · intro p hp
        simp only [divisionInputs, hb0, ↓reduceIte, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨ha, hb, Nat.pos_of_ne_zero hb0⟩
        · exact ih b (a % b) hb ((Nat.mod_lt a (Nat.pos_of_ne_zero hb0)).le.trans hb) p hp

/-- All division calls can use the original common operand width. -/
theorem gcd_division_input_sizes (a b : ℕ)
    (p : ℕ × ℕ) (hp : p ∈ divisionInputs (2 * b.size + 1) a b) :
    p.1.size ≤ (max a b).size ∧ p.2.size ≤ (max a b).size ∧ 0 < p.2 := by
  have h := divisionInputs_bounds _ a b (max a b) (le_max_left _ _) (le_max_right _ _) p hp
  exact ⟨Nat.size_le_size h.1, Nat.size_le_size h.2.1, h.2.2⟩

end GodMoveEuclideanBitIterations

#print axioms GodMoveEuclideanBitIterations.twice_mod_lt
#print axioms GodMoveEuclideanBitIterations.two_step_size_lt
#print axioms GodMoveEuclideanBitIterations.euclid_correct_of_size_le
#print axioms GodMoveEuclideanBitIterations.gcd_value
#print axioms GodMoveEuclideanBitIterations.gcd_finished
#print axioms GodMoveEuclideanBitIterations.gcd_divisions_le
#print axioms GodMoveEuclideanBitIterations.divisionInputs_length
#print axioms GodMoveEuclideanBitIterations.gcd_division_input_sizes
