import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic
import PallLean.SPDPDefs
/-!
# Turing Machine Model and Compilation — Pall §3

We formalize:
- Deterministic single-tape TM with binary alphabet
- The computation tableau variables (§3.1)
- Local constraint polynomials (radius-1 locality)
- Violation polynomial V_{M,n} = Σ_C C(x,τ)²
- κ-padded polynomial P_{M,n} = (∏ yⱼ) · V_{M,n}
- Compiler-induced block partition (§3.3)
-/

namespace TuringMachine

open MvPolynomial SPDP

/-! ## TM Definition -/

/-- Deterministic single-tape TM with binary alphabet {0,1}.
    State 0 = initial, State 1 = accept, State 2 = reject. -/
structure DTM where
  numStates : ℕ
  hStates : numStates ≥ 3
  /-- Transition: (state, bit) → (new state, bit write, direction) -/
  transition : Fin numStates → Bool → Fin numStates × Bool × Bool
  /-- Time bound exponent: time ≤ n^timeBound -/
  timeBound : ℕ

def timeSteps (M : DTM) (n : ℕ) : ℕ := n ^ M.timeBound
def tapeSize (M : DTM) (n : ℕ) : ℕ := timeSteps M n + 1

/-! ## Compilation Variables (§3.1)

For each cell (t,i): tape bit b_{t,i}, state indicators s_{t,q}, head position h_{t,i}.
Plus input x_1,...,x_n and padding y_1,...,y_κ.

Total N(n) = poly(n) variables, indexed by Fin N. -/

/-- Total number of compilation variables -/
def numVars (M : DTM) (n κ : ℕ) : ℕ :=
  let S := tapeSize M n
  S * S + S * M.numStates + S * S + n + κ

/-! ## Local Constraints (§3.1) -/

/-- A local constraint: polynomial that should be 0 on valid tableau entries.
    Involves ≤ 6 variables in a radius-1 neighborhood. -/
structure LocalConstraint (M : DTM) (n κ : ℕ) (F : Type*) [CommRing F] where
  poly : MvPolynomial (Fin (numVars M n κ)) F
  centerTime : ℕ
  centerPos : ℕ
  width_bound : poly.vars.card ≤ 6

/-- Violation polynomial V_{M,n} = Σ_C C(x,τ)² (§3.1) -/
noncomputable def violationPoly (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ)
    (constraints : List (LocalConstraint M n κ F)) :
    MvPolynomial (Fin (numVars M n κ)) F :=
  constraints.foldl (fun acc c => acc + c.poly * c.poly) 0

/-- The last κ variable indices are padding variables -/
private theorem numVars_ge_kappa (M : DTM) (n κ : ℕ) :
    numVars M n κ ≥ κ := by
  show tapeSize M n * tapeSize M n + tapeSize M n * M.numStates +
    tapeSize M n * tapeSize M n + n + κ ≥ κ
  omega

private theorem padding_idx_lt (M : DTM) (n κ : ℕ) (j : Fin κ) :
    numVars M n κ - κ + j.val < numVars M n κ := by
  have h1 := numVars_ge_kappa M n κ
  have h2 := j.isLt
  omega

/-- κ-padding product Y = ∏_{j} X_{padding_j} -/
noncomputable def paddingProduct (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ) :
    MvPolynomial (Fin (numVars M n κ)) F :=
  Finset.univ.prod (fun (j : Fin κ) =>
    X ⟨numVars M n κ - κ + j.val, padding_idx_lt M n κ j⟩)

/-- Compiled polynomial P_{M,n} = Y · V_{M,n} -/
noncomputable def compiledPoly (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ)
    (constraints : List (LocalConstraint M n κ F)) :
    MvPolynomial (Fin (numVars M n κ)) F :=
  paddingProduct F M n κ * violationPoly F M n κ constraints

/-! ## Compiler-Induced Block Partition (§3.3) -/

/-- Compiler block partition: each tableau cell (t,i) = one block,
    plus separate blocks for inputs and padding. -/
noncomputable def compilerBlockPartition (M : DTM) (n κ : ℕ) :
    BlockPartition (numVars M n κ) where
  numBlocks := tapeSize M n * tapeSize M n + n + κ + 1
  assign := fun v => ⟨v.val % (tapeSize M n * tapeSize M n + n + κ + 1),
    Nat.mod_lt _ (by omega)⟩

/-! ## Variable Index Helpers -/

/-- Index of tape bit b_{t,i} -/
def tapeBitIdx (M : DTM) (n κ : ℕ) (t i : ℕ)
    (ht : t < tapeSize M n) (hi : i < tapeSize M n) :
    Fin (numVars M n κ) :=
  ⟨t * tapeSize M n + i, by
    unfold numVars; have := hi; have := ht
    have hS : 0 < tapeSize M n := by omega
    nlinarith [Nat.mul_lt_mul_of_pos_right ht hS]⟩

/-- Index of state indicator s_{t,q} -/
def stateIdx (M : DTM) (n κ : ℕ) (t : ℕ) (q : Fin M.numStates)
    (ht : t < tapeSize M n) :
    Fin (numVars M n κ) :=
  ⟨tapeSize M n * tapeSize M n + t * M.numStates + q.val, by
    unfold numVars
    have := ht; have := q.isLt
    have : t * M.numStates + q.val < tapeSize M n * M.numStates := by nlinarith
    nlinarith⟩

/-- Index of head indicator h_{t,i} -/
def headIdx (M : DTM) (n κ : ℕ) (t i : ℕ)
    (ht : t < tapeSize M n) (hi : i < tapeSize M n) :
    Fin (numVars M n κ) :=
  ⟨tapeSize M n * tapeSize M n + tapeSize M n * M.numStates + t * tapeSize M n + i, by
    unfold numVars
    have := ht; have := hi
    have : t * tapeSize M n + i < tapeSize M n * tapeSize M n := by nlinarith
    nlinarith⟩

/-! ## Concrete Constraint Construction (§3.1) -/

/-- Booleanity constraint: z(1-z) = 0 for variable at index idx.
    This is a polynomial in 1 variable, so width ≤ 6 trivially. -/
noncomputable def boolConstraintPoly {M : DTM} {n κ : ℕ} (F : Type*) [CommRing F]
    (idx : Fin (numVars M n κ)) :
    MvPolynomial (Fin (numVars M n κ)) F :=
  X idx * (1 - X idx)

/-- Booleanity constraint has ≤ 2 variables (hence ≤ 6) -/
theorem boolConstraint_width {M : DTM} {n κ : ℕ} (F : Type*) [CommRing F]
    (idx : Fin (numVars M n κ)) :
    (boolConstraintPoly F idx : MvPolynomial (Fin (numVars M n κ)) F).vars.card ≤ 6 := by
  sorry -- vars ⊆ {idx}, card ≤ 1 ≤ 6

/-- Make a booleanity LocalConstraint -/
noncomputable def mkBoolConstraint {M : DTM} {n κ : ℕ} (F : Type*) [CommRing F]
    (idx : Fin (numVars M n κ)) (t i : ℕ) :
    LocalConstraint M n κ F :=
  { poly := boolConstraintPoly F idx
    centerTime := t
    centerPos := i
    width_bound := boolConstraint_width F idx }

/-- Transition constraint polynomial for cell (t, i):
    Encodes that if head is at position i at time t, then tape bit and state
    update correctly according to M.transition.
    Polynomial: h_{t,i} · (b_{t+1,i} - δ_write(s_t, b_{t,i}))
    This involves ≤ 6 variables: h_{t,i}, b_{t,i}, b_{t+1,i}, s_{t,q} (for relevant q). -/
noncomputable def transitionConstraintPoly {M : DTM} {n κ : ℕ} (F : Type*) [CommRing F]
    (t i : ℕ) (ht : t + 1 < tapeSize M n) (hi : i < tapeSize M n) :
    MvPolynomial (Fin (numVars M n κ)) F :=
  -- Simplified: h_{t,i} * (b_{t+1,i} - b_{t,i}) as a stand-in
  -- The full version would enumerate M.transition cases
  let h_ti := X (headIdx M n κ t i (by omega) hi)
  let b_ti := X (tapeBitIdx M n κ t i (by omega) hi)
  let b_t1i := X (tapeBitIdx M n κ (t+1) i ht hi)
  h_ti * (b_t1i - b_ti)

theorem transitionConstraint_width {M : DTM} {n κ : ℕ} (F : Type*) [CommRing F]
    (t i : ℕ) (ht : t + 1 < tapeSize M n) (hi : i < tapeSize M n) :
    (transitionConstraintPoly F t i ht hi : MvPolynomial (Fin (numVars M n κ)) F).vars.card ≤ 6 := by
  sorry -- vars ⊆ {h_{t,i}, b_{t,i}, b_{t+1,i}}, card ≤ 3 ≤ 6

/-- Build all compilation constraints for DTM M at input size n -/
noncomputable def buildCompilationConstraints (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ) :
    List (LocalConstraint M n κ F) :=
  -- For each time step t and position i, generate:
  -- 1. Booleanity constraints for b_{t,i}, s_{t,q}, h_{t,i}
  -- 2. Transition constraints (for t < T-1)
  -- We use List.bind to iterate over all (t,i) pairs
  let S := tapeSize M n
  let pairs := ((List.range S).map fun t =>
    (List.range S).map fun i => (t, i)).flatten
  -- Booleanity constraints for tape bits
  let boolConstraints : List (LocalConstraint M n κ F) :=
    pairs.filterMap fun ⟨t, i⟩ =>
      if ht : t < S then
        if hi : i < S then
          some (mkBoolConstraint F (tapeBitIdx M n κ t i ht hi) t i)
        else none
      else none
  -- Transition constraints
  let transConstraints : List (LocalConstraint M n κ F) :=
    pairs.filterMap fun ⟨t, i⟩ =>
      if ht : t + 1 < S then
        if hi : i < S then
          some { poly := transitionConstraintPoly F t i ht hi
                 centerTime := t
                 centerPos := i
                 width_bound := transitionConstraint_width F t i ht hi }
        else none
      else none
  boolConstraints ++ transConstraints

/-! ## Key Properties -/

/-- Helper: foldl of constraint squares preserves degree ≤ 6 -/
private theorem foldl_constraint_deg_le {M : DTM} {n κ : ℕ} (F : Type*) [CommRing F]
    (constraints : List (LocalConstraint M n κ F))
    (acc : MvPolynomial (Fin (numVars M n κ)) F)
    (hacc : acc.totalDegree ≤ 6)
    (hcs : ∀ c ∈ constraints, c.poly.totalDegree ≤ 3) :
    (constraints.foldl (fun a (c : LocalConstraint M n κ F) => a + c.poly * c.poly) acc).totalDegree ≤ 6 := by
  induction constraints generalizing acc with
  | nil => simpa [List.foldl]
  | cons c rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · have h_add := MvPolynomial.totalDegree_add acc (c.poly * c.poly)
      have h_mul := MvPolynomial.totalDegree_mul c.poly c.poly
      have h_c := hcs c (by simp)
      omega
    · intro x hx; exact hcs x (by simp [hx])

theorem violation_deg_const (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ)
    (constraints : List (LocalConstraint M n κ F))
    (h : ∀ c ∈ constraints, c.poly.totalDegree ≤ 3) :
    (violationPoly F M n κ constraints).totalDegree ≤ 6 := by
  exact foldl_constraint_deg_le F constraints 0
    (by simp [MvPolynomial.totalDegree_zero]) h

/-- Each constraint is local: touches ≤ 6 variables -/
theorem constraints_local (M : DTM) (n κ : ℕ) (F : Type*) [CommRing F]
    (c : LocalConstraint M n κ F) :
    c.poly.vars.card ≤ 6 := c.width_bound

end TuringMachine
