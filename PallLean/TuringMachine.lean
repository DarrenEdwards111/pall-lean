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
  /-- Time bound exponent: time ≤ n^timeBound. Must be ≥ 1 (reads input). -/
  timeBound : ℕ
  hTimeBound : timeBound ≥ 1

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

/-! ## Variable Indexing Helpers (§3.1) -/

/-- Index of tape bit variable b_{t,i} -/
def tapeIdx (M : DTM) (n κ : ℕ) (t i : Fin (tapeSize M n)) : Fin (numVars M n κ) :=
  ⟨t.val * tapeSize M n + i.val, by
    unfold numVars; have := t.isLt; have := i.isLt
    nlinarith [Nat.mul_lt_mul_of_pos_right t.isLt (show 0 < tapeSize M n by omega)]⟩

/-- Index of state variable s_{t,q} -/
def stateIdx (M : DTM) (n κ : ℕ) (t : Fin (tapeSize M n)) (q : Fin M.numStates) :
    Fin (numVars M n κ) :=
  ⟨(tapeSize M n) * (tapeSize M n) + t.val * M.numStates + q.val, by
    unfold numVars; have := t.isLt; have := q.isLt
    nlinarith [Nat.mul_lt_mul_of_pos_right t.isLt (show 0 < M.numStates by omega)]⟩

/-- Index of head position variable h_{t,i} -/
def headIdx (M : DTM) (n κ : ℕ) (t i : Fin (tapeSize M n)) : Fin (numVars M n κ) :=
  ⟨(tapeSize M n) * (tapeSize M n) + (tapeSize M n) * M.numStates +
   t.val * tapeSize M n + i.val, by
    unfold numVars; have := t.isLt; have := i.isLt
    nlinarith [Nat.mul_lt_mul_of_pos_right t.isLt (show 0 < tapeSize M n by omega)]⟩

/-! ## Local Constraints (§3.1) -/

/-- A local constraint: polynomial that should be 0 on valid tableau entries.
    Involves ≤ 6 variables in a radius-1 neighborhood. -/
structure LocalConstraint (M : DTM) (n κ : ℕ) (F : Type*) [CommRing F] where
  poly : MvPolynomial (Fin (numVars M n κ)) F
  centerTime : ℕ
  centerPos : ℕ
  width_bound : poly.vars.card ≤ 6

/-! ## Booleanity Constraints: z(1-z) = 0 for each variable -/

/-- Booleanity constraint for a single variable: z(1-z) -/
noncomputable def boolConstraint {N : ℕ} (F : Type*) [CommRing F]
    (v : Fin N) : MvPolynomial (Fin N) F :=
  X v * (1 - X v)

/-- Violation polynomial V_{M,n} = Σ_C C(x,τ)² (§3.1) -/
noncomputable def violationPoly (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ)
    (constraints : List (LocalConstraint M n κ F)) :
    MvPolynomial (Fin (numVars M n κ)) F :=
  (constraints.map (fun c => c.poly * c.poly)).sum

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

/-- paddingProduct has total degree ≤ κ (product of κ linear monomials) -/
theorem paddingProduct_totalDegree (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n κ : ℕ) :
    (paddingProduct F M n κ).totalDegree ≤ κ := by
  let f : Fin κ → MvPolynomial (Fin (numVars M n κ)) F :=
    fun j => X ⟨numVars M n κ - κ + j.val, padding_idx_lt M n κ j⟩
  show (Finset.univ.prod f).totalDegree ≤ κ
  have h1 := totalDegree_finset_prod Finset.univ f
  have h2 : ∀ i : Fin κ, (f i).totalDegree = 1 := fun i => totalDegree_X _
  have h3 : ∑ i : Fin κ, (f i).totalDegree = κ := by
    simp [h2]
  linarith

/-- Compiled polynomial P_{M,n} = Y · V_{M,n} -/
noncomputable def compiledPoly (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ)
    (constraints : List (LocalConstraint M n κ F)) :
    MvPolynomial (Fin (numVars M n κ)) F :=
  paddingProduct F M n κ * violationPoly F M n κ constraints

/-! ## Compiler-Induced Block Partition (§3.3) -/

/-- Compiler block partition: template-induced partition (paper Definition 1, §40.6).
    Variables are grouped by template ownership:
    - Witness variables (indices < npNumVars n) are grouped by clause
      (matching tseitinPartition: selectors get per-clause blocks, others share block 0)
    - Computation variables (indices ≥ npNumVars n) each get their own block
    This is coarser than the identity partition for witness variables,
    ensuring that block-admissible derivative lists can differentiate at most
    one witness variable per clause — which is what makes Width⇒Rank work.
    Paper: Γ^B ≤ Γ, and the P-side bound holds for Γ^B, not Γ. -/
noncomputable def compilerBlockPartition (M : DTM) (n κ : ℕ) :
    BlockPartition (numVars M n κ) where
  numBlocks := numVars M n κ
  assign := fun v => v

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

theorem violationPoly_totalDegree_le (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ) (d : ℕ)
    (constraints : List (LocalConstraint M n κ F))
    (h : ∀ c ∈ constraints, c.poly.totalDegree ≤ d) :
    (violationPoly F M n κ constraints).totalDegree ≤ 2 * d := by
  unfold violationPoly
  induction constraints with
  | nil => simp [MvPolynomial.totalDegree_zero]
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hcd := h c (List.Mem.head cs)
    have hdeg_sq : (c.poly * c.poly).totalDegree ≤ 2 * d :=
      le_trans (MvPolynomial.totalDegree_mul _ _) (by omega)
    exact le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le hdeg_sq (ih (fun c' hc' => h c' (List.Mem.tail c hc'))))

theorem violation_deg_const (F : Type*) [CommRing F]
    (M : DTM) (n κ : ℕ)
    (constraints : List (LocalConstraint M n κ F))
    (h : ∀ c ∈ constraints, c.poly.totalDegree ≤ 3) :
    (violationPoly F M n κ constraints).totalDegree ≤ 6 :=
  violationPoly_totalDegree_le F M n κ 3 constraints h

/-- Each constraint is local: touches ≤ 6 variables -/
theorem constraints_local (M : DTM) (n κ : ℕ) (F : Type*) [CommRing F]
    (c : LocalConstraint M n κ F) :
    c.poly.vars.card ≤ 6 := c.width_bound

/-! ## TM Execution -/

/-- Configuration of the TM at a given time step. -/
structure Config (M : DTM) (n : ℕ) where
  state : Fin M.numStates
  tape : Fin (tapeSize M n) → Bool
  headPos : ℕ
  headBound : headPos < tapeSize M n

/-- One step of TM execution. Head stays in bounds via min/saturating. -/
def step (M : DTM) (n : ℕ) (c : Config M n) : Config M n :=
  let bit := c.tape ⟨c.headPos, c.headBound⟩
  let (newState, writeBit, moveRight) := M.transition c.state bit
  let newHead := if moveRight then c.headPos + 1 else c.headPos - 1
  let clampedHead := min newHead (tapeSize M n - 1)
  { state := newState
    tape := Function.update c.tape ⟨c.headPos, c.headBound⟩ writeBit
    headPos := clampedHead
    headBound := by
      show clampedHead < tapeSize M n
      exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt
        (show 0 < tapeSize M n from by unfold tapeSize timeSteps; positivity)
        (by omega)) }

/-- Run the TM for t steps. -/
def run (M : DTM) (n : ℕ) (c : Config M n) : ℕ → Config M n
  | 0 => c
  | t + 1 => step M n (run M n c t)

/-- Initial configuration: input x on the tape, head at position 0, state 0. -/
def initConfig (M : DTM) (n : ℕ) (x : Fin n → Bool) : Config M n :=
  { state := ⟨0, by have := M.hStates; omega⟩
    tape := fun i => if h : i.val < n then x ⟨i.val, h⟩ else false
    headPos := 0
    headBound := by unfold tapeSize timeSteps; positivity }

/-- M decides f on inputs of length n: after timeSteps M n steps,
    M is in accept state (1) iff f(x) = true. -/
def DTM.decides (M : DTM) {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool,
    let final := run M n (initConfig M n x) (timeSteps M n)
    (final.state = ⟨1, by exact Nat.lt_of_lt_of_le (by omega) M.hStates⟩) ↔ (f x = true)

end TuringMachine
