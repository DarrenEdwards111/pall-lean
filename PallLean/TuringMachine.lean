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

/-- Compiler block partition: each tableau cell (t,i) = one block,
    plus separate blocks for inputs and padding. -/
noncomputable def compilerBlockPartition (M : DTM) (n κ : ℕ) :
    BlockPartition (numVars M n κ) where
  numBlocks := tapeSize M n * tapeSize M n + n + κ + 1
  assign := fun v => ⟨v.val % (tapeSize M n * tapeSize M n + n + κ + 1),
    Nat.mod_lt _ (by omega)⟩

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
  -- violationPoly = (constraints.map (c ↦ c² )).sum
  -- totalDegree(c² ) ≤ 2 · totalDegree(c) ≤ 6
  -- totalDegree(sum) ≤ max of totalDegrees ≤ 6
  unfold violationPoly
  induction constraints with
  | nil => simp [MvPolynomial.totalDegree_zero]
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hdeg_c : c.poly.totalDegree ≤ 3 := h c (List.Mem.head cs)
    have hdeg_sq : (c.poly * c.poly).totalDegree ≤ 6 :=
      le_trans (MvPolynomial.totalDegree_mul _ _) (by omega)
    have hcs : ∀ c' ∈ cs, c'.poly.totalDegree ≤ 3 :=
      fun c' hc' => h c' (List.Mem.tail c hc')
    have hdeg_rest : MvPolynomial.totalDegree (List.sum (List.map (fun c => c.poly * c.poly) cs)) ≤ 6 := ih hcs
    exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le hdeg_sq hdeg_rest)

/-- Each constraint is local: touches ≤ 6 variables -/
theorem constraints_local (M : DTM) (n κ : ℕ) (F : Type*) [CommRing F]
    (c : LocalConstraint M n κ F) :
    c.poly.vars.card ≤ 6 := c.width_bound

end TuringMachine
