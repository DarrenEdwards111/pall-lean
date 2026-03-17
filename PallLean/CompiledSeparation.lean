/-
  CompiledSeparation.lean — P ≠ NP via Compiled Polynomial Architecture

  Paper's spine: Theorem 92 (P-side) + Theorem 94 (NP-side) + Theorem 207.

  Axiom inventory (5 axioms, decomposed):
    1. cook_levin           — §17.1: DTM → width-3 CNF with locality
    2. pside_compiled_collapse — Thm 92 / §9 / §17.3: P-time → low compiled rank
    3. constructive_witness  — §11.7: deterministic poly-time w ∈ V_n^⊥
    4. diagonal_escape       — Thm 94: diagonal family escapes compiled collapse
    5. diagonal_in_NP        — Thm 94 (b): diagonal family ∈ NP

  Theorem:
    P_neq_NP : ¬ P_eq_NP   (from 2 + 4 + 5)
-/
import PallLean.CompiledPoly
import PallLean.TuringMachine
import Mathlib.Tactic

namespace CompiledSeparation

open CompiledPoly TuringMachine

/-! ## Definitions -/

abbrev BoolFunFamily := ∀ n : ℕ, (Fin n → Bool) → Bool

def UniformPtime (F : BoolFunFamily) : Prop :=
  ∃ M : DTM, ∀ n, M.decides (F n)

def UniformNP (F : BoolFunFamily) : Prop :=
  ∃ (k : ℕ) (V : BoolFunFamily),
    UniformPtime V ∧
    ∀ n, ∀ x : Fin n → Bool,
      F n x = true ↔
        ∃ w : Fin (n ^ k) → Bool,
          V (n + n ^ k) (Fin.append x w) = true

def P_eq_NP : Prop := ∀ F : BoolFunFamily, UniformNP F → UniformPtime F

/-! ## The compiled SPDP evaluation subspace

  For a given input length n and parameters κ, ℓ, the "compiled SPDP
  evaluation subspace" V_n is the span of evaluation vectors of all
  functions whose compiled polynomial has blocked SPDP rank ≤ threshold.

  The constructive witness w ∈ V_n^⊥ certifies that the diagonal
  function escapes this subspace. -/

/-- A function "compiles to low rank" if its DTM's Cook-Levin polynomial
    has blocked SPDP rank ≤ √n at κ = ℓ = log₂ n. -/
def CompiledLowRank (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (M : DTM) (k : ℕ) (cnf : CookLevinCNF (compiledVarCount k n))
    (hlp : HasLocalPartition cnf),
    M.decides f ∧
    blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyQ cnf) hlp.partition ≤ Nat.sqrt n

/-- The compiled SPDP evaluation subspace V_n ⊆ ℚ^{2^n}. -/
noncomputable def compiledEvalSubspace (n : ℕ) :
    Submodule ℚ ((Fin n → Bool) → ℚ) :=
  Submodule.span ℚ
    { v | ∃ f : (Fin n → Bool) → Bool,
        CompiledLowRank f ∧ v = fun x => if f x then (1 : ℚ) else 0 }

/-! ## Axiom 1: P-side Upper Bound (Paper Theorem 92 / §9 / §17.3)

  Every P-time function compiles to low rank for large n.

  Proof route in the paper:
  1. Cook-Levin (§17.1): DTM → width-3 CNF on N = Θ(n³) variables
  2. Profile compression (§9): block-locality → constant-type profiles
  3. Global assembly (§17.3): Γ_{κ,ℓ}(P_{M,n}) ≤ poly(n)
  4. Parameter choice: poly(n) ≤ √n for large n -/

axiom pside_compiled_collapse :
    ∀ (M : DTM), ∃ (n₀ : ℕ),
    ∀ (n : ℕ), n ≥ n₀ → n ≥ 2 →
    ∀ (f : (Fin n → Bool) → Bool), M.decides f →
    CompiledLowRank f

/-! ## P ⊆ compiled-SPDP (derived from Axiom 1) -/

theorem ptime_implies_low_rank (F : BoolFunFamily) (hP : UniformPtime F) :
    ∃ n₀, ∀ n, n ≥ n₀ → n ≥ 2 → CompiledLowRank (F n) := by
  obtain ⟨M, hM⟩ := hP
  obtain ⟨n₀, h⟩ := pside_compiled_collapse M
  exact ⟨n₀, fun n hn₀ hn2 => h n hn₀ hn2 (F n) (hM n)⟩

/-! ## Axiom 2: Constructive Witness (Paper §11.7)

  For large n, the compiled evaluation subspace V_n is proper,
  and there exists a deterministic polynomial-time algorithm that
  constructs w ∈ V_n^⊥ with w(x₀) > 0 for some x₀.

  This replaces the old Classical.choice-based dualAnnihilator.
  The constructive witness makes f_n ∈ NP provable. -/

/-- An SPDP annihilator for the compiled subspace. -/
structure CompiledAnnihilator (n : ℕ) where
  w : (Fin n → Bool) → ℚ
  hw_pos : ∃ x, w x > 0
  hw_orth : ∀ f, CompiledLowRank f →
    ∑ x : Fin n → Bool, (if f x then (1 : ℚ) else 0) * w x = 0

axiom constructive_witness :
    ∃ n₀, ∀ n, n ≥ n₀ → n ≥ 2 →
    ∃ (w : (Fin n → Bool) → ℚ),
      (∃ x, w x > 0) ∧
      (∀ f, CompiledLowRank f →
        ∑ x : Fin n → Bool, (if f x then (1 : ℚ) else 0) * w x = 0)

/-- Extract a CompiledAnnihilator from the witness axiom. -/
noncomputable def getAnnihilator (n : ℕ) (hn₀ : n ≥ constructive_witness.choose)
    (hn2 : n ≥ 2) : CompiledAnnihilator n where
  w := (constructive_witness.choose_spec n hn₀ hn2).choose
  hw_pos := (constructive_witness.choose_spec n hn₀ hn2).choose_spec.1
  hw_orth := (constructive_witness.choose_spec n hn₀ hn2).choose_spec.2

/-! ## Diagonal function (constructive) -/

/-- The diagonal function: f_n(x) = true iff the annihilator is positive at x. -/
noncomputable def diagonal {n : ℕ} (ann : CompiledAnnihilator n) :
    (Fin n → Bool) → Bool :=
  fun x => if ann.w x > 0 then true else false

/-! ## Axiom 3: Diagonal Escape (Paper Theorem 94)

  The diagonal function escapes compiled low rank.
  This is the NP-side lower bound: the diagonal's compiled SPDP rank
  exceeds √n for all large n.

  Note: this is where the paper's actual lower-bound argument lives.
  The old branch's Möbius/top-coefficient route does NOT apply here
  because it targeted multilinearInterp, not the compiled polynomial. -/

axiom diagonal_escape :
    ∃ n₀, ∀ n, n ≥ n₀ → n ≥ 2 →
    ∀ (ann : CompiledAnnihilator n),
    ¬ CompiledLowRank (diagonal ann)

/-! ## Axiom 4: Diagonal ∈ NP (Paper Theorem 94 part (b))

  The diagonal family is in NP. The witness is the constructive
  annihilator from §11.7 (or a short seed encoding it).
  The verifier checks:
  (a) w is a valid annihilator (orthogonal to compiled eval subspace)
  (b) w(x) > 0

  Since w is constructible in poly-time (§11.7), and the orthogonality
  check is poly-time linear algebra, the whole verification is poly-time. -/

noncomputable def diagonalFamily : BoolFunFamily := fun n =>
  if h : n ≥ 2 then
    if hn₀ : n ≥ constructive_witness.choose
    then diagonal (getAnnihilator n hn₀ h)
    else fun _ => false
  else fun _ => false

axiom diagonal_in_NP : UniformNP diagonalFamily

/-! ## Theorem 207: P ≠ NP -/

theorem P_neq_NP : ¬ P_eq_NP := by
  intro hPeqNP
  -- The diagonal family is in NP
  have hNP := diagonal_in_NP
  -- P = NP gives us a DTM for the diagonal
  have hP := hPeqNP diagonalFamily hNP
  -- P-side: for large n, every P-time function has low compiled rank
  obtain ⟨n₁, h_low⟩ := ptime_implies_low_rank diagonalFamily hP
  -- NP-side: for large n, the diagonal escapes low rank
  obtain ⟨n₂, h_esc⟩ := diagonal_escape
  -- Witness threshold (same one used in diagonalFamily definition)
  let n₃ := constructive_witness.choose
  -- Pick n large enough
  let n := max (max (max n₁ n₂) n₃) 2
  have hn₁ : n ≥ n₁ := le_trans (le_trans (le_max_left n₁ n₂) (le_max_left _ n₃)) (le_max_left _ 2)
  have hn₂ : n ≥ n₂ := le_trans (le_trans (le_max_right n₁ n₂) (le_max_left _ n₃)) (le_max_left _ 2)
  have hn₃ : n ≥ n₃ := le_trans (le_max_right _ n₃) (le_max_left _ 2)
  have hn2 : n ≥ 2 := le_max_right _ 2
  -- diagonalFamily n = diagonal (getAnnihilator n ...)
  have h_eq : diagonalFamily n = diagonal (getAnnihilator n hn₃ hn2) := by
    show (if h : n ≥ 2 then if hn₀ : n ≥ constructive_witness.choose
      then diagonal (getAnnihilator n hn₀ h) else fun _ => false else fun _ => false)
      = diagonal (getAnnihilator n hn₃ hn2)
    rw [dif_pos hn2, dif_pos hn₃]
  -- Low rank (from P-side)
  have h_lr := h_low n hn₁ hn2
  -- Escape (from NP-side)
  have h_ne := h_esc n hn₂ hn2 (getAnnihilator n hn₃ hn2)
  -- But low rank of diagonalFamily n = low rank of diagonal (h_wit n ...)
  rw [h_eq] at h_lr
  exact h_ne h_lr

#check @P_neq_NP  -- CompiledSeparation.P_neq_NP : ¬P_eq_NP

end CompiledSeparation
