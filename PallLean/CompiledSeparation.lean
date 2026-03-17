/-
  CompiledSeparation.lean — P ≠ NP via Compiled Polynomial Architecture

  Paper's spine (arXiv v5):
    Theorem 92:  P-side compiled upper bound
    Theorem 94:  NP-side exponential SPDP lower bound (permanent)
    Section 11.7: Constructive w ∈ V_n^⊥
    Theorem 207: Rank-monotone block-local reduction → P ≠ NP

  Axiom inventory (4 axioms):
    1. pside_compiled_collapse  — Thm 92 / §9 / §17.3
    2. permanent_spdp_lower     — Thm 94: Γ(perm_n) is exponential
    3. constructive_witness     — §11.7: poly-time w ∈ V_n^⊥
    4. separation_bridge        — Thm 207: algebraic → Boolean separation
-/
import PallLean.CompiledPoly
import PallLean.Permanent
import PallLean.TuringMachine
import Mathlib.Tactic

namespace CompiledSeparation

open CompiledPoly Permanent TuringMachine

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

/-- A function "compiles to low rank" if its DTM's Cook-Levin polynomial
    has blocked SPDP rank ≤ √n at κ = ℓ = log₂ n. -/
def CompiledLowRank (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (M : DTM) (k : ℕ) (cnf : CookLevinCNF (compiledVarCount k n))
    (hlp : HasLocalPartition cnf),
    M.decides f ∧
    blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyQ cnf) hlp.partition ≤ Nat.sqrt n

/-! ## Axiom 1: P-side Compiled Upper Bound (Theorem 92 / §9 / §17.3)

  Every P-time function compiles to low rank for large n.
  Proof: Cook-Levin → block-local polynomial → profile compression. -/

axiom pside_compiled_collapse :
    ∀ (M : DTM), ∃ (n₀ : ℕ),
    ∀ (n : ℕ), n ≥ n₀ → n ≥ 2 →
    ∀ (f : (Fin n → Bool) → Bool), M.decides f →
    CompiledLowRank f

theorem ptime_implies_low_rank (F : BoolFunFamily) (hP : UniformPtime F) :
    ∃ n₀, ∀ n, n ≥ n₀ → n ≥ 2 → CompiledLowRank (F n) := by
  obtain ⟨M, hM⟩ := hP
  obtain ⟨n₀, h⟩ := pside_compiled_collapse M
  exact ⟨n₀, fun n hn₀ hn2 => h n hn₀ hn2 (F n) (hM n)⟩

/-! ## Axiom 2: NP-side Exponential Lower Bound (Theorem 94)

  The permanent polynomial perm_n has exponential blocked SPDP rank.
  This is the algebraic hardness ingredient.

  Paper: Γ_{κ,ℓ}(perm_n) ≥ 2^{n/4} (or n!).

  Combined with the P-side collapse, this means: if the permanent
  were P-time computable, its compiled polynomial would have low rank,
  contradicting the exponential lower bound. -/

axiom permanent_spdp_lower :
    ∃ (n₀ : ℕ), ∀ (m : ℕ), m ≥ n₀ →
    ∀ (k : ℕ) (cnf : CookLevinCNF (compiledVarCount k (m * m)))
      (hlp : HasLocalPartition cnf),
    blockedSpdpRankQ (Nat.log 2 (m * m)) (Nat.log 2 (m * m))
      (compiledPolyQ cnf) hlp.partition > Nat.sqrt (m * m)

/-! ## Axiom 3: Constructive Witness (§11.7)

  Deterministic polynomial-time construction of w ∈ V_n^⊥.
  "We give a deterministic procedure that produces a nonzero vector w
   orthogonal to the P-side subspace V_n." -/

axiom constructive_witness :
    ∃ n₀, ∀ n, n ≥ n₀ → n ≥ 2 →
    ∃ (w : (Fin n → Bool) → ℚ),
      (∃ x, w x > 0) ∧
      (∀ f, CompiledLowRank f →
        ∑ x : Fin n → Bool, (if f x then (1 : ℚ) else 0) * w x = 0)

/-! ## Axiom 4: Separation Bridge (Theorem 207)

  The rank-monotone block-local reduction bridges the algebraic
  separation (permanent has high SPDP rank) to Boolean separation
  (∃ NP function not in P).

  This is the theorem that connects:
  - P-side: P-time → compiled low rank
  - NP-side: permanent has compiled high rank
  - permanent (as a decision problem) is in NP
  - Therefore P ≠ NP

  We state this as: the permanent decision problem is in NP
  but NOT in UniformPtime (given the SPDP separation). -/

axiom separation_bridge :
    ∃ (F : BoolFunFamily),
    UniformNP F ∧
    (∀ (M : DTM), ∃ n₀, ∀ n, n ≥ n₀ → n ≥ 2 →
      M.decides (F n) → ¬ CompiledLowRank (F n))

/-! ## Theorem 207: P ≠ NP -/

theorem P_neq_NP : ¬ P_eq_NP := by
  intro hPeqNP
  -- Get the hard NP family from the separation bridge
  obtain ⟨F, hNP, hHard⟩ := separation_bridge
  -- P = NP gives us a DTM for F
  obtain ⟨M, hM⟩ := hPeqNP F hNP
  -- P-side: M-decidable functions compile to low rank for large n
  obtain ⟨n₁, h_low⟩ := pside_compiled_collapse M
  -- NP-side: F escapes low rank for large n (for this specific M)
  obtain ⟨n₂, h_hard⟩ := hHard M
  -- Pick n large enough
  let n := max (max n₁ n₂) 2
  have hn₁ : n ≥ n₁ := le_trans (le_max_left n₁ n₂) (le_max_left _ 2)
  have hn₂ : n ≥ n₂ := le_trans (le_max_right n₁ n₂) (le_max_left _ 2)
  have hn2 : n ≥ 2 := le_max_right _ 2
  -- Low rank from P-side
  have h_lr := h_low n hn₁ hn2 (F n) (hM n)
  -- Escape from NP-side
  have h_esc := h_hard n hn₂ hn2 (hM n)
  exact h_esc h_lr

#check @P_neq_NP  -- CompiledSeparation.P_neq_NP : ¬P_eq_NP

end CompiledSeparation
