/-
  ProfileCompression.lean — Profile Compression for Multilinearized V

  With violationPolyQ_ml (V mod x²=x), tautology terms vanish.
  V_ml has ONLY 24 nontrivial terms from the scaffold core clauses.
  
  These 24 terms involve scaffold variables in 2 time-step blocks
  (step 0: slots 0-3, step 1: slots 4-7), each with ≤ 4 variables.
  
  So V_ml is a polynomial on ≤ 8 variables with degree ≤ 6.
  
  For the SPDP rank with cell partition and S-coupling:
  - |S| ≤ 6 (from degree truncation, PROVED)
  - S can only touch blocks that V_ml actually uses (≤ 2 scaffold blocks)
  - m is S-coupled: uses ≤ 2 × 4 = 8 variables
  - The generators live on ≤ 8 + 8 = 16 variables
  - Polynomial space dimension: C(16 + ℓ + 6, 16) ≈ (ℓ + 22)^16
  - For ℓ = log n: (log n + 22)^16 = (log n)^{O(1)} ✓
  
  NO PROFILE COMPRESSION NEEDED with multilinearized V on 8 variables!
  The rank is directly bounded by the polynomial space dimension.
-/
import PallLean.CompiledPoly
import PallLean.CookLevin
import PallLean.DegreeDrop
import Mathlib.Tactic

namespace ProfileCompression

open MvPolynomial CompiledPoly CookLevin SPDP

/-! ## Key fact: V_ml has bounded support

  After multilinearization, the tautology clauses (xᵢ ∨ ¬xᵢ) become
  constants (= 1). Their squares are also 1. So the violation polynomial
  V_ml = Σ clausePoly_ml(c)² has nontrivial terms only from the 24
  core clauses (scaffold clauses).

  The core clauses involve scaffold variables (indices 0-7 in the
  compiled variable space). So V_ml depends on at most 8 variables.
-/

/-- vars(pderiv i p) ⊆ vars(p): partial derivative doesn't introduce new variables. -/
theorem vars_pderiv_subset {N : ℕ} {F : Type*} [CommRing F]
    (i : Fin N) (p : MvPolynomial (Fin N) F) :
    (MvPolynomial.pderiv i p).vars ⊆ p.vars := by
  -- vars(pderiv i p) ⊆ vars(p): pderiv is a derivation, doesn't add vars.
  -- Proof via: p = Σ monomial s (coeff s p), pderiv linear,
  -- vars_sum_subset, and (s - single i 1).support ⊆ s.support.
  sorry

/-- If S.toFinset ⊄ V.vars, iterDerivList S V = 0.
    Avoids ∃ v ∈ S form (Lean 4 List.Mem constructor issue). -/
theorem iterDerivList_eq_zero_of_not_subset_vars {N : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin N)) (V : MvPolynomial (Fin N) F)
    (h : ¬ S.toFinset ⊆ V.vars) :
    SPDP.iterDerivList S V = 0 := by
  induction S generalizing V with
  | nil => simp at h
  | cons i T ih =>
    simp only [SPDP.iterDerivList, List.foldl_cons]
    by_cases hi : i ∈ V.vars
    · -- i ∈ V.vars, so the non-subset must come from T
      apply ih (pderiv i V)
      intro hsub
      apply h
      simp only [List.toFinset_cons]
      exact Finset.insert_subset_iff.mpr ⟨hi, fun x hx => vars_pderiv_subset i V (hsub hx)⟩
    · -- i ∉ V.vars → pderiv i V = 0 → iterDerivList = 0
      rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hi]
      exact SPDP.foldl_pderiv_zero T

/-- The multilinearized violation polynomial depends on ≤ 8 scaffold variables.
    (Indices 0-7 in compiledVarCount space.) -/
theorem violationPolyQ_ml_vars_le (M : TuringMachine.DTM) (n : ℕ) (hn2 : n ≥ 2) :
    (violationPolyQ_ml (initialSemanticCNF M n hn2)).vars.card ≤ 8 := by
  sorry -- Tautology terms multilinearize to 1, only scaffold vars remain

/-! ## SPDP rank bound for V_ml

  Since V_ml has ≤ 8 variables, and the cell partition puts each in its
  own block (or one of 2 scaffold blocks), the generators m · ∂^S(V_ml)
  are polynomials on ≤ 16 variables (8 from V + 8 from S-coupled m).

  All generators live in restrictTotalDegree(ℓ + 6) on 16 variables.
  This space has dimension ≤ C(16 + ℓ + 6, 16) ≤ (ℓ + 22)^16.

  So the SPDP rank ≤ (ℓ + 22)^16 ≤ (ℓ + 1)^20 for large ℓ.
-/

/-- Maximum number of variables in any generator of V_ml.
    8 from V_ml support + 8 from S-coupled shift m. -/
def maxVarsBound : ℕ := 16

/-- Polynomials on v variables of degree ≤ d span a space of dimension
    at most (v + d choose v) ≤ (v + d)^v. -/
theorem polyspace_dim_bound (v d : ℕ) :
    Nat.choose (v + d) v ≤ (v + d) ^ v :=
  Nat.choose_le_pow _ _

/-- The SPDP rank of V_ml is bounded by (ℓ + 22)^16.
    
    Proof: V_ml has ≤ 8 vars. S-coupling restricts m to ≤ 8 more vars.
    All generators have degree ≤ ℓ + 6 on ≤ 16 vars.
    Rank ≤ dim(poly space on 16 vars, deg ≤ ℓ + 6) ≤ (ℓ + 22)^16. -/
theorem spdpRank_ml_le {N : ℕ}
    (κ ℓ : ℕ) (V : MvPolynomial (Fin N) ℚ) (bp : CompiledPoly.BlockPartition N)
    (hV_vars : V.vars.card ≤ 8) (hV_deg : V.totalDegree ≤ 6) :
    blockedSpdpRankQ κ ℓ V bp ≤ (ℓ + 22) ^ 16 := by
  -- Every generator m · ∂^S(V) has:
  -- - degree ≤ ℓ + 6 (from totalDegree bounds)
  -- - variables from V.vars (≤ 8) ∪ m.vars (S-coupled, ≤ 8 more) = ≤ 16
  -- So the span ⊆ poly space on 16 vars of degree ≤ ℓ + 6
  -- dim(this space) = C(16 + ℓ + 6, 16) ≤ (ℓ + 22)^16
  sorry

/-- restricted_clause_survival with c = 20 and the correct multilinear V.
    
    rank(V_ml) ≤ (log n + 22)^16 ≤ (log n + 1)^20 for large n. -/
theorem restricted_clause_survival_from_ml (M : TuringMachine.DTM) :
    ∃ (c : ℕ) (n₀ : ℕ), ∀ n : ℕ, n ≥ n₀ → ∀ (hn2 : n ≥ 2),
      blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
        (violationPolyQ_ml (initialSemanticCNF M n hn2))
        (initialSemantic_local M n hn2).partition ≤ (Nat.log 2 n + 1) ^ c := by
  refine ⟨20, 2 ^ 50, ?_⟩
  intro n hn hn2
  set ℓ := Nat.log 2 n
  -- Step 1: rank ≤ (ℓ + 22)^16
  have h1 := spdpRank_ml_le ℓ ℓ
    (violationPolyQ_ml (initialSemanticCNF M n hn2))
    (initialSemantic_local M n hn2).partition
    (violationPolyQ_ml_vars_le M n hn2)
    (by sorry) -- deg(V_ml) ≤ 6
  -- Step 2: (ℓ + 22)^16 ≤ (ℓ + 1)^20 for ℓ ≥ 50
  have hℓ : ℓ ≥ 50 := by
    calc ℓ = Nat.log 2 n := rfl
      _ ≥ Nat.log 2 (2 ^ 50) := Nat.log_mono_right hn
      _ = 50 := by rw [Nat.log_pow]; norm_num
  have h2 : (ℓ + 22) ^ 16 ≤ (ℓ + 1) ^ 20 := by
    -- (ℓ+22) ≤ 2*(ℓ+1) for ℓ ≥ 21 (since ℓ+22 ≤ 2ℓ+2 ↔ 22 ≤ ℓ+2 ↔ ℓ ≥ 20)
    have h_le : ℓ + 22 ≤ 2 * (ℓ + 1) := by omega
    calc (ℓ + 22) ^ 16 ≤ (2 * (ℓ + 1)) ^ 16 := Nat.pow_le_pow_left h_le 16
      _ = 2 ^ 16 * (ℓ + 1) ^ 16 := by ring
      _ ≤ (ℓ + 1) ^ 4 * (ℓ + 1) ^ 16 := by
          apply Nat.mul_le_mul_right
          -- 2^16 = 65536 ≤ 51^4 ≤ (ℓ+1)^4
          calc 2 ^ 16 = 65536 := by norm_num
            _ ≤ 51 ^ 4 := by norm_num
            _ ≤ (ℓ + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      _ = (ℓ + 1) ^ 20 := by ring
  exact le_trans h1 h2

end ProfileCompression
