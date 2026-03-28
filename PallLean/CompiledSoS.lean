import PallLean.MultilinearSPDP
import PallLean.NPWitness
import PallLean.Compiler
import Mathlib.Tactic

/-!
# CompiledSoS — Paper §17 Sum-of-Squares Compiled Polynomial

Paper-faithful P-side rank bound via the locality argument (Theorem 92).

The key insight: the compiled polynomial PM,n = 1 - Σ C² has CONSTANT degree
(≤ 2d₀ where d₀ = max constraint degree). For κ > 2d₀, ALL κ-th derivatives
vanish, giving SPDP rank = 0.

For our specific constraints (degree ≤ 2):
  PM,n = 1 - Σ c_i² has degree ≤ 4
  For κ ≥ 5: all κ-th derivatives are 0 → rank = 0

## Paper reference:
- §17.1: Construction of PM,n = 1 - Σ C²
- §17.2: Locality and SPDP rows (Lemma 91)
- §17.3: Polynomial upper bound on Γ (equation (5))
- Theorem 92: P ⇒ poly-SPDP
-/

namespace CompiledSoS

open SPDP MultilinearSPDP NPWitness Tseitin Compiler TuringMachine MvPolynomial

/-- The compiled polynomial in sum-of-squares form:
    PM,n = 1 - Σ_C C(x,τ)²
    where C ranges over all compilation constraints.
    This has degree ≤ 2 × max_degree(C) ≤ 4.

    Paper §17.1: "From now on write PM,n for this constant-degree version." -/
noncomputable def compiledPolySoS (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (numVars M n (Nat.log 2 n))) F :=
  1 - violationPolyOf F M n

/-- compiledPolySoS has totalDegree ≤ 4.
    Each constraint has degree ≤ 2, so C² has degree ≤ 4.
    The sum has degree ≤ max(degree(terms)) ≤ 4.
    And 1 has degree 0. So max(0, 4) = 4. -/
theorem compiledPolySoS_totalDegree (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n : ℕ) :
    (compiledPolySoS F M n).totalDegree ≤ 4 := by
  unfold compiledPolySoS
  calc (1 - violationPolyOf F M n).totalDegree
      ≤ max (1 : MvPolynomial _ F).totalDegree (violationPolyOf F M n).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ max 0 4 := by
        apply max_le_max
        · simp [MvPolynomial.totalDegree_one]
        · exact violationPolyOf_totalDegree F M n
    _ = 4 := by omega

/-- For κ ≥ 5 > 4 = degree(compiledPolySoS), all κ-th derivatives vanish.
    Therefore the SPDP subspace is {0} and rank = 0.

    Paper §17.3 equation (5): Γ_{κ,ℓ}(PM,n) ≤ n^O(1).
    In fact, for our degree-4 polynomial and κ ≥ 5, rank = 0 ≤ n^O(1). -/
theorem compiledPolySoS_spdp_rank_zero (F : Type*) [Field F] [Nontrivial F]
    (M : DTM) (n : ℕ)
    (κ : ℕ) (hκ : κ ≥ 5) (ℓ : ℕ) :
    mlBlockedSpdpRank (compiledPartition M n) κ ℓ
      (compiledPolySoS F M n) = 0 := by
  -- Every generator mlProj(m × ∂^S p) = 0 because ∂^S p = 0:
  -- p has degree ≤ 4, and |S| = κ ≥ 5 > 4.
  -- Differentiating a degree-d polynomial d+1 times gives 0.
  unfold mlBlockedSpdpRank
  -- The subspace is {0} because every generator is 0.
  -- iterDerivList S p = 0 for |S| = κ ≥ 5 > 4 = deg(p).
  -- The subspace is {0} because every generator is 0.
  -- Use: every generator has the form mlProj(m * iterDerivList S p) = mlProj(m * 0) = 0.
  -- Every generator mlProj(m * iterDerivList S p) = 0 because
  -- iterDerivList S p = 0 (|S| = κ ≥ 5 > 4 ≥ deg(p)).
  -- So the subspace = span({0}) = ⊥, which has finrank = 0.
  have hdeg := compiledPolySoS_totalDegree F M n
  have hgen_zero : ∀ (S : List (Fin (numVars M n (Nat.log 2 n))))
      (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) F),
      S.length = κ →
      mlProj (m * iterDerivList S (compiledPolySoS F M n)) = 0 := by
    intro S m hlen
    have hzero : iterDerivList S (compiledPolySoS F M n) = 0 :=
      iterDerivList_eq_zero_of_totalDegree_lt S _ (by omega)
    rw [hzero, mul_zero, mlProj_zero]
  -- mlBlockedSpdpSubspace = span of generators = span of {0} = ⊥
  show Module.finrank F ↥(mlBlockedSpdpSubspace (compiledPartition M n) κ ℓ
      (compiledPolySoS F M n)) = 0
  have hsub : mlBlockedSpdpSubspace (compiledPartition M n) κ ℓ
      (compiledPolySoS F M n) = ⊥ := by
    rw [eq_bot_iff, mlBlockedSpdpSubspace]
    apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, _, _, _, hq⟩
    have : q = 0 := by rw [hq]; exact hgen_zero S m hlen
    exact this ▸ Submodule.zero_mem _
  rw [hsub]
  exact finrank_bot F _

/-- Corollary: compiledPolySoS has mlBlockedSpdpRank ≤ n^215 (trivially, since rank = 0). -/
theorem compiledPolySoS_rank_le (M : DTM) (n : ℕ) (hn : n ≥ max 4 M.numStates)
    (κ : ℕ) (hκ : κ ≥ 5) (hκ_le : κ ≤ Nat.log 2 n) :
    mlBlockedSpdpRank (compiledPartition M n) κ κ
      (compiledPolySoS ℚ M n) ≤ n ^ 215 := by
  rw [compiledPolySoS_spdp_rank_zero ℚ M n κ hκ κ]
  exact Nat.zero_le _

end CompiledSoS
