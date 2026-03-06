import Mathlib
import PallLean.DecisionMobiusBridge

/-!
# MUS Distribution — NP-side Möbius mass lower bounds

## Goal

Show that specific SAT formula families have superpolynomially many MUSes,
giving superpolynomial Möbius mass via `mus_mobius_eq_neg_one`.

## Families

1. **Unit Clause Family**: For n variables, create 2n unit clauses:
   (x₁), (¬x₁), (x₂), (¬x₂), ..., (xₙ), (¬xₙ).
   Each contradictory pair {(xᵢ), (¬xᵢ)} is a MUS of size 2.
   Products of k disjoint contradictory pairs give MUSes of size 2k.
   Count: C(n,k) MUSes of size 2k.

2. **Tseitin Formulas on Expander Graphs**: Known to have exponentially
   many MUSes (connection to proof complexity lower bounds).
-/

namespace MUSDistribution

open Finset BigOperators DecisionMobiusBridge

/-! ## 1. Unit Clause Family -/

/-- The unit clause family over n variables.
    Clause 2i = (xᵢ), clause 2i+1 = (¬xᵢ).
    Total: m = 2n clauses.

    The key property: subset S is UNSAT iff it contains some
    contradictory pair {2i, 2i+1}. -/
structure UnitClauseFamily (n : ℕ) where
  /-- Decision function: UNSAT iff some contradictory pair is included. -/
  D : SATDecision (2 * n)
  /-- Core axiom: S is SAT iff no contradictory pair {2i, 2i+1} ⊆ S. -/
  h_sat : ∀ S : Finset (Fin (2 * n)),
    D.isSAT S = true ↔
    ∀ i : Fin n, ¬(⟨2 * i.val, by have := i.isLt; omega⟩ ∈ S ∧
                    ⟨2 * i.val + 1, by have := i.isLt; omega⟩ ∈ S)

/-- A contradictory pair for variable i. -/
def contrPair (n : ℕ) (i : Fin n) : Finset (Fin (2 * n)) :=
  {⟨2 * i.val, by have := i.isLt; omega⟩,
   ⟨2 * i.val + 1, by have := i.isLt; omega⟩}

/-- Contradictory pairs are nonempty. -/
lemma contrPair_nonempty (n : ℕ) (i : Fin n) : (contrPair n i).Nonempty :=
  ⟨⟨2 * i.val, by have := i.isLt; omega⟩, by simp [contrPair]⟩

/-- The two elements of a contradictory pair are distinct. -/
lemma contrPair_ne (n : ℕ) (i : Fin n) :
    (⟨2 * i.val, by have := i.isLt; omega⟩ : Fin (2 * n)) ≠
    ⟨2 * i.val + 1, by have := i.isLt; omega⟩ := by
  simp [Fin.ext_iff]

/-- Contradictory pairs have exactly 2 elements. -/
lemma contrPair_card (n : ℕ) (i : Fin n) : (contrPair n i).card = 2 := by
  simp only [contrPair]
  exact Finset.card_pair (contrPair_ne n i)

/-- A contradictory pair is a MUS in the unit clause family. -/
theorem contrPair_is_mus (F : UnitClauseFamily n) (i : Fin n) :
    IsMUS F.D (contrPair n i) := by
  constructor
  · -- contrPair is UNSAT
    by_contra h
    simp only [Bool.not_eq_false] at h
    have h' := (F.h_sat (contrPair n i)).mp h i
    apply h'
    exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))⟩
  · -- Every proper subset is SAT
    intro T hT hne
    have hT_sub := Finset.mem_powerset.mp hT
    -- T ⊂ contrPair i means T.card < 2
    have hT_lt : T.card < 2 := by
      have hsub : T ⊂ contrPair n i := lt_of_le_of_ne hT_sub hne
      calc T.card < (contrPair n i).card := Finset.card_lt_card hsub
        _ = 2 := contrPair_card n i
    -- Show T is SAT by showing no variable has both literals in T
    suffices h : ∀ j : Fin n, ¬(⟨2*j.val, by have := j.isLt; omega⟩ ∈ T ∧
        ⟨2*j.val+1, by have := j.isLt; omega⟩ ∈ T) from (F.h_sat T).mpr h
    intro j ⟨hj1, hj2⟩
    -- T contains 2 distinct elements → card ≥ 2, contradicting card < 2
    have hne_j : (⟨2*j.val, by have := j.isLt; omega⟩ : Fin (2*n)) ≠
                 ⟨2*j.val+1, by have := j.isLt; omega⟩ := by simp [Fin.ext_iff]
    have hsub2 : ({⟨2*j.val, by have := j.isLt; omega⟩,
                   ⟨2*j.val+1, by have := j.isLt; omega⟩} : Finset (Fin (2*n))) ⊆ T := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hj1, hj2⟩
    have : 2 ≤ T.card := by
      have hc := Finset.card_pair hne_j
      have hle := Finset.card_le_card hsub2
      omega
    omega

/-- Each contradictory pair has Möbius coefficient -1. -/
theorem contrPair_mobius (F : UnitClauseFamily n) (i : Fin n) :
    mobiusCoeff F.D (contrPair n i) = -1 :=
  mus_mobius_eq_neg_one F.D _ (contrPair_nonempty n i) (contrPair_is_mus F i)

/-- The number of MUSes of size 2 is at least n (one per variable). -/
theorem mus_count_size2_ge_n (F : UnitClauseFamily n) :
    n ≤ ((Finset.univ : Finset (Fin (2*n))).powerset.filter
      (fun S => S.card = 2 ∧ F.D.isSAT S = false ∧
        ∀ T ∈ S.powerset, T ≠ S → F.D.isSAT T = true)).card := by
  sorry

/-! ## 2. Products of Contradictory Pairs

For k disjoint contradictory pairs, their union is UNSAT and every
proper subset is SAT (when restricted to these 2k clauses).

The union of k disjoint contradictory pairs has Möbius coefficient
(-1)^k by the product formula. -/

/-- A set of k disjoint contradictory pairs, selected by choosing k
    variables from [n]. The union has size 2k and is a "product MUS". -/
def pairUnion (n : ℕ) (vars : Finset (Fin n)) : Finset (Fin (2 * n)) :=
  vars.biUnion (contrPair n)

/-- The Möbius coefficient of a union of k disjoint contradictory pairs
    equals (-1)^k (product of independent -1 contributions). -/
theorem pairUnion_mobius (F : UnitClauseFamily n)
    (vars : Finset (Fin n)) (hne : vars.Nonempty) :
    mobiusCoeff F.D (pairUnion n vars) = (-1) ^ vars.card := by
  -- By decomposable product theorem: f̂(A∪B) = f̂(A) · f̂(B)
  -- Each contradictory pair contributes -1, and pairs are independent.
  sorry

/-- **NP-side mass lower bound**: The Möbius mass at level 2k is at least
    C(n, k) — one for each choice of k variables forming k contradictory pairs.

    For k = ⌊log₂ n⌋, this gives superpolynomial mass. -/
theorem mobius_mass_level_2k_lower (F : UnitClauseFamily n) (k : ℕ)
    (hk : k ≤ n) :
    n.choose k ≤ DecisionMobiusBridge.mobiusMassLevel F.D (2 * k) := by
  -- Each of the C(n,k) sets of k variables gives a distinct element
  -- of (2n).powerset with card = 2k and |f̂| = 1.
  sorry

/-- **Superpolynomial mass**: For any polynomial bound n^C, there exists
    n₀ such that for all n ≥ n₀, the Möbius mass at level 2·⌊log₂ n⌋
    exceeds n^C. -/
theorem superpolynomial_mobius_mass :
    ∀ C : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (F : UnitClauseFamily n),
        n ^ C < DecisionMobiusBridge.mobiusMassLevel F.D (2 * Nat.log 2 n) := by
  -- Follows from mobius_mass_level_2k_lower and choose_log_superpolynomial.
  -- C(n, log₂ n) > n^C for large enough n.
  sorry

/-! ## 3. Staged Bridge Claims

The bridge argument now has three components:

### NP-side (this file): ✅ (modulo sorry's for counting)
For unit clause families, Möbius mass at level 2k ≥ C(n,k).
At k = log₂ n, this is superpolynomial.

### Correctness (DecisionMobiusBridge.lean): ✅ PROVED
Any correct solver computes the same boolean function f(z) = SAT(z),
so the Möbius mass is representation-invariant (mus_mobius_eq_neg_one).

### P-side: OPEN
Does poly-time computation limit achievable Möbius mass?

The unit clause family is particularly interesting because:
- SAT for unit clauses is in **P** (actually in **co-NP ∩ P**)
- The decision function f(z) = "is clause subset z satisfiable?" is easy
- But its Möbius mass is still superpolynomial!

**This means Möbius mass alone does NOT separate P from NP.**

The key insight: having high Möbius mass is necessary for NP-hard
instances but NOT sufficient. The separation must come from
additional structure beyond mass (e.g., the specific pattern of
MUS interactions, or the relationship between MUS size and formula size).

### Where the actual P ≠ NP content lives:

The separation between P and NP-complete problems requires:
1. Not just "does f have high Möbius mass?" (unit clauses show P can too)
2. But "does the COMPILED SEARCH POLYNOMIAL have structure that
   forces superpolynomial representation?" — the algebraic complexity
   of the search, not just the decision function.

This is consistent with the earlier finding that extraction_rank_monotone
(or its search-side equivalent) IS the mathematical content of P ≠ NP. -/

end MUSDistribution
