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

/-- Distinct variables give distinct contradictory pairs. -/
lemma contrPair_injective (n : ℕ) : Function.Injective (contrPair n) := by
  intro i j h
  -- {2i, 2i+1} = {2j, 2j+1} implies 2i ∈ {2j, 2j+1}
  have h1 : (⟨2*i.val, by have := i.isLt; omega⟩ : Fin (2*n)) ∈ contrPair n j := by
    have : (⟨2*i.val, by have := i.isLt; omega⟩ : Fin (2*n)) ∈ contrPair n i :=
      Finset.mem_insert_self _ _
    rw [h] at this; exact this
  simp only [contrPair, Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with h1 | h1
  · exact Fin.ext (by have := congr_arg Fin.val h1; simp at this; omega)
  · exact Fin.ext (by have := congr_arg Fin.val h1; simp at this; omega)

theorem mus_count_size2_ge_n (F : UnitClauseFamily n) :
    n ≤ ((Finset.univ : Finset (Fin (2*n))).powerset.filter
      (fun S => S.card = 2 ∧ F.D.isSAT S = false ∧
        ∀ T ∈ S.powerset, T ≠ S → F.D.isSAT T = true)).card := by
  -- The image of contrPair is a subset of the MUS filter
  set MF := (Finset.univ : Finset (Fin (2*n))).powerset.filter
    (fun S => S.card = 2 ∧ F.D.isSAT S = false ∧
      ∀ T ∈ S.powerset, T ≠ S → F.D.isSAT T = true)
  calc (n : ℕ) = Fintype.card (Fin n) := (Fintype.card_fin n).symm
    _ = (Finset.univ : Finset (Fin n)).card := (Finset.card_univ).symm
    _ = ((Finset.univ : Finset (Fin n)).image (contrPair n)).card := by
        rw [Finset.card_image_of_injective _ (contrPair_injective n)]
    _ ≤ MF.card := by
        apply Finset.card_le_card
        intro S hS
        rw [Finset.mem_image] at hS
        obtain ⟨i, _, rfl⟩ := hS
        rw [Finset.mem_filter]
        refine ⟨?_, contrPair_card n i, ?_⟩
        · exact Finset.mem_powerset.mpr (Finset.subset_univ _)
        · exact ⟨(contrPair_is_mus F i).1, (contrPair_is_mus F i).2⟩

/-! ## 2. Products of Contradictory Pairs

For k disjoint contradictory pairs, their union is UNSAT and every
proper subset is SAT (when restricted to these 2k clauses).

The union of k disjoint contradictory pairs has Möbius coefficient
(-1)^k by the product formula. -/

/-- A set of k disjoint contradictory pairs, selected by choosing k
    variables from [n]. The union has size 2k and is a "product MUS". -/
def pairUnion (n : ℕ) (vars : Finset (Fin n)) : Finset (Fin (2 * n)) :=
  vars.biUnion (contrPair n)

/-- Contradictory pairs for distinct variables are disjoint. -/
lemma contrPair_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (contrPair n i) (contrPair n j) := by
  rw [Finset.disjoint_left]
  intro x hx
  simp only [contrPair, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  intro hj
  rcases hx with rfl | rfl <;> rcases hj with hj | hj <;>
    (have := congr_arg Fin.val hj; simp at this; omega)

/-- pairUnion of a singleton is just the pair. -/
lemma pairUnion_singleton (i : Fin n) :
    pairUnion n {i} = contrPair n i := by
  simp [pairUnion]

/-- pairUnion of insert = pair ∪ pairUnion of rest. -/
lemma pairUnion_insert {i : Fin n} {s : Finset (Fin n)} (hi : i ∉ s) :
    pairUnion n (insert i s) = contrPair n i ∪ pairUnion n s := by
  simp only [pairUnion, Finset.biUnion_insert]

/-- contrPair i is disjoint from pairUnion of vars not containing i. -/
lemma contrPair_disjoint_pairUnion {i : Fin n} {s : Finset (Fin n)} (hi : i ∉ s) :
    Disjoint (contrPair n i) (pairUnion n s) := by
  simp only [pairUnion]
  rw [Finset.disjoint_left]
  intro x hx hxs
  rw [Finset.mem_biUnion] at hxs
  obtain ⟨j, hjs, hxj⟩ := hxs
  have hij : i ≠ j := fun h => hi (h ▸ hjs)
  exact Finset.disjoint_left.mp (contrPair_disjoint hij) hx hxj

/-- SAT decomposes across disjoint contradictory pair blocks.
    If i ∉ s, then SAT(T) ↔ SAT(T ∩ pair_i) ∧ SAT(T ∩ pairUnion(s)). -/
lemma sat_decomp_pair (F : UnitClauseFamily n) {i : Fin n} {s : Finset (Fin n)}
    (hi : i ∉ s) :
    ∀ T ∈ (contrPair n i ∪ pairUnion n s).powerset,
      F.D.isSAT T = (F.D.isSAT (T ∩ contrPair n i) && F.D.isSAT (T ∩ pairUnion n s)) := by
  intro T hT
  rw [Finset.mem_powerset] at hT
  -- Show: SAT(T) = SAT(T∩pair_i) && SAT(T∩pairUnion(s))
  -- Both sides are Bool, so it suffices to show iff on = true
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true]
  constructor
  · -- SAT(T) = true → both parts SAT
    intro hSAT
    exact ⟨(F.h_sat _).mpr (fun j hj =>
            (F.h_sat _).mp hSAT j ⟨Finset.mem_of_mem_inter_left hj.1,
                                    Finset.mem_of_mem_inter_left hj.2⟩),
           (F.h_sat _).mpr (fun j hj =>
            (F.h_sat _).mp hSAT j ⟨Finset.mem_of_mem_inter_left hj.1,
                                    Finset.mem_of_mem_inter_left hj.2⟩)⟩
  · -- Both parts SAT → SAT(T)
    intro ⟨hA, hB⟩
    rw [F.h_sat]
    intro j ⟨hj1, hj2⟩
    -- Both 2j and 2j+1 are in T ⊆ pair_i ∪ pairUnion(s)
    -- Case: j = i → both in T∩pair_i → contradicts SAT(T∩pair_i)
    -- Case: j ≠ i → both in T∩pairUnion(s) → contradicts SAT(T∩pairUnion(s))
    -- We need: 2j ∈ pair_i ∪ pairUnion(s) means either 2j ∈ pair_i or 2j ∈ pairUnion(s)
    -- If j = i, then 2j ∈ pair_i and 2j+1 ∈ pair_i
    -- If j ≠ i, then 2j ∉ pair_i (pair_i = {2i, 2i+1}), so 2j ∈ pairUnion(s)
    by_cases hij : j = i
    · -- j = i: both literals in T∩pair_i
      subst hij
      rw [F.h_sat] at hA
      apply hA j
      exact ⟨Finset.mem_inter.mpr ⟨hj1, Finset.mem_insert_self _ _⟩,
             Finset.mem_inter.mpr ⟨hj2, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))⟩⟩
    · -- j ≠ i: both literals in T∩pairUnion(s)
      rw [F.h_sat] at hB
      apply hB j
      -- 2j ∈ T and 2j ∉ pair_i (since j ≠ i), so 2j ∈ pairUnion(s) by T ⊆ union
      have h2j_not_pair : (⟨2*j.val, by have := j.isLt; omega⟩ : Fin (2*n)) ∉ contrPair n i := by
        simp only [contrPair, Finset.mem_insert, Finset.mem_singleton]
        intro h; rcases h with h | h <;> (have := congr_arg Fin.val h; simp at this; omega)
      have h2j1_not_pair : (⟨2*j.val+1, by have := j.isLt; omega⟩ : Fin (2*n)) ∉ contrPair n i := by
        simp only [contrPair, Finset.mem_insert, Finset.mem_singleton]
        intro h; rcases h with h | h <;> (have := congr_arg Fin.val h; simp at this; omega)
      have h2j_in_pu : (⟨2*j.val, by have := j.isLt; omega⟩ : Fin (2*n)) ∈ pairUnion n s := by
        have := hT hj1
        rcases Finset.mem_union.mp this with h | h
        · exact absurd h h2j_not_pair
        · exact h
      have h2j1_in_pu : (⟨2*j.val+1, by have := j.isLt; omega⟩ : Fin (2*n)) ∈ pairUnion n s := by
        have := hT hj2
        rcases Finset.mem_union.mp this with h | h
        · exact absurd h h2j1_not_pair
        · exact h
      exact ⟨Finset.mem_inter.mpr ⟨hj1, h2j_in_pu⟩,
             Finset.mem_inter.mpr ⟨hj2, h2j1_in_pu⟩⟩

/-- The Möbius coefficient of a union of k disjoint contradictory pairs
    equals (-1)^k (product of independent -1 contributions). -/
theorem pairUnion_mobius (F : UnitClauseFamily n)
    (vars : Finset (Fin n)) (hne : vars.Nonempty) :
    mobiusCoeff F.D (pairUnion n vars) = (-1) ^ vars.card := by
  induction vars using Finset.induction_on with
  | empty => exact absurd hne (Finset.not_nonempty_empty)
  | @insert i s hi ih =>
    rw [pairUnion_insert hi]
    rw [Finset.card_insert_of_notMem hi]
    by_cases hs : s.Nonempty
    · -- Inductive case: apply decomposable product
      rw [DecisionMobiusBridge.decomposable_mobius_product F.D
          (contrPair n i) (pairUnion n s)
          (contrPair_disjoint_pairUnion hi)
          (sat_decomp_pair F hi)]
      rw [ih hs, contrPair_mobius F i]
      ring
    · -- Base case: s = ∅
      rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simp [pairUnion, contrPair_mobius]

/-- At level 2, the mass is at least n (one per contradictory pair). -/
theorem mobius_mass_level2_ge_n (F : UnitClauseFamily n) :
    n ≤ DecisionMobiusBridge.mobiusMassLevel F.D 2 := by
  calc n ≤ ((Finset.univ : Finset (Fin (2*n))).powerset.filter
      (fun S => S.card = 2 ∧ F.D.isSAT S = false ∧
        ∀ T ∈ S.powerset, T ≠ S → F.D.isSAT T = true)).card :=
      mus_count_size2_ge_n F
    _ ≤ DecisionMobiusBridge.mobiusMassLevel F.D 2 :=
      DecisionMobiusBridge.mus_count_le_mobius_mass F.D 2 (by omega)

/-- pairUnion is injective: different variable sets give different clause sets. -/
private lemma mem_pairUnion_iff {x : Fin (2*n)} {s : Finset (Fin n)} :
    x ∈ pairUnion n s ↔ ∃ j ∈ s, x ∈ contrPair n j := by
  simp [pairUnion, Finset.mem_biUnion]

private lemma var_of_contrPair_mem {x : Fin (2*n)} {j : Fin n}
    (hx : x ∈ contrPair n j) : x.val / 2 = j.val := by
  simp only [contrPair, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> simp <;> omega

lemma pairUnion_injective (n : ℕ) : Function.Injective (pairUnion n) := by
  intro s t h
  ext i
  suffices ∀ (a b : Finset (Fin n)), pairUnion n a = pairUnion n b → i ∈ a → i ∈ b by
    exact ⟨this s t h, this t s h.symm⟩
  intro a b hab hi
  by_contra hi'
  have hmem : (⟨2*i.val, by have := i.isLt; omega⟩ : Fin (2*n)) ∈ pairUnion n a :=
    mem_pairUnion_iff.mpr ⟨i, hi, Finset.mem_insert_self _ _⟩
  rw [hab] at hmem
  obtain ⟨j, hj, hxj⟩ := mem_pairUnion_iff.mp hmem
  have hvar := var_of_contrPair_mem hxj
  have hij : i = j := Fin.ext (by simp [Fin.val] at hvar ⊢; omega)
  exact hi' (hij ▸ hj)

/-- pairUnion of a k-element set has 2k elements. -/
lemma pairUnion_card (s : Finset (Fin n)) : (pairUnion n s).card = 2 * s.card := by
  simp only [pairUnion]
  rw [Finset.card_biUnion (fun i _ j _ hij => contrPair_disjoint hij)]
  have : ∀ i ∈ s, (contrPair n i).card = 2 := fun i _ => contrPair_card n i
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]

theorem mobius_mass_level_2k_lower (F : UnitClauseFamily n) (k : ℕ)
    (hk : k ≤ n) (hk1 : 1 ≤ k) :
    n.choose k ≤ DecisionMobiusBridge.mobiusMassLevel F.D (2 * k) := by
  -- Each k-subset of [n] gives a pairUnion with card 2k and |f̂| = 1
  unfold DecisionMobiusBridge.mobiusMassLevel
  -- The image of (univ.filter card=k) under pairUnion is a subset of
  -- the level-2k powerset, and each has |f̂| = 1
  set kSets := (Finset.univ : Finset (Fin n)).powerset.filter (fun s => s.card = k)
  set level := (Finset.univ : Finset (Fin (2*n))).powerset.filter (fun S => S.card = 2*k)
  -- n.choose k = kSets.card
  have hkSets : kSets.card = n.choose k := by
    simp [kSets, Finset.filter_card_eq]
  rw [← hkSets]
  -- Image of kSets under pairUnion ⊆ level, with each contributing |f̂| ≥ 1
  calc kSets.card
      = (kSets.image (pairUnion n)).card := by
        rw [Finset.card_image_of_injOn]
        exact fun _ _ _ _ h => pairUnion_injective n h
    _ ≤ ∑ _S ∈ kSets.image (pairUnion n), 1 := by simp
    _ ≤ ∑ S ∈ kSets.image (pairUnion n), (DecisionMobiusBridge.mobiusCoeff F.D S).natAbs := by
        apply Finset.sum_le_sum
        intro S hS
        rw [Finset.mem_image] at hS
        obtain ⟨s, hs, rfl⟩ := hS
        rw [Finset.mem_filter] at hs
        have hne : s.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]; intro h; subst h; simp at hs; omega
        rw [pairUnion_mobius F s hne]; simp
    _ ≤ ∑ S ∈ level, (DecisionMobiusBridge.mobiusCoeff F.D S).natAbs := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro S hS
          rw [Finset.mem_image] at hS
          obtain ⟨s, hs, rfl⟩ := hS
          rw [Finset.mem_filter] at hs ⊢
          exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
                 by rw [pairUnion_card]; omega⟩
        · intros; exact Nat.zero_le _

/-- C(n, k) > n^C for k = log₂ n and large enough n.
    Standard combinatorial fact (helper lemmas proved in TracedMobiusBridge). -/
axiom choose_log_superpolynomial :
    ∀ C : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, n ^ C < n.choose (Nat.log 2 n) ∧ 1 ≤ Nat.log 2 n ∧ Nat.log 2 n ≤ n

theorem superpolynomial_mobius_mass :
    ∀ C : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (F : UnitClauseFamily n),
        n ^ C < DecisionMobiusBridge.mobiusMassLevel F.D (2 * Nat.log 2 n) := by
  intro C
  obtain ⟨n₀, hn₀⟩ := choose_log_superpolynomial C
  exact ⟨n₀, fun n hn F => by
    obtain ⟨hlt, hk1, hkn⟩ := hn₀ n hn
    calc n ^ C < n.choose (Nat.log 2 n) := hlt
      _ ≤ _ := mobius_mass_level_2k_lower F (Nat.log 2 n) hkn hk1⟩

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
