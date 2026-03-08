import Mathlib
import PallLean.DecisionMobiusBridge

/-!
# MUS/Möbius Structure → OBDD Width Lower Bound

## Goal

Turn search-side Möbius/MUS structure into a resource lower bound:
κ independent MUSes force OBDD width ≥ 2^κ for the clause-subset-SAT function.

## Key insight

The interesting function is NOT the assignment-SAT function (Fin n → Bool) → Bool,
which is constant false when any MUS exists. The interesting function is the
**clause-subset-SAT** decision function:

  f : {0,1}^m → {0,1}, f(z) = 1 iff the clause subset {c : z_c = 1} is satisfiable.

This is exactly the function studied in DecisionMobiusBridge.

## Architecture

1. **Residual functions** and **OBDD model** (generic, over any Boolean function)
2. **Distinct residuals → width** (standard counting argument)
3. **Unit clause family**: concrete instance with n pairwise disjoint MUSes
4. **Main theorem**: with interleaving ordering, OBDD width ≥ 2^n

## Variable ordering matters

The bound 2^κ holds when the ordering INTERLEAVES the MUSes (splits each one).
With worst-case ordering (all of M₁ before all of M₂), width can be much smaller.
We prove the bound for a specific (interleaving) ordering.
-/

namespace MUSWidthLowerBound

open Finset BigOperators

/-! ## Layer 1: Boolean Functions and Residuals -/

/-- A Boolean function on m variables. -/
def BoolFun (m : ℕ) := (Fin m → Bool) → Bool

/-- A partial assignment: fixes the first k variables. -/
def PartialAssignment (m : ℕ) (k : ℕ) := Fin k → Bool

noncomputable instance : Fintype (PartialAssignment m k) :=
  inferInstanceAs (Fintype (Fin k → Bool))

noncomputable instance : DecidableEq (PartialAssignment m k) :=
  inferInstanceAs (DecidableEq (Fin k → Bool))

/-- The residual function after fixing the first k variables. -/
def residual {m : ℕ} (f : BoolFun m) (k : ℕ) (hk : k ≤ m)
    (α : PartialAssignment m k) : BoolFun (m - k) :=
  fun β => f (fun i =>
    if h : i.val < k then α ⟨i.val, h⟩
    else β ⟨i.val - k, by omega⟩)

/-! ## Layer 2: OBDD Model -/

/-- An OBDD for a function on m variables with a specific variable ordering. -/
structure OBDD (m : ℕ) where
  width : Fin (m + 1) → ℕ
  width_pos : ∀ i, 0 < width i
  computes : BoolFun m
  route : (k : Fin (m + 1)) → PartialAssignment m k.val → Fin (width k)
  route_residual : ∀ (k : Fin (m + 1)) (hk : k.val ≤ m)
    (α₁ α₂ : PartialAssignment m k.val),
    route k α₁ = route k α₂ →
    residual computes k.val hk α₁ = residual computes k.val hk α₂

/-! ## Layer 3: Width Lower Bounds -/

/-- If g factors through f, then card(image g) ≤ card(image f). -/
private lemma card_image_le_of_factors_through {α β γ : Type*}
    [DecidableEq β] [DecidableEq γ] [Fintype α]
    (f : α → β) (g : α → γ)
    (h : ∀ a₁ a₂ : α, g a₁ = g a₂ → f a₁ = f a₂) :
    (Finset.univ.image f).card ≤ (Finset.univ.image g).card := by
  classical
  have h_rep : ∀ b ∈ Finset.univ.image f, ∃ a : α, f a = b := by
    intro b hb; exact (Finset.mem_image.mp hb).imp fun a ha => ha.2
  choose rep h_rep using h_rep
  let inj : ↥(Finset.univ.image f) → ↥(Finset.univ.image g) :=
    fun ⟨b, hb⟩ => ⟨g (rep b hb), Finset.mem_image.mpr ⟨rep b hb, Finset.mem_univ _, rfl⟩⟩
  have h_inj : Function.Injective inj := by
    intro ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ heq
    simp only [inj, Subtype.mk.injEq] at heq
    have hf := h _ _ heq
    rw [h_rep b₁ hb₁, h_rep b₂ hb₂] at hf
    exact Subtype.ext hf
  have := Fintype.card_le_of_injective inj h_inj
  simp only [Fintype.card_coe] at this
  exact this

/-- Number of distinct residuals (via truth table encoding). -/
noncomputable def numDistinctResiduals {m : ℕ} (f : BoolFun m) (k : ℕ) (hk : k ≤ m) : ℕ :=
  (Finset.univ (α := PartialAssignment m k)).image
    (fun α => (Finset.univ (α := Fin (m - k) → Bool)).image (residual f k hk α))
  |>.card

/-- OBDD width ≥ number of distinct residuals. -/
theorem width_ge_distinct_residuals {m : ℕ} (B : OBDD m) (k : Fin (m + 1))
    (hk : k.val ≤ m) :
    numDistinctResiduals B.computes k.val hk ≤ B.width k := by
  unfold numDistinctResiduals
  let ttMap := fun (α : PartialAssignment m k.val) =>
    (Finset.univ (α := Fin (m - ↑k) → Bool)).image (residual B.computes k.val hk α)
  calc (Finset.univ.image ttMap).card
      ≤ (Finset.univ.image (B.route k)).card := by
        apply card_image_le_of_factors_through
        intro α₁ α₂ hr
        simp only [ttMap]
        congr 1
        exact funext fun β => congrFun (B.route_residual k hk α₁ α₂ hr) β
    _ ≤ B.width k := by
        have : (Finset.univ.image (B.route k)).card ≤ (Finset.univ : Finset (Fin (B.width k))).card :=
          Finset.card_le_card (Finset.subset_univ _)
        simp [Finset.card_univ, Fintype.card_fin] at this
        exact this

/-- Direct width bound via injection through routing. -/
theorem width_ge_of_injective_residuals {m : ℕ} (B : OBDD m) (k : Fin (m + 1))
    (hk : k.val ≤ m)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (assign : ι → PartialAssignment m k.val)
    (h_inj : ∀ i j : ι, i ≠ j →
      residual B.computes k.val hk (assign i) ≠ residual B.computes k.val hk (assign j)) :
    Fintype.card ι ≤ B.width k := by
  have h_route_inj : Function.Injective (fun i => B.route k (assign i)) := by
    intro i j hr
    by_contra h_ne
    exact h_inj i j h_ne (B.route_residual k hk (assign i) (assign j) hr)
  calc Fintype.card ι
      ≤ Fintype.card (Fin (B.width k)) := Fintype.card_le_of_injective _ h_route_inj
    _ = B.width k := Fintype.card_fin _

/-! ## Layer 4: Unit Clause Family — Concrete Lower Bound -/

/-- The interleaved unit clause SAT function on 2n variables.
    The first n positions are "positive literal included?" and the last n are
    "negative literal included?". Variable i is contradicted iff both
    position i (positive) and position n+i (negative) are true.

    f(z) = 1 iff ∀i ∈ Fin n, ¬(z(i) ∧ z(n+i)).

    This is the clause-subset-SAT function under the interleaving ordering
    that puts one clause from each MUS in the first half. -/
def interleavedSAT (n : ℕ) : BoolFun (2 * n) :=
  fun z => (Finset.univ.filter (fun i : Fin n =>
    z ⟨i.val, by omega⟩ = true ∧ z ⟨n + i.val, by omega⟩ = true)).card == 0

/-- Evaluation lemma: residual of interleavedSAT at depth n evaluates to
    checking that no variable has both its positive and negative literal included. -/
theorem interleavedSAT_residual_eval (n : ℕ) (hn : n ≤ 2 * n)
    (α : PartialAssignment (2 * n) n) (β : Fin (2 * n - n) → Bool) :
    residual (interleavedSAT n) n hn α β =
    ((Finset.univ.filter (fun i : Fin n =>
      α ⟨i.val, i.isLt⟩ = true ∧ β ⟨i.val, by omega⟩ = true)).card == 0) := by
  -- Unfold definitions
  simp only [residual, interleavedSAT]
  -- Goal should be: filter on {i : α(pos_i) ∧ β(neg_i)} has same card
  -- where pos_i = ⟨i.val, _⟩ and neg_i = ⟨n + i.val, _⟩
  -- The residual concat maps position p to α(p) if p < n, else β(p - n).
  -- interleavedSAT checks: for each i, ¬(z(i) ∧ z(n+i)).
  -- After concat: z(i) = α(i) (since i < n), z(n+i) = β(i) (since n+i ≥ n, (n+i)-n = i).
  -- So the check is: for each i, ¬(α(i) ∧ β(i)). ✓
  congr 1
  congr 1
  ext ⟨i, hi⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- LHS: (if ⟨i,_⟩.val < n then α ... else β ...)(⟨i,_⟩) = true ∧
  --       (if ⟨n+i,_⟩.val < n then α ... else β ...)(⟨n+i,_⟩) = true
  -- i < n (since i : Fin n), so first dite selects α
  -- n + i ≥ n, so second dite selects β with index (n+i) - n = i
  -- After ext, the goal involves dite on Fin.val comparisons.
  -- Use split/if to resolve the dite's.
  have pos_lt : (⟨i, by omega⟩ : Fin (2 * n)).val < n := hi
  simp only [Fin.val_mk, dif_pos pos_lt]
  -- After resolving the first dite, need to handle the second
  -- ⟨n + i, _⟩.val = n + i ≥ n, so dif_neg
  have neg_nlt : ¬ (n + i < n) := by omega
  simp only [dif_neg neg_nlt, Nat.add_sub_cancel_left]

/-- Different subsets give different residual functions.
    If α₁ ≠ α₂, there exists j where α₁(j) ≠ α₂(j). WLOG α₁(j) = true, α₂(j) = false.
    Take β with β(j) = true, β(i) = false for i ≠ j.
    Then residual(α₁)(β) checks j and finds α₁(j) ∧ β(j) = true → returns false.
    But residual(α₂)(β): α₂(j) = false → j doesn't contribute → returns true. -/
theorem interleavedSAT_residuals_injective (n : ℕ) (hn : n ≤ 2 * n)
    (α₁ α₂ : PartialAssignment (2 * n) n)
    (hne : α₁ ≠ α₂) :
    residual (interleavedSAT n) n hn α₁ ≠ residual (interleavedSAT n) n hn α₂ := by
  -- α₁ ≠ α₂ → ∃ j, α₁(j) ≠ α₂(j)
  have ⟨j, hj⟩ : ∃ j, α₁ j ≠ α₂ j := by
    by_contra h; push_neg at h; exact hne (funext h)

  -- WLOG α₁(j) = true, α₂(j) = false (or vice versa; by symmetry)
  -- Construct β that is the indicator of {j}: β(j) = true, β(i) = false for i ≠ j
  intro h_eq
  -- h_eq says the two residual functions are equal
  -- Evaluate both at the indicator of {j}
  let β : Fin (2 * n - n) → Bool := fun k =>
    if k.val = j.val then true else false
  have h1 := congr_fun h_eq β
  rw [interleavedSAT_residual_eval, interleavedSAT_residual_eval] at h1
  -- h1 compares two filter-card-beq-0 expressions at the indicator β of {j}
  -- β ⟨i.val, _⟩ = true iff i.val = j.val
  -- For αₖ: the filter contains i iff αₖ(i) = true ∧ i = j, i.e., just {j} if αₖ(j)=true
  -- Compute each filter's card:
  -- Compute card of filter for each α: card = if α(j) then 1 else 0
  have h_card : ∀ (α : PartialAssignment (2 * n) n),
      (Finset.univ.filter (fun i : Fin n =>
        α ⟨i.val, i.isLt⟩ = true ∧ β ⟨i.val, by omega⟩ = true)).card =
      if α j = true then 1 else 0 := by
    intro α
    by_cases hα : α j = true
    · -- Filter = {j}
      rw [if_pos hα]
      have : Finset.univ.filter (fun i : Fin n =>
          α ⟨i.val, i.isLt⟩ = true ∧ β ⟨i.val, by omega⟩ = true) = {j} := by
        ext ⟨k, hk⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, β, Fin.val_mk]
        constructor
        · intro ⟨_, h2⟩
          by_cases heq : k = j.val
          · exact Fin.ext heq
          · simp [heq] at h2
        · intro h; subst h; exact ⟨hα, by simp⟩
      rw [this, Finset.card_singleton]
    · -- Filter = ∅: no i has both α(i)=true and i=j (since α(j)=false)
      rw [if_neg hα]
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_false_of_mem
      intro ⟨k, hk⟩ _
      simp only [β, Fin.val_mk, not_and]
      intro h1
      by_cases heq : k = j.val
      · simp only [heq, ↓reduceIte]
        intro
        have hkj : (⟨k, hk⟩ : Fin n) = j := Fin.ext heq
        exact absurd (hkj ▸ h1) hα
      · simp [heq]
  rw [h_card α₁, h_card α₂] at h1
  cases h1a : α₁ j <;> cases h2a : α₂ j <;> simp_all

/-- **The concrete width lower bound:**
    Any OBDD computing interleavedSAT n has width ≥ 2^n at level n.

    Proof: 2^n distinct prefixes give 2^n distinct residual functions
    (by interleavedSAT_residuals_injective), so width ≥ 2^n
    (by width_ge_of_injective_residuals). -/
theorem unit_clause_obdd_width (n : ℕ) (B : OBDD (2 * n))
    (h_comp : B.computes = interleavedSAT n) :
    B.width ⟨n, by omega⟩ ≥ 2 ^ n := by
  have hn : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by omega)
  rw [ge_iff_le, ← Fintype.card_fin (2 ^ n)]
  apply width_ge_of_injective_residuals B ⟨n, by omega⟩ hn
    (fun (b : Fin (2^n)) =>
      fun (i : Fin n) => b.val.testBit i.val)
  intro i j hij
  rw [h_comp]
  apply interleavedSAT_residuals_injective
  -- Need: different Fin(2^n) values give different testBit assignments
  intro h_eq
  apply hij
  apply Fin.ext
  -- h_eq : (fun k => i.val.testBit k.val) = (fun k => j.val.testBit k.val)
  -- Need: i.val = j.val
  -- Two naturals < 2^n with the same testBit on all positions < n are equal
  have h_bits : ∀ k : Fin n, i.val.testBit k.val = j.val.testBit k.val := by
    intro k; exact congr_fun h_eq k
  -- i.val < 2^n and j.val < 2^n, and they agree on bits 0..n-1
  -- For bits ≥ n: both are 0 since i.val, j.val < 2^n
  have h_all_bits : ∀ k : ℕ, i.val.testBit k = j.val.testBit k := by
    intro k
    by_cases hk : k < n
    · exact h_bits ⟨k, hk⟩
    · -- bit k ≥ n: both are 0 since values < 2^n
      have hi := i.isLt  -- i.val < 2^n
      have hj := j.isLt  -- j.val < 2^n
      have h2n : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_eq_false_of_lt (by linarith), Nat.testBit_eq_false_of_lt (by linarith)]
  exact Nat.eq_of_testBit_eq h_all_bits

end MUSWidthLowerBound
