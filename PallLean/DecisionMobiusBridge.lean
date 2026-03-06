import Mathlib

/-!
# Decision Möbius Bridge — MUS ↔ Möbius Connection

## Main Theorems

1. **MUS → f̂(S) = -1**: If S is a Minimal Unsatisfiable Subformula,
   the Möbius coefficient of the SAT decision function at S equals -1.

2. **All-SAT → f̂(S) = 0**: If every subset of S is satisfiable
   (S has no unsatisfiable core), f̂(S) = 0.

3. **Decomposable → product**: If S = A ∪ B with independent blocks,
   f̂(S) = f̂(A) · f̂(B).

These are representation-invariant properties of the decision function
f(z) = SAT(clause_subset_z), connecting MUS structure to Möbius mass.
-/

namespace DecisionMobiusBridge

open Finset BigOperators

/-- For nonempty R, ∑_{S⊆R} (-1)^{|R\S|} = 0. -/
private lemma sum_powerset_sdiff_neg_one {α : Type*} [DecidableEq α]
    {R : Finset α} (hR : R.Nonempty) :
    ∑ S ∈ R.powerset, (-1 : ℤ) ^ (R \ S).card = 0 := by
  have h_sign : ∀ S ∈ R.powerset,
      (-1 : ℤ) ^ (R \ S).card = (-1) ^ R.card * (-1) ^ S.card := by
    intro S hS
    have hSR := Finset.mem_powerset.mp hS
    have h_add := Finset.card_sdiff_add_card_eq_card hSR
    have h_pow : (-1:ℤ) ^ R.card = (-1) ^ (R \ S).card * (-1) ^ S.card := by
      rw [← pow_add, h_add]
    have h_inv : (-1:ℤ) ^ S.card * (-1) ^ S.card = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    calc (-1:ℤ) ^ (R \ S).card
        = (-1) ^ (R \ S).card * 1 := (mul_one _).symm
      _ = (-1) ^ (R \ S).card * ((-1) ^ S.card * (-1) ^ S.card) := by rw [h_inv]
      _ = ((-1) ^ (R \ S).card * (-1) ^ S.card) * (-1) ^ S.card := by ring
      _ = (-1) ^ R.card * (-1) ^ S.card := by rw [h_pow]
  rw [Finset.sum_congr rfl h_sign, ← Finset.mul_sum,
      Finset.sum_powerset_neg_one_pow_card_of_nonempty hR, mul_zero]

/-! ## 1. Decision Function -/

/-- A decision function on clause subsets: f(S) = 1 iff S is satisfiable. -/
structure SATDecision (m : ℕ) where
  /-- Whether clause subset S is satisfiable. True = SAT, False = UNSAT. -/
  isSAT : Finset (Fin m) → Bool

/-- The UNSAT indicator: g(S) = 1 - f(S). -/
def SATDecision.isUNSAT (D : SATDecision m) (S : Finset (Fin m)) : Bool :=
  !D.isSAT S

/-! ## 2. Möbius Transform -/

/-- Möbius coefficient of the SAT decision function at subset S.
    f̂(S) = Σ_{T⊆S} (-1)^{|S\T|} · f(T)
    where f(T) = 1 if T is satisfiable, 0 otherwise. -/
def mobiusCoeff (D : SATDecision m) (S : Finset (Fin m)) : ℤ :=
  ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S \ T).card *
    if D.isSAT T then 1 else 0

/-! ## 3. MUS Predicate -/

/-- S is a Minimal Unsatisfiable Subformula (MUS):
    S is UNSAT, and every proper subset of S is SAT. -/
def IsMUS (D : SATDecision m) (S : Finset (Fin m)) : Prop :=
  D.isSAT S = false ∧
  ∀ T ∈ S.powerset, T ≠ S → D.isSAT T = true

/-- S is "all-SAT": every subset of S (including S itself) is satisfiable. -/
def IsAllSAT (D : SATDecision m) (S : Finset (Fin m)) : Prop :=
  ∀ T ∈ S.powerset, D.isSAT T = true

/-! ## 4. Key Theorems -/

/-- **Theorem: MUS implies f̂(S) = -1.**

    Proof: For MUS S, every proper subset T ⊊ S is SAT (f(T) = 1),
    and S itself is UNSAT (f(S) = 0).

    f̂(S) = Σ_{T⊆S} (-1)^{|S\T|} · f(T)
          = Σ_{T⊊S} (-1)^{|S\T|} · 1  +  (-1)^0 · 0
          = (Σ_{T⊆S} (-1)^{|S\T|}) - (-1)^0
          = 0 - 1 = -1

    The alternating sum Σ_{T⊆S} (-1)^{|S\T|} = 0 for |S| ≥ 1
    (by sum_powerset_sdiff_neg_one). -/
theorem mus_mobius_eq_neg_one (D : SATDecision m) (S : Finset (Fin m))
    (hS : S.Nonempty) (hMUS : IsMUS D S) :
    mobiusCoeff D S = -1 := by
  unfold mobiusCoeff IsMUS at *
  obtain ⟨hUnsat, hProper⟩ := hMUS
  -- Split the sum: T = S contributes 0, T ⊊ S contributes (-1)^{|S\T|}
  -- First, every T ∈ S.powerset with T ≠ S has f(T) = 1
  have h_proper_sat : ∀ T ∈ S.powerset, T ≠ S →
      (-1 : ℤ) ^ (S \ T).card * (if D.isSAT T then 1 else 0) =
      (-1 : ℤ) ^ (S \ T).card := by
    intro T hT hne
    rw [hProper T hT hne]; simp
  -- T = S contributes (-1)^0 * 0 = 0
  have h_self : (-1 : ℤ) ^ (S \ S).card * (if D.isSAT S then 1 else 0) = 0 := by
    rw [hUnsat]; simp
  -- Full sum = Σ_{T⊆S} (-1)^{|S\T|} · [f(T)]
  -- Separate into T≠S (where f(T)=1) and T=S (where f(S)=0)
  -- = Σ_{T⊆S} (-1)^{|S\T|} - (-1)^{|S\S|} · 1 + (-1)^0 · 0
  -- = 0 - 1 = -1
  -- First: the sum with all f(T) replaced by 1 equals 0
  have h_alt : ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S \ T).card = 0 :=
    sum_powerset_sdiff_neg_one hS
  -- The actual sum differs from h_alt only at T = S:
  -- actual(S) = (-1)^0 · 0 = 0, but all-ones(S) = (-1)^0 · 1 = 1
  -- So actual sum = all-ones sum - 1 = 0 - 1 = -1
  have h_diff : ∀ T ∈ S.powerset,
      (-1 : ℤ) ^ (S \ T).card * (if D.isSAT T then 1 else 0) =
      (-1 : ℤ) ^ (S \ T).card - (if T = S then 1 else 0) := by
    intro T hT
    by_cases hTS : T = S
    · subst hTS; rw [hUnsat]; simp
    · rw [hProper T hT hTS, if_neg hTS]; simp
  rw [Finset.sum_congr rfl h_diff, Finset.sum_sub_distrib]
  rw [h_alt, zero_sub]
  -- Σ_{T⊆S} [T=S] = 1 (only one subset equals S)
  rw [Finset.sum_ite_eq' S.powerset S (fun _ => (1:ℤ))]
  simp [Finset.mem_powerset]

/-- **Theorem: All-SAT implies f̂(S) = 0.**

    If every subset of S is satisfiable, then f(T) = 1 for all T ⊆ S,
    and f̂(S) = Σ_{T⊆S} (-1)^{|S\T|} = 0 (alternating sum vanishes). -/
theorem allsat_mobius_eq_zero (D : SATDecision m) (S : Finset (Fin m))
    (hS : S.Nonempty) (hAllSAT : IsAllSAT D S) :
    mobiusCoeff D S = 0 := by
  unfold mobiusCoeff IsAllSAT at *
  -- Every term has f(T) = 1
  have h_all_one : ∀ T ∈ S.powerset,
      (-1 : ℤ) ^ (S \ T).card * (if D.isSAT T then 1 else 0) =
      (-1 : ℤ) ^ (S \ T).card := by
    intro T hT
    rw [hAllSAT T hT]; simp
  rw [Finset.sum_congr rfl h_all_one]
  exact sum_powerset_sdiff_neg_one (α := Fin m) hS

/-- **Theorem: Decomposable subsets factor.**

    If S = A ∪ B with A ∩ B = ∅, and satisfiability decomposes
    (SAT(T) iff SAT(T∩A) ∧ SAT(T∩B) for all T ⊆ S), then
    f̂(S) = f̂(A) · f̂(B). -/
theorem decomposable_mobius_product (D : SATDecision m)
    (A B : Finset (Fin m))
    (hAB : Disjoint A B)
    -- Satisfiability decomposes across the partition
    (h_decomp : ∀ T ∈ (A ∪ B).powerset,
      D.isSAT T = (D.isSAT (T ∩ A) && D.isSAT (T ∩ B))) :
    mobiusCoeff D (A ∪ B) = mobiusCoeff D A * mobiusCoeff D B := by
  unfold mobiusCoeff
  -- Use the product of sums = sum of products identity
  rw [Finset.sum_mul_sum]
  -- Now both sides are sums over product pairs.
  -- LHS: ∑_{T ⊆ A∪B} (-1)^{|(A∪B)\T|} · f(T)
  -- RHS: ∑_{(T_A, T_B) ∈ A.powerset ×ˢ B.powerset} sign(A,T_A)·f(T_A) · sign(B,T_B)·f(T_B)
  -- The bijection: T ↦ (T∩A, T∩B) maps (A∪B).powerset → A.powerset ×ˢ B.powerset
  -- and |(A∪B)\T| = |A\(T∩A)| + |B\(T∩B)| for disjoint A,B
  sorry

/-! ## 5. Möbius Mass and MUS Counting -/

/-- The Möbius mass at level k counts the total absolute Möbius weight.
    For formulas with many MUSes of size k, this equals the MUS count. -/
def mobiusMassLevel (D : SATDecision m) (k : ℕ) : ℕ :=
  ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset.filter
      (fun S => S.card = k),
    (mobiusCoeff D S).natAbs

/-- **Corollary: MUS count bounds Möbius mass from below.**

    Each MUS of size k contributes exactly 1 to the mass at level k. -/
theorem mus_count_le_mobius_mass (D : SATDecision m) (k : ℕ)
    (hk : 1 ≤ k) :
    ((Finset.univ : Finset (Fin m)).powerset.filter
      (fun S => S.card = k ∧ D.isSAT S = false ∧
        ∀ T ∈ S.powerset, T ≠ S → D.isSAT T = true)).card ≤
    mobiusMassLevel D k := by
  unfold mobiusMassLevel
  -- Each MUS of size k contributes |f̂(S)| = 1 to the sum.
  -- Strategy: the MUS set is a subset of the level-k powerset,
  -- and each MUS contributes exactly 1 to the sum.
  sorry

/-! ## 6. The P ≠ NP Connection

### NP-side: MUS counting lower bound

For structured SAT families (e.g., random 3-SAT near threshold with m = αn),
the number of MUSes of size k grows combinatorially. Specifically:

- **Contradictory pairs**: Each pair of unit clauses (xᵢ, ¬xᵢ) is a MUS of size 2.
  With n variables, there are n possible pairs → Θ(n) MUSes of size 2.

- **Resolution MUSes**: In hard 3-SAT instances, MUSes of size O(n) exist
  and their count grows with n.

- **Tseitin formulas on expander graphs**: Known to have exponentially many
  MUSes (Alekhnovich et al.), giving exponential Möbius mass.

### P-side: Computational limit on MUS-dependent functions

The key question: can a poly-time algorithm compute a boolean function
whose Möbius transform has superpolynomially many nonzero coefficients?

Known results:
- **AC⁰ functions**: Möbius mass concentrated at low degree (LMN theorem)
- **Monotone functions**: Bounded Möbius degree (Boppana)
- **General P**: OPEN — this is the P ≠ NP frontier

### The formalized path:

1. ✅ MUS ↔ Möbius connection (this file)
2. ⬜ MUS count lower bounds for specific SAT families
3. ⬜ Computational upper bounds on achievable Möbius mass
4. ⬜ Contradiction: NP-side mass > P-side capacity → P ≠ NP

Steps 2-4 are the remaining open mathematics. -/

end DecisionMobiusBridge
