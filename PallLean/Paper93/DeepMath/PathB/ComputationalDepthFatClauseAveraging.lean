import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionWidthSize

/-!
# The popular-literal averaging lemma (toward general DAG size–width)

The Ben-Sasson–Wigderson *general* (DAG) size–width bound runs through the
**fat-clause method**: in a refutation, look at the clauses of width `> d` ("fat"),
find a literal appearing in many of them, restrict it (killing a fraction of the
fat clauses), and recurse.  The combinatorial heart is the averaging step proved
here: among any family `F` of fat clauses over `n` literals, *some* literal lies in
`≥ d·|F| / n` of them.

By double counting, the total literal–clause incidence is `∑_{C∈F} |C| > d·|F|`, and
there are `n = |Lit|` literals, so the most popular literal meets the average:
`n · (incidence ℓ) ≥ d·|F|`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open scoped BigOperators

variable {Lit : Type*} [Fintype Lit] [DecidableEq Lit]

/-- **Double counting.**  Summing, over literals, the number of clauses containing
each literal equals the total width of the family. -/
theorem sum_incidence_eq (F : Finset (ResolutionClause Lit)) :
    ∑ ℓ : Lit, (F.filter (fun C => ℓ ∈ C)).card = ∑ C ∈ F, C.card := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **Popular-literal averaging.**  In a family `F` of fat clauses (each of width
`> d`) over the literal type `Lit`, some literal `ℓ` lies in enough clauses that
`d·|F| ≤ |Lit| · (number of clauses of F containing ℓ)`. -/
theorem exists_popular_literal [Nonempty Lit]
    (F : Finset (ResolutionClause Lit)) {d : ℕ} (hfat : ∀ C ∈ F, d < C.card) :
    ∃ ℓ : Lit, d * F.card ≤ Fintype.card Lit * (F.filter (fun C => ℓ ∈ C)).card := by
  by_contra h
  push_neg at h
  have hlt : ∑ ℓ : Lit, Fintype.card Lit * (F.filter (fun C => ℓ ∈ C)).card
      < ∑ _ℓ : Lit, d * F.card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun ℓ _ => h ℓ)
  rw [Finset.sum_const, ← Finset.mul_sum, sum_incidence_eq, Finset.card_univ,
    smul_eq_mul] at hlt
  -- hlt : |Lit| * (∑ C ∈ F, C.card) < |Lit| * (d * F.card)
  have hsum : ∑ C ∈ F, C.card < d * F.card := Nat.lt_of_mul_lt_mul_left hlt
  have hge : d * F.card + F.card ≤ ∑ C ∈ F, C.card := by
    rw [← Nat.succ_mul]
    calc (d + 1) * F.card = ∑ _C ∈ F, (d + 1) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ C ∈ F, C.card := Finset.sum_le_sum (fun C hC => hfat C hC)
  omega

/-- **Multiplicative-decay step.**  Restricting the popular literal `ℓ` (setting it
true) removes every clause of `F` containing `ℓ`; by the averaging bound the
surviving fat clauses `F'` (those *not* containing `ℓ`) satisfy
`n · |F'| ≤ (n - d) · |F|`.  This is the per-round reduction the fat-clause
recursion iterates: a `(1 - d/n)`-factor drop in the fat-clause count. -/
theorem fat_count_decreases [Nonempty Lit]
    (F : Finset (ResolutionClause Lit)) {d : ℕ} (hfat : ∀ C ∈ F, d < C.card) :
    ∃ ℓ : Lit, Fintype.card Lit * (F.filter (fun C => ℓ ∉ C)).card
      ≤ (Fintype.card Lit - d) * F.card := by
  obtain ⟨ℓ, hℓ⟩ := exists_popular_literal F hfat
  refine ⟨ℓ, ?_⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) (p := fun C => ℓ ∈ C)
  have hdist : Fintype.card Lit * (F.filter (fun C => ℓ ∈ C)).card
      + Fintype.card Lit * (F.filter (fun C => ℓ ∉ C)).card
      = Fintype.card Lit * F.card := by
    rw [← Nat.mul_add, hsplit]
  have hnd : (Fintype.card Lit - d) * F.card = Fintype.card Lit * F.card - d * F.card :=
    Nat.sub_mul _ _ _
  omega

/-! ## The multiplicative-decay recursion (quantitative core, integer form) -/

/-- **Decay recursion.**  If a fat-count sequence drops by the per-round factor
(`n·a_{i+1} ≤ (n-d)·a_i`), then after `k` rounds `n^k · a_k ≤ (n-d)^k · a_0`. -/
theorem decay_pow {n d : ℕ} (a : ℕ → ℕ) (hstep : ∀ i, n * a (i + 1) ≤ (n - d) * a i) :
    ∀ k, n ^ k * a k ≤ (n - d) ^ k * a 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc n ^ (k + 1) * a (k + 1)
        = n ^ k * (n * a (k + 1)) := by rw [pow_succ, mul_assoc]
      _ ≤ n ^ k * ((n - d) * a k) := Nat.mul_le_mul (le_refl _) (hstep k)
      _ = (n - d) * (n ^ k * a k) := by rw [mul_left_comm]
      _ ≤ (n - d) * ((n - d) ^ k * a 0) := Nat.mul_le_mul (le_refl _) ih
      _ = (n - d) ^ (k + 1) * a 0 := by rw [← mul_assoc, ← pow_succ']

/-- **The fat clauses are exhausted.**  Once the decayed bound drops below `n^k`
(which happens after `≈ (n/d)·ln a₀` rounds, with `d` chosen `≈ √(n log S)`), the
fat-count is forced to `0` — no fat clauses survive, so the residual refutation has
width `≤ d`.  This is the integer core; the round-count / `√`-optimisation of `d` is
the only remaining (real-valued) accounting. -/
theorem decay_zero {n d : ℕ} (a : ℕ → ℕ) (hstep : ∀ i, n * a (i + 1) ≤ (n - d) * a i)
    (k : ℕ) (hk : (n - d) ^ k * a 0 < n ^ k) : a k = 0 := by
  by_contra h
  have h1 : 0 < a k := Nat.pos_of_ne_zero h
  have hle : n ^ k ≤ n ^ k * a k := Nat.le_mul_of_pos_right _ h1
  have := decay_pow a hstep k
  omega

/-- Binomial lower bound `m^{k+1} + (k+1)·d·m^k ≤ (m+d)^{k+1}` (two leading terms). -/
theorem bernoulli_pow (m d : ℕ) : ∀ k, m ^ (k + 1) + (k + 1) * d * m ^ k ≤ (m + d) ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp [pow_succ, Nat.mul_comm]
  | succ k ih =>
    have hexp : (m + d) ^ (k + 2) = (m + d) ^ (k + 1) * m + (m + d) ^ (k + 1) * d := by
      rw [pow_succ]; ring
    have hstep : ((m ^ (k + 1) + (k + 1) * d * m ^ k)) * m
        + (m ^ (k + 1) + (k + 1) * d * m ^ k) * d
        ≤ (m + d) ^ (k + 1) * m + (m + d) ^ (k + 1) * d :=
      Nat.add_le_add (Nat.mul_le_mul_right _ ih) (Nat.mul_le_mul_right _ ih)
    rw [hexp]
    refine le_trans ?_ hstep
    have e1 : (m ^ (k + 1) + (k + 1) * d * m ^ k) * m = m ^ (k + 2) + (k + 1) * d * m ^ (k + 1) := by
      rw [pow_succ, pow_succ]; ring
    have e2 : (m ^ (k + 1) + (k + 1) * d * m ^ k) * d
        = m ^ (k + 1) * d + (k + 1) * d * d * m ^ k := by ring
    rw [e1, e2]
    have : m ^ (k + 2) + (k + 1 + 1) * d * m ^ (k + 1)
        = m ^ (k + 2) + (k + 1) * d * m ^ (k + 1) + m ^ (k + 1) * d := by ring
    rw [this]
    omega

/-- **The decay terminates.**  With a per-round drop `n·a_{i+1} ≤ (n-d)·a_i` and
`1 ≤ d ≤ n-1` (so `0 < n-d < n`), the fat-count reaches `0`: `∃ k, a k = 0`. -/
theorem exists_decay_zero {n d : ℕ} (a : ℕ → ℕ)
    (hstep : ∀ i, n * a (i + 1) ≤ (n - d) * a i) (hd1 : 1 ≤ d) (hdn : d + 1 ≤ n) :
    ∃ k, a k = 0 := by
  rcases Nat.eq_zero_or_pos (a 0) with h0 | h0
  · exact ⟨0, h0⟩
  · refine ⟨(a 0 - 1) * (n - d) + 1, decay_zero a hstep _ ?_⟩
    set m := n - d with hm
    have hm1 : 1 ≤ m := by omega
    have hmn : m + d = n := by omega
    set K := (a 0 - 1) * m with hK
    have hbern := bernoulli_pow m d K
    rw [hmn] at hbern
    -- hbern : m^(K+1) + (K+1)*d*m^K ≤ n^(K+1)
    have hlt : (a 0) * m ^ (K + 1) < m ^ (K + 1) + (K + 1) * d * m ^ K := by
      have hmpos : 0 < m ^ K := pow_pos hm1 K
      have hkey : (a 0 - 1) * m * m ^ K < (K + 1) * d * m ^ K := by
        have hlt2 : (a 0 - 1) * m < (K + 1) * d := by
          rw [hK]
          have h1 : (a 0 - 1) * m + 1 ≤ ((a 0 - 1) * m + 1) * d := by
            calc (a 0 - 1) * m + 1 = ((a 0 - 1) * m + 1) * 1 := by rw [Nat.mul_one]
              _ ≤ ((a 0 - 1) * m + 1) * d := mul_le_mul_left' hd1 _
          omega
        exact mul_lt_mul_of_pos_right hlt2 hmpos
      have ha0m : a 0 * m = (a 0 - 1) * m + m := by
        have hle : m ≤ a 0 * m := Nat.le_mul_of_pos_left m h0
        rw [Nat.sub_one_mul]
        omega
      have e3 : (a 0) * m ^ (K + 1) = (a 0 - 1) * m * m ^ K + m * m ^ K := by
        rw [pow_succ, mul_comm (m ^ K) m, ← mul_assoc, ha0m, add_mul]
      have e4 : m ^ (K + 1) = m * m ^ K := by rw [pow_succ, mul_comm]
      rw [e3, e4]
      omega
    calc (n - d) ^ (K + 1) * a 0 = (a 0) * m ^ (K + 1) := by rw [hm]; ring
      _ < m ^ (K + 1) + (K + 1) * d * m ^ K := hlt
      _ ≤ n ^ (K + 1) := hbern

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.exists_popular_literal
#print axioms PallLean.Paper93.DeepMath.PathB.fat_count_decreases
#print axioms PallLean.Paper93.DeepMath.PathB.decay_pow
#print axioms PallLean.Paper93.DeepMath.PathB.decay_zero
#print axioms PallLean.Paper93.DeepMath.PathB.exists_decay_zero
