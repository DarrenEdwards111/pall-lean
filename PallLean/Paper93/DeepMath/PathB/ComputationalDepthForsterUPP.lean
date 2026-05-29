import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForsterUnconditional
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUPPBridge

/-!
# Forster ⇒ UPP communication lower bound (one honest brick toward circuits)

This file chains the unconditional, concrete Forster sign-rank lower bound
(`ForsterUnconditional.walsh_sign_rank`) with the *existing* Paturi–Simon
direction in `ComputationalDepthUPPBridge.lean`
(`hasSignRankLE_of_uppProtocolCostLE : UPPProtocolCostLE M c → HasSignRankLE M (2^c)`)
to obtain a genuine **unbounded-error (UPP) communication complexity lower
bound** for the Walsh–Hadamard matrix:

  `walsh_uppCost_lower : UPPProtocolCostLE (walshMatrix) c → (k : ℝ) ≤ 2 * c`,

i.e. the UPP cost of the `2^k × 2^k` Walsh matrix is at least `k/2`.

The connecting lemma `exists_unitRealization_of_hasSignRankLE` turns a sign-rank
factorisation (`HasSignRankLE`) into a `Forster.UnitRealization` by normalising
the factor vectors — the genuine bridge between the sign-rank predicate and the
Forster machinery.

**Honest scope.**  This is the *restricted* result: a communication-complexity
lower bound (equivalently, against depth-2 majority/threshold structure), the
legitimate first step of "sign rank ⇒ circuits".  It is **not** P≠NP: turning a
poly-size *general* circuit into a low-cost UPP protocol is the genuine wall (the
margin-free `O(log s)` protocol — the constant-bias route is the full-rank
dead-end documented in the UPP bridge).
-/

namespace PallLean.Paper93.DeepMath.PathB.ForsterUPP

open scoped BigOperators Matrix RealInnerProductSpace
open Forster ForsterUnconditional

variable {m n d : ℕ}

/-- **Sign-rank factorisation ⇒ unit realization.**  A `HasSignRankLE M d`
witness `M ≈ sgn (B·C)` yields a `Forster.UnitRealization M d` by taking the rows
of `B` and columns of `C` as the vectors and normalising them (they are nonzero
because their inner products — the entries of `B·C` — are nonzero).  Also forces
`0 < d` for a nonempty matrix. -/
theorem exists_unitRealization_of_hasSignRankLE (M : Fin m → Fin n → Bool)
    (hm : 0 < m) (hn : 0 < n) (hsr : HasSignRankLE M d) :
    0 < d ∧ Nonempty (UnitRealization M d) := by
  obtain ⟨B, C, hBC⟩ := hsr
  set rowB : Fin m → EuclideanSpace ℝ (Fin d) :=
    fun i => (WithLp.equiv 2 (Fin d → ℝ)).symm (fun k => B i k) with hrowB
  set colC : Fin n → EuclideanSpace ℝ (Fin d) :=
    fun j => (WithLp.equiv 2 (Fin d → ℝ)).symm (fun k => C k j) with hcolC
  have hinner : ∀ i j, (⟪rowB i, colC j⟫ : ℝ) = (B * C) i j := by
    intro i j
    rw [eucl_inner_eq_sum, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun k _ => rfl)
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exfalso
      subst h
      have hb := hBC ⟨0, hm⟩ ⟨0, hn⟩
      simp [Matrix.mul_apply] at hb
    · exact h
  have hrowne : ∀ i, rowB i ≠ 0 := by
    intro i h
    have hb := hBC i ⟨0, hn⟩
    rw [← hinner i ⟨0, hn⟩, h, inner_zero_left, mul_zero] at hb
    exact lt_irrefl 0 hb
  have hcolne : ∀ j, colC j ≠ 0 := by
    intro j h
    have hb := hBC ⟨0, hm⟩ j
    rw [← hinner ⟨0, hm⟩ j, h, inner_zero_right, mul_zero] at hb
    exact lt_irrefl 0 hb
  refine ⟨hd0, ⟨{
      u := fun i => ‖rowB i‖⁻¹ • rowB i
      w := fun j => ‖colC j‖⁻¹ • colC j
      u_unit := ?_
      w_unit := ?_
      sign_ok := ?_ }⟩⟩
  · intro i
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr (hrowne i)),
      inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr (hrowne i)))]
  · intro j
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr (hcolne j)),
      inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr (hcolne j)))]
  · intro i j
    rw [real_inner_smul_left, real_inner_smul_right, hinner]
    have hu : 0 < ‖rowB i‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (hrowne i))
    have hw : 0 < ‖colC j‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (hcolne j))
    nlinarith [mul_pos (mul_pos hu hw) (hBC i j)]

/-- **Forster lower bound in `HasSignRankLE` form for the Walsh matrix.**  Any
sign-rank-`d` factorisation of the `2^k × 2^k` Walsh–Hadamard matrix has
`√(2^k) ≤ d`. -/
theorem walsh_hasSignRankLE_lower {m' k : ℕ} (hmk : m' + 1 = 2 ^ k) {d : ℕ}
    (hsr : HasSignRankLE (walshMatrix hmk) d) :
    Real.sqrt ((2 : ℝ) ^ k) ≤ (d : ℝ) := by
  have hcast : ((m' + 1 : ℕ) : ℝ) = (2 : ℝ) ^ k := by rw [hmk]; push_cast; ring
  obtain ⟨hd0, ⟨R⟩⟩ :=
    exists_unitRealization_of_hasSignRankLE (walshMatrix hmk) (Nat.succ_pos m') (Nat.succ_pos m') hsr
  by_cases hdm' : d ≤ m'
  · have hb := walsh_sign_rank hmk hd0 hdm' R
    rwa [hcast] at hb
  · push_neg at hdm'
    have hge : (2 : ℝ) ^ k ≤ (d : ℝ) := by
      rw [← hcast]; exact_mod_cast hdm'
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    calc Real.sqrt ((2 : ℝ) ^ k)
        ≤ Real.sqrt ((2 : ℝ) ^ k * (2 : ℝ) ^ k) :=
          Real.sqrt_le_sqrt (le_mul_of_one_le_left (by positivity) h1)
      _ = (2 : ℝ) ^ k := Real.sqrt_mul_self (by positivity)
      _ ≤ (d : ℝ) := hge

/-- **UPP communication lower bound for the Walsh matrix.**  Any unbounded-error
communication protocol for the `2^k × 2^k` Walsh–Hadamard matrix has cost
`c ≥ k/2`: combining the Paturi–Simon bound `cost c ⇒ sign-rank ≤ 2^c` with the
Forster sign-rank lower bound `√(2^k)` gives `√(2^k) ≤ 2^c`, i.e. `k ≤ 2c`. -/
theorem walsh_uppCost_lower {m' k : ℕ} (hmk : m' + 1 = 2 ^ k) {c : ℕ}
    (hc : UPPProtocolCostLE (walshMatrix hmk) c) :
    (k : ℝ) ≤ 2 * (c : ℝ) := by
  have hb := walsh_hasSignRankLE_lower hmk (hasSignRankLE_of_uppProtocolCostLE hc)
  -- `√(2^k) ≤ (2^c : ℕ : ℝ) = 2^c`
  have hbc : Real.sqrt ((2 : ℝ) ^ k) ≤ (2 : ℝ) ^ c := by
    have : ((2 ^ c : ℕ) : ℝ) = (2 : ℝ) ^ c := by push_cast; ring
    rwa [this] at hb
  -- square: `2^k ≤ (2^c)^2 = 2^(2c)`
  have hsq : (2 : ℝ) ^ k ≤ ((2 : ℝ) ^ c) ^ 2 := by
    have hroot : ((2 : ℝ) ^ k) = (Real.sqrt ((2 : ℝ) ^ k)) ^ 2 :=
      (Real.sq_sqrt (by positivity)).symm
    rw [hroot]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hbc 2
  rw [← pow_mul] at hsq
  -- `2^k ≤ 2^(c*2)` ⇒ `k ≤ c*2`
  have hk : k ≤ c * 2 := by
    have := (pow_le_pow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mp hsq
    exact this
  have : (k : ℝ) ≤ (c * 2 : ℕ) := by exact_mod_cast hk
  push_cast at this
  linarith

#print axioms PallLean.Paper93.DeepMath.PathB.ForsterUPP.exists_unitRealization_of_hasSignRankLE
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterUPP.walsh_uppCost_lower
