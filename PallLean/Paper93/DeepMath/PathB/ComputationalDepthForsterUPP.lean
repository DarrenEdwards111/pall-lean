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

open scoped BigOperators Matrix RealInnerProductSpace Matrix.Norms.L2Operator
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

/-- **Discharging the framework's `ForsterLowerBound` assumption.**  In
`ComputationalDepthSignRankInvariant.lean`, `ForsterLowerBound M B` (`sign rank
≥ B`) is carried as a *labelled hypothesis* ("here it is a labelled hypothesis").
For the `2^{2j} × 2^{2j}` Walsh–Hadamard matrix it is now a **theorem**:
`ForsterLowerBound (walshMatrix) (2^j)`, i.e. sign rank `≥ 2^j = √(2^{2j})`.

This turns the conditional no-go `no_small_depth2` into one whose Forster input is
genuinely proven (its remaining hypothesis — the budget→dimension *bridge* — is
the open/dead-end direction, not this one). -/
theorem walsh_forsterLowerBound {m' j : ℕ} (hmk : m' + 1 = 2 ^ (2 * j)) :
    ForsterLowerBound (walshMatrix hmk) (2 ^ j) := by
  intro d hsr
  have hb := walsh_hasSignRankLE_lower hmk hsr
  rw [show 2 * j = j * 2 from Nat.mul_comm 2 j, pow_mul,
    Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 ^ j)] at hb
  exact_mod_cast hb

/-- **The `±1` operator norm is at least `√(#rows)`.**  Evaluating the `L²`
operator norm of `sgnMat M` (square, `(m'+1)×(m'+1)`) on a standard basis vector
gives a column of `±1` entries, whose `L²` norm is `√(m'+1)`. -/
theorem sgnMat_opNorm_ge {m' : ℕ} (M : Fin (m' + 1) → Fin (m' + 1) → Bool) :
    Real.sqrt ((m' + 1 : ℕ) : ℝ) ≤ ‖sgnMat M‖ := by
  set j₀ : Fin (m' + 1) := ⟨0, Nat.succ_pos m'⟩ with hj0
  set x : EuclideanSpace ℝ (Fin (m' + 1)) := EuclideanSpace.single j₀ 1 with hx
  have hmul := (sgnMat M).l2_opNorm_mulVec x
  rw [EuclideanSpace.norm_single, norm_one, mul_one] at hmul
  have hcomp : ∀ i, ((EuclideanSpace.equiv (Fin (m' + 1)) ℝ).symm (sgnMat M *ᵥ x)) i
      = sgn (M i j₀) := by
    intro i
    show (sgnMat M *ᵥ x) i = sgn (M i j₀)
    simp only [hx, Matrix.mulVec, dotProduct, sgnMat, Matrix.of_apply,
      EuclideanSpace.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hsq : ‖(EuclideanSpace.equiv (Fin (m' + 1)) ℝ).symm (sgnMat M *ᵥ x)‖ ^ 2
      = ((m' + 1 : ℕ) : ℝ) := by
    rw [eucl_normSq_eq_sum]
    have hone : ∀ i, ((EuclideanSpace.equiv (Fin (m' + 1)) ℝ).symm (sgnMat M *ᵥ x)) i ^ 2
        = 1 := by
      intro i; rw [hcomp i]; cases M i j₀ <;> simp [sgn]
    rw [Finset.sum_congr rfl (fun i _ => hone i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hcol : ‖(EuclideanSpace.equiv (Fin (m' + 1)) ℝ).symm (sgnMat M *ᵥ x)‖
      = Real.sqrt ((m' + 1 : ℕ) : ℝ) := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rwa [hcol] at hmul

/-- **General Forster sign-rank lower bound (any square `±1` matrix).**  Every
sign-rank-`d` factorisation of a square Bool matrix `M` satisfies
`√((m'+1)²)/‖sgnMat M‖ ≤ d`.  This is the fundamental theorem of which the Walsh
bound is one instance; the `d > m'` edge uses `sgnMat_opNorm_ge`. -/
theorem forster_signRank_lower {m' : ℕ} (M : Fin (m' + 1) → Fin (m' + 1) → Bool)
    (hμ : 0 < ‖sgnMat M‖) {d : ℕ} (hsr : HasSignRankLE M d) :
    Real.sqrt (((m' + 1 : ℕ) : ℝ) * ((m' + 1 : ℕ) : ℝ)) / ‖sgnMat M‖ ≤ (d : ℝ) := by
  obtain ⟨hd0, ⟨R⟩⟩ :=
    exists_unitRealization_of_hasSignRankLE M (Nat.succ_pos m') (Nat.succ_pos m') hsr
  by_cases hdm' : d ≤ m'
  · exact forster_bound_unconditional hd0 hdm' R (by positivity) hμ
  · push_neg at hdm'
    have hNpos : (0 : ℝ) < ((m' + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m'
    have hsqrtpos : (0 : ℝ) < Real.sqrt ((m' + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hNpos
    rw [Real.sqrt_mul_self hNpos.le]
    calc ((m' + 1 : ℕ) : ℝ) / ‖sgnMat M‖
        ≤ ((m' + 1 : ℕ) : ℝ) / Real.sqrt ((m' + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_left hNpos.le hsqrtpos (sgnMat_opNorm_ge M)
      _ = Real.sqrt ((m' + 1 : ℕ) : ℝ) := Real.div_sqrt
      _ ≤ ((m' + 1 : ℕ) : ℝ) := by
          calc Real.sqrt ((m' + 1 : ℕ) : ℝ)
              ≤ Real.sqrt (((m' + 1 : ℕ) : ℝ) * ((m' + 1 : ℕ) : ℝ)) :=
                Real.sqrt_le_sqrt (le_mul_of_one_le_left hNpos.le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m')))
            _ = ((m' + 1 : ℕ) : ℝ) := Real.sqrt_mul_self hNpos.le
      _ ≤ (d : ℝ) := by exact_mod_cast hdm'

#print axioms PallLean.Paper93.DeepMath.PathB.ForsterUPP.exists_unitRealization_of_hasSignRankLE
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterUPP.walsh_uppCost_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterUPP.walsh_forsterLowerBound
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterUPP.forster_signRank_lower
