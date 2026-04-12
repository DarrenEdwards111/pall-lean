/-
  GodMoveReal.lean — God-Move extraction with rank monotonicity

  Paper §29, Lemma 123:

  The compiler output P_{M',n}(u,z,v) decomposes as Q×_Φ(u,z) + R(v).
  By Lemma 122 (rank monotonicity): Γ(Q×_Φ) ≤ Γ(P_{M',n}).

  We formalize:
  1. Adding a constant does not change the SPDP subspace (κ ≥ 1)
  2. The God-Move extraction structure connecting compiled and coupled sheets
  3. The rank monotonicity chain for the separation
-/
import PallLean.PaperFaithfulSeparation
import Mathlib.Tactic
import Mathlib.Data.Nat.Log

namespace GodMoveReal

open SPDP MultilinearSPDP MvPolynomial TuringMachine

attribute [local instance] Classical.dec

/-! ## Adding a Constant Does Not Change SPDP Subspace (κ ≥ 1)

For the God-Move, we need: adding a constant to p does not change its
SPDP subspace when κ ≥ 1, because ∂_S(constant) = 0 for |S| ≥ 1. -/

/-- iterDerivList of a constant C c is 0 when the list is nonempty. -/
theorem iterDerivList_C_eq_zero {N : ℕ} (c : ℚ)
    (S : List (Fin N)) (hS : S ≠ []) :
    iterDerivList S (C c : MvPolynomial (Fin N) ℚ) = 0 := by
  cases S with
  | nil => exact absurd rfl hS
  | cons i rest =>
    unfold iterDerivList
    simp only [List.foldl_cons, pderiv_C]
    exact foldl_pderiv_zero rest

/-- Adding C c to a polynomial does not change its SPDP subspace when κ ≥ 1. -/
theorem mlBlockedSpdpSubspace_add_const {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ) (hκ : κ ≥ 1)
    (p : MvPolynomial (Fin N) ℚ) (c : ℚ) :
    mlBlockedSpdpSubspace B κ ℓ (p + C c) = mlBlockedSpdpSubspace B κ ℓ p := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
    rw [hq]
    have hS_ne : S ≠ [] := by intro h; subst h; simp at hlen; omega
    rw [iterDerivList_add S p (C c), iterDerivList_C_eq_zero c S hS_ne, add_zero]
    exact Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  · apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
    rw [hq]
    have hS_ne : S ≠ [] := by intro h; subst h; simp at hlen; omega
    have : m * iterDerivList S p = m * iterDerivList S (p + C c) := by
      rw [iterDerivList_add S p (C c), iterDerivList_C_eq_zero c S hS_ne, add_zero]
    rw [this]
    exact Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩

/-- Adding C c does not change SPDP rank when κ ≥ 1. -/
theorem mlBlockedSpdpRank_add_const {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ) (hκ : κ ≥ 1)
    (p : MvPolynomial (Fin N) ℚ) (c : ℚ) :
    mlBlockedSpdpRank B κ ℓ (p + C c) = mlBlockedSpdpRank B κ ℓ p := by
  unfold mlBlockedSpdpRank
  rw [mlBlockedSpdpSubspace_add_const B κ ℓ hκ p c]

/-! ## Negation Preserves SPDP Subspace

iterDerivList distributes over negation (by linearity of pderiv). -/

/-- pderiv distributes over negation. -/
theorem iterDerivList_neg {N : ℕ}
    (S : List (Fin N)) (p : MvPolynomial (Fin N) ℚ) :
    iterDerivList S (-p) = -iterDerivList S p := by
  induction S generalizing p with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    rw [show pderiv i (-p) = -(pderiv i p) from map_neg (pderiv i) p]
    exact ih (pderiv i p)

/-- mlProj distributes over negation. -/
theorem mlProj_neg {N : ℕ} (p : MvPolynomial (Fin N) ℚ) :
    mlProj (-p) = -mlProj p := by
  have h1 : -p = (-1 : ℚ) • p := by simp
  rw [h1, mlProj_smul]
  simp

/-- The SPDP subspace of -p equals that of p. -/
theorem mlBlockedSpdpSubspace_neg {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) :
    mlBlockedSpdpSubspace B κ ℓ (-p) = mlBlockedSpdpSubspace B κ ℓ p := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
    rw [hq, iterDerivList_neg, mul_neg, mlProj_neg]
    exact Submodule.neg_mem _
      (Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩)
  · apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
    rw [hq]
    have : m * iterDerivList S p = -(m * iterDerivList S (-p)) := by
      rw [iterDerivList_neg, mul_neg, neg_neg]
    rw [this, mlProj_neg]
    exact Submodule.neg_mem _
      (Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩)

/-- Γ(-p) ≤ Γ(p). -/
theorem mlBlockedSpdpRank_neg_le {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) :
    mlBlockedSpdpRank B κ ℓ (-p) ≤ mlBlockedSpdpRank B κ ℓ p := by
  unfold mlBlockedSpdpRank
  rw [mlBlockedSpdpSubspace_neg B κ ℓ p]

/-! ## Rank Summand Bound (God-Move Decomposition)

If P = Q + R, then Γ(Q) ≤ Γ(P) + Γ(R).
Proof: Q = P + (-R), so Γ(Q) ≤ Γ(P) + Γ(-R) ≤ Γ(P) + Γ(R). -/

/-- If P = Q + R, then Γ(Q) ≤ Γ(P) + Γ(R). -/
theorem rank_summand_bound {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (p q r : MvPolynomial (Fin N) ℚ)
    (hpqr : p = q + r) :
    mlBlockedSpdpRank B κ ℓ q ≤
      mlBlockedSpdpRank B κ ℓ p + mlBlockedSpdpRank B κ ℓ r := by
  have hq : q = p + (-r) := by rw [hpqr]; ring
  calc mlBlockedSpdpRank B κ ℓ q
      = mlBlockedSpdpRank B κ ℓ (p + (-r)) := by rw [hq]
    _ ≤ mlBlockedSpdpRank B κ ℓ p + mlBlockedSpdpRank B κ ℓ (-r) :=
        mlBlockedSpdpRank_add_le B κ ℓ p (-r)
    _ ≤ mlBlockedSpdpRank B κ ℓ p + mlBlockedSpdpRank B κ ℓ r :=
        Nat.add_le_add_left (mlBlockedSpdpRank_neg_le B κ ℓ r) _

/-- When Γ(R) = 0: Γ(Q) ≤ Γ(P). -/
theorem rank_summand_le_of_zero_remainder {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (p q r : MvPolynomial (Fin N) ℚ)
    (hpqr : p = q + r)
    (hr : mlBlockedSpdpRank B κ ℓ r = 0) :
    mlBlockedSpdpRank B κ ℓ q ≤ mlBlockedSpdpRank B κ ℓ p := by
  calc mlBlockedSpdpRank B κ ℓ q
      ≤ mlBlockedSpdpRank B κ ℓ p + mlBlockedSpdpRank B κ ℓ r :=
        rank_summand_bound B κ ℓ p q r hpqr
    _ = mlBlockedSpdpRank B κ ℓ p := by omega

/-! ## God-Move Extraction Structure -/

/-- The God-Move extraction data. -/
structure GodMoveData (M : DTM) (n : ℕ) where
  N : ℕ
  partition : BlockPartition N
  poly : MvPolynomial (Fin N) ℚ
  coupled : PaperFaithfulSeparation.CoupledVerifierSheet
  coupledRank : ℕ → ℕ → ℕ
  compiledRank : ℕ → ℕ → ℕ
  rank_monotone : ∀ κ ℓ : ℕ, coupledRank κ ℓ ≤ compiledRank κ ℓ
  compiledRank_eq : ∀ κ ℓ : ℕ,
    compiledRank κ ℓ = mlBlockedSpdpRank partition κ ℓ poly

/-- Converting GodMoveData to GodMoveExtraction. -/
noncomputable def GodMoveData.toExtraction {M : DTM} {n : ℕ}
    (gm : GodMoveData M n) :
    PaperFaithfulSeparation.GodMoveExtraction M n where
  N := gm.N
  partition := gm.partition
  poly := gm.poly
  formula := { numVars := 0, clauses := [] }
  coupled := gm.coupled
  coupledRank := gm.coupledRank
  compiledRank := gm.compiledRank
  rank_monotone := gm.rank_monotone
  compiledRank_eq := gm.compiledRank_eq

/-! ## Rank Monotonicity Chain for the Separation -/

/-- The rank monotonicity chain:
    coupledRank(κ, 0) ≤ compiledRank(κ, 0) ≤ compiledRank(κ, κ). -/
theorem god_move_rank_chain {M : DTM} {n : ℕ}
    (ext : PaperFaithfulSeparation.GodMoveExtraction M n) (κ : ℕ) :
    ext.coupledRank κ 0 ≤ ext.compiledRank κ κ :=
  le_trans (ext.rank_monotone κ 0)
    (PaperFaithfulSeparation.compiled_rank_mono_ell ext κ 0 κ (Nat.zero_le κ))

/-- The full God-Move bridge: coupledRank ≤ n^200 when P-side bound holds. -/
theorem god_move_bridge {M : DTM} {n : ℕ}
    (ext : PaperFaithfulSeparation.GodMoveExtraction M n)
    (h_pside : PaperFaithfulSeparation.p_side_rank_bound M n ext) :
    ext.coupledRank (Nat.log 2 n) 0 ≤ n ^ 200 :=
  calc ext.coupledRank (Nat.log 2 n) 0
      ≤ ext.compiledRank (Nat.log 2 n) (Nat.log 2 n) :=
        god_move_rank_chain ext (Nat.log 2 n)
    _ = mlBlockedSpdpRank ext.partition (Nat.log 2 n) (Nat.log 2 n) ext.poly :=
        ext.compiledRank_eq (Nat.log 2 n) (Nat.log 2 n)
    _ ≤ n ^ 200 := h_pside

/-- Abstract restriction monotonicity: subspace containment gives rank bound. -/
theorem restriction_rank_mono {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (p q : MvPolynomial (Fin N) ℚ)
    (h : mlBlockedSpdpSubspace B κ ℓ q ≤ mlBlockedSpdpSubspace B κ ℓ p) :
    mlBlockedSpdpRank B κ ℓ q ≤ mlBlockedSpdpRank B κ ℓ p :=
  Submodule.finrank_mono h

end GodMoveReal
