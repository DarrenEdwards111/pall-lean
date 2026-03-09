/-
  WidthRank.lean — §9 Width⇒Rank Theorem (Theorem 23)

  Proved theorems:
  - finrank_iSup_fin_le: finrank(⨆ Vᵢ) ≤ k × D₀ (subadditivity)
  - rank_le_of_subspace_cover: subspace cover → SPDP rank bound (A4 PROVED)
  - profile_to_poly_bound: profile decomposition → polynomial rank (assembly)

  The compiler axiom (in FullCompiler.lean) provides the subspace cover.
-/
import PallLean.SPDPDefs
import PallLean.ProfileCompression
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace WidthRank

open SPDP ProfileCompression

/-! ## iSup decomposition for Fin (k+1) -/

theorem iSup_fin_succ {α : Type*} [CompleteLattice α] {k : ℕ}
    (f : Fin (k+1) → α) :
    (⨆ i, f i) = (⨆ i : Fin k, f (Fin.castSucc i)) ⊔ f (Fin.last k) := by
  apply le_antisymm
  · apply iSup_le; intro i
    refine Fin.lastCases ?_ ?_ i
    · exact le_sup_right
    · intro j; exact le_sup_of_le_left (le_iSup (fun j => f (Fin.castSucc j)) j)
  · apply sup_le
    · exact iSup_le (fun j => le_iSup f (Fin.castSucc j))
    · exact le_iSup f (Fin.last k)

/-! ## Subadditivity of finrank over finite sups (PROVED)

    finrank(⨆ i : Fin k, W i) ≤ k × D₀ when each finrank(W i) ≤ D₀.
    Proved by induction using finrank_sup_add_finrank_inf_eq. -/
theorem finrank_iSup_fin_le {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (k : ℕ) : ∀ (W : Fin k → Submodule K V)
    [∀ i, FiniteDimensional K (W i)]
    (D₀ : ℕ), (∀ i, Module.finrank K (W i) ≤ D₀) →
    Module.finrank K ↥(⨆ i, W i) ≤ k * D₀ := by
  induction k with
  | zero =>
    intro W _ D₀ _
    have : (⨆ i : Fin 0, W i) = ⊥ := iSup_of_empty _
    rw [this]; simp [finrank_bot]
  | succ k ih =>
    intro W _ D₀ hW
    rw [iSup_fin_succ W]
    have hih := ih (fun i => W (Fin.castSucc i)) D₀ (fun i => hW (Fin.castSucc i))
    calc Module.finrank K ↥((⨆ i : Fin k, W (Fin.castSucc i)) ⊔ W (Fin.last k))
        ≤ Module.finrank K ↥(⨆ i : Fin k, W (Fin.castSucc i)) +
          Module.finrank K ↥(W (Fin.last k)) := by
            have := Submodule.finrank_sup_add_finrank_inf_eq
              (⨆ i : Fin k, W (Fin.castSucc i)) (W (Fin.last k))
            omega
      _ ≤ k * D₀ + D₀ := by linarith [hW (Fin.last k)]
      _ = (k + 1) * D₀ := by ring

/-! ## A4: Rank from subspace cover (PROVED)

    If blockedSpdpSubspace ≤ ⨆ i : Fin N, V i and each finrank(V i) ≤ D₀,
    then blockedSpdpRank ≤ N × D₀.

    This is the "subadditivity" step of Theorem 23:
    Γ = dim(RowSpan) ≤ dim(Σ V_h) ≤ Σ dim(V_h) ≤ |H| · max dim. -/
theorem rank_le_of_subspace_cover {F : Type*} [Field F] {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F)
    (N D₀ : ℕ) (V : Fin N → Submodule F (MvPolynomial (Fin n) F))
    [∀ i, FiniteDimensional F (V i)]
    (hcover : blockedSpdpSubspace B κ ℓ p ≤ ⨆ i, V i)
    (hdim : ∀ i, Module.finrank F (V i) ≤ D₀) :
    blockedSpdpRank B κ ℓ p ≤ N * D₀ :=
  calc blockedSpdpRank B κ ℓ p
      = Module.finrank F (blockedSpdpSubspace B κ ℓ p) := rfl
    _ ≤ Module.finrank F ↥(⨆ i, V i) := Submodule.finrank_mono hcover
    _ ≤ N * D₀ := finrank_iSup_fin_le N V D₀ hdim

/-! ## Arithmetic assembly -/

theorem succ_pow_le_pow_succ (n k : ℕ) (hn : n ≥ 2 ^ k) :
    (n + 1) ^ k ≤ n ^ (k + 1) := by
  calc (n + 1) ^ k
      ≤ (2 * n) ^ k := by
        apply Nat.pow_le_pow_left
        have : n ≥ 1 := le_trans (Nat.one_le_pow k 2 (by omega)) hn
        omega
    _ = 2 ^ k * n ^ k := by ring
    _ ≤ n * n ^ k := Nat.mul_le_mul_right _ hn
    _ = n ^ (k + 1) := by ring

theorem profile_to_poly_bound {Γ R n m D numP maxD : ℕ}
    (hm : m ≥ 1) (hD : D ≥ 1)
    (hR : R ≤ n)
    (hn : n ≥ 2 ^ (m + D))
    (hΓ : Γ ≤ numP * maxD)
    (hP : numP ≤ (R + 1) ^ m)
    (hDim : maxD ≤ Nat.choose (R + D) D) :
    Γ ≤ n ^ (m + D + 1) := by
  have h2 : Nat.choose (R + D) D ≤ (R + 1) ^ D := choose_le_pow R D
  calc Γ
      ≤ numP * maxD := hΓ
    _ ≤ (R + 1) ^ m * Nat.choose (R + D) D := Nat.mul_le_mul hP hDim
    _ ≤ (R + 1) ^ m * (R + 1) ^ D := Nat.mul_le_mul_left _ h2
    _ = (R + 1) ^ (m + D) := by ring
    _ ≤ (n + 1) ^ (m + D) := Nat.pow_le_pow_left (by omega) (m + D)
    _ ≤ n ^ (m + D + 1) := succ_pow_le_pow_succ n (m + D) hn

end WidthRank
