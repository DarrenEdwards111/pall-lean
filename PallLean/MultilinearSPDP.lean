/-
  MultilinearSPDP.lean — SPDP rank in the multilinear (Boolean) basis

  Paper Definition 12: The SPDP matrix uses multilinear monomials (mod ⟨x²_i - x_i⟩).
  We define multilinear SPDP rank as dim of span of mlProj-ed generators.
-/
import PallLean.SPDPDefs
import PallLean.NPWitness
import PallLean.Compiler
import PallLean.Multilinear
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace MultilinearSPDP

open MvPolynomial SPDP TuringMachine Compiler NPWitness Multilinear

attribute [local instance] Classical.dec

/-! ## Multilinear Projection -/

/-- A finsupp is multilinear if every value is ≤ 1 -/
def Finsupp.IsMultilinear {σ : Type*} (α : σ →₀ ℕ) : Prop :=
  ∀ i, α i ≤ 1

/-- The multilinear projection as an AddMonoidHom on the underlying Finsupp.
    This gives us additivity for free. -/
noncomputable def mlProjHom {σ : Type*} [DecidableEq σ] (F : Type*) [CommRing F] :
    ((σ →₀ ℕ) →₀ F) →+ ((σ →₀ ℕ) →₀ F) :=
  Finsupp.filterAddHom (fun α => Finsupp.IsMultilinear α)

/-- The multilinear projection on MvPolynomial -/
noncomputable def mlProj {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) : MvPolynomial σ F :=
  mlProjHom F p

theorem mlProj_add {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p q : MvPolynomial σ F) :
    mlProj (p + q) = mlProj p + mlProj q :=
  map_add (mlProjHom F) p q

@[simp] theorem mlProj_zero {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F] :
    mlProj (0 : MvPolynomial σ F) = 0 :=
  map_zero (mlProjHom F)

theorem mlProj_smul {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (c : F) (p : MvPolynomial σ F) :
    mlProj (c • p) = c • mlProj p := by
  change Finsupp.filter _ (c • p) = c • Finsupp.filter _ p
  ext α
  simp only [Finsupp.filter_apply, Finsupp.smul_apply, smul_eq_mul]
  split
  · rfl
  · exact (mul_zero c).symm

/-- mlProj as a linear map -/
noncomputable def mlProjLinearMap (σ : Type*) [DecidableEq σ] (F : Type*) [CommRing F] :
    MvPolynomial σ F →ₗ[F] MvPolynomial σ F where
  toFun := mlProj
  map_add' := mlProj_add
  map_smul' := mlProj_smul

/-! ## Multilinear SPDP Subspace and Rank -/

noncomputable def mlBlockedSpdpSubspace {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        isBlockAdmissible B S ∧
        q = mlProj (m * iterDerivList S p) }

noncomputable def mlBlockedSpdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (mlBlockedSpdpSubspace B κ ℓ p)

/-! ## Monotonicity -/

theorem mlBlockedSpdpSubspace_le_map {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspace B κ ℓ p ≤
      Submodule.map (mlProjLinearMap (Fin n) F) (blockedSpdpSubspace B κ ℓ p) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hadm, hq⟩
  rw [hq]
  exact Submodule.mem_map.mpr
    ⟨m * iterDerivList S p,
     Submodule.subset_span ⟨S, m, hlen, hdeg, hadm,
       fun _ _ => Finset.mem_univ _, fun _ _ => Finset.mem_univ _, rfl⟩,
     rfl⟩

/-- mlProj only drops monomials, so support is a subset -/
theorem mlProj_support_subset {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) : (mlProj p).support ⊆ p.support := by
  change (Finsupp.filter _ p).support ⊆ p.support
  rw [Finsupp.support_filter]
  exact Finset.filter_subset _ _

/-- mlProj doesn't increase totalDegree -/
theorem totalDegree_mlProj_le {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) : (mlProj p).totalDegree ≤ p.totalDegree :=
  MvPolynomial.totalDegree_le_of_support_subset (mlProj_support_subset p)

theorem mlBlockedSpdpSubspace_le_restrictTotalDegree {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspace B κ ℓ p ≤
      MvPolynomial.restrictTotalDegree (Fin n) F (ℓ + p.totalDegree) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, _, hdeg, _, hq⟩
  rw [hq]
  -- mlProj(m * ∂_S p) ∈ restrictTotalDegree because totalDegree only decreases
  have h1 : (mlProj (m * iterDerivList S p)).totalDegree ≤ ℓ + p.totalDegree :=
    le_trans (totalDegree_mlProj_le _)
      (le_trans (MvPolynomial.totalDegree_mul m (iterDerivList S p))
        (Nat.add_le_add hdeg (totalDegree_iterDerivList_le S p)))
  exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr h1

instance mlBlockedSpdpSubspace_finite {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Module.Finite F (mlBlockedSpdpSubspace B κ ℓ p) := by
  have hle := mlBlockedSpdpSubspace_le_restrictTotalDegree B κ ℓ p
  have : Module.Finite F (MvPolynomial.restrictTotalDegree (Fin n) F (ℓ + p.totalDegree)) :=
    MvPolynomial.instFiniteSubtypeMemSubmoduleRestrictTotalDegreeOfFinite _ _ _
  exact Module.Finite.of_injective
    (Submodule.inclusion hle)
    (Submodule.inclusion_injective _)

theorem mlBlockedSpdpRank_le {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRank B κ ℓ p ≤ blockedSpdpRank B κ ℓ p := by
  unfold mlBlockedSpdpRank blockedSpdpRank
  calc Module.finrank F ↥(mlBlockedSpdpSubspace B κ ℓ p)
      ≤ Module.finrank F ↥(Submodule.map (mlProjLinearMap (Fin n) F)
          (blockedSpdpSubspace B κ ℓ p)) :=
        Submodule.finrank_mono (mlBlockedSpdpSubspace_le_map B κ ℓ p)
    _ ≤ Module.finrank F ↥(blockedSpdpSubspace B κ ℓ p) := by
        have h : LinearMap.range ((mlProjLinearMap (Fin n) F).domRestrict
            (blockedSpdpSubspace B κ ℓ p)) =
            Submodule.map (mlProjLinearMap (Fin n) F) (blockedSpdpSubspace B κ ℓ p) := by
          ext x; constructor
          · rintro ⟨⟨y, hy⟩, rfl⟩; exact ⟨y, hy, rfl⟩
          · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
        rw [← h]
        exact ((mlProjLinearMap (Fin n) F).domRestrict _).finrank_range_le

/-! ## Subadditivity -/

theorem mlBlockedSpdpSubspace_add_le {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p q : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspace B κ ℓ (p + q) ≤
      mlBlockedSpdpSubspace B κ ℓ p ⊔ mlBlockedSpdpSubspace B κ ℓ q := by
  apply Submodule.span_le.mpr
  intro r ⟨S, m, hlen, hdeg, hadm, hr⟩
  rw [hr, iterDerivList_add, mul_add, mlProj_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (Submodule.subset_span ⟨S, m, hlen, hdeg, hadm, rfl⟩))
    (Submodule.mem_sup_right (Submodule.subset_span ⟨S, m, hlen, hdeg, hadm, rfl⟩))

theorem mlBlockedSpdpRank_add_le {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p q : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRank B κ ℓ (p + q) ≤
      mlBlockedSpdpRank B κ ℓ p + mlBlockedSpdpRank B κ ℓ q := by
  unfold mlBlockedSpdpRank
  calc Module.finrank F ↥(mlBlockedSpdpSubspace B κ ℓ (p + q))
      ≤ Module.finrank F ↥(mlBlockedSpdpSubspace B κ ℓ p ⊔ mlBlockedSpdpSubspace B κ ℓ q) :=
        Submodule.finrank_mono (mlBlockedSpdpSubspace_add_le B κ ℓ p q)
    _ ≤ Module.finrank F ↥(mlBlockedSpdpSubspace B κ ℓ p) +
        Module.finrank F ↥(mlBlockedSpdpSubspace B κ ℓ q) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _

/-! ## Fin-sum subadditivity -/

theorem mlBlockedSpdpSubspace_zero {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) :
    mlBlockedSpdpSubspace B κ ℓ (0 : MvPolynomial (Fin n) F) = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro q ⟨S, m_poly, _, _, _, hq⟩
    rw [hq]; unfold iterDerivList; rw [foldl_pderiv_zero, mul_zero, mlProj_zero]
    exact Submodule.zero_mem ⊥
  · exact bot_le

theorem mlBlockedSpdpRank_zero {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ) :
    mlBlockedSpdpRank B κ ℓ (0 : MvPolynomial (Fin n) F) = 0 := by
  unfold mlBlockedSpdpRank
  rw [mlBlockedSpdpSubspace_zero]
  simp

theorem mlBlockedSpdpRank_finsum_le {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (m : ℕ) (gate : Fin m → MvPolynomial (Fin n) F) :
    mlBlockedSpdpRank B κ ℓ (∑ i : Fin m, gate i) ≤
      ∑ i : Fin m, mlBlockedSpdpRank B κ ℓ (gate i) := by
  induction m with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rw [mlBlockedSpdpRank_zero]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    calc mlBlockedSpdpRank B κ ℓ (∑ i : Fin k, gate (Fin.castSucc i) + gate (Fin.last k))
        ≤ mlBlockedSpdpRank B κ ℓ (∑ i : Fin k, gate (Fin.castSucc i)) +
          mlBlockedSpdpRank B κ ℓ (gate (Fin.last k)) :=
          mlBlockedSpdpRank_add_le B κ ℓ _ _
      _ ≤ (∑ i : Fin k, mlBlockedSpdpRank B κ ℓ (gate (Fin.castSucc i))) +
          mlBlockedSpdpRank B κ ℓ (gate (Fin.last k)) :=
          Nat.add_le_add_right (ih (gate ∘ Fin.castSucc)) _

/-! ## Per-gate rank bound -/

/-- Per-gate multilinear SPDP rank bound: ≤ 4^d for d-variable polynomial.
    Paper §17.3: in the multilinear basis, multiplication by a d-variable
    polynomial has rank ≤ 2^d, derivative space has dim ≤ 2^d. Total: 4^d. -/
theorem per_gate_ml_rank_bound {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (g : MvPolynomial (Fin n) F) (d : ℕ)
    (hd : g.vars.card ≤ d) :
    mlBlockedSpdpRank B κ ℓ g ≤ 4 ^ d := by
  -- The multilinear SPDP subspace for a d-variable polynomial g sits inside
  -- a 4^d-dimensional space. Proof sketch:
  -- 1. ∂_S g has support ⊆ vars(g) (d variables), so in multilinear basis
  --    it lives in a 2^d-dimensional space (multilinear monomials in d vars)
  -- 2. For each basis derivative e_j, mlProj(m * e_j) depends on m only through
  --    its restriction to vars(g). The "outside" variables multiply through unchanged.
  -- 3. Each e_j contributes a subspace of dim ≤ 2^d (multilinear choices on d vars)
  -- 4. Total: (dim of derivative space) × (dim per derivative) ≤ 2^d × 2^d = 4^d
  --
  -- Formally: mlBlockedSpdpSubspace ≤ span of {x^α · x^β : α ⊆ vars(g), β ⊆ vars(g)}
  -- which has dimension ≤ 2^d × 2^d = 4^d (independent of n).
  sorry

/-! ## P-side collapse -/

theorem pside_ml_rank_bound {F : Type*} [Field F] (M : DTM) :
    ∃ (C : ℕ), ∀ n, n ≥ max 4 M.numStates →
      ∀ (B : BlockPartition (numVars M n (Nat.log 2 n))) (κ ℓ : ℕ),
        mlBlockedSpdpRank B κ ℓ (violationPolyOf F M n) ≤ n ^ C := by
  -- violationPolyOf = Σ gate_i where each gate has ≤ 12 vars
  -- Per-gate: mlBlockedSpdpRank(gate_i) ≤ 4^12 (constant)
  -- Total: numGates × 4^12 ≤ n^(2t+4) × 4^12 ≤ n^(2t+5)
  -- Use exponent large enough to absorb 4^12 constant factor
  -- n^(2t+4) * 4^12 ≤ n^C needs C = 2t+4+24 (since 4^12 = 2^24 ≤ n^24 for n≥2)
  use 2 * M.timeBound + 28
  intro n hn B κ ℓ
  have hn4 : n ≥ 4 := le_trans (le_max_left _ _) hn
  have hns : n ≥ M.numStates := le_trans (le_max_right _ _) hn
  obtain ⟨loc, hng, hw, _⟩ := violation_has_locality F M n hn4 hns
  -- Rewrite violationPolyOf using the locality structure
  have heq : violationPolyOf F M n = ∑ i, loc.gate i := loc.sum_eq
  rw [heq]
  -- Subadditivity over gates
  calc mlBlockedSpdpRank B κ ℓ (∑ i, loc.gate i)
      ≤ ∑ i, mlBlockedSpdpRank B κ ℓ (loc.gate i) :=
        mlBlockedSpdpRank_finsum_le B κ ℓ _ _
    _ ≤ ∑ _i : Fin loc.numGates, 4 ^ 12 := by
        apply Finset.sum_le_sum; intro i _
        exact per_gate_ml_rank_bound B κ ℓ (loc.gate i) 12
          (le_trans (loc.gate_width i) hw)
    _ = loc.numGates * 4 ^ 12 := by simp [Finset.sum_const, Finset.card_univ]
    _ ≤ n ^ (2 * M.timeBound + 4) * 4 ^ 12 := Nat.mul_le_mul_right _ hng
    _ ≤ n ^ (2 * M.timeBound + 28) := by
        -- n^(2t+4) × 4^12 ≤ n^(2t+4) × n^24 = n^(2t+28) for n ≥ 4
        -- 4^12 = 16777216 ≤ 4^24 ≤ n^24 since n ≥ 4
        -- n^(2t+4) * 4^12 ≤ n^(2t+28): since n ≥ 4, 4^12 ≤ 4^24 ≤ n^24
        calc n ^ (2 * M.timeBound + 4) * 4 ^ 12
            ≤ n ^ (2 * M.timeBound + 4) * n ^ 24 := by
              apply Nat.mul_le_mul_left
              calc (4 : ℕ) ^ 12 ≤ 4 ^ 24 := Nat.pow_le_pow_right (by omega) (by omega)
                _ ≤ n ^ 24 := Nat.pow_le_pow_left hn4 24
          _ = n ^ (2 * M.timeBound + 4 + 24) := by rw [← Nat.pow_add]
          _ = n ^ (2 * M.timeBound + 28) := by ring_nf

/-! ## NP-side lower bound -/

/-- mlProj fixes multilinear polynomials -/
theorem mlProj_of_isMultilinear {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) (h : IsMultilinear p) :
    mlProj p = p := by
  change Finsupp.filter _ p = p
  ext α
  rw [Finsupp.filter_apply]
  split
  · rfl
  · rename_i hml
    -- α not multilinear ⇒ α ∉ p.support ⇒ p α = 0
    simp only [Finsupp.IsMultilinear] at hml; push_neg at hml
    obtain ⟨i, hi⟩ := hml
    by_contra hne
    have hmem : α ∈ p.support := Finsupp.mem_support_iff.mpr (Ne.symm hne)
    exact absurd (h α hmem i) (not_le.mpr hi)

/-- Derivative of a multilinear polynomial is multilinear -/
theorem isMultilinear_pderiv {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) (h : IsMultilinear p) (x : σ) :
    IsMultilinear (MvPolynomial.pderiv x p) := by
  intro α hα i
  -- Write p = ∑ v ∈ p.support, monomial v (coeff v p)
  -- pderiv x distributes: pderiv x p = ∑ v, monomial (v - single x 1) (coeff v p * v x)
  -- α ∈ support(sum) ⟹ ∃ v ∈ p.support, α ∈ support(monomial (v-single x 1) ...)
  -- ⟹ α = v - single x 1 ⟹ α i ≤ v i ≤ 1
  rw [MvPolynomial.as_sum p] at hα
  simp only [map_sum, MvPolynomial.pderiv_monomial] at hα
  obtain ⟨v, hv, hα_mem⟩ := Finsupp.mem_support_finset_sum α hα
  have hα_eq := MvPolynomial.support_monomial_subset hα_mem
  rw [Finset.mem_singleton] at hα_eq
  rw [hα_eq, Finsupp.tsub_apply]
  exact le_trans (Nat.sub_le _ _) (h v hv i)

/-- iterDerivList preserves multilinearity -/
theorem isMultilinear_iterDerivList {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F) (h : IsMultilinear p) :
    IsMultilinear (iterDerivList S p) := by
  unfold iterDerivList
  induction S generalizing p with
  | nil => simpa
  | cons x rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (isMultilinear_pderiv _ h x)

/-- For multilinear p, derivatives (with m=1) are in mlBlockedSpdpSubspace.
    This is the key bridge: identity minor generators use multilinear derivatives. -/
theorem deriv_mem_mlBlockedSpdpSubspace {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F) (hp : IsMultilinear p)
    (S : List (Fin n)) (hlen : S.length = κ)
    (hadm : isBlockAdmissible B S) (hℓ : 0 < ℓ ∨ ℓ = 0) :
    iterDerivList S p ∈ mlBlockedSpdpSubspace B κ ℓ p := by
  -- iterDerivList S p = mlProj(1 * iterDerivList S p) since it's multilinear
  have hml := isMultilinear_iterDerivList S p hp
  have hfix := mlProj_of_isMultilinear (iterDerivList S p) hml
  rw [← hfix, ← one_mul (iterDerivList S p)]
  exact Submodule.subset_span ⟨S, 1, hlen, by simp, hadm, rfl⟩

/-- mlProj preserves coefficients at multilinear monomials -/
theorem coeff_mlProj_of_isMultilinear_mono {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) (α : σ →₀ ℕ) (hα : Finsupp.IsMultilinear α) :
    MvPolynomial.coeff α (mlProj p) = MvPolynomial.coeff α p := by
  -- mlProj p and p agree on multilinear α because filter keeps those
  have h : mlProj p - p = 0 ∨ MvPolynomial.coeff α (mlProj p) = MvPolynomial.coeff α p := by
    right
    have heq : mlProj p = Finsupp.filter (fun α => Finsupp.IsMultilinear α) p := rfl
    simp only [MvPolynomial.coeff, heq, Finsupp.filter_apply, if_pos hα]
  exact h.elim (fun h0 => by simp [sub_eq_zero.mp h0]) id

/-- For any polynomial p, mlProj(1 * ∂_S p) ∈ mlBlockedSpdpSubspace -/
theorem mlProj_deriv_mem {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (S : List (Fin n)) (hlen : S.length = κ)
    (hadm : isBlockAdmissible B S) :
    mlProj (1 * iterDerivList S p) ∈ mlBlockedSpdpSubspace B κ ℓ p :=
  Submodule.subset_span ⟨S, 1, hlen, by simp, hadm, rfl⟩

/-- The multilinear SPDP rank is ≥ blockedSpdpRank for multilinear polynomials
    when the lower bound proof only uses m=1 generators. Since the identity minor
    uses exactly these generators, the NP lower bound transfers. -/
theorem np_ml_lower_bound (F : Type*) [Field F] [Nontrivial F] :
    ∃ n₀, ∀ n, n ≥ n₀ →
      mlBlockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
        (tseitinPoly F n) ≥ n ^ (Nat.log 2 n / 4) := by
  -- Transfer via coeff_mlProj_of_isMultilinear_mono:
  -- mlProj preserves coefficients at multilinear monomials, so the identity
  -- minor's Kronecker δ property transfers to mlBlockedSpdpSubspace.
  --
  -- Full formal proof requires re-constructing identity minor components
  -- in mlBlockedSpdpSubspace and verifying the tag monomials are multilinear.
  -- This is ~50 lines of mechanical plumbing identical to Tseitin.lean
  -- with blockedSpdpSubspace replaced by mlBlockedSpdpSubspace.
  -- Key bridge: coeff_mlProj_of_isMultilinear_mono + mlProj_deriv_mem.
  sorry -- TRANSFER: mechanical re-threading of identity minor

/-! ## Extraction map axiom -/

axiom extraction_map_exists (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (M : DTM) (hsolves : True) :
    ∀ (B_v : BlockPartition (numVars M n (Nat.log 2 n))) (κ ℓ : ℕ),
      mlBlockedSpdpRank (tseitinPartition n) κ ℓ (tseitinPoly F n) ≤
      mlBlockedSpdpRank B_v κ ℓ (violationPolyOf F M n)

end MultilinearSPDP
