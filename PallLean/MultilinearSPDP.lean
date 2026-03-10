/-
  MultilinearSPDP.lean — SPDP rank in the multilinear (Boolean) basis

  Paper Definition 12: The SPDP matrix uses multilinear monomials (mod ⟨x²_i - x_i⟩).
  We define multilinear SPDP rank as dim of span of mlProj-ed generators.
-/
import PallLean.SPDPDefs
import PallLean.NPWitness
import PallLean.Compiler
import PallLean.IdentityMinor
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace MultilinearSPDP

open MvPolynomial SPDP TuringMachine Compiler NPWitness Tseitin

attribute [local instance] Classical.dec

/-! ## Multilinear Projection -/

/-- A polynomial is multilinear if every variable has degree ≤ 1. -/
def IsMultilinear {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) : Prop :=
  ∀ α ∈ p.support, ∀ i, α i ≤ 1

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

/-- Coarser partitions have smaller SPDP subspaces.
    If B₁.assign i = B₁.assign j → B₂.assign i = B₂.assign j
    (i.e. B₂ is coarser than B₁), then B₂-admissible → B₁-admissible,
    so subspace(B₂) ⊆ subspace(B₁). -/
theorem mlBlockedSpdpSubspace_mono_partition {n : ℕ} {F : Type*} [CommRing F]
    (B₁ B₂ : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (hrefine : ∀ i j : Fin n, B₁.assign i = B₁.assign j → B₂.assign i = B₂.assign j) :
    mlBlockedSpdpSubspace B₂ κ ℓ p ≤ mlBlockedSpdpSubspace B₁ κ ℓ p := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hadm, hq⟩
  apply Submodule.subset_span
  exact ⟨S, m, hlen, hdeg, isBlockAdmissible_coarsen B₁ B₂ S hrefine hadm, hq⟩

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

-- pside_ml_rank_bound (old, tableau-only) archived — replaced by pside_full_ml_rank_bound

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

/-- mlProj of rowPoly is in mlBlockedSpdpSubspace.
    rowPoly = iterDerivList (selectorList) (coupledVerifier) = 1 * iterDerivList S p,
    so mlProj(1 * iterDerivList S p) is a generator of mlBlockedSpdpSubspace. -/
theorem rowPoly_mem_ml_subspace [Field F]
    (Φ : TseitinFormula) (B : BlockPartition (tseitinNumVars Φ))
    (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ))
    (hB : ∀ (cs : List (Fin Φ.clauses.length)),
      cs.Nodup → (∀ c ∈ cs, c ∈ pack.selected) → cs.length = κ →
      isBlockAdmissible B (cs.map (selectorIdx Φ))) :
    mlProj (IdentityMinor.rowPoly F Φ pack κ i) ∈
      mlBlockedSpdpSubspace B κ ℓ (coupledVerifier F Φ) := by
  -- rowPoly = iterDerivList (selectorList) (coupledVerifier)
  -- mlProj(1 * iterDerivList S p) is a generator of mlBlockedSpdpSubspace
  have h1 : IdentityMinor.rowPoly F Φ pack κ i =
      1 * iterDerivList (IdentityMinor.selectorList Φ pack κ i) (coupledVerifier F Φ) := by
    unfold IdentityMinor.rowPoly; rw [one_mul]
  rw [h1]
  apply Submodule.subset_span
  refine ⟨IdentityMinor.selectorList Φ pack κ i, 1, ?_, ?_, ?_, rfl⟩
  · -- length = κ
    show (IdentityMinor.selectorList Φ pack κ i).length = κ
    unfold IdentityMinor.selectorList
    rw [List.length_map]
    exact IdentityMinor.getSubset_length pack κ i
  · -- deg ≤ ℓ
    simp [MvPolynomial.totalDegree_one]
  · -- admissible
    show isBlockAdmissible B (IdentityMinor.selectorList Φ pack κ i)
    unfold IdentityMinor.selectorList
    exact hB _ (IdentityMinor.getSubset_nodup pack κ i)
      (IdentityMinor.getSubset_subset pack κ i)
      (IdentityMinor.getSubset_length pack κ i)

/-- Tag monomials from disjoint packing are multilinear: each variable has exponent ≤ 1.
    Follows from: (1) each clause contributes single v 1 for 3 distinct variables,
    (2) the disjoint packing ensures selected clauses use disjoint variable sets. -/
theorem tagMono_isMultilinear {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    Finsupp.IsMultilinear (IdentityMinor.tagMono F Φ pack κ i) := by
  exact IdentityMinor.tagMono_le_one (F := F) Φ pack κ i

/-- General rank-from-linear-independence for any finite-dimensional submodule -/
private theorem finrank_ge_of_linearIndependent {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Nontrivial R]
    (V : Submodule R M) [Module.Finite R V]
    (k : ℕ) (elements : Fin k → V)
    (hli : LinearIndependent R (Subtype.val ∘ elements)) :
    Module.finrank R V ≥ k := by
  have hrange : ∀ i, (Subtype.val ∘ elements) i ∈ V := fun i => (elements i).2
  have hspan : Submodule.span R (Set.range (Subtype.val ∘ elements)) ≤ V :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hrange)
  have hcard := finrank_span_eq_card hli
  haveI : Module.Finite R (Submodule.span R (Set.range (Subtype.val ∘ elements))) :=
    Module.Finite.span_of_finite R (Set.finite_range _)
  have hmono := Submodule.finrank_mono hspan
  simp [Fintype.card_fin] at hcard
  omega

theorem np_ml_lower_bound (F : Type*) [Field F] [Nontrivial F] :
    ∃ n₀, ∀ n, n ≥ n₀ →
      mlBlockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
        (tseitinPoly F n) ≥ n ^ (Nat.log 2 n / 4) := by
  -- Follow the same structure as np_side_lb, but with mlBlockedSpdpRank
  obtain ⟨n₀, hn₀⟩ := NPWitness.binomial_lower_bound
  use max n₀ (2^10)
  intro n hn
  have hn₀' : n ≥ n₀ := le_trans (le_max_left _ _) hn
  have hn1024 : n ≥ 2^10 := le_trans (le_max_right _ _) hn
  have hv := tseitinAt_vertices n (by omega)
  have pack := Tseitin.disjoint_packing_exists (tseitinAt n) (by omega)
  -- Get identity minor components (R in blockedSpdpSubspace, τ, signs)
  let κ := Nat.log 2 n
  have hκ : κ ≤ pack.selected.length := by
    have hps := pack.size_bound; rw [hv] at hps
    exact (log2_le_div30 n (by linarith [show (2:ℕ)^10 = 1024 from by norm_num])).trans hps
  let c := IdentityMinor.identity_minor_components (F := F) (tseitinAt n) pack κ κ hκ
  obtain ⟨hsigns, hkron⟩ := IdentityMinor.identity_minor_components_signs
    (tseitinAt n) pack κ κ hκ (F := F)
  -- Lift R to mlBlockedSpdpSubspace via mlProj
  let mlV := mlBlockedSpdpSubspace (tseitinPartition n) κ κ (tseitinPoly F n)
  have hmem : ∀ i, mlProj (c.1 i).val ∈ mlV :=
    fun i => rowPoly_mem_ml_subspace (tseitinAt n) _ pack κ κ i
      (fun cs hnd _ _ => IdentityMinor.tseitinPartition_admissible_general (tseitinAt n) cs hnd)
  let R' : Fin (Nat.choose pack.selected.length κ) → ↥mlV :=
    fun i => ⟨mlProj (c.1 i).val, hmem i⟩
  -- Kronecker transfer: coeff(τ_j, mlProj(R_i)) = coeff(τ_j, R_i) via multilinear tags
  have hkron' : ∀ i j, MvPolynomial.coeff (c.2.1 i) (R' j).val =
      if i = j then c.2.2 i else 0 := by
    intro i j
    show MvPolynomial.coeff (c.2.1 i) (mlProj (c.1 j).val) = _
    -- c.2.1 i = tagMono F (tseitinAt n) pack κ i — need IsMultilinear
    have hml : Finsupp.IsMultilinear (c.2.1 i) := by
      show Finsupp.IsMultilinear (IdentityMinor.tagMono F (tseitinAt n) pack κ i)
      exact tagMono_isMultilinear (tseitinAt n) pack κ i
    rw [coeff_mlProj_of_isMultilinear_mono _ _ hml]
    exact hkron i j
  -- Linear independence via Kronecker δ (same proof as identity_minor_lower_bound_aux)
  have hli : LinearIndependent F (Subtype.val ∘ R') := by
    rw [linearIndependent_iff']
    intro S g hg a ha
    have h0 : (coeffLin F (c.2.1 a))
        (∑ j ∈ S, g j • (Subtype.val ∘ R') j) = 0 := by rw [hg]; exact map_zero _
    simp only [map_sum, LinearMap.map_smul, Function.comp, smul_eq_mul] at h0
    simp only [coeffLin, LinearMap.coe_mk, AddHom.coe_mk] at h0
    have hsub : ∀ j ∈ S, g j * MvPolynomial.coeff (c.2.1 a) (R' j).val =
        if j = a then g j * c.2.2 a else 0 := by
      intro j _
      rw [hkron' a j]
      by_cases h : a = j
      · subst h; simp
      · simp [h, show j ≠ a from fun h' => h (h' ▸ rfl)]
    rw [Finset.sum_congr rfl hsub, Finset.sum_ite_eq' S a, if_pos ha] at h0
    rcases hsigns a with hs | hs <;> rw [hs] at h0 <;> simp at h0 <;> exact h0
  -- Conclude: finrank ≥ k
  have hfr := finrank_ge_of_linearIndependent mlV _ R' hli
  calc mlBlockedSpdpRank (tseitinPartition n) κ κ (tseitinPoly F n) ≥
        Nat.choose pack.selected.length κ := hfr
    _ ≥ Nat.choose (n / 30) κ := by
        apply Nat.choose_le_choose
        have := pack.size_bound; rw [hv] at this; exact this
    _ ≥ n ^ (Nat.log 2 n / 4) := hn₀ n hn₀'

/-! ## Restriction monotonicity for SPDP rank -/

/-- Restriction map: given injection f : Fin n ↪ Fin m, restrict p from Fin m to Fin n
    by evaluating non-image variables to 0 and mapping image variables back.
    Formally: aeval (fun j : Fin m => if j ∈ Set.range f then X (f.invFun j) else 0) -/
noncomputable def restrictPoly {n m : ℕ} (F : Type*) [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f) :
    MvPolynomial (Fin m) F →ₐ[F] MvPolynomial (Fin n) F :=
  MvPolynomial.aeval (fun j =>
    if h : ∃ i, f i = j then MvPolynomial.X h.choose
    else 0)

/-- Block partition pullback along an injection -/
noncomputable def pullbackPartition {n m : ℕ}
    (B : BlockPartition m) (f : Fin n → Fin m) : BlockPartition n where
  numBlocks := B.numBlocks
  assign := fun i => B.assign (f i)

/-! ## Extraction map (Paper §34, Lemma 40) -/

/-- restrictPoly applied to X j gives X (f⁻¹ j) if j ∈ range f, else 0 -/
theorem restrictPoly_X {n m : ℕ} (F : Type*) [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f) (j : Fin m) :
    restrictPoly F f hf (MvPolynomial.X j) =
      if h : ∃ i, f i = j then MvPolynomial.X h.choose else 0 := by
  unfold restrictPoly; simp [MvPolynomial.aeval_X]

/-- The choose from restrictPoly is the unique preimage -/
theorem restrictPoly_choose_spec {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (j : Fin m) (h : ∃ i, f i = j) : f h.choose = j := h.choose_spec

theorem restrictPoly_choose_eq {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (i : Fin n) : (⟨i, rfl⟩ : ∃ k, f k = f i).choose = i := by
  have := (⟨i, rfl⟩ : ∃ k, f k = f i).choose_spec
  exact hf this

/-- Chain rule: pderiv i (restrictPoly p) = restrictPoly (pderiv (f i) p) -/
theorem pderiv_restrictPoly {n m : ℕ} (F : Type*) [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (i : Fin n) (p : MvPolynomial (Fin m) F) :
    MvPolynomial.pderiv i (restrictPoly F f hf p) =
    restrictPoly F f hf (MvPolynomial.pderiv (f i) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [restrictPoly, MvPolynomial.pderiv_C, map_zero]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p j ih =>
    -- Goal: pderiv i (rP p * rP (X j)) = rP (pderiv (f i) (p * X j))
    -- where rP = restrictPoly F f hf
    -- Expand RHS: rP (pderiv (f i) p * X j + p * pderiv (f i) (X j))
    rw [MvPolynomial.pderiv_mul]
    rw [map_add (restrictPoly F f hf), map_mul (restrictPoly F f hf), map_mul (restrictPoly F f hf)]
    -- Expand LHS: pderiv i (rP p) * rP (X j) + rP p * pderiv i (rP (X j))
    rw [MvPolynomial.pderiv_mul]
    -- Use IH on first term
    rw [ih]
    -- Remains: rP p * pderiv i (rP (X j)) = rP p * rP (pderiv (f i) (X j))
    congr 1
    -- Show: pderiv i (rP (X j)) = rP (pderiv (f i) (X j))
    rw [MvPolynomial.pderiv_X (f i) j]
    simp only [Pi.single_apply]
    by_cases hfi : f i = j
    · -- f i = j, goal involves `if f i = j then 1 else 0`
      subst hfi
      -- Now j is gone, replaced by f i
      simp only [if_pos rfl, map_one]
      have hj : ∃ k, f k = f i := ⟨i, rfl⟩
      simp only [restrictPoly_X, dif_pos hj]
      rw [MvPolynomial.pderiv_X]
      simp only [Pi.single_apply]
      have : hj.choose = i := hf hj.choose_spec
      rw [this, if_pos rfl]; simp
    · -- f i ≠ j
      rw [if_neg (Ne.symm hfi)]
      -- Goal: rP p * pderiv i (rP (X j)) = rP (p * 0)
      simp only [mul_zero, map_zero]
      -- Goal: rP p * pderiv i (rP (X j)) = 0
      by_cases hj : ∃ k, f k = j
      · simp only [restrictPoly_X, dif_pos hj]
        -- pderiv i (X hj.choose) where hj.choose ≠ i
        rw [MvPolynomial.pderiv_X, Pi.single_apply]
        have : hj.choose ≠ i := fun h => hfi (by rw [← hj.choose_spec, h])
        rw [if_neg this]; simp
      · simp only [restrictPoly_X, dif_neg hj, map_zero, mul_zero]

/-- Iterated chain rule -/
theorem iterDerivList_restrictPoly {n m : ℕ} (F : Type*) [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (S : List (Fin n)) (p : MvPolynomial (Fin m) F) :
    iterDerivList S (restrictPoly F f hf p) =
    restrictPoly F f hf (iterDerivList (S.map f) p) := by
  unfold iterDerivList
  induction S generalizing p with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl, List.map]
    rw [pderiv_restrictPoly F f hf a]
    exact ih (MvPolynomial.pderiv (f a) p)

/-- restrictPoly is a left inverse to rename f -/
theorem restrictPoly_rename {n m : ℕ} (F : Type*) [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f) (p : MvPolynomial (Fin n) F) :
    restrictPoly F f hf (MvPolynomial.rename f p) = p := by
  unfold restrictPoly
  rw [MvPolynomial.aeval_rename]
  have : (fun j => if h : ∃ k, f k = j then MvPolynomial.X h.choose else 0) ∘ f =
         fun i => (MvPolynomial.X i : MvPolynomial (Fin n) F) := by
    ext i; simp only [Function.comp]
    have h : ∃ k, f k = f i := ⟨i, rfl⟩
    simp only [dif_pos h]; rw [show h.choose = i from hf h.choose_spec]
  rw [this, MvPolynomial.aeval_X_left]; simp

/-- restrictPoly commutes with multiplication by renamed polynomials -/
theorem restrictPoly_mul_rename {n m : ℕ} (F : Type*) [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (mul : MvPolynomial (Fin n) F) (q : MvPolynomial (Fin m) F) :
    restrictPoly F f hf (MvPolynomial.rename f mul * q) =
    mul * restrictPoly F f hf q := by
  rw [map_mul, restrictPoly_rename F f hf mul]

/-- mlProj of a monomial: keeps it if multilinear, drops if not -/
theorem mlProj_monomial {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (s : σ →₀ ℕ) (a : F) :
    mlProj (MvPolynomial.monomial s a) =
    if Finsupp.IsMultilinear s then MvPolynomial.monomial s a else 0 := by
  -- mlProj = Finsupp.filter IsMultilinear
  -- filter p (monomial s a) keeps coeff at d iff p d, so:
  -- coeff d (filter p (monomial s a)) = if p d ∧ d = s then a else 0
  show Finsupp.filter (fun α => Finsupp.IsMultilinear α) (MvPolynomial.monomial s a) = _
  ext d
  rw [Finsupp.filter_apply]
  -- LHS: if IsMultilinear d then coeff d (monomial s a) else 0
  -- RHS: coeff d (if IsMultilinear s then monomial s a else 0)
  -- coeff d (monomial s a) = if d = s then a else 0
  change (if Finsupp.IsMultilinear d then MvPolynomial.coeff d (MvPolynomial.monomial s a) else 0) =
         MvPolynomial.coeff d (if Finsupp.IsMultilinear s then MvPolynomial.monomial s a else 0)
  rw [MvPolynomial.coeff_monomial]
  by_cases hml_s : Finsupp.IsMultilinear s
  · simp only [if_pos hml_s]
    rw [MvPolynomial.coeff_monomial]
    by_cases hds : d = s
    · subst hds; simp [hml_s]
    · rw [if_neg (Ne.symm hds)]; simp
  · simp only [if_neg hml_s, map_zero, MvPolynomial.coeff_zero]
    by_cases hds : d = s
    · subst hds; simp [hml_s]
    · rw [if_neg (Ne.symm hds)]; simp

/-- restrictPoly on a monomial is either 0 or a monomial with pulled-back exponents.
    This is the key structural lemma for mlProj_restrictPoly. -/
theorem restrictPoly_monomial_form {n m : ℕ} (F : Type*) [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f) (s : Fin m →₀ ℕ) (a : F) :
    (restrictPoly F f hf (MvPolynomial.monomial s a) = 0) ∨
    (∃ t : Fin n →₀ ℕ, restrictPoly F f hf (MvPolynomial.monomial s a) =
      MvPolynomial.monomial t a ∧ (∀ i, t i = s (f i)) ∧
      (∀ j ∈ s.support, j ∈ Set.range f)) := by
  by_cases h_range : ∀ j ∈ s.support, j ∈ Set.range f
  · -- All vars in range f: rP(monomial s a) = monomial t a
    right
    -- Build t : Fin n →₀ ℕ with t i = s(f i)
    refine ⟨Finsupp.equivFunOnFinite.symm (fun i => s (f i)), ?_, fun i => by simp, h_range⟩
    -- restrictPoly (monomial s a) = monomial t a
    -- Key: monomial s a = rename f (monomial t a) when support s ⊆ range f
    -- and t i = s(f i), so mapDomain f t = s on support
    -- Show: restrictPoly (monomial s a) = monomial t a
    -- where t = equivFunOnFinite.symm (fun i => s (f i))
    set t := Finsupp.equivFunOnFinite.symm (fun i => s (f i)) with ht_def
    -- Key: monomial s a = rename f (monomial t a) since mapDomain f t = s
    have ht_apply : ∀ i, t i = s (f i) := fun i => by simp [ht_def]
    have h_map : Finsupp.mapDomain f t = s := by
      ext j
      by_cases hj : j ∈ Set.range f
      · obtain ⟨i, rfl⟩ := hj
        rw [Finsupp.mapDomain_apply hf, ht_apply]
      · -- j ∉ range f: mapDomain f t j = 0 and s j = 0
        have hsj : s j = 0 := by
          by_contra h
          exact hj (h_range j (Finsupp.mem_support_iff.mpr h))
        rw [hsj]
        rw [Finsupp.mapDomain, Finsupp.sum_apply]
        apply Finset.sum_eq_zero
        intro i _
        simp only [Finsupp.single_apply, if_neg (show f i ≠ j from fun h => hj ⟨i, h⟩)]
    rw [show MvPolynomial.monomial s a =
        MvPolynomial.rename f (MvPolynomial.monomial t a) from by
      rw [MvPolynomial.rename_monomial, h_map]]
    exact restrictPoly_rename F f hf _
  · -- Some var not in range f: result is 0
    left
    push_neg at h_range
    obtain ⟨j, hj_supp, hj_range⟩ := h_range
    -- restrictPoly = aeval g where g j = X(f⁻¹ j) or 0
    -- aeval g (monomial s a) = C a * ∏_{j ∈ s.support} g(j)^(s j)
    -- g(j) = 0 since j ∉ range f, so 0^(s j) = 0, product = 0
    unfold restrictPoly
    rw [MvPolynomial.aeval_monomial]
    apply mul_eq_zero_of_right
    unfold Finsupp.prod
    apply Finset.prod_eq_zero hj_supp
    simp only [dif_neg (show ¬∃ i, f i = j from fun ⟨i, hi⟩ => hj_range ⟨i, hi⟩)]
    exact zero_pow (Finsupp.mem_support_iff.mp hj_supp)

/-- If rP(monomial s a) = monomial t a with t i = s(f i), then IsMultilinear t ↔ IsMultilinear s -/
theorem isMultilinear_pullback {n m : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f)
    (s : Fin m →₀ ℕ) (t : Fin n →₀ ℕ) (ht : ∀ i, t i = s (f i))
    (hs_range : ∀ j ∈ s.support, j ∈ Set.range f) :
    Finsupp.IsMultilinear t ↔ Finsupp.IsMultilinear s := by
  constructor
  · intro hml j
    by_cases hj : j ∈ s.support
    · obtain ⟨i, rfl⟩ := hs_range j hj
      exact ht i ▸ hml i
    · simp only [Finsupp.mem_support_iff, not_not] at hj
      rw [hj]; exact Nat.zero_le 1
  · intro hml i
    rw [ht]; exact hml (f i)

/-- restrictPoly commutes with mlProj -/
theorem mlProj_restrictPoly {n m : ℕ} (F : Type*) [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (p : MvPolynomial (Fin m) F) :
    mlProj (restrictPoly F f hf p) = restrictPoly F f hf (mlProj p) := by
  -- Strategy: reduce to monomials via as_sum, then use mlProj_monomial
  -- + the fact that rP(monomial s a) is either 0 or a monomial with
  -- IsMultilinear preserved (by injectivity of f).
  --
  -- Per-monomial claim: mlProj(rP(monomial s a)) = rP(mlProj(monomial s a))
  suffices key : ∀ (s : Fin m →₀ ℕ) (a : F),
      mlProj (restrictPoly F f hf (MvPolynomial.monomial s a)) =
      restrictPoly F f hf (mlProj (MvPolynomial.monomial s a)) by
    conv_lhs => rw [MvPolynomial.as_sum p]
    conv_rhs => rw [MvPolynomial.as_sum p]
    simp only [map_sum (restrictPoly F f hf)]
    change mlProjHom F (∑ x ∈ p.support, _) =
           (restrictPoly F f hf) (mlProjHom F (∑ v ∈ p.support, _))
    rw [map_sum (mlProjHom F), map_sum (mlProjHom F), map_sum (restrictPoly F f hf)]
    exact Finset.sum_congr rfl (fun s _ => key s (MvPolynomial.coeff s p))
  -- Prove the per-monomial claim
  intro s a
  rw [mlProj_monomial]
  by_cases hml : Finsupp.IsMultilinear s
  · -- IsMultilinear s: goal is mlProj(rP(monomial s a)) = rP(monomial s a)
    simp only [if_pos hml]
    cases restrictPoly_monomial_form F f hf s a with
    | inl h0 => simp [h0, mlProj]
    | inr h =>
      obtain ⟨t, ht, ht_eq, hs_range⟩ := h
      rw [ht]
      have hml_t : Finsupp.IsMultilinear t :=
        (isMultilinear_pullback f hf s t ht_eq hs_range).mpr hml
      rw [mlProj_monomial, if_pos hml_t]
  · -- ¬IsMultilinear s: goal is mlProj(rP(monomial s a)) = rP(0)
    simp only [if_neg hml]
    cases restrictPoly_monomial_form F f hf s a with
    | inl h0 => simp [h0, mlProj]
    | inr h =>
      obtain ⟨t, ht, ht_eq, hs_range⟩ := h
      rw [ht]
      have hml_t : ¬Finsupp.IsMultilinear t := fun h =>
        hml ((isMultilinear_pullback f hf s t ht_eq hs_range).mp h)
      rw [mlProj_monomial, if_neg hml_t]; unfold restrictPoly; simp

/-- restrictPoly is also an F-linear map on MvPolynomial -/
noncomputable def restrictPolyLinearMap {n m : ℕ} (F : Type*) [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f) :
    MvPolynomial (Fin m) F →ₗ[F] MvPolynomial (Fin n) F :=
  (restrictPoly F f hf).toLinearMap

/-- The small-side subspace is contained in the image of the big-side subspace
    under restrictPoly. -/
theorem mlBlockedSpdpSubspace_restrict_le_map {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : BlockPartition m) (κ ℓ : ℕ) (p : MvPolynomial (Fin m) F) :
    mlBlockedSpdpSubspace (pullbackPartition B f) κ ℓ (restrictPoly F f hf p) ≤
    Submodule.map (restrictPolyLinearMap F f hf) (mlBlockedSpdpSubspace B κ ℓ p) := by
  -- Each generator of the LHS is the image of a big-side element under rP
  apply Submodule.span_le.mpr
  intro q ⟨S, mul, hlen, hdeg, hadm, hq⟩
  simp only [Submodule.mem_map, SetLike.mem_coe]
  -- The preimage in the big space
  let S' := S.map f
  let q := iterDerivList S' p
  let mul' := MvPolynomial.rename f mul
  -- Candidate preimage: mlProj(mul' * q) in the big subspace
  refine ⟨mlProj (mul' * q), ?_, ?_⟩
  · -- mlProj(mul' * q) ∈ mlBlockedSpdpSubspace B κ ℓ p
    apply Submodule.subset_span
    exact ⟨S', mul', by simp [S', hlen], by
      exact le_trans (MvPolynomial.totalDegree_rename_le f mul) hdeg, by
      -- isBlockAdmissible B (S.map f) from isBlockAdmissible (pullback B f) S
      constructor
      · exact List.Nodup.map hf hadm.1
      · intro b
        -- (S.map f).filter (B.assign · = b) has same length as S.filter (pullback.assign · = b)
        have hfm : ∀ (L : List (Fin n)),
            (L.map f).filter (fun j => B.assign j = b) =
            (L.filter (fun i => B.assign (f i) = b)).map f := by
          intro L; induction L with
          | nil => simp
          | cons a rest ih =>
            simp only [List.map, List.filter]
            by_cases h : B.assign (f a) = b
            · simp [h, ih]
            · simp [h, ih]
        rw [hfm, List.length_map]
        exact hadm.2 b, rfl⟩
  · -- rP(mlProj(mul' * q)) = mlProj(mul * iterDerivList S (rP p))
    rw [show restrictPolyLinearMap F f hf (mlProj (mul' * q)) =
      restrictPoly F f hf (mlProj (mul' * q)) from rfl]
    rw [← mlProj_restrictPoly F f hf]
    rw [restrictPoly_mul_rename F f hf mul q]
    rw [← iterDerivList_restrictPoly F f hf S p]
    rw [hq]

/-- Restriction monotonicity for mlBlockedSpdpRank (Lemma 40(b)). -/
theorem restriction_rank_monotone (F : Type*) [Field F] [Nontrivial F]
    {n m : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : BlockPartition m) (κ ℓ : ℕ) (p : MvPolynomial (Fin m) F) :
    mlBlockedSpdpRank (pullbackPartition B f) κ ℓ (restrictPoly F f hf p) ≤
    mlBlockedSpdpRank B κ ℓ p := by
  unfold mlBlockedSpdpRank
  calc Module.finrank F (mlBlockedSpdpSubspace (pullbackPartition B f) κ ℓ (restrictPoly F f hf p))
      ≤ Module.finrank F (Submodule.map (restrictPolyLinearMap F f hf) (mlBlockedSpdpSubspace B κ ℓ p)) := by
        exact Submodule.finrank_mono (mlBlockedSpdpSubspace_restrict_le_map f hf B κ ℓ p)
    _ ≤ Module.finrank F (mlBlockedSpdpSubspace B κ ℓ p) :=
        Submodule.finrank_map_le _ _

/-- Adding a constant does not change mlBlockedSpdpRank when κ ≥ 1.
    Proof sketch: pderiv of C c = 0, so C c contributes nothing to
    any generator mlProj(m * iterDerivList S (p + C c)) when |S| = κ ≥ 1. -/
-- Helper: pderiv of constant is zero
private theorem pderiv_C {σ : Type*} {R : Type*} [CommSemiring R] [DecidableEq σ]
    (i : σ) (c : R) : MvPolynomial.pderiv i (MvPolynomial.C c) = 0 := by
  simp [MvPolynomial.pderiv_C]

-- Helper: foldl pderiv starting from 0 = 0
private theorem foldl_pderiv_zero' {n : ℕ} {F : Type*} [CommRing F]
    (l : List (Fin n)) :
    l.foldl (fun q i => MvPolynomial.pderiv i q) (0 : MvPolynomial (Fin n) F) = 0 := by
  induction l with
  | nil => simp
  | cons a rest ih => simp only [List.foldl, map_zero]; exact ih

-- Helper: iterDerivList of constant is zero when list nonempty
private theorem iterDerivList_C_eq_zero {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (c : F) (hS : S ≠ []) :
    iterDerivList S (MvPolynomial.C c) = (0 : MvPolynomial (Fin n) F) := by
  unfold iterDerivList
  cases S with
  | nil => exact absurd rfl hS
  | cons a rest =>
    simp only [List.foldl, pderiv_C]
    exact foldl_pderiv_zero' rest

-- Helper: foldl pderiv distributes over addition
private theorem foldl_pderiv_add {n : ℕ} {F : Type*} [CommRing F]
    (l : List (Fin n)) (p q : MvPolynomial (Fin n) F) :
    l.foldl (fun r i => MvPolynomial.pderiv i r) (p + q) =
    l.foldl (fun r i => MvPolynomial.pderiv i r) p +
    l.foldl (fun r i => MvPolynomial.pderiv i r) q := by
  induction l generalizing p q with
  | nil => simp
  | cons a rest ih => simp only [List.foldl]; rw [map_add]; exact ih _ _

-- Helper: iterDerivList distributes over addition
private theorem iterDerivList_add {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (p q : MvPolynomial (Fin n) F) :
    iterDerivList S (p + q) = iterDerivList S p + iterDerivList S q := by
  unfold iterDerivList; exact foldl_pderiv_add S p q

-- Helper: iterDerivList (p + C c) = iterDerivList p when S nonempty
private theorem iterDerivList_add_C {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F) (c : F) (hS : S ≠ []) :
    iterDerivList S (p + MvPolynomial.C c) = iterDerivList S p := by
  rw [iterDerivList_add, iterDerivList_C_eq_zero S c hS, add_zero]

theorem mlBlockedSpdpRank_add_const (F : Type*) [Field F] [Nontrivial F]
    {n : ℕ} (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) (c : F)
    (hκ : κ ≥ 1) :
    mlBlockedSpdpRank B κ ℓ (p + MvPolynomial.C c) = mlBlockedSpdpRank B κ ℓ p := by
  unfold mlBlockedSpdpRank
  -- Suffices: the subspaces are equal
  have hsub : mlBlockedSpdpSubspace B κ ℓ (p + MvPolynomial.C c) =
              mlBlockedSpdpSubspace B κ ℓ p := by
    unfold mlBlockedSpdpSubspace
    have hgen : ∀ (r : MvPolynomial (Fin n) F),
        (∃ S m, S.length = κ ∧ m.totalDegree ≤ ℓ ∧ isBlockAdmissible B S ∧
          r = mlProj (m * iterDerivList S (p + MvPolynomial.C c))) ↔
        (∃ S m, S.length = κ ∧ m.totalDegree ≤ ℓ ∧ isBlockAdmissible B S ∧
          r = mlProj (m * iterDerivList S p)) := by
      intro r; constructor <;> intro ⟨S, m, hlen, hdeg, hadm, hq⟩
      · exact ⟨S, m, hlen, hdeg, hadm, by
          rw [hq, iterDerivList_add_C S p c (by intro h; subst h; simp at hlen; omega)]⟩
      · exact ⟨S, m, hlen, hdeg, hadm, by
          rw [hq, iterDerivList_add_C S p c (by intro h; subst h; simp at hlen; omega)]⟩
    have hset : { q : MvPolynomial (Fin n) F | ∃ S m, S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        isBlockAdmissible B S ∧ q = mlProj (m * iterDerivList S (p + MvPolynomial.C c))} =
      { q | ∃ S m, S.length = κ ∧ m.totalDegree ≤ ℓ ∧ isBlockAdmissible B S ∧
        q = mlProj (m * iterDerivList S p)} := by
      ext q; exact hgen q
    rw [hset]
  rw [hsub]

/-- A coarser partition has smaller or equal SPDP rank.
    If B₁ refines B₂ (same block in B₂ implies same block in B₁), then
    B₂-admissible sequences are a subset of B₁-admissible sequences,
    so the B₂ subspace ⊆ B₁ subspace, hence rank(B₂) ≤ rank(B₁). -/
theorem mlBlockedSpdpRank_coarsen {n : ℕ} (F : Type*) [Field F] [Nontrivial F]
    (B₁ B₂ : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (hrefine : ∀ i j : Fin n, B₁.assign i = B₁.assign j → B₂.assign i = B₂.assign j) :
    mlBlockedSpdpRank B₂ κ ℓ p ≤ mlBlockedSpdpRank B₁ κ ℓ p := by
  -- B₂-admissible ⊆ B₁-admissible, so subspace(B₂) ⊆ subspace(B₁)
  unfold mlBlockedSpdpRank
  apply Submodule.finrank_mono
  apply mlBlockedSpdpSubspace_mono_partition
  exact hrefine

/-! ## Paper-faithful compiled polynomial (§34, Theorem 181)

The paper's compiled polynomial P_{M',n} = Q×_Φ(u) + R_{M',Φ}(v) consists of:
- The coupled verifier sheet Q× (tseitinPoly) on witness variables
- The tableau constraints R (violationPolyOf) on all variables -/

/-- Canonical inclusion of witness variables into compiled variable space. -/
noncomputable def witnessInclusion (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    Fin (npNumVars n) → Fin (numVars M n (Nat.log 2 n)) :=
  fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt h_le⟩

theorem witnessInclusion_injective (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    Function.Injective (witnessInclusion M n h_le) :=
  fun a b h => Fin.ext (Fin.mk.inj h)

/-- The coupled verifier sheet Q×_Φ embedded in the compiled variable space. -/
noncomputable def verifierSheetOf (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n : ℕ) (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    MvPolynomial (Fin (numVars M n (Nat.log 2 n))) F :=
  MvPolynomial.rename (witnessInclusion M n h_le) (tseitinPoly F n)

/-- The full compiled polynomial P_{M',n} = Q×_Φ(u) + R_{M',Φ}(v).
    Paper: Theorem 181, §34.1. -/
noncomputable def fullCompiledPoly (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n : ℕ) (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    MvPolynomial (Fin (numVars M n (Nat.log 2 n))) F :=
  verifierSheetOf F M n h_le + violationPolyOf F M n

/-- §34.1: tableau constraints restricted to witness vars give a constant.
    Paper: Lemma 182. -/
theorem tableau_restriction_const (F : Type*) [Field F] [Nontrivial F]
    (M : DTM) (n : ℕ) (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∃ c : F, restrictPoly F (witnessInclusion M n h_le)
      (witnessInclusion_injective M n h_le) (violationPolyOf F M n) = MvPolynomial.C c := by
  sorry

/-- P-side upper bound for the full compiled polynomial.
    Paper: Theorem 181 Item 3. -/
theorem pside_full_ml_rank_bound {F : Type*} [Field F] (M : DTM) :
    ∃ (C : ℕ), ∀ n, n ≥ max 4 M.numStates →
      ∀ (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
        (B : BlockPartition (numVars M n (Nat.log 2 n))) (κ ℓ : ℕ),
        mlBlockedSpdpRank B κ ℓ (fullCompiledPoly F M n h_le) ≤ n ^ C := by
  sorry

/-- §34 Compiler extraction: NP-side rank ≤ P-side rank.

    Paper-faithful proof chain using fullCompiledPoly = verifierSheet + tableau:
    1. restriction_rank_monotone on fullCompiledPoly
    2. restrictPoly(fullCompiled) = restrictPoly(rename f tseitin) + restrictPoly(tableau)
       = tseitin + C(c)  [by restrictPoly_rename + §34.1 additive separability]
    3. mlBlockedSpdpRank_add_const: Γ(B, p + C c) = Γ(B, p)
    4. mlBlockedSpdpRank_coarsen: identity pullback refines tseitin partition
    5. Chain: Γ(tseitin) ≤ Γ(pullback) ≤ Γ(compiled) -/
theorem extraction_rank_monotone (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (M : DTM) (hsolves : True) (hn : n ≥ 4) :
    ∀ (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) (κ ℓ : ℕ),
      κ ≥ 1 →
      mlBlockedSpdpRank (tseitinPartition n) κ ℓ (tseitinPoly F n) ≤
      mlBlockedSpdpRank (compiledPartition M n) κ ℓ
        (fullCompiledPoly F M n h_le) := by
  intro h_le κ ℓ hκ
  let f := witnessInclusion M n h_le
  have hf_inj := witnessInclusion_injective M n h_le
  -- Step 1: restriction_rank_monotone on fullCompiledPoly
  have h_restrict := restriction_rank_monotone F f hf_inj (compiledPartition M n) κ ℓ
    (fullCompiledPoly F M n h_le)
  -- Step 2: restrictPoly(fullCompiled) = tseitin + C(c)
  -- fullCompiledPoly = verifierSheetOf + violationPolyOf
  -- = rename f (tseitinPoly) + violationPolyOf
  -- restrictPoly preserves + (it's an AlgHom)
  have h_add : restrictPoly F f hf_inj (fullCompiledPoly F M n h_le) =
      restrictPoly F f hf_inj (verifierSheetOf F M n h_le) +
      restrictPoly F f hf_inj (violationPolyOf F M n) := by
    unfold fullCompiledPoly
    exact map_add (restrictPoly F f hf_inj) _ _
  -- restrictPoly(rename f (tseitinPoly)) = tseitinPoly by restrictPoly_rename
  have h_sheet : restrictPoly F f hf_inj (verifierSheetOf F M n h_le) =
      tseitinPoly F n := by
    unfold verifierSheetOf
    exact restrictPoly_rename F f hf_inj (tseitinPoly F n)
  -- §34.1: restrictPoly(tableau) = C(c) (additive separability)
  obtain ⟨c, hc⟩ := tableau_restriction_const F M n h_le
  -- Combine
  rw [h_add, h_sheet, hc] at h_restrict
  -- Now h_restrict: Γ(pullback, tseitin + C c) ≤ Γ(compiled, fullCompiled)
  -- Step 3: add_const — remove the constant
  let h_pullback := pullbackPartition (compiledPartition M n) f
  rw [mlBlockedSpdpRank_add_const F h_pullback κ ℓ (tseitinPoly F n) c hκ] at h_restrict
  -- Step 4: coarsen — pullback of identity partition refines tseitin partition
  have h_coarsen := mlBlockedSpdpRank_coarsen F h_pullback (tseitinPartition n) κ ℓ
    (tseitinPoly F n) (by
      intro i j h_eq
      change (compiledPartition M n).assign (f i) = (compiledPartition M n).assign (f j) at h_eq
      simp only [compiledPartition, compilerBlockPartition] at h_eq
      have := hf_inj (Fin.ext (Fin.mk.inj h_eq))
      rw [this])
  linarith

end MultilinearSPDP
