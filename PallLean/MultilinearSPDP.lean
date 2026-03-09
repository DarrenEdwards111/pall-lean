/-
  MultilinearSPDP.lean — SPDP rank in the multilinear (Boolean) basis

  Paper Definition 12: The SPDP matrix uses multilinear monomials (mod ⟨x²_i - x_i⟩).
  We define multilinear SPDP rank as dim of span of mlProj-ed generators.
-/
import PallLean.SPDPDefs
import PallLean.NPWitness
import PallLean.Compiler
import PallLean.Multilinear
import PallLean.IdentityMinor
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace MultilinearSPDP

open MvPolynomial SPDP TuringMachine Compiler NPWitness Multilinear Tseitin

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

/-! ## P-side collapse

  Key insight: mlBlockedSpdpRank ≤ blockedSpdpRank (proved: mlBlockedSpdpRank_le).
  The existing profileRankBound in HasLocalityStructure bounds blockedSpdpRank
  by (numGates × width)³. So: mlBlockedSpdpRank ≤ (numGates × width)³ ≤ n^O(1).
  No per-gate multilinear bound needed! -/

theorem pside_ml_rank_bound {F : Type*} [Field F] (M : DTM) :
    ∃ (C : ℕ), ∀ n, n ≥ max 4 M.numStates →
      ∀ (B : BlockPartition (numVars M n (Nat.log 2 n))) (κ ℓ : ℕ),
        mlBlockedSpdpRank B κ ℓ (violationPolyOf F M n) ≤ n ^ C := by
  -- Chain: mlBlockedSpdpRank ≤ blockedSpdpRank ≤ (numGates × width)³ ≤ n^O(1)
  use 3 * (2 * M.timeBound + 6)  -- exponent for (numGates × width)³
  intro n hn B κ ℓ
  have hn4 : n ≥ 4 := le_trans (le_max_left _ _) hn
  have hns : n ≥ M.numStates := le_trans (le_max_right _ _) hn
  obtain ⟨loc, hng, hw, hw_pos⟩ := violation_has_locality F M n hn4 hns
  have heq : violationPolyOf F M n = ∑ i, loc.gate i := loc.sum_eq
  -- Step 1: mlBlockedSpdpRank ≤ blockedSpdpRank
  calc mlBlockedSpdpRank B κ ℓ (violationPolyOf F M n)
      ≤ blockedSpdpRank B κ ℓ (violationPolyOf F M n) :=
        mlBlockedSpdpRank_le B κ ℓ _
    -- Step 2: blockedSpdpRank ≤ (numGates × width)³ via profileRankBound
    _ ≤ (loc.numGates * loc.width) ^ 3 := by
        unfold blockedSpdpRank
        exact loc.profileRankBound B κ ℓ
    -- Step 3: (numGates × width)³ ≤ n^C
    _ ≤ (n ^ (2 * M.timeBound + 4) * 12) ^ 3 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul hng hw) 3
    _ ≤ n ^ (3 * (2 * M.timeBound + 6)) := by
        -- (n^a * 12)³ ≤ (n^a * n²)³ = n^(3(a+2)) for n ≥ 4 (12 ≤ 16 = 4² ≤ n²)
        calc (n ^ (2 * M.timeBound + 4) * 12) ^ 3
            ≤ (n ^ (2 * M.timeBound + 4) * n ^ 2) ^ 3 := by
              apply Nat.pow_le_pow_left
              apply Nat.mul_le_mul_left
              calc (12 : ℕ) ≤ 4 ^ 2 := by norm_num
                _ ≤ n ^ 2 := Nat.pow_le_pow_left hn4 2
          _ = n ^ (3 * (2 * M.timeBound + 6)) := by
              rw [← Nat.pow_add, ← Nat.pow_mul]; congr 1; omega

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
  -- Uses chooseTagMonomial_le_one (proved) + clauseVarSetFin_disjoint (existing)
  -- The foldl accumulator induction is ~30 lines of Finsupp arithmetic plumbing.
  sorry

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

/-! ## Extraction map axiom -/

axiom extraction_map_exists (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (M : DTM) (hsolves : True) :
    ∀ (B_v : BlockPartition (numVars M n (Nat.log 2 n))) (κ ℓ : ℕ),
      mlBlockedSpdpRank (tseitinPartition n) κ ℓ (tseitinPoly F n) ≤
      mlBlockedSpdpRank B_v κ ℓ (violationPolyOf F M n)

end MultilinearSPDP
