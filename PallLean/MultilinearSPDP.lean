/-
  MultilinearSPDP.lean — SPDP rank in the multilinear (Boolean) basis

  Paper Definition 12: The SPDP matrix uses multilinear monomials (mod ⟨x²_i - x_i⟩).
  We define multilinear SPDP rank as dim of span of mlProj-ed generators.
-/
import PallLean.SPDPDefs
import PallLean.NPWitness
import PallLean.Compiler
import PallLean.IdentityMinor
import PallLean.LowDegAnnihilation
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Basic

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

/-! ## Paper-faithful identity-minor multilinear columns

The paper's NP-side minor is built in the multilinear basis from the start.
The lemmas below expose that fact for the existing `IdentityMinor` construction:
the tag exponent vectors, and hence the monomial columns used by the Kronecker
minor, are square-free. -/

namespace IdentityMinorPaperFaithful

open IdentityMinor

/-- The identity-minor tag exponent vector is square-free. -/
theorem tagMono_finsupp_isMultilinear {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    Finsupp.IsMultilinear (IdentityMinor.tagMono F Φ pack κ i) := by
  intro x
  exact IdentityMinor.tagMono_le_one (F := F) Φ pack κ i x

/-- Therefore each monomial column indexed by a tag exponent is multilinear as
a polynomial. -/
theorem monomial_tagMono_isMultilinear {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ)) (a : F) :
    IsMultilinear (MvPolynomial.monomial (IdentityMinor.tagMono F Φ pack κ i) a) := by
  intro α hα x
  have hsub := MvPolynomial.support_monomial_subset hα
  rw [Finset.mem_singleton] at hsub
  rw [hsub]
  exact tagMono_finsupp_isMultilinear (F := F) Φ pack κ i x

/-- The packaged identity-minor components use multilinear column monomials.
This is the formal version of the paper §27 statement that the minor is already
constructed in the multilinear basis. -/
theorem identity_minor_components_columns_multilinear {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (hκ : κ ≤ pack.selected.length) :
    ∀ i, Finsupp.IsMultilinear
      ((IdentityMinor.identity_minor_components (F := F) Φ pack κ ℓ hκ).2.1 i) := by
  intro i
  change Finsupp.IsMultilinear (IdentityMinor.tagMono F Φ pack κ i)
  exact tagMono_finsupp_isMultilinear (F := F) Φ pack κ i

end IdentityMinorPaperFaithful


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
        m.vars ⊆ S.toFinset ∧  -- Lemma 18: shift support ⊆ derivative variables
        isBlockAdmissible B S ∧
        q = mlProj (m * iterDerivList S p) }

noncomputable def mlBlockedSpdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (mlBlockedSpdpSubspace B κ ℓ p)

/-! ## Paper-faithful inclusive-κ variant

Paper's Definition 12 (Lemma 40(c) recap, line 2662 of the paper):
"rows indexed by all partial derivatives ∂^α p of total order **|α| ≤ κ**"

The existing `mlBlockedSpdpSubspace` uses the strict `|S| = κ`
convention. This is inequivalent to the paper's `|α| ≤ κ` convention
(we have a concrete counterexample at N=2, g=X₀, p=X₁, κ=1 where the
`=` version admits rank-2 shifted rank-0 behavior violating Lemma 40).

The inclusive-κ variant below matches the paper exactly and is the
convention under which `gadget_spdp_subspace_factoring` (Lemma 40(c))
becomes a true statement. Existing proofs using the `=` version
(e.g., `mlBlockedSpdpRank_add_lowDeg`) rely on the strict equality and
are NOT claims about paper-faithful rank — they are claims about a
Lean-internal rank quantity that happens to have useful algebraic
properties. -/
noncomputable def mlBlockedSpdpSubspaceInc {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧
        m.vars ⊆ S.toFinset ∧
        isBlockAdmissible B S ∧
        q = mlProj (m * iterDerivList S p) }

noncomputable def mlBlockedSpdpRankInc {n : ℕ} {F : Type*} [CommRing F]
    [Nontrivial F] (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (mlBlockedSpdpSubspaceInc B κ ℓ p)

/-- The strict-equality subspace is contained in the inclusive-κ
variant: a `=κ` generator satisfies `≤κ`. -/
theorem mlBlockedSpdpSubspace_le_inc
    {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspace B κ ℓ p ≤ mlBlockedSpdpSubspaceInc B κ ℓ p := by
  apply Submodule.span_le.mpr
  rintro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  exact Submodule.subset_span ⟨S, m, hlen.le, hdeg, hvars, hadm, hq⟩

/-- Inclusive-κ subspace decomposes as the join over all strict-κ' ≤ κ
subspaces. Bridge between the two conventions. -/
theorem mlBlockedSpdpSubspaceInc_eq_iSup
    {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspaceInc B κ ℓ p =
      ⨆ (κ' : ℕ) (_ : κ' ≤ κ), mlBlockedSpdpSubspace B κ' ℓ p := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
    refine Submodule.mem_iSup_of_mem S.length ?_
    refine Submodule.mem_iSup_of_mem hlen ?_
    exact Submodule.subset_span ⟨S, m, rfl, hdeg, hvars, hadm, hq⟩
  · apply iSup_le
    intro κ'
    apply iSup_le
    intro hκ'
    apply Submodule.span_le.mpr
    rintro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
    exact Submodule.subset_span
      ⟨S, m, hlen ▸ hκ', hdeg, hvars, hadm, hq⟩

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
  intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  apply Submodule.subset_span
  exact ⟨S, m, hlen, hdeg, hvars, isBlockAdmissible_coarsen B₁ B₂ S hrefine hadm, hq⟩

/-- Monotonicity in the degree parameter ℓ: larger ℓ means more generators,
    hence a larger subspace. -/
theorem mlBlockedSpdpSubspace_mono_ell {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ : ℕ) {ℓ₁ ℓ₂ : ℕ} (hℓ : ℓ₁ ≤ ℓ₂)
    (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspace B κ ℓ₁ p ≤ mlBlockedSpdpSubspace B κ ℓ₂ p := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  apply Submodule.subset_span
  exact ⟨S, m, hlen, le_trans hdeg hℓ, hvars, hadm, hq⟩

theorem mlBlockedSpdpSubspace_le_map {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspace B κ ℓ p ≤
      Submodule.map (mlProjLinearMap (Fin n) F) (blockedSpdpSubspace B κ ℓ p) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
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
  intro q ⟨S, m, _, hdeg, _, _, hq⟩
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

/-- Inclusive-κ subspace contained in `restrictTotalDegree ℓ + p.totalDegree`. -/
theorem mlBlockedSpdpSubspaceInc_le_restrictTotalDegree {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspaceInc B κ ℓ p ≤
      MvPolynomial.restrictTotalDegree (Fin n) F (ℓ + p.totalDegree) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, _, hdeg, _, _, hq⟩
  rw [hq]
  have h1 : (mlProj (m * iterDerivList S p)).totalDegree ≤ ℓ + p.totalDegree :=
    le_trans (totalDegree_mlProj_le _)
      (le_trans (MvPolynomial.totalDegree_mul m (iterDerivList S p))
        (Nat.add_le_add hdeg (totalDegree_iterDerivList_le S p)))
  exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr h1

instance mlBlockedSpdpSubspaceInc_finite {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Module.Finite F (mlBlockedSpdpSubspaceInc B κ ℓ p) := by
  have hle := mlBlockedSpdpSubspaceInc_le_restrictTotalDegree B κ ℓ p
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

/-- Monotonicity in the degree parameter ℓ for rank. -/
theorem mlBlockedSpdpRank_mono_ell {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ : ℕ) {ℓ₁ ℓ₂ : ℕ} (hℓ : ℓ₁ ≤ ℓ₂)
    (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRank B κ ℓ₁ p ≤ mlBlockedSpdpRank B κ ℓ₂ p := by
  unfold mlBlockedSpdpRank
  exact Submodule.finrank_mono (mlBlockedSpdpSubspace_mono_ell B κ hℓ p)

/-! ## Subadditivity -/

theorem mlBlockedSpdpSubspace_add_le {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p q : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspace B κ ℓ (p + q) ≤
      mlBlockedSpdpSubspace B κ ℓ p ⊔ mlBlockedSpdpSubspace B κ ℓ q := by
  apply Submodule.span_le.mpr
  intro r ⟨S, m, hlen, hdeg, hvars, hadm, hr⟩
  rw [hr, iterDerivList_add, mul_add, mlProj_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩))
    (Submodule.mem_sup_right (Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩))

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
    intro q ⟨S, m_poly, _, _, _, _, hq⟩
    rw [hq]; unfold iterDerivList; rw [foldl_pderiv_zero, mul_zero, mlProj_zero]
    exact Submodule.zero_mem ⊥
  · exact bot_le

theorem mlBlockedSpdpSubspaceInc_zero {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) :
    mlBlockedSpdpSubspaceInc B κ ℓ (0 : MvPolynomial (Fin n) F) = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro q ⟨S, m_poly, _, _, _, _, hq⟩
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
  exact Submodule.subset_span ⟨S, 1, hlen, by simp, by simp [MvPolynomial.vars_one], hadm, rfl⟩

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
  Submodule.subset_span ⟨S, 1, hlen, by simp, by simp [MvPolynomial.vars_one], hadm, rfl⟩

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
  refine ⟨IdentityMinor.selectorList Φ pack κ i, 1, ?_, ?_, ?_, ?_, rfl⟩
  · -- length = κ
    show (IdentityMinor.selectorList Φ pack κ i).length = κ
    unfold IdentityMinor.selectorList
    rw [List.length_map]
    exact IdentityMinor.getSubset_length pack κ i
  · -- deg ≤ ℓ
    simp [MvPolynomial.totalDegree_one]
  · -- vars ⊆ S.toFinset: vars(1) = ∅ ⊆ anything
    simp [MvPolynomial.vars_one]
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

/-- Projection preserves the Kronecker identity-minor coefficients because the
column tags are square-free.  This is the paper-faithful algebraic bridge from
the full polynomial rows to the multilinear/projected NP-window rows: no
quotient-kernel injectivity is used. -/
theorem identity_minor_components_kronecker_after_mlProj {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (hκ : κ ≤ pack.selected.length) :
    ∀ i j, MvPolynomial.coeff
      ((IdentityMinor.identity_minor_components (F := F) Φ pack κ ℓ hκ).2.1 i)
      (mlProj ((IdentityMinor.identity_minor_components (F := F) Φ pack κ ℓ hκ).1 j).val) =
      if i = j then
        (IdentityMinor.identity_minor_components (F := F) Φ pack κ ℓ hκ).2.2 i
      else 0 := by
  intro i j
  obtain ⟨_, hkron⟩ := IdentityMinor.identity_minor_components_signs
    (F := F) Φ pack κ ℓ hκ
  have hml : Finsupp.IsMultilinear
      ((IdentityMinor.identity_minor_components (F := F) Φ pack κ ℓ hκ).2.1 i) := by
    change Finsupp.IsMultilinear (IdentityMinor.tagMono F Φ pack κ i)
    exact tagMono_isMultilinear Φ pack κ i
  rw [coeff_mlProj_of_isMultilinear_mono _ _ hml]
  exact hkron i j

/-- A Kronecker dual family gives linear independence.  If linear functionals
`φᵢ` evaluate a vector family `vⱼ` as a diagonal matrix with nonzero diagonal
`uᵢ`, then no nontrivial finite linear relation among the `vⱼ` can exist: apply
`φₐ` to a relation containing `vₐ` and the diagonal entry isolates its
coefficient. -/
theorem linearIndependent_of_kronecker_dual
    {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    {k : ℕ} (v : Fin k → M) (φ : Fin k → M →ₗ[F] F) (u : Fin k → F)
    (hu : ∀ i, u i ≠ 0)
    (hkron : ∀ i j, φ i (v j) = if i = j then u i else 0) :
    LinearIndependent F v := by
  rw [linearIndependent_iff']
  intro S g hg a ha
  have h0 : φ a (∑ j ∈ S, g j • v j) = 0 := by
    rw [hg]
    exact map_zero (φ a)
  simp only [map_sum, LinearMap.map_smul, smul_eq_mul] at h0
  have hsub : ∀ j ∈ S, g j * φ a (v j) = if j = a then g j * u a else 0 := by
    intro j _
    rw [hkron a j]
    by_cases h : a = j
    · subst h; simp
    · simp [h, show j ≠ a from fun h' => h (h' ▸ rfl)]
  rw [Finset.sum_congr rfl hsub, Finset.sum_ite_eq' S a, if_pos ha] at h0
  exact mul_eq_zero.mp h0 |>.resolve_right (hu a)

/-- Direct projected Kronecker δ theorem for the identity-minor rows.  The
square-free tag monomial is not removed by `mlProj`, so the original
`IdentityMinor.kronecker_delta` survives exactly after projecting the row. -/
theorem identity_minor_projected_kronecker_delta {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i j : Fin (Nat.choose pack.selected.length κ)) :
    MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
      (mlProj (IdentityMinor.rowPoly F Φ pack κ j)) =
        if i = j then IdentityMinor.subsetSign F Φ pack κ i else 0 := by
  have hml : Finsupp.IsMultilinear (IdentityMinor.tagMono F Φ pack κ i) :=
    tagMono_isMultilinear Φ pack κ i
  rw [coeff_mlProj_of_isMultilinear_mono _ _ hml]
  exact IdentityMinor.kronecker_delta (F := F) Φ pack κ i j

/-- Diagonal projected coefficient: the private tag extracts the row's sign. -/
theorem identity_minor_projected_diagonal_coeff
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
      (mlProj (IdentityMinor.rowPoly F Φ pack κ i)) =
        IdentityMinor.subsetSign F Φ pack κ i := by
  rw [identity_minor_projected_kronecker_delta (F := F) Φ pack κ i i]
  simp

/-- The diagonal projected coefficient is a unit sign (`±1`). -/
theorem identity_minor_projected_diagonal_coeff_unit
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
      (mlProj (IdentityMinor.rowPoly F Φ pack κ i)) = 1 ∨
    MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
      (mlProj (IdentityMinor.rowPoly F Φ pack κ i)) = -1 := by
  rw [identity_minor_projected_diagonal_coeff (F := F) Φ pack κ i]
  exact IdentityMinor.subsetSign_unit Φ pack κ i

/-- Off-diagonal projected coefficient vanishing: a private tag for `i` sees no
projected row indexed by a distinct subset `j`. -/
theorem identity_minor_projected_offdiag_coeff_zero
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i j : Fin (Nat.choose pack.selected.length κ)) (hij : i ≠ j) :
    MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
      (mlProj (IdentityMinor.rowPoly F Φ pack κ j)) = 0 := by
  rw [identity_minor_projected_kronecker_delta (F := F) Φ pack κ i j]
  simp [hij]

/-- Each projected identity-minor row is nonzero.  The diagonal tag coefficient
survives `mlProj` because the tag is square-free, and that coefficient is the
unit `subsetSign`. -/
theorem identity_minor_projected_row_ne_zero {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    mlProj (IdentityMinor.rowPoly F Φ pack κ i) ≠ 0 := by
  intro hzero
  let s : F := IdentityMinor.subsetSign F Φ pack κ i
  have hs_nonzero : s ≠ 0 := by
    change IdentityMinor.subsetSign F Φ pack κ i ≠ 0
    rcases IdentityMinor.subsetSign_unit (F := F) Φ pack κ i with hs | hs <;> rw [hs] <;> simp
  have hcoeff : MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
      (mlProj (IdentityMinor.rowPoly F Φ pack κ i)) = s := by
    rw [identity_minor_projected_diagonal_coeff (F := F) Φ pack κ i]
  rw [hzero, MvPolynomial.coeff_zero] at hcoeff
  exact hs_nonzero hcoeff.symm

/-- The projected identity-minor rows are linearly independent as polynomials.
This is the bare algebraic core of the NP-side lower bound, independent of any
particular submodule packaging: square-free tags give a signed identity matrix
after multilinear projection. -/
theorem identity_minor_projected_rows_linearIndependent {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ) :
    LinearIndependent F (fun i : Fin (Nat.choose pack.selected.length κ) =>
      mlProj (IdentityMinor.rowPoly F Φ pack κ i)) := by
  let signs : Fin (Nat.choose pack.selected.length κ) → F :=
    fun i => IdentityMinor.subsetSign F Φ pack κ i
  have hsigns : ∀ i, signs i = 1 ∨ signs i = -1 := by
    intro i
    exact IdentityMinor.subsetSign_unit Φ pack κ i
  have hu : ∀ i, signs i ≠ 0 := by
    intro i
    rcases hsigns i with hs | hs <;> rw [hs] <;> simp
  apply linearIndependent_of_kronecker_dual
    (fun i : Fin (Nat.choose pack.selected.length κ) => mlProj (IdentityMinor.rowPoly F Φ pack κ i))
    (fun i => coeffLin F (IdentityMinor.tagMono F Φ pack κ i))
    signs hu
  intro i j
  simp only [coeffLin, LinearMap.coe_mk, AddHom.coe_mk]
  exact identity_minor_projected_kronecker_delta (F := F) Φ pack κ i j

/-- The projected identity-minor span generated by the multilinear projections
of the identity-minor rows.  This is the reusable NP-side witness subspace: all
subsequent lower bounds are dimension/containment facts about this one object. -/
noncomputable def projectedIdentityMinorSpan {F : Type*} [CommRing F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ) :
    Submodule F (MvPolynomial (Fin (tseitinNumVars Φ)) F) :=
  Submodule.span F (Set.range
    (fun i : Fin (Nat.choose pack.selected.length κ) =>
      mlProj (IdentityMinor.rowPoly F Φ pack κ i)))

/-- The projected identity-minor row span has exactly the expected
binomial dimension.  This packages the Kronecker-dual independence as a clean
finite-dimensional algebra statement: the projected rows themselves carry a
`choose(|pack|, κ)`-dimensional identity-minor subspace. -/
theorem identity_minor_projected_rows_span_finrank {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ) :
    Module.finrank F (projectedIdentityMinorSpan (F := F) Φ pack κ) =
      Nat.choose pack.selected.length κ := by
  dsimp [projectedIdentityMinorSpan]
  rw [finrank_span_eq_card
    (identity_minor_projected_rows_linearIndependent (F := F) Φ pack κ)]
  exact Fintype.card_fin _

/-- The projected identity-minor span is finite, because it is generated by the
finite family of projected rows indexed by `Fin (choose |pack| κ)`. -/
theorem projectedIdentityMinorSpan_finite {F : Type*} [Field F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ) :
    Module.Finite F (projectedIdentityMinorSpan (F := F) Φ pack κ) := by
  dsimp [projectedIdentityMinorSpan]
  exact Module.Finite.span_of_finite F (Set.finite_range _)

/-- The projected identity-minor rows form a basis of the named projected
identity-minor span.  This packages the Kronecker-dual independence and the
definition of the witness subspace into a reusable coordinate object for later
transport arguments. -/
noncomputable def projectedIdentityMinorBasis {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ) :
    Module.Basis (Fin (Nat.choose pack.selected.length κ)) F
      (projectedIdentityMinorSpan (F := F) Φ pack κ) :=
  Module.Basis.span (identity_minor_projected_rows_linearIndependent (F := F) Φ pack κ)

/-- The named basis vector is exactly the corresponding projected identity-minor
row, viewed inside the projected-minor span. -/
theorem projectedIdentityMinorBasis_apply
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    ((projectedIdentityMinorBasis (F := F) Φ pack κ i :
        projectedIdentityMinorSpan (F := F) Φ pack κ) :
      MvPolynomial (Fin (tseitinNumVars Φ)) F) =
      mlProj (IdentityMinor.rowPoly F Φ pack κ i) := by
  exact Module.Basis.span_apply
    (identity_minor_projected_rows_linearIndependent (F := F) Φ pack κ) i

/-- Projected basis rows in fully expanded product-rule form.

This combines the coordinate-level projected basis object with the concrete
Leibniz/product derivative theorem from `IdentityMinor`: each basis vector is
the multilinear projection of the signed selected-gadget product times the
undifferentiated verifier factors on the complement. -/
theorem projectedIdentityMinorBasis_eq_mlProj_signed_gadgetProd_mul_remaining
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    ((projectedIdentityMinorBasis (F := F) Φ pack κ i :
        projectedIdentityMinorSpan (F := F) Φ pack κ) :
      MvPolynomial (Fin (tseitinNumVars Φ)) F) =
      mlProj
        (C ((-1 : F) ^ κ) *
          ((IdentityMinor.getSubset pack κ i).map (clauseGadget F Φ)).prod *
          ((Finset.univ : Finset (Fin Φ.clauses.length)) \
              (IdentityMinor.getSubset pack κ i).toFinset).prod (IdentityMinor.cvFactor F Φ)) := by
  rw [projectedIdentityMinorBasis_apply]
  rw [IdentityMinor.rowPoly_eq_signed_gadgetProd_mul_remaining]

/-- Body-supported multilinear coefficients of projected basis rows are pure
gadget-product coefficients, up to the Leibniz sign.

This is the projected coefficient-level row-purification statement: after
`mlProj`, any multilinear body column still ignores the complement verifier
factors and sees only the selected gadget product. -/
theorem coeff_body_projectedIdentityMinorBasis_eq_signed_gadgetProd
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ))
    (m : (Fin (tseitinNumVars Φ)) →₀ ℕ)
    (hmulti : Finsupp.IsMultilinear m)
    (hbody : CoeffDisjoint.monomSupportedIn m
      {v : Fin (tseitinNumVars Φ) | v.val < Φ.graph.numEdges + 3 * Φ.clauses.length}) :
    MvPolynomial.coeff m
      (((projectedIdentityMinorBasis (F := F) Φ pack κ i :
          projectedIdentityMinorSpan (F := F) Φ pack κ) :
        MvPolynomial (Fin (tseitinNumVars Φ)) F)) =
      ((-1 : F) ^ κ) *
        MvPolynomial.coeff m ((IdentityMinor.getSubset pack κ i).map (clauseGadget F Φ)).prod := by
  rw [projectedIdentityMinorBasis_apply]
  rw [coeff_mlProj_of_isMultilinear_mono _ _ hmulti]
  exact IdentityMinor.coeff_body_rowPoly_eq_signed_gadgetProd Φ pack κ i m hbody


/-- Projected identity-minor basis rows retain the full Kronecker delta system
on tag columns.  Multilinear projection does not alter these coefficients
because the tag monomials are multilinear. -/
theorem coeff_tagMono_projectedIdentityMinorBasis_kronecker
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i j : Fin (Nat.choose pack.selected.length κ)) :
    MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
      (((projectedIdentityMinorBasis (F := F) Φ pack κ j :
          projectedIdentityMinorSpan (F := F) Φ pack κ) :
        MvPolynomial (Fin (tseitinNumVars Φ)) F)) =
      if i = j then IdentityMinor.subsetSign F Φ pack κ i else 0 := by
  rw [projectedIdentityMinorBasis_apply]
  rw [coeff_mlProj_of_isMultilinear_mono]
  exact IdentityMinor.kronecker_delta Φ pack κ i j
  exact tagMono_isMultilinear Φ pack κ i


/-- The selected tag coefficient of its own projected basis row is the signed
identity-minor diagonal entry.  This is the diagonal minor entry after both
row-purification and multilinear projection. -/
theorem coeff_tagMono_projectedIdentityMinorBasis_self_eq_subsetSign
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
      (((projectedIdentityMinorBasis (F := F) Φ pack κ i :
          projectedIdentityMinorSpan (F := F) Φ pack κ) :
        MvPolynomial (Fin (tseitinNumVars Φ)) F)) =
      IdentityMinor.subsetSign F Φ pack κ i := by
  rw [projectedIdentityMinorBasis_apply]
  rw [coeff_mlProj_of_isMultilinear_mono]
  exact IdentityMinor.coeff_tagMono_rowPoly_self_eq_subsetSign Φ pack κ i
  exact tagMono_isMultilinear Φ pack κ i


/-- Each named projected identity-minor basis vector is an actual SPDP row of
`coupledVerifier`, provided the selected selector list is block-admissible.

This is the explicit row-membership version of the Route-B NP-side bridge: the
basis vector is definitionally the projected selector-derivative row by
`projectedIdentityMinorBasis_apply`, and `rowPoly_mem_ml_subspace` exhibits that
row as a generator of `mlBlockedSpdpSubspace`. -/
theorem projectedIdentityMinorBasis_mem_mlSubspace
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (B : BlockPartition (tseitinNumVars Φ))
    (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ))
    (hB : ∀ (cs : List (Fin Φ.clauses.length)),
      cs.Nodup → (∀ c ∈ cs, c ∈ pack.selected) → cs.length = κ →
      isBlockAdmissible B (cs.map (selectorIdx Φ))) :
    ((projectedIdentityMinorBasis (F := F) Φ pack κ i :
        projectedIdentityMinorSpan (F := F) Φ pack κ) :
      MvPolynomial (Fin (tseitinNumVars Φ)) F) ∈
      mlBlockedSpdpSubspace B κ ℓ (coupledVerifier F Φ) := by
  rw [projectedIdentityMinorBasis_apply]
  exact rowPoly_mem_ml_subspace Φ B pack κ ℓ i hB

/-- Canonical-partition specialization: every named projected identity-minor
basis vector lies in the canonical Tseitin SPDP row space. -/
theorem projectedIdentityMinorBasis_mem_canonical_mlSubspace
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    ((projectedIdentityMinorBasis (F := F) Φ pack κ i :
        projectedIdentityMinorSpan (F := F) Φ pack κ) :
      MvPolynomial (Fin (tseitinNumVars Φ)) F) ∈
      mlBlockedSpdpSubspace (IdentityMinor.tseitinPartition Φ) κ ℓ
        (coupledVerifier F Φ) := by
  exact projectedIdentityMinorBasis_mem_mlSubspace
    (F := F) Φ (IdentityMinor.tseitinPartition Φ) pack κ ℓ i
    (fun cs hnd _ _ => IdentityMinor.tseitinPartition_admissible_general Φ cs hnd)

/-- The identity-minor sign is self-inverse.  This turns the signed
Kronecker minor into an honest dual coordinate system. -/
theorem subsetSign_mul_self {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    IdentityMinor.subsetSign F Φ pack κ i *
      IdentityMinor.subsetSign F Φ pack κ i = 1 := by
  rcases IdentityMinor.subsetSign_unit (F := F) Φ pack κ i with h | h <;> rw [h] <;> ring

/-- Signed coefficient functional dual to a projected identity-minor basis row.
It first extracts the private tag coefficient and then multiplies by the same
`±1` sign, using `sign² = 1` to normalize the diagonal to one. -/
noncomputable def projectedIdentityMinorDual {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (j : Fin (Nat.choose pack.selected.length κ)) :
    projectedIdentityMinorSpan (F := F) Φ pack κ →ₗ[F] F :=
  (IdentityMinor.subsetSign F Φ pack κ j) •
    ((coeffLin F (IdentityMinor.tagMono F Φ pack κ j)).comp
      (Submodule.subtype (projectedIdentityMinorSpan (F := F) Φ pack κ)))

/-- The signed tag coefficient functionals are exactly dual to the projected
identity-minor basis.  This is the explicit Kronecker coordinate form of the
projected minor and is the cleanest object for later Π+ transport. -/
theorem projectedIdentityMinorDual_basis_apply
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (i j : Fin (Nat.choose pack.selected.length κ)) :
    projectedIdentityMinorDual (F := F) Φ pack κ j
      (projectedIdentityMinorBasis (F := F) Φ pack κ i) =
      if i = j then (1 : F) else 0 := by
  dsimp [projectedIdentityMinorDual]
  rw [projectedIdentityMinorBasis_apply]
  simp only [coeffLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [identity_minor_projected_kronecker_delta (F := F) Φ pack κ j i]
  by_cases h : i = j
  · subst i
    simp [subsetSign_mul_self (F := F) Φ pack κ j]
  · have hji : ¬ j = i := by exact fun h' => h h'.symm
    simp [h, hji]

/-- The signed coefficient functional is exactly the `j`th coordinate map
of the projected identity-minor basis. -/
theorem projectedIdentityMinorDual_eq_basis_repr_coord
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (j : Fin (Nat.choose pack.selected.length κ)) :
    projectedIdentityMinorDual (F := F) Φ pack κ j =
      ((Finsupp.lapply j : (Fin (Nat.choose pack.selected.length κ) →₀ F) →ₗ[F] F).comp
        (projectedIdentityMinorBasis (F := F) Φ pack κ).repr.toLinearMap) := by
  apply Module.Basis.ext (projectedIdentityMinorBasis (F := F) Φ pack κ)
  intro i
  rw [projectedIdentityMinorDual_basis_apply]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Finsupp.lapply_apply]
  rw [Module.Basis.repr_self_apply]

/-- Reconstruction in the projected identity-minor witness subspace: every
witness vector is the finite sum of its signed tag coefficients times the
projected identity-minor basis rows. -/
theorem projectedIdentityMinor_dual_reconstruction
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
    (∑ i : Fin (Nat.choose pack.selected.length κ),
      projectedIdentityMinorDual (F := F) Φ pack κ i x •
        projectedIdentityMinorBasis (F := F) Φ pack κ i) = x := by
  simp [projectedIdentityMinorDual_eq_basis_repr_coord,
    Module.Basis.sum_repr (projectedIdentityMinorBasis (F := F) Φ pack κ) x]

/-- Raw private-tag coefficients are signed coordinates in the projected
identity-minor basis.  Equivalently, the coordinate of `x` along row `i` is
`subsetSign_i` times the tag coefficient, and since the sign is self-inverse
the coefficient itself is `subsetSign_i` times the coordinate. -/
theorem projectedIdentityMinor_coeff_eq_signed_repr_coord
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (x : projectedIdentityMinorSpan (F := F) Φ pack κ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
        ((x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
          MvPolynomial (Fin (tseitinNumVars Φ)) F) =
      IdentityMinor.subsetSign F Φ pack κ i *
        ((projectedIdentityMinorBasis (F := F) Φ pack κ).repr x i) := by
  let s : F := IdentityMinor.subsetSign F Φ pack κ i
  have hcoord : projectedIdentityMinorDual (F := F) Φ pack κ i x =
      (projectedIdentityMinorBasis (F := F) Φ pack κ).repr x i := by
    rw [projectedIdentityMinorDual_eq_basis_repr_coord]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Finsupp.lapply_apply]
  dsimp [projectedIdentityMinorDual] at hcoord
  change s * MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
      ((x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
        MvPolynomial (Fin (tseitinNumVars Φ)) F) =
      (projectedIdentityMinorBasis (F := F) Φ pack κ).repr x i at hcoord
  calc
    MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
        ((x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
          MvPolynomial (Fin (tseitinNumVars Φ)) F)
        = (1 : F) * MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
            ((x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
              MvPolynomial (Fin (tseitinNumVars Φ)) F) := by simp
    _ = (s * s) * MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
            ((x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
              MvPolynomial (Fin (tseitinNumVars Φ)) F) := by
          rw [subsetSign_mul_self (F := F) Φ pack κ i]
    _ = s * (s * MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
            ((x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
              MvPolynomial (Fin (tseitinNumVars Φ)) F)) := by ring
    _ = s * ((projectedIdentityMinorBasis (F := F) Φ pack κ).repr x i) := by rw [hcoord]

/-- Basis coordinates are exactly signed private-tag coefficients.  This is the
coordinate extraction theorem in the forward direction: the raw coefficient is
not merely separating, it computes the `Basis.repr` coordinate up to the same
self-inverse sign. -/
theorem projectedIdentityMinor_repr_coord_eq_signed_coeff
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (x : projectedIdentityMinorSpan (F := F) Φ pack κ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    ((projectedIdentityMinorBasis (F := F) Φ pack κ).repr x i) =
      IdentityMinor.subsetSign F Φ pack κ i *
        MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
          ((x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
            MvPolynomial (Fin (tseitinNumVars Φ)) F) := by
  have hcoord : projectedIdentityMinorDual (F := F) Φ pack κ i x =
      (projectedIdentityMinorBasis (F := F) Φ pack κ).repr x i := by
    rw [projectedIdentityMinorDual_eq_basis_repr_coord]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Finsupp.lapply_apply]
  rw [← hcoord]
  rfl


/-- Coordinate-space sign flip for the projected identity minor.  Multiplying
each coordinate by its `±1` minor sign is a linear equivalence, with itself as
inverse. -/
noncomputable def projectedIdentityMinorSignEquiv
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ) :
    ((Fin (Nat.choose pack.selected.length κ) → F) ≃ₗ[F]
      (Fin (Nat.choose pack.selected.length κ) → F)) where
  toFun := fun a i => IdentityMinor.subsetSign F Φ pack κ i * a i
  invFun := fun a i => IdentityMinor.subsetSign F Φ pack κ i * a i
  left_inv := by
    intro a
    ext i
    simp only
    rw [← mul_assoc, subsetSign_mul_self (F := F) Φ pack κ i, one_mul]
  right_inv := by
    intro a
    ext i
    simp only
    rw [← mul_assoc, subsetSign_mul_self (F := F) Φ pack κ i, one_mul]
  map_add' := by
    intro a b
    ext i
    simp [mul_add]
  map_smul' := by
    intro c a
    ext i
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm]

/-- The private tag coefficient map is a linear equivalence from the projected
identity-minor span to the standard coordinate space.  It is the usual basis
coordinate equivalence followed by the self-inverse diagonal sign flip. -/
noncomputable def projectedIdentityMinorTagCoeffEquiv
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ) :
    projectedIdentityMinorSpan (F := F) Φ pack κ ≃ₗ[F]
      (Fin (Nat.choose pack.selected.length κ) → F) :=
  (projectedIdentityMinorBasis (F := F) Φ pack κ).equivFun.trans
    (projectedIdentityMinorSignEquiv (F := F) Φ pack κ)

/-- Applying the tag-coefficient equivalence is literally extracting the
private tag coefficient. -/
theorem projectedIdentityMinorTagCoeffEquiv_apply
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (x : projectedIdentityMinorSpan (F := F) Φ pack κ)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    projectedIdentityMinorTagCoeffEquiv (F := F) Φ pack κ x i =
      MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
        ((x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
          MvPolynomial (Fin (tseitinNumVars Φ)) F) := by
  dsimp [projectedIdentityMinorTagCoeffEquiv, projectedIdentityMinorSignEquiv]
  exact (projectedIdentityMinor_coeff_eq_signed_repr_coord (F := F) Φ pack κ x i).symm

/-- The private tag coefficient map is injective.  This is the linear-equivalence
version of tag-coordinate separation. -/
theorem projectedIdentityMinorTagCoeffEquiv_injective
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ) :
    Function.Injective (projectedIdentityMinorTagCoeffEquiv (F := F) Φ pack κ) :=
  (projectedIdentityMinorTagCoeffEquiv (F := F) Φ pack κ).injective


/-- Explicit inverse for the tag-coefficient equivalence: prescribed private-tag
coordinates `a` are realized by the signed sum of projected basis rows. -/
theorem projectedIdentityMinorTagCoeffEquiv_symm_apply
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (a : Fin (Nat.choose pack.selected.length κ) → F) :
    (projectedIdentityMinorTagCoeffEquiv (F := F) Φ pack κ).symm a =
      ∑ i : Fin (Nat.choose pack.selected.length κ),
        (IdentityMinor.subsetSign F Φ pack κ i * a i) •
          projectedIdentityMinorBasis (F := F) Φ pack κ i := by
  dsimp [projectedIdentityMinorTagCoeffEquiv, projectedIdentityMinorSignEquiv]
  rw [Module.Basis.equivFun_symm_apply]

/-- Prescribed tag coordinates are realized exactly: extracting private tag
coefficients from the explicit inverse of the tag-coordinate equivalence returns
the original coordinate function. -/
theorem projectedIdentityMinorTagCoeffEquiv_apply_symm
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (a : Fin (Nat.choose pack.selected.length κ) → F)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
      (((projectedIdentityMinorTagCoeffEquiv (F := F) Φ pack κ).symm a :
          projectedIdentityMinorSpan (F := F) Φ pack κ) :
        MvPolynomial (Fin (tseitinNumVars Φ)) F) = a i := by
  rw [← projectedIdentityMinorTagCoeffEquiv_apply (F := F) Φ pack κ
    ((projectedIdentityMinorTagCoeffEquiv (F := F) Φ pack κ).symm a) i]
  simp

/-- Concrete prescribed-coordinate realization without mentioning `.symm`: the
signed basis sum has private tag coefficient `a i`. -/
theorem coeff_tagMono_projectedIdentityMinor_signed_basis_sum
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (a : Fin (Nat.choose pack.selected.length κ) → F)
    (i : Fin (Nat.choose pack.selected.length κ)) :
    MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
      (((∑ j : Fin (Nat.choose pack.selected.length κ),
          (IdentityMinor.subsetSign F Φ pack κ j * a j) •
            projectedIdentityMinorBasis (F := F) Φ pack κ j :
          projectedIdentityMinorSpan (F := F) Φ pack κ) :
        projectedIdentityMinorSpan (F := F) Φ pack κ) :
        MvPolynomial (Fin (tseitinNumVars Φ)) F) = a i := by
  rw [← projectedIdentityMinorTagCoeffEquiv_symm_apply (F := F) Φ pack κ a]
  exact projectedIdentityMinorTagCoeffEquiv_apply_symm (F := F) Φ pack κ a i


/-- Coefficient reconstruction: every vector in the projected minor span is the
finite sum of projected basis rows weighted by the signed private-tag
coefficients extracted from that same vector. -/
theorem projectedIdentityMinor_coeff_reconstruction
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
    (∑ i : Fin (Nat.choose pack.selected.length κ),
      (IdentityMinor.subsetSign F Φ pack κ i *
        MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
          ((x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
            MvPolynomial (Fin (tseitinNumVars Φ)) F)) •
        projectedIdentityMinorBasis (F := F) Φ pack κ i) = x := by
  convert projectedIdentityMinor_dual_reconstruction (F := F) Φ pack κ x using 2

/-- Extensionality for the projected identity-minor span: two vectors are equal
as soon as all their private tag coefficients agree. -/
theorem projectedIdentityMinor_ext_of_forall_tag_coeff_eq
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (x y : projectedIdentityMinorSpan (F := F) Φ pack κ)
    (hcoeff : ∀ i : Fin (Nat.choose pack.selected.length κ),
      MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
        ((x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
          MvPolynomial (Fin (tseitinNumVars Φ)) F) =
      MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
        ((y : projectedIdentityMinorSpan (F := F) Φ pack κ) :
          MvPolynomial (Fin (tseitinNumVars Φ)) F)) :
    x = y := by
  apply (projectedIdentityMinorBasis (F := F) Φ pack κ).repr.injective
  ext i
  rw [projectedIdentityMinor_repr_coord_eq_signed_coeff (F := F) Φ pack κ x i]
  rw [projectedIdentityMinor_repr_coord_eq_signed_coeff (F := F) Φ pack κ y i]
  rw [hcoeff i]

/-- Private tag coefficients separate points of the projected identity-minor
span.  If all tag coordinates vanish, the span vector itself is zero. -/
theorem projectedIdentityMinor_eq_zero_of_forall_tag_coeff_zero
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (x : projectedIdentityMinorSpan (F := F) Φ pack κ)
    (hcoeff : ∀ i : Fin (Nat.choose pack.selected.length κ),
      MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
        ((x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
          MvPolynomial (Fin (tseitinNumVars Φ)) F) = 0) :
    x = 0 := by
  have hrecon := projectedIdentityMinor_coeff_reconstruction (F := F) Φ pack κ x
  rw [← hrecon]
  simp [hcoeff]

/-- Vanishing of all private tag coefficients is equivalent to vanishing in the
projected identity-minor span. -/
theorem projectedIdentityMinor_forall_tag_coeff_zero_iff
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ)
    (x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
    (∀ i : Fin (Nat.choose pack.selected.length κ),
      MvPolynomial.coeff (IdentityMinor.tagMono F Φ pack κ i)
        ((x : projectedIdentityMinorSpan (F := F) Φ pack κ) :
          MvPolynomial (Fin (tseitinNumVars Φ)) F) = 0) ↔ x = 0 := by
  constructor
  · intro h
    exact projectedIdentityMinor_eq_zero_of_forall_tag_coeff_zero (F := F) Φ pack κ x h
  · intro hx i
    rw [hx]
    simp


/-- The projected identity-minor row span is contained in the multilinear SPDP
subspace whenever the selector derivative lists are block-admissible.  This is
the clean span-level form of the paper's NP-window preservation: the whole
projected identity-minor subspace, not merely each row separately, lives inside
the SPDP row space. -/
theorem identity_minor_projected_rows_span_le_mlSubspace {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (B : BlockPartition (tseitinNumVars Φ))
    (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (hB : ∀ (cs : List (Fin Φ.clauses.length)),
      cs.Nodup → (∀ c ∈ cs, c ∈ pack.selected) → cs.length = κ →
      isBlockAdmissible B (cs.map (selectorIdx Φ))) :
    projectedIdentityMinorSpan (F := F) Φ pack κ ≤
      mlBlockedSpdpSubspace B κ ℓ (coupledVerifier F Φ) := by
  apply Submodule.span_le.mpr
  rintro q ⟨i, rfl⟩
  exact rowPoly_mem_ml_subspace Φ B pack κ ℓ i hB

/-- Inclusive-window version of the span containment.  The same projected
identity-minor span lies in the paper-faithful `|α| ≤ κ` SPDP window because
the strict `|α| = κ` subspace embeds into the inclusive one. -/
theorem identity_minor_projected_rows_span_le_mlSubspaceInc {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (B : BlockPartition (tseitinNumVars Φ))
    (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (hB : ∀ (cs : List (Fin Φ.clauses.length)),
      cs.Nodup → (∀ c ∈ cs, c ∈ pack.selected) → cs.length = κ →
      isBlockAdmissible B (cs.map (selectorIdx Φ))) :
    projectedIdentityMinorSpan (F := F) Φ pack κ ≤
      mlBlockedSpdpSubspaceInc B κ ℓ (coupledVerifier F Φ) := by
  exact le_trans
    (identity_minor_projected_rows_span_le_mlSubspace (F := F) Φ B pack κ ℓ hB)
    (mlBlockedSpdpSubspace_le_inc B κ ℓ (coupledVerifier F Φ))

/-- Span-containment proof of the projected identity-minor lower bound: the
projected identity-minor span has exact binomial dimension and is contained in
the SPDP row space, so the SPDP rank is at least that binomial dimension. -/
theorem identity_minor_projected_rank_lower_from_span {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (B : BlockPartition (tseitinNumVars Φ))
    (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (hB : ∀ (cs : List (Fin Φ.clauses.length)),
      cs.Nodup → (∀ c ∈ cs, c ∈ pack.selected) → cs.length = κ →
      isBlockAdmissible B (cs.map (selectorIdx Φ))) :
    mlBlockedSpdpRank B κ ℓ (coupledVerifier F Φ) ≥
      Nat.choose pack.selected.length κ := by
  let W : Submodule F (MvPolynomial (Fin (tseitinNumVars Φ)) F) :=
    projectedIdentityMinorSpan (F := F) Φ pack κ
  have hWfin : Module.finrank F W = Nat.choose pack.selected.length κ := by
    dsimp [W]
    exact identity_minor_projected_rows_span_finrank (F := F) Φ pack κ
  have hle : W ≤ mlBlockedSpdpSubspace B κ ℓ (coupledVerifier F Φ) := by
    dsimp [W]
    exact identity_minor_projected_rows_span_le_mlSubspace (F := F) Φ B pack κ ℓ hB
  haveI : Module.Finite F W := Module.Finite.span_of_finite F (Set.finite_range _)
  have hmono := Submodule.finrank_mono hle
  dsimp [mlBlockedSpdpRank]
  omega

/-- Inclusive-window span-containment proof of the projected identity-minor
lower bound. -/
theorem identity_minor_projected_rank_lower_inc_from_span {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (B : BlockPartition (tseitinNumVars Φ))
    (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (hB : ∀ (cs : List (Fin Φ.clauses.length)),
      cs.Nodup → (∀ c ∈ cs, c ∈ pack.selected) → cs.length = κ →
      isBlockAdmissible B (cs.map (selectorIdx Φ))) :
    mlBlockedSpdpRankInc B κ ℓ (coupledVerifier F Φ) ≥
      Nat.choose pack.selected.length κ := by
  let W : Submodule F (MvPolynomial (Fin (tseitinNumVars Φ)) F) :=
    projectedIdentityMinorSpan (F := F) Φ pack κ
  have hWfin : Module.finrank F W = Nat.choose pack.selected.length κ := by
    dsimp [W]
    exact identity_minor_projected_rows_span_finrank (F := F) Φ pack κ
  have hle : W ≤ mlBlockedSpdpSubspaceInc B κ ℓ (coupledVerifier F Φ) := by
    dsimp [W]
    exact identity_minor_projected_rows_span_le_mlSubspaceInc (F := F) Φ B pack κ ℓ hB
  haveI : Module.Finite F W := Module.Finite.span_of_finite F (Set.finite_range _)
  have hmono := Submodule.finrank_mono hle
  dsimp [mlBlockedSpdpRankInc]
  omega

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

/-- Rank lower bound from a Kronecker dual certificate inside a submodule.  This
combines `linearIndependent_of_kronecker_dual` with the usual dimension lower
bound for a linearly independent family contained in a finite-dimensional
submodule. -/
theorem finrank_ge_of_kronecker_dual
    {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (V : Submodule F M) [Module.Finite F V]
    {k : ℕ} (elements : Fin k → V) (φ : Fin k → M →ₗ[F] F) (u : Fin k → F)
    (hu : ∀ i, u i ≠ 0)
    (hkron : ∀ i j, φ i ((elements j).val) = if i = j then u i else 0) :
    Module.finrank F V ≥ k := by
  exact finrank_ge_of_linearIndependent V k elements
    (linearIndependent_of_kronecker_dual (Subtype.val ∘ elements) φ u hu hkron)

/-- The projected identity-minor rows already force a rank lower bound in the
multilinear SPDP subspace.  This packages the paper-faithful NP-side algebra:
private-support Kronecker tags survive `mlProj`, giving linear independence of
the projected derivative rows and hence dimension at least `choose L κ`. -/
theorem identity_minor_projected_rank_lower {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (B : BlockPartition (tseitinNumVars Φ))
    (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (hκ : κ ≤ pack.selected.length)
    (hB : ∀ (cs : List (Fin Φ.clauses.length)),
      cs.Nodup → (∀ c ∈ cs, c ∈ pack.selected) → cs.length = κ →
      isBlockAdmissible B (cs.map (selectorIdx Φ))) :
    mlBlockedSpdpRank B κ ℓ (coupledVerifier F Φ) ≥
      Nat.choose pack.selected.length κ := by
  exact identity_minor_projected_rank_lower_from_span (F := F) Φ B pack κ ℓ hB

/-- Inclusive-κ version of `identity_minor_projected_rank_lower`.  This is the
version matching the paper's `|α| ≤ κ` derivative-window convention: the same
projected identity-minor rows belong to the inclusive subspace via the strict →
inclusive containment, and the Kronecker coefficient functionals give the same
linear independence certificate. -/
theorem identity_minor_projected_rank_lower_inc {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (B : BlockPartition (tseitinNumVars Φ))
    (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (hκ : κ ≤ pack.selected.length)
    (hB : ∀ (cs : List (Fin Φ.clauses.length)),
      cs.Nodup → (∀ c ∈ cs, c ∈ pack.selected) → cs.length = κ →
      isBlockAdmissible B (cs.map (selectorIdx Φ))) :
    mlBlockedSpdpRankInc B κ ℓ (coupledVerifier F Φ) ≥
      Nat.choose pack.selected.length κ := by
  exact identity_minor_projected_rank_lower_inc_from_span (F := F) Φ B pack κ ℓ hB

/-- Canonical-partition projected identity-minor span containment for the
coupled Tseitin verifier.  This is the paper-faithful NP-window preservation
statement at the level of subspaces: the full projected minor span embeds in
the canonical Tseitin SPDP row space. -/
theorem coupledVerifier_projected_identity_minor_span_le_mlSubspace
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ ℓ : ℕ) :
    projectedIdentityMinorSpan (F := F) Φ pack κ ≤
      mlBlockedSpdpSubspace (IdentityMinor.tseitinPartition Φ) κ ℓ
        (coupledVerifier F Φ) := by
  exact identity_minor_projected_rows_span_le_mlSubspace
    (F := F) Φ (IdentityMinor.tseitinPartition Φ) pack κ ℓ
    (fun cs hnd _ _ => IdentityMinor.tseitinPartition_admissible_general Φ cs hnd)

/-- Inclusive-window canonical span containment for the coupled Tseitin verifier. -/
theorem coupledVerifier_projected_identity_minor_span_le_mlSubspaceInc
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ ℓ : ℕ) :
    projectedIdentityMinorSpan (F := F) Φ pack κ ≤
      mlBlockedSpdpSubspaceInc (IdentityMinor.tseitinPartition Φ) κ ℓ
        (coupledVerifier F Φ) := by
  exact identity_minor_projected_rows_span_le_mlSubspaceInc
    (F := F) Φ (IdentityMinor.tseitinPartition Φ) pack κ ℓ
    (fun cs hnd _ _ => IdentityMinor.tseitinPartition_admissible_general Φ cs hnd)

/-- Canonical coupled-verifier projected identity-minor span has exact binomial
dimension.  Together with the two containment lemmas above, this isolates the
NP-side rank lower bound as pure dimension monotonicity. -/
theorem coupledVerifier_projected_identity_minor_span_finrank
    {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ : ℕ) :
    Module.finrank F (projectedIdentityMinorSpan (F := F) Φ pack κ) =
      Nat.choose pack.selected.length κ := by
  exact identity_minor_projected_rows_span_finrank (F := F) Φ pack κ

/-- Canonical-partition specialization of the projected identity-minor lower
bound for the coupled Tseitin verifier.  Selector lists are admissible in
`IdentityMinor.tseitinPartition`, so the generic projected rank theorem applies
without an external admissibility hypothesis. -/
theorem coupledVerifier_projected_identity_minor_rank_lower {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (hκ : κ ≤ pack.selected.length) :
    mlBlockedSpdpRank (IdentityMinor.tseitinPartition Φ) κ ℓ (coupledVerifier F Φ) ≥
      Nat.choose pack.selected.length κ := by
  exact identity_minor_projected_rank_lower_from_span
    (F := F) Φ (IdentityMinor.tseitinPartition Φ) pack κ ℓ
    (fun cs hnd _ _ => IdentityMinor.tseitinPartition_admissible_general Φ cs hnd)

/-- Inclusive-window canonical-partition specialization of the same coupled
verifier identity-minor lower bound. -/
theorem coupledVerifier_projected_identity_minor_rank_lower_inc {F : Type*} [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (pack : DisjointPacking Φ) (κ ℓ : ℕ)
    (hκ : κ ≤ pack.selected.length) :
    mlBlockedSpdpRankInc (IdentityMinor.tseitinPartition Φ) κ ℓ (coupledVerifier F Φ) ≥
      Nat.choose pack.selected.length κ := by
  exact identity_minor_projected_rank_lower_inc_from_span
    (F := F) Φ (IdentityMinor.tseitinPartition Φ) pack κ ℓ
    (fun cs hnd _ _ => IdentityMinor.tseitinPartition_admissible_general Φ cs hnd)

/-- Concrete Tseitin-family projected identity-minor subspace certificate.
There is an explicit projected identity-minor subspace inside the canonical
Tseitin NP window whose dimension is at least `choose (n/30) (log₂ n)`.
This is stronger than the rank inequality: it exposes the actual subspace that
carries the minor and is the right object for later Π+ transport. -/
theorem tseitinAt_projected_identity_minor_subspace_certificate
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn1024 : n ≥ 2^10) (heven : 2 ∣ n) :
    ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F),
      W ≤ mlBlockedSpdpSubspace (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)) ∧
      Nat.choose (n / 30) (Nat.log 2 n) ≤ Module.finrank F W := by
  have hv := tseitinAt_vertices n (by omega) heven
  have pack := Tseitin.disjoint_packing_exists (tseitinAt n) (by omega)
  let κ := Nat.log 2 n
  let W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F) :=
    projectedIdentityMinorSpan (F := F) (tseitinAt n) pack κ
  refine ⟨W, ?_, ?_⟩
  · dsimp [W]
    exact coupledVerifier_projected_identity_minor_span_le_mlSubspace
      (F := F) (tseitinAt n) pack κ κ
  · have hWfin : Module.finrank F W = Nat.choose pack.selected.length κ := by
      dsimp [W]
      exact coupledVerifier_projected_identity_minor_span_finrank
        (F := F) (tseitinAt n) pack κ
    rw [hWfin]
    apply Nat.choose_le_choose
    have hps := pack.size_bound
    rw [hv] at hps
    exact hps

/-- Inclusive-window version of the concrete projected identity-minor subspace
certificate.  The same explicit projected minor span sits inside every
`|α| ≤ log₂ n` window with arbitrary shift degree `ℓ`. -/
theorem tseitinAt_projected_identity_minor_subspace_certificate_inc
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn1024 : n ≥ 2^10) (heven : 2 ∣ n) (ℓ : ℕ) :
    ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F),
      W ≤ mlBlockedSpdpSubspaceInc (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)) ∧
      Nat.choose (n / 30) (Nat.log 2 n) ≤ Module.finrank F W := by
  have hv := tseitinAt_vertices n (by omega) heven
  have pack := Tseitin.disjoint_packing_exists (tseitinAt n) (by omega)
  let κ := Nat.log 2 n
  let W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F) :=
    projectedIdentityMinorSpan (F := F) (tseitinAt n) pack κ
  refine ⟨W, ?_, ?_⟩
  · dsimp [W]
    exact coupledVerifier_projected_identity_minor_span_le_mlSubspaceInc
      (F := F) (tseitinAt n) pack κ ℓ
  · have hWfin : Module.finrank F W = Nat.choose pack.selected.length κ := by
      dsimp [W]
      exact coupledVerifier_projected_identity_minor_span_finrank
        (F := F) (tseitinAt n) pack κ
    rw [hWfin]
    apply Nat.choose_le_choose
    have hps := pack.size_bound
    rw [hv] at hps
    exact hps

/-- Concrete-threshold projected identity-minor subspace certificate with the
full super-polynomial dimension lower bound.  This upgrades the binomial
subspace certificate using the concrete binomial estimate, so the witness
subspace itself has dimension at least `n^(log₂ n / 4)`. -/
theorem tseitinAt_projected_identity_minor_subspace_superpoly_certificate
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn : n ≥ 2 ^ 804) (heven : 2 ∣ n) :
    ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F),
      W ≤ mlBlockedSpdpSubspace (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)) ∧
      n ^ (Nat.log 2 n / 4) ≤ Module.finrank F W := by
  have hn1024 : n ≥ 2^10 := by
    have : (2 : ℕ) ^ 10 ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
    exact le_trans this hn
  have hn20 : n ≥ 2 ^ 20 := le_trans (by
    exact Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 20 ≤ 804)) hn
  obtain ⟨W, hWle, hWdim⟩ :=
    tseitinAt_projected_identity_minor_subspace_certificate F n hn1024 heven
  refine ⟨W, hWle, ?_⟩
  exact le_trans (BinomialBound.binomial_lower_bound_concrete n hn20) hWdim

/-- Inclusive-window concrete-threshold projected identity-minor subspace
certificate with the full super-polynomial dimension lower bound. -/
theorem tseitinAt_projected_identity_minor_subspace_superpoly_certificate_inc
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn : n ≥ 2 ^ 804) (heven : 2 ∣ n) (ℓ : ℕ) :
    ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F),
      W ≤ mlBlockedSpdpSubspaceInc (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)) ∧
      n ^ (Nat.log 2 n / 4) ≤ Module.finrank F W := by
  have hn1024 : n ≥ 2^10 := by
    have : (2 : ℕ) ^ 10 ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
    exact le_trans this hn
  have hn20 : n ≥ 2 ^ 20 := le_trans (by
    exact Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 20 ≤ 804)) hn
  obtain ⟨W, hWle, hWdim⟩ :=
    tseitinAt_projected_identity_minor_subspace_certificate_inc F n hn1024 heven ℓ
  refine ⟨W, hWle, ?_⟩
  exact le_trans (BinomialBound.binomial_lower_bound_concrete n hn20) hWdim

/-- A finite subspace certificate gives a rank lower bound for the ambient
finite-dimensional row space.  This is the abstract dimension-monotonicity step
used to turn explicit projected-minor subspaces into SPDP rank lower bounds. -/
theorem rank_lower_of_finite_subspace_certificate
    {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (V W : Submodule F M) [Module.Finite F V] [Module.Finite F W] (d : ℕ)
    (hWV : W ≤ V) (hdim : d ≤ Module.finrank F W) :
    d ≤ Module.finrank F V := by
  exact le_trans hdim (Submodule.finrank_mono hWV)

/-- Finite version of the concrete projected identity-minor subspace certificate.
It records explicitly that the witness subspace is finitely generated, so it can
feed dimension-monotonicity lemmas without reconstructing its spanning family. -/
theorem tseitinAt_projected_identity_minor_finite_subspace_certificate
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn1024 : n ≥ 2^10) (heven : 2 ∣ n) :
    ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F),
      Module.Finite F W ∧
      W ≤ mlBlockedSpdpSubspace (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)) ∧
      Nat.choose (n / 30) (Nat.log 2 n) ≤ Module.finrank F W := by
  have hv := tseitinAt_vertices n (by omega) heven
  have pack := Tseitin.disjoint_packing_exists (tseitinAt n) (by omega)
  let κ := Nat.log 2 n
  let W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F) :=
    projectedIdentityMinorSpan (F := F) (tseitinAt n) pack κ
  refine ⟨W, ?_, ?_, ?_⟩
  · dsimp [W]
    exact Module.Finite.span_of_finite F (Set.finite_range _)
  · dsimp [W]
    exact coupledVerifier_projected_identity_minor_span_le_mlSubspace
      (F := F) (tseitinAt n) pack κ κ
  · have hWfin : Module.finrank F W = Nat.choose pack.selected.length κ := by
      dsimp [W]
      exact coupledVerifier_projected_identity_minor_span_finrank
        (F := F) (tseitinAt n) pack κ
    rw [hWfin]
    apply Nat.choose_le_choose
    have hps := pack.size_bound
    rw [hv] at hps
    exact hps

/-- Inclusive-window finite projected-minor subspace certificate. -/
theorem tseitinAt_projected_identity_minor_finite_subspace_certificate_inc
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn1024 : n ≥ 2^10) (heven : 2 ∣ n) (ℓ : ℕ) :
    ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F),
      Module.Finite F W ∧
      W ≤ mlBlockedSpdpSubspaceInc (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)) ∧
      Nat.choose (n / 30) (Nat.log 2 n) ≤ Module.finrank F W := by
  have hv := tseitinAt_vertices n (by omega) heven
  have pack := Tseitin.disjoint_packing_exists (tseitinAt n) (by omega)
  let κ := Nat.log 2 n
  let W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F) :=
    projectedIdentityMinorSpan (F := F) (tseitinAt n) pack κ
  refine ⟨W, ?_, ?_, ?_⟩
  · dsimp [W]
    exact Module.Finite.span_of_finite F (Set.finite_range _)
  · dsimp [W]
    exact coupledVerifier_projected_identity_minor_span_le_mlSubspaceInc
      (F := F) (tseitinAt n) pack κ ℓ
  · have hWfin : Module.finrank F W = Nat.choose pack.selected.length κ := by
      dsimp [W]
      exact coupledVerifier_projected_identity_minor_span_finrank
        (F := F) (tseitinAt n) pack κ
    rw [hWfin]
    apply Nat.choose_le_choose
    have hps := pack.size_bound
    rw [hv] at hps
    exact hps

/-- Rank lower bound derived solely from the finite projected-minor subspace
certificate. -/
theorem tseitinAt_coupledVerifier_projected_rank_lower_choose_div30_from_finite_subspace_certificate
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn1024 : n ≥ 2^10) (heven : 2 ∣ n) :
    Nat.choose (n / 30) (Nat.log 2 n) ≤
      mlBlockedSpdpRank (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)) := by
  obtain ⟨W, hWfinite, hWle, hdim⟩ :=
    tseitinAt_projected_identity_minor_finite_subspace_certificate F n hn1024 heven
  haveI : Module.Finite F W := hWfinite
  dsimp [mlBlockedSpdpRank]
  exact rank_lower_of_finite_subspace_certificate
    (mlBlockedSpdpSubspace (IdentityMinor.tseitinPartition (tseitinAt n))
      (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)))
    W (Nat.choose (n / 30) (Nat.log 2 n)) hWle hdim

/-- Inclusive-window rank lower bound derived solely from the finite
projected-minor subspace certificate. -/
theorem tseitinAt_coupledVerifier_projected_rank_lower_choose_div30_inc_from_finite_subspace_certificate
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn1024 : n ≥ 2^10) (heven : 2 ∣ n) (ℓ : ℕ) :
    Nat.choose (n / 30) (Nat.log 2 n) ≤
      mlBlockedSpdpRankInc (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)) := by
  obtain ⟨W, hWfinite, hWle, hdim⟩ :=
    tseitinAt_projected_identity_minor_finite_subspace_certificate_inc F n hn1024 heven ℓ
  haveI : Module.Finite F W := hWfinite
  dsimp [mlBlockedSpdpRankInc]
  exact rank_lower_of_finite_subspace_certificate
    (mlBlockedSpdpSubspaceInc (IdentityMinor.tseitinPartition (tseitinAt n))
      (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)))
    W (Nat.choose (n / 30) (Nat.log 2 n)) hWle hdim

/-- Finite concrete-threshold projected identity-minor subspace certificate with
the full super-polynomial dimension lower bound.  This is the strongest
structural NP-side witness currently available: a finitely generated projected
minor subspace inside the canonical window, already of super-polynomial
dimension. -/
theorem tseitinAt_projected_identity_minor_finite_subspace_superpoly_certificate
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn : n ≥ 2 ^ 804) (heven : 2 ∣ n) :
    ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F),
      Module.Finite F W ∧
      W ≤ mlBlockedSpdpSubspace (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)) ∧
      n ^ (Nat.log 2 n / 4) ≤ Module.finrank F W := by
  have hn1024 : n ≥ 2^10 := by
    have : (2 : ℕ) ^ 10 ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
    exact le_trans this hn
  have hn20 : n ≥ 2 ^ 20 := le_trans (by
    exact Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 20 ≤ 804)) hn
  obtain ⟨W, hWfinite, hWle, hdim⟩ :=
    tseitinAt_projected_identity_minor_finite_subspace_certificate F n hn1024 heven
  refine ⟨W, hWfinite, hWle, ?_⟩
  exact le_trans (BinomialBound.binomial_lower_bound_concrete n hn20) hdim

/-- Inclusive-window finite concrete-threshold projected identity-minor subspace
certificate with the full super-polynomial dimension lower bound. -/
theorem tseitinAt_projected_identity_minor_finite_subspace_superpoly_certificate_inc
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn : n ≥ 2 ^ 804) (heven : 2 ∣ n) (ℓ : ℕ) :
    ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F),
      Module.Finite F W ∧
      W ≤ mlBlockedSpdpSubspaceInc (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)) ∧
      n ^ (Nat.log 2 n / 4) ≤ Module.finrank F W := by
  have hn1024 : n ≥ 2^10 := by
    have : (2 : ℕ) ^ 10 ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
    exact le_trans this hn
  have hn20 : n ≥ 2 ^ 20 := le_trans (by
    exact Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 20 ≤ 804)) hn
  obtain ⟨W, hWfinite, hWle, hdim⟩ :=
    tseitinAt_projected_identity_minor_finite_subspace_certificate_inc F n hn1024 heven ℓ
  refine ⟨W, hWfinite, hWle, ?_⟩
  exact le_trans (BinomialBound.binomial_lower_bound_concrete n hn20) hdim

/-- Concrete-threshold rank lower bound derived solely from the finite
super-polynomial projected-minor subspace certificate. -/
theorem tseitinAt_coupledVerifier_projected_rank_lower_superpoly_from_finite_subspace_certificate
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn : n ≥ 2 ^ 804) (heven : 2 ∣ n) :
      mlBlockedSpdpRank (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)) ≥
          n ^ (Nat.log 2 n / 4) := by
  obtain ⟨W, hWfinite, hWle, hdim⟩ :=
    tseitinAt_projected_identity_minor_finite_subspace_superpoly_certificate F n hn heven
  haveI : Module.Finite F W := hWfinite
  dsimp [mlBlockedSpdpRank]
  exact rank_lower_of_finite_subspace_certificate
    (mlBlockedSpdpSubspace (IdentityMinor.tseitinPartition (tseitinAt n))
      (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)))
    W (n ^ (Nat.log 2 n / 4)) hWle hdim

/-- Inclusive-window concrete-threshold rank lower bound derived solely from the
finite super-polynomial projected-minor subspace certificate. -/
theorem tseitinAt_coupledVerifier_projected_rank_lower_superpoly_inc_from_finite_subspace_certificate
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn : n ≥ 2 ^ 804) (heven : 2 ∣ n) (ℓ : ℕ) :
      mlBlockedSpdpRankInc (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)) ≥
          n ^ (Nat.log 2 n / 4) := by
  obtain ⟨W, hWfinite, hWle, hdim⟩ :=
    tseitinAt_projected_identity_minor_finite_subspace_superpoly_certificate_inc F n hn heven ℓ
  haveI : Module.Finite F W := hWfinite
  dsimp [mlBlockedSpdpRankInc]
  exact rank_lower_of_finite_subspace_certificate
    (mlBlockedSpdpSubspaceInc (IdentityMinor.tseitinPartition (tseitinAt n))
      (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)))
    W (n ^ (Nat.log 2 n / 4)) hWle hdim

/-- Concrete Tseitin-family version: the disjoint-packing construction gives at
least `n/30` private clauses, hence the projected multilinear identity minor has
rank at least `choose (n/30) (log₂ n)` for the coupled verifier. -/
theorem tseitinAt_coupledVerifier_projected_rank_lower_choose_div30
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn1024 : n ≥ 2^10) (heven : 2 ∣ n) :
    Nat.choose (n / 30) (Nat.log 2 n) ≤
      mlBlockedSpdpRank (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)) := by
  exact tseitinAt_coupledVerifier_projected_rank_lower_choose_div30_from_finite_subspace_certificate
    F n hn1024 heven

/-- Inclusive-window concrete Tseitin-family version, with arbitrary shift degree
`ℓ`.  This is the direct paper-window form of the coupled-verifier NP-side
minor lower bound. -/
theorem tseitinAt_coupledVerifier_projected_rank_lower_choose_div30_inc
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn1024 : n ≥ 2^10) (heven : 2 ∣ n) (ℓ : ℕ) :
    Nat.choose (n / 30) (Nat.log 2 n) ≤
      mlBlockedSpdpRankInc (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)) := by
  exact tseitinAt_coupledVerifier_projected_rank_lower_choose_div30_inc_from_finite_subspace_certificate
    F n hn1024 heven ℓ

/-- Asymptotic finite projected-minor subspace certificate for the coupled
Tseitin verifier: eventually, every even `n` has a finitely generated projected
identity-minor subspace inside the NP window whose dimension is already at
least `n^(log₂ n / 4)`. -/
theorem coupledVerifier_projected_finite_subspace_superpoly_certificate
    (F : Type*) [Field F] [Nontrivial F] :
    ∃ n₀, ∀ n, n ≥ n₀ → 2 ∣ n →
      ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F),
        Module.Finite F W ∧
        W ≤ mlBlockedSpdpSubspace (IdentityMinor.tseitinPartition (tseitinAt n))
          (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)) ∧
        n ^ (Nat.log 2 n / 4) ≤ Module.finrank F W := by
  obtain ⟨n₀, hn₀⟩ := NPWitness.binomial_lower_bound
  use max n₀ (2^10)
  intro n hn heven
  have hn₀' : n ≥ n₀ := le_trans (le_max_left _ _) hn
  have hn1024 : n ≥ 2^10 := le_trans (le_max_right _ _) hn
  obtain ⟨W, hWfinite, hWle, hdim⟩ :=
    tseitinAt_projected_identity_minor_finite_subspace_certificate F n hn1024 heven
  refine ⟨W, hWfinite, hWle, ?_⟩
  exact le_trans (hn₀ n hn₀') hdim

/-- Inclusive-window asymptotic finite projected-minor subspace certificate. -/
theorem coupledVerifier_projected_finite_subspace_superpoly_certificate_inc
    (F : Type*) [Field F] [Nontrivial F] (ℓ : ℕ) :
    ∃ n₀, ∀ n, n ≥ n₀ → 2 ∣ n →
      ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars (tseitinAt n))) F),
        Module.Finite F W ∧
        W ≤ mlBlockedSpdpSubspaceInc (IdentityMinor.tseitinPartition (tseitinAt n))
          (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)) ∧
        n ^ (Nat.log 2 n / 4) ≤ Module.finrank F W := by
  obtain ⟨n₀, hn₀⟩ := NPWitness.binomial_lower_bound
  use max n₀ (2^10)
  intro n hn heven
  have hn₀' : n ≥ n₀ := le_trans (le_max_left _ _) hn
  have hn1024 : n ≥ 2^10 := le_trans (le_max_right _ _) hn
  obtain ⟨W, hWfinite, hWle, hdim⟩ :=
    tseitinAt_projected_identity_minor_finite_subspace_certificate_inc F n hn1024 heven ℓ
  refine ⟨W, hWfinite, hWle, ?_⟩
  exact le_trans (hn₀ n hn₀') hdim

/-- Asymptotic rank lower bound derived from the asymptotic finite projected-minor
subspace certificate. -/
theorem coupledVerifier_projected_rank_lower_superpoly_from_asymptotic_finite_subspace_certificate
    (F : Type*) [Field F] [Nontrivial F] :
    ∃ n₀, ∀ n, n ≥ n₀ → 2 ∣ n →
      mlBlockedSpdpRank (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)) ≥
          n ^ (Nat.log 2 n / 4) := by
  obtain ⟨n₀, hcert⟩ := coupledVerifier_projected_finite_subspace_superpoly_certificate F
  use n₀
  intro n hn heven
  obtain ⟨W, hWfinite, hWle, hdim⟩ := hcert n hn heven
  haveI : Module.Finite F W := hWfinite
  dsimp [mlBlockedSpdpRank]
  exact rank_lower_of_finite_subspace_certificate
    (mlBlockedSpdpSubspace (IdentityMinor.tseitinPartition (tseitinAt n))
      (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)))
    W (n ^ (Nat.log 2 n / 4)) hWle hdim

/-- Inclusive-window asymptotic rank lower bound derived from the asymptotic
finite projected-minor subspace certificate. -/
theorem coupledVerifier_projected_rank_lower_superpoly_inc_from_asymptotic_finite_subspace_certificate
    (F : Type*) [Field F] [Nontrivial F] (ℓ : ℕ) :
    ∃ n₀, ∀ n, n ≥ n₀ → 2 ∣ n →
      mlBlockedSpdpRankInc (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)) ≥
          n ^ (Nat.log 2 n / 4) := by
  obtain ⟨n₀, hcert⟩ := coupledVerifier_projected_finite_subspace_superpoly_certificate_inc F ℓ
  use n₀
  intro n hn heven
  obtain ⟨W, hWfinite, hWle, hdim⟩ := hcert n hn heven
  haveI : Module.Finite F W := hWfinite
  dsimp [mlBlockedSpdpRankInc]
  exact rank_lower_of_finite_subspace_certificate
    (mlBlockedSpdpSubspaceInc (IdentityMinor.tseitinPartition (tseitinAt n))
      (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)))
    W (n ^ (Nat.log 2 n / 4)) hWle hdim

/-- Super-polynomial NP-side lower bound for the projected multilinear coupled
Tseitin verifier.  This composes the paper-faithful projected identity-minor
rank theorem with the standard binomial estimate, without touching the compiled
polynomial or any quotient-kernel argument. -/
theorem coupledVerifier_projected_rank_lower_superpoly
    (F : Type*) [Field F] [Nontrivial F] :
    ∃ n₀, ∀ n, n ≥ n₀ → 2 ∣ n →
      mlBlockedSpdpRank (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)) ≥
          n ^ (Nat.log 2 n / 4) := by
  exact coupledVerifier_projected_rank_lower_superpoly_from_asymptotic_finite_subspace_certificate F

/-- Inclusive-window super-polynomial NP-side lower bound for the projected
multilinear coupled Tseitin verifier.  The shift degree is arbitrary because
the identity-minor rows use the unit shift. -/
theorem coupledVerifier_projected_rank_lower_superpoly_inc
    (F : Type*) [Field F] [Nontrivial F] (ℓ : ℕ) :
    ∃ n₀, ∀ n, n ≥ n₀ → 2 ∣ n →
      mlBlockedSpdpRankInc (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)) ≥
          n ^ (Nat.log 2 n / 4) := by
  exact coupledVerifier_projected_rank_lower_superpoly_inc_from_asymptotic_finite_subspace_certificate F ℓ

/-- Concrete-threshold version of the coupled-verifier projected NP lower bound. -/
theorem coupledVerifier_projected_rank_lower_superpoly_concrete
    (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (hn : n ≥ 2 ^ 804) (heven : 2 ∣ n) :
      mlBlockedSpdpRank (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) (Nat.log 2 n) (coupledVerifier F (tseitinAt n)) ≥
          n ^ (Nat.log 2 n / 4) := by
  exact tseitinAt_coupledVerifier_projected_rank_lower_superpoly_from_finite_subspace_certificate
    F n hn heven

/-- Concrete-threshold inclusive-window version of the coupled-verifier projected
NP lower bound. -/
theorem coupledVerifier_projected_rank_lower_superpoly_concrete_inc
    (F : Type*) [Field F] [Nontrivial F] (ℓ : ℕ)
    (n : ℕ) (hn : n ≥ 2 ^ 804) (heven : 2 ∣ n) :
      mlBlockedSpdpRankInc (IdentityMinor.tseitinPartition (tseitinAt n))
        (Nat.log 2 n) ℓ (coupledVerifier F (tseitinAt n)) ≥
          n ^ (Nat.log 2 n / 4) := by
  exact tseitinAt_coupledVerifier_projected_rank_lower_superpoly_inc_from_finite_subspace_certificate
    F n hn heven ℓ

theorem np_ml_lower_bound (F : Type*) [Field F] [Nontrivial F] :
    ∃ n₀, ∀ n, n ≥ n₀ → 2 ∣ n →
      mlBlockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
        (tseitinPoly F n) ≥ n ^ (Nat.log 2 n / 4) := by
  -- Follow the same structure as np_side_lb, but with mlBlockedSpdpRank
  obtain ⟨n₀, hn₀⟩ := NPWitness.binomial_lower_bound
  use max n₀ (2^10)
  intro n hn heven
  have hn₀' : n ≥ n₀ := le_trans (le_max_left _ _) hn
  have hn1024 : n ≥ 2^10 := le_trans (le_max_right _ _) hn
  have hv := tseitinAt_vertices n (by omega) heven
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

/-- Generalized NP-side lower bound for any shift-degree parameter ℓ.
    Since the identity minor rows use shift m = 1 (degree 0), they live in
    mlBlockedSpdpSubspace B κ ℓ p for ANY ℓ ≥ 0.  In particular ℓ = 0 works. -/
theorem np_ml_lower_bound_any_ell (F : Type*) [Field F] [Nontrivial F] (ℓ : ℕ) :
    ∃ n₀, ∀ n, n ≥ n₀ → 2 ∣ n →
      mlBlockedSpdpRank (tseitinPartition n) (Nat.log 2 n) ℓ
        (tseitinPoly F n) ≥ n ^ (Nat.log 2 n / 4) := by
  obtain ⟨n₀, hn₀⟩ := NPWitness.binomial_lower_bound
  use max n₀ (2^10)
  intro n hn heven
  have hn₀' : n ≥ n₀ := le_trans (le_max_left _ _) hn
  have hn1024 : n ≥ 2^10 := le_trans (le_max_right _ _) hn
  have hv := tseitinAt_vertices n (by omega) heven
  have pack := Tseitin.disjoint_packing_exists (tseitinAt n) (by omega)
  let κ := Nat.log 2 n
  have hκ : κ ≤ pack.selected.length := by
    have hps := pack.size_bound; rw [hv] at hps
    exact (log2_le_div30 n (by linarith [show (2:ℕ)^10 = 1024 from by norm_num])).trans hps
  let c := IdentityMinor.identity_minor_components (F := F) (tseitinAt n) pack κ ℓ hκ
  obtain ⟨hsigns, hkron⟩ := IdentityMinor.identity_minor_components_signs
    (tseitinAt n) pack κ ℓ hκ (F := F)
  let mlV := mlBlockedSpdpSubspace (tseitinPartition n) κ ℓ (tseitinPoly F n)
  have hmem : ∀ i, mlProj (c.1 i).val ∈ mlV :=
    fun i => rowPoly_mem_ml_subspace (tseitinAt n) _ pack κ ℓ i
      (fun cs hnd _ _ => IdentityMinor.tseitinPartition_admissible_general (tseitinAt n) cs hnd)
  let R' : Fin (Nat.choose pack.selected.length κ) → ↥mlV :=
    fun i => ⟨mlProj (c.1 i).val, hmem i⟩
  have hkron' : ∀ i j, MvPolynomial.coeff (c.2.1 i) (R' j).val =
      if i = j then c.2.2 i else 0 := by
    intro i j
    show MvPolynomial.coeff (c.2.1 i) (mlProj (c.1 j).val) = _
    have hml : Finsupp.IsMultilinear (c.2.1 i) := by
      show Finsupp.IsMultilinear (IdentityMinor.tagMono F (tseitinAt n) pack κ i)
      exact tagMono_isMultilinear (tseitinAt n) pack κ i
    rw [coeff_mlProj_of_isMultilinear_mono _ _ hml]
    exact hkron i j
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
  have hfr := finrank_ge_of_linearIndependent mlV _ R' hli
  calc mlBlockedSpdpRank (tseitinPartition n) κ ℓ (tseitinPoly F n) ≥
        Nat.choose pack.selected.length κ := hfr
    _ ≥ Nat.choose (n / 30) κ := by
        apply Nat.choose_le_choose
        have := pack.size_bound; rw [hv] at this; exact this
    _ ≥ n ^ (Nat.log 2 n / 4) := hn₀ n hn₀'

/-- Concrete-threshold version: for n ≥ 2^804 and even, the NP lower bound holds
    at any ℓ.  This avoids existential quantification over the threshold. -/
theorem np_ml_lower_bound_concrete (F : Type*) [Field F] [Nontrivial F] (ℓ : ℕ)
    (n : ℕ) (hn : n ≥ 2 ^ 804) (heven : 2 ∣ n) :
    mlBlockedSpdpRank (tseitinPartition n) (Nat.log 2 n) ℓ
      (tseitinPoly F n) ≥ n ^ (Nat.log 2 n / 4) := by
  have hn1024 : n ≥ 1024 := by
    have : (1024 : ℕ) ≤ 2 ^ 804 := by
      calc (1024 : ℕ) = 2 ^ 10 := by norm_num
      _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hv := tseitinAt_vertices n (by omega) heven
  have pack := Tseitin.disjoint_packing_exists (tseitinAt n) (by omega)
  let κ := Nat.log 2 n
  have hκ : κ ≤ pack.selected.length := by
    have hps := pack.size_bound; rw [hv] at hps
    exact (log2_le_div30 n (by omega)).trans hps
  let c := IdentityMinor.identity_minor_components (F := F) (tseitinAt n) pack κ ℓ hκ
  obtain ⟨hsigns, hkron⟩ := IdentityMinor.identity_minor_components_signs
    (tseitinAt n) pack κ ℓ hκ (F := F)
  let mlV := mlBlockedSpdpSubspace (tseitinPartition n) κ ℓ (tseitinPoly F n)
  have hmem : ∀ i, mlProj (c.1 i).val ∈ mlV :=
    fun i => rowPoly_mem_ml_subspace (tseitinAt n) _ pack κ ℓ i
      (fun cs hnd _ _ => IdentityMinor.tseitinPartition_admissible_general (tseitinAt n) cs hnd)
  let R' : Fin (Nat.choose pack.selected.length κ) → ↥mlV :=
    fun i => ⟨mlProj (c.1 i).val, hmem i⟩
  have hkron' : ∀ i j, MvPolynomial.coeff (c.2.1 i) (R' j).val =
      if i = j then c.2.2 i else 0 := by
    intro i j
    show MvPolynomial.coeff (c.2.1 i) (mlProj (c.1 j).val) = _
    have hml : Finsupp.IsMultilinear (c.2.1 i) := by
      show Finsupp.IsMultilinear (IdentityMinor.tagMono F (tseitinAt n) pack κ i)
      exact tagMono_isMultilinear (tseitinAt n) pack κ i
    rw [coeff_mlProj_of_isMultilinear_mono _ _ hml]
    exact hkron i j
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
  have hfr := finrank_ge_of_linearIndependent mlV _ R' hli
  -- Binomial bound: n ≥ 2^804 ≥ 2^20
  have hn20 : n ≥ 2 ^ 20 := le_trans (by
    calc (2 : ℕ) ^ 20 ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)) hn
  have hbin : Nat.choose (n / 30) (Nat.log 2 n) ≥ n ^ (Nat.log 2 n / 4) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  calc mlBlockedSpdpRank (tseitinPartition n) κ ℓ (tseitinPoly F n) ≥
        Nat.choose pack.selected.length κ := hfr
    _ ≥ Nat.choose (n / 30) κ := by
        apply Nat.choose_le_choose
        have := pack.size_bound; rw [hv] at this; exact this
    _ ≥ n ^ (Nat.log 2 n / 4) := hbin

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
  intro q ⟨S, mul, hlen, hdeg, hvars, hadm, hq⟩
  simp only [Submodule.mem_map, SetLike.mem_coe]
  -- The preimage in the big space
  let S' := S.map f
  let q := iterDerivList S' p
  let mul' := MvPolynomial.rename f mul
  -- Candidate preimage: mlProj(mul' * q) in the big subspace
  refine ⟨mlProj (mul' * q), ?_, ?_⟩
  · -- mlProj(mul' * q) ∈ mlBlockedSpdpSubspace B κ ℓ p
    apply Submodule.subset_span
    refine ⟨S', mul', by simp [S', hlen], ?_, ?_, ?_, rfl⟩
    · -- totalDegree
      exact le_trans (MvPolynomial.totalDegree_rename_le f mul) hdeg
    · -- mul'.vars ⊆ S'.toFinset: vars(rename f mul) ⊆ (S.map f).toFinset
      show (MvPolynomial.rename f mul).vars ⊆ (S.map f).toFinset
      intro v hv
      have hsub := MvPolynomial.vars_rename f mul
      have hv' := hsub hv
      simp only [Finset.mem_image] at hv'
      obtain ⟨w, hw, rfl⟩ := hv'
      rw [List.mem_toFinset]
      have hwS : w ∈ S := List.mem_toFinset.mp (hvars hw)
      exact List.mem_map.mpr ⟨w, hwS, rfl⟩
    · -- isBlockAdmissible B (S.map f) from isBlockAdmissible (pullback B f) S
      constructor
      · exact List.Nodup.map hf hadm.1
      · intro b
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
        exact hadm.2 b
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

theorem iterDerivList_eq_zero_of_totalDegree_lt {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (q : MvPolynomial (Fin n) F) (h : q.totalDegree < S.length) :
    iterDerivList S q = 0 := by
  unfold iterDerivList
  conv_lhs => rw [q.as_sum]
  rw [LowDeg.foldl_pderiv_finset_sum]
  apply Finset.sum_eq_zero
  intro s hs
  exact LowDeg.foldl_pderiv_monomial_zero S s _ (lt_of_le_of_lt (le_totalDegree hs) h)

-- Helper: iterDerivList distributes over addition
private theorem iterDerivList_add {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (p q : MvPolynomial (Fin n) F) :
    iterDerivList S (p + q) = iterDerivList S p + iterDerivList S q := by
  unfold iterDerivList; exact LowDeg.foldl_pderiv_add S p q

-- Helper: iterDerivList (p + C c) = iterDerivList p when S nonempty
private theorem iterDerivList_add_C {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F) (c : F) (hS : S ≠ []) :
    iterDerivList S (p + MvPolynomial.C c) = iterDerivList S p := by
  rw [iterDerivList_add, iterDerivList_C_eq_zero S c hS, add_zero]

/-- Low-degree polynomials are invisible to SPDP rank at order κ > totalDegree.
    Generalizes mlBlockedSpdpRank_add_const from constants to bounded-degree polys. -/
theorem mlBlockedSpdpRank_add_lowDeg (F : Type*) [Field F] [Nontrivial F]
    {n : ℕ} (B : BlockPartition n) (κ ℓ : ℕ) (p q : MvPolynomial (Fin n) F)
    (hq : q.totalDegree < κ) :
    mlBlockedSpdpRank B κ ℓ (p + q) = mlBlockedSpdpRank B κ ℓ p := by
  unfold mlBlockedSpdpRank
  have hsub : mlBlockedSpdpSubspace B κ ℓ (p + q) = mlBlockedSpdpSubspace B κ ℓ p := by
    unfold mlBlockedSpdpSubspace
    have hgen : ∀ (r : MvPolynomial (Fin n) F),
        (∃ S m, S.length = κ ∧ m.totalDegree ≤ ℓ ∧ m.vars ⊆ S.toFinset ∧ isBlockAdmissible B S ∧
          r = mlProj (m * iterDerivList S (p + q))) ↔
        (∃ S m, S.length = κ ∧ m.totalDegree ≤ ℓ ∧ m.vars ⊆ S.toFinset ∧ isBlockAdmissible B S ∧
          r = mlProj (m * iterDerivList S p)) := by
      intro r; constructor <;> intro ⟨S, m, hlen, hdeg, hvars, hadm, hr⟩
      · have : iterDerivList S q = 0 :=
          iterDerivList_eq_zero_of_totalDegree_lt S q (by omega)
        rw [iterDerivList_add, this, add_zero] at hr
        exact ⟨S, m, hlen, hdeg, hvars, hadm, hr⟩
      · have hq0 : iterDerivList S q = 0 :=
          iterDerivList_eq_zero_of_totalDegree_lt S q (by omega)
        exact ⟨S, m, hlen, hdeg, hvars, hadm, by
          rw [hr, iterDerivList_add, hq0, add_zero]⟩
    congr 1; ext r'; exact hgen r'
  rw [hsub]

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
        (∃ S m, S.length = κ ∧ m.totalDegree ≤ ℓ ∧ m.vars ⊆ S.toFinset ∧ isBlockAdmissible B S ∧
          r = mlProj (m * iterDerivList S (p + MvPolynomial.C c))) ↔
        (∃ S m, S.length = κ ∧ m.totalDegree ≤ ℓ ∧ m.vars ⊆ S.toFinset ∧ isBlockAdmissible B S ∧
          r = mlProj (m * iterDerivList S p)) := by
      intro r; constructor <;> intro ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
      · exact ⟨S, m, hlen, hdeg, hvars, hadm, by
          rw [hq, iterDerivList_add_C S p c (by intro h; subst h; simp at hlen; omega)]⟩
      · exact ⟨S, m, hlen, hdeg, hvars, hadm, by
          rw [hq, iterDerivList_add_C S p c (by intro h; subst h; simp at hlen; omega)]⟩
    have hset : { q : MvPolynomial (Fin n) F | ∃ S m, S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        m.vars ⊆ S.toFinset ∧ isBlockAdmissible B S ∧ q = mlProj (m * iterDerivList S (p + MvPolynomial.C c))} =
      { q | ∃ S m, S.length = κ ∧ m.totalDegree ≤ ℓ ∧ m.vars ⊆ S.toFinset ∧ isBlockAdmissible B S ∧
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

/-- Template-induced block partition for the compiled variable space.
    Mirrors tseitinPartition on witness variables (indices < npNumVars n):
    - Selector variables → per-clause blocks (block c+1)
    - Non-selector witness vars → block 0
    Computation variables (indices ≥ npNumVars n) → block 0.

    This is COARSER than the identity partition, making block-admissible
    derivatives more restrictive. Width⇒Rank (Theorem 32) uses this
    to bound Γ^B ≤ n^O(1).

    Block layout:
    - Block 0: literal witness vars + all computation vars
    - Block c+1: selector variable for clause c -/
noncomputable def compiledPartition (M : DTM) (n : ℕ) :
    BlockPartition (numVars M n (Nat.log 2 n)) where
  numBlocks := numVars M n (Nat.log 2 n)
  assign := fun v =>
    let Φ := tseitinAt n
    let base := Φ.graph.numEdges + 3 * Φ.clauses.length
    if h : v.val ≥ base ∧ v.val - base < Φ.clauses.length ∧
           v.val < npNumVars n then
      ⟨v.val - base + 1, by omega⟩
    else
      ⟨0, by omega⟩

/-- The compiled partition refines tseitinPartition via witnessInclusion:
    if two witness vars are in the same compiled block, they're in the same tseitin block. -/
theorem compiledPartition_refines_tseitin (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (i j : Fin (npNumVars n))
    (h_eq : (compiledPartition M n).assign
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt h_le⟩ =
     (compiledPartition M n).assign
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt h_le⟩) :
    (tseitinPartition n).assign i = (tseitinPartition n).assign j := by
  -- compiledPartition on witness vars mirrors tseitinPartition exactly.
  -- Key: for Fin(npNumVars n), v.val < npNumVars n always holds,
  -- so the three-way compiled condition reduces to the two-way tseitin condition.
  unfold compiledPartition at h_eq
  unfold tseitinPartition IdentityMinor.tseitinPartition
  have hi_np : i.val < npNumVars n := i.isLt
  have hj_np : j.val < npNumVars n := j.isLt
  -- Simplify: the dite in compiledPartition has three conjuncts, third is v<npNumVars
  -- For witness vars this third conjunct is always true
  -- So compiledPartition(i) = tseitinPartition(i) for witness vars
  -- Work at the level of Fin.val
  ext
  simp only [Fin.val_mk] at h_eq ⊢
  -- Split on the four cases of (i selector?) × (j selector?)
  by_cases hi : i.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
    i.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length
  · -- i is a selector
    have hi3 : i.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
      i.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length ∧
      (⟨i.val, Nat.lt_of_lt_of_le hi_np h_le⟩ : Fin _).val < npNumVars n := ⟨hi.1, hi.2, hi_np⟩
    simp only [dif_pos hi3, Fin.val_mk] at h_eq
    by_cases hj : j.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
      j.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length
    · have hj3 : j.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
        j.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length ∧
        (⟨j.val, Nat.lt_of_lt_of_le hj_np h_le⟩ : Fin _).val < npNumVars n := ⟨hj.1, hj.2, hj_np⟩
      simp only [dif_pos hj3, Fin.mk.injEq] at h_eq
      simp only [dif_pos hi, dif_pos hj, Fin.val_mk]; omega
    · have hj3 : ¬(j.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
        j.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length ∧
        (⟨j.val, Nat.lt_of_lt_of_le hj_np h_le⟩ : Fin _).val < npNumVars n) := by
        intro ⟨a, b, _⟩; exact hj ⟨a, b⟩
      simp only [dif_neg hj3, Fin.mk.injEq] at h_eq; omega
  · -- i is not a selector
    have hi3 : ¬(i.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
      i.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length ∧
      (⟨i.val, Nat.lt_of_lt_of_le hi_np h_le⟩ : Fin _).val < npNumVars n) := by
      intro ⟨a, b, _⟩; exact hi ⟨a, b⟩
    simp only [dif_neg hi3, Fin.val_mk] at h_eq
    by_cases hj : j.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
      j.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length
    · have hj3 : j.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
        j.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length ∧
        (⟨j.val, Nat.lt_of_lt_of_le hj_np h_le⟩ : Fin _).val < npNumVars n := ⟨hj.1, hj.2, hj_np⟩
      simp only [dif_pos hj3, Fin.mk.injEq] at h_eq; omega
    · simp only [dif_neg hi, dif_neg hj]

/-- Canonical inclusion of witness variables into compiled variable space. -/
noncomputable def witnessInclusion (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    Fin (npNumVars n) → Fin (numVars M n (Nat.log 2 n)) :=
  fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt h_le⟩

theorem witnessInclusion_injective (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    Function.Injective (witnessInclusion M n h_le) :=
  fun a b h => Fin.ext (Fin.mk.inj h)

/-- The verifier sheet in PRODUCT form: ∏_c (1 - z_c g_c).
    Used for the NP-side lower bound (identity-minor structure).
    WARNING: has degree O(n) and EXPONENTIAL SPDP rank. -/
noncomputable def verifierSheetOf (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n : ℕ) (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    MvPolynomial (Fin (numVars M n (Nat.log 2 n))) F :=
  MvPolynomial.rename (witnessInclusion M n h_le) (tseitinPoly F n)

/-- The verifier constraint for clause c: z_c × g_c.
    This has degree ≤ 4 (selector degree 1 + gadget degree 3) and width ≤ 4. -/
noncomputable def verifierConstraint (F : Type*) [CommRing F] [Nontrivial F]
    (n : ℕ) (c : Fin (tseitinAt n).clauses.length) :
    MvPolynomial (Fin (npNumVars n)) F :=
  MvPolynomial.X (selectorIdx (tseitinAt n) c) * clauseGadget F (tseitinAt n) c

/-- Sum-of-squares verifier: Σ_c (z_c g_c)².
    Each term has degree ≤ 8 and width ≤ 4.
    Agrees with the product verifier on the Boolean cube. -/
noncomputable def verifierSoS (F : Type*) [CommRing F] [Nontrivial F] (n : ℕ) :
    MvPolynomial (Fin (npNumVars n)) F :=
  Finset.univ.sum (fun c => (verifierConstraint F n c) ^ 2)

/-- Degree bound for one verifier constraint: totalDegree ≤ 4. -/
private theorem verifierConstraint_totalDegree (F : Type*) [CommRing F] [Nontrivial F]
    (n : ℕ) (c : Fin (tseitinAt n).clauses.length) :
    (verifierConstraint F n c).totalDegree ≤ 4 := by
  unfold verifierConstraint
  calc
    (MvPolynomial.X (R := F) (selectorIdx (tseitinAt n) c) * clauseGadget F (tseitinAt n) c).totalDegree
        ≤ (MvPolynomial.X (R := F) (selectorIdx (tseitinAt n) c)).totalDegree
          + (clauseGadget F (tseitinAt n) c).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + 3 := by
        have hx : (MvPolynomial.X (R := F) (selectorIdx (tseitinAt n) c)).totalDegree ≤ 1 := by
          simpa [MvPolynomial.totalDegree_X]
        have hg : (clauseGadget F (tseitinAt n) c).totalDegree ≤ 3 :=
          clauseGadget_totalDegree F (tseitinAt n) c
        omega
    _ = 4 := by norm_num

/-- Sum-of-squares verifier has totalDegree ≤ 8 -/
theorem verifierSoS_totalDegree (F : Type*) [CommRing F] [Nontrivial F] (n : ℕ) :
    (verifierSoS F n).totalDegree ≤ 8 := by
  unfold verifierSoS
  classical
  let t : Finset (Fin (tseitinAt n).clauses.length) := Finset.univ
  have hsum : (t.sum (fun c => (verifierConstraint F n c) ^ 2)).totalDegree ≤ 8 := by
    subst t
    refine Finset.induction_on (Finset.univ : Finset (Fin (tseitinAt n).clauses.length)) ?h0 ?hstep
    · simp [MvPolynomial.totalDegree_zero]
    · intro a s ha ih
      have ha8 : (((verifierConstraint F n a) ^ 2)).totalDegree ≤ 8 := by
        calc
          ((verifierConstraint F n a) ^ 2).totalDegree
              ≤ 2 * (verifierConstraint F n a).totalDegree := MvPolynomial.totalDegree_pow _ _
          _ ≤ 2 * 4 := Nat.mul_le_mul_left 2 (verifierConstraint_totalDegree F n a)
          _ = 8 := by norm_num
      rw [Finset.sum_insert ha]
      exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le ha8 ih)
  simpa using hsum

/-- The full compiled polynomial in SUM-OF-SQUARES form (Paper §17.1 Theorem 92):
    P_{M,n} = 1 - verifierSoS - violationPoly
    = 1 - Σ_c (z_c g_c)² - Σ_i c_i²

    This has CONSTANT degree (≤ 8) and POLYNOMIAL SPDP rank.
    Used for the P-side upper bound. -/
noncomputable def fullCompiledPolySoS (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n : ℕ) (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    MvPolynomial (Fin (numVars M n (Nat.log 2 n))) F :=
  1 - MvPolynomial.rename (witnessInclusion M n h_le) (verifierSoS F n)
    - violationPolyOf F M n

/-- fullCompiledPolySoS has totalDegree ≤ 8 -/
theorem fullCompiledPolySoS_totalDegree (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n : ℕ) (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    (fullCompiledPolySoS F M n h_le).totalDegree ≤ 8 := by
  unfold fullCompiledPolySoS
  have hrename_le :
      (MvPolynomial.rename (witnessInclusion M n h_le) (verifierSoS F n)).totalDegree
        ≤ (verifierSoS F n).totalDegree :=
    MvPolynomial.totalDegree_rename_le (witnessInclusion M n h_le) (verifierSoS F n)
  have hrename8 :
      (MvPolynomial.rename (witnessInclusion M n h_le) (verifierSoS F n)).totalDegree ≤ 8 :=
    le_trans hrename_le (verifierSoS_totalDegree F n)
  have hsub1 :
      (1 - MvPolynomial.rename (witnessInclusion M n h_le) (verifierSoS F n)).totalDegree
        ≤ max 0 8 := by
    calc
      (1 - MvPolynomial.rename (witnessInclusion M n h_le) (verifierSoS F n)).totalDegree
          ≤ max (1 : MvPolynomial _ F).totalDegree
              (MvPolynomial.rename (witnessInclusion M n h_le) (verifierSoS F n)).totalDegree :=
              MvPolynomial.totalDegree_sub _ _
      _ ≤ max 0 8 := by
          apply max_le_max
          · simp [MvPolynomial.totalDegree_one]
          · exact hrename8
  calc
    (1 - MvPolynomial.rename (witnessInclusion M n h_le) (verifierSoS F n)
      - violationPolyOf F M n).totalDegree
        ≤ max
            (1 - MvPolynomial.rename (witnessInclusion M n h_le) (verifierSoS F n)).totalDegree
            (violationPolyOf F M n).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
    _ ≤ max (max 0 8) 4 := by
          exact max_le_max hsub1 (violationPolyOf_totalDegree F M n)
    _ = 8 := by norm_num

/-- The old product-form compiled polynomial. Kept for extraction_rank_monotone. -/
noncomputable def fullCompiledPoly (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n : ℕ) (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    MvPolynomial (Fin (numVars M n (Nat.log 2 n))) F :=
  verifierSheetOf F M n h_le + violationPolyOf F M n

/-- aeval with degree-1 substitutions on a monomial: degree ≤ monomial degree -/
private theorem aeval_monomial_totalDegree_le {n m : ℕ} {F : Type*} [CommRing F]
    (g : Fin m → MvPolynomial (Fin n) F)
    (hg : ∀ i, (g i).totalDegree ≤ 1)
    (s : Fin m →₀ ℕ) (c : F) :
    ((aeval g) (monomial s c)).totalDegree ≤ s.sum (fun _ k => k) := by
  rw [aeval_monomial]
  calc ((algebraMap F _ c * s.prod (fun i k => g i ^ k)).totalDegree)
      ≤ (algebraMap F (MvPolynomial (Fin n) F) c).totalDegree +
        (s.prod (fun i k => g i ^ k)).totalDegree := totalDegree_mul _ _
    _ ≤ 0 + (s.prod (fun i k => g i ^ k)).totalDegree := by
        simp [totalDegree_C]
    _ = (s.prod (fun i k => g i ^ k)).totalDegree := by ring
    _ ≤ s.sum (fun i k => (g i ^ k).totalDegree) := by
        unfold Finsupp.prod; exact totalDegree_finset_prod _ _
    _ ≤ s.sum (fun i k => k * 1) := by
        apply Finsupp.sum_le_sum; intro i _
        exact le_trans (totalDegree_pow _ _) (Nat.mul_le_mul_left _ (hg i))
    _ = s.sum (fun _ k => k) := by congr 1; ext i k; ring

/-- totalDegree of Finset.sum ≤ bound when each summand ≤ bound -/
private theorem totalDegree_finset_sum_le' {ι σ : Type*} {F : Type*} [CommSemiring F]
    (t : Finset ι) (f : ι → MvPolynomial σ F) (d : ℕ)
    (h : ∀ i ∈ t, (f i).totalDegree ≤ d) :
    (∑ i ∈ t, f i).totalDegree ≤ d := by
  induction t using Finset.cons_induction with
  | empty => simp [totalDegree_zero]
  | cons a t ha ih =>
    rw [Finset.sum_cons]
    exact le_trans (totalDegree_add _ _) (max_le
      (h a (Finset.mem_cons_self a t))
      (ih (fun i hi => h i (Finset.mem_cons.mpr (Or.inr hi)))))

/-- aeval with degree-≤-1 substitutions doesn't increase totalDegree -/
private theorem aeval_totalDegree_le {n m : ℕ} {F : Type*} [CommRing F]
    (g : Fin m → MvPolynomial (Fin n) F)
    (hg : ∀ i, (g i).totalDegree ≤ 1)
    (p : MvPolynomial (Fin m) F) :
    ((aeval g) p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finset_sum_le'
  intro s hs
  exact le_trans (aeval_monomial_totalDegree_le g hg s _) (le_totalDegree hs)

/-- restrictPoly doesn't increase totalDegree (substitutes X or 0, both degree ≤ 1) -/
theorem restrictPoly_totalDegree_le {n m : ℕ} (F : Type*) [CommRing F] [Nontrivial F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (p : MvPolynomial (Fin m) F) :
    (restrictPoly F f hf p).totalDegree ≤ p.totalDegree := by
  unfold restrictPoly
  apply aeval_totalDegree_le
  intro i; split
  · exact le_of_eq (totalDegree_X _)
  · simp [totalDegree_zero]

/-- §34.1: tableau constraints restricted to witness vars have bounded degree.
    restrictPoly doesn't increase degree, and violationPolyOf has degree ≤ 4. -/
theorem tableau_restriction_lowDeg (F : Type*) [Field F] [Nontrivial F]
    (M : DTM) (n : ℕ) (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    (restrictPoly F (witnessInclusion M n h_le)
      (witnessInclusion_injective M n h_le) (violationPolyOf F M n)).totalDegree ≤ 4 :=
  le_trans (restrictPoly_totalDegree_le F _ _ _) (violationPolyOf_totalDegree F M n)

/-! ## Width⇒Rank decomposition (§9)

The Width⇒Rank theorem is decomposed into 3 sub-axioms corresponding
to the 3 mathematical ingredients of the paper's proof:

**Layer 1** (`iterDerivList_prod_leibniz`): The iterated Leibniz rule.
∂_S(∏ f_i) decomposes as a sum over "derivative assignments" — functions
that assign each derivative in S to one of the m factors. This is
standard multivariate calculus (binary product rule applied inductively).

**Layer 2** (`profile_count_le`): Stars-and-bars profile counting (Lemma 20).
The number of "derivative histograms" (how many derivatives per factor,
constrained to ≤ w per factor by block-admissibility) is bounded by
C(w+m, m) ≤ (w+m)^m. PROVED via Nat.choose_le_pow.

**Layer 3** (`within_profile_rank_le`): Within-profile dimension bound (Lemma 22).
For a fixed derivative histogram, the SPDP generators span a subspace of
bounded dimension. This uses the block-factorable structure: contributions
from different factors are (approximately) independent in the multilinear
coefficient space, giving a dimension bound via symmetric tensor products.
This is the irreducible hard core of the proof.

The combined bound:
  rank ≤ #profiles × max(dim/profile)
       ≤ (w+m)^m × (w+1)^(m·w)
       ≤ (m·w)^(3w)
-/

/-- Layer 2: Profile counting (Lemma 20, §9.1). PROVED.
    C(w+m, m) ≤ (w+m)^m by Nat.choose_le_pow. -/
theorem profile_count_le (m width : ℕ) :
    Nat.choose (width + m) m ≤ (width + m) ^ m :=
  Nat.choose_le_pow _ _

/- Width⇒Rank (Theorem 23, §9): REMOVED — see compiled_spdp_rank_bound below.

    The generic product bound was FALSE for arbitrary products.
    Replaced by compiler-scoped axioms matching paper's Lemma 32.

    **Paper proof** (§9, ~10 pages, 3 layers):

    Layer 1 — Leibniz product rule:
      ∂_S(∏ f_i) = Σ_{α: S→Fin m} ∏_i ∂_{α⁻¹(i)} f_i
      Standard multivariate calculus. Binary case: Derivation.leibniz.
      Extended to Finset.prod by induction.

    Layer 2 — Profile counting (Lemma 20):
      Group assignments by histogram h(i) = |α⁻¹(i)|.
      Block-admissibility forces h(i) ≤ w (≤ w blocks per factor,
      ≤ 1 derivative per block). Number of histograms:
        |H| ≤ C(w+m, m) ≤ (w+m)^m   [stars-and-bars]
      PROVED in this file as `profile_count_le` via `Nat.choose_le_pow`.

    Layer 3 — Within-profile dimension (Lemma 22):
      For fixed histogram h, generators span V_h with
        dim(V_h) ≤ ∏_i C(h(i) + d_i - 1, d_i - 1) ≤ (w+1)^(m·w)
      Uses dim(Sym^k W) = C(k + dim W - 1, dim W - 1) and the
      block-factorable structure (different factors contribute
      independently to the multilinear coefficient space).

    Combined: rank ≤ Σ_h dim(V_h) ≤ |H| · max dim(V_h)
            ≤ (w+m)^m · (w+1)^(m·w) ≤ (m·w)^(3·w).

    **Why this bound is correct for our usage** (width=4, m≤n):
      (m·4)^12 ≤ (4n)^12 = 4^12 · n^12 ≤ n^25 for n ≥ 4.
      The exponent 3w = 12 is constant because width = O(1).

    **§9 Profile compression axiom** (replaces monolithic width_to_rank).

    For a product of m factors, each with ≤ w vars, degree ≤ w,
    touching ≤ w blocks, the SPDP subspace has finrank ≤ (m+w+1)^(w+1).

    Proof outline (§9 Lemmas 29-31):
    • Layer 1 (Leibniz): derivatives decompose by allocation to factors
    • Layer 2 (Profile): group allocations by histogram over types
    • Layer 3 (Commutativity): allocation result depends on derivative SET
    • Profile compression: single-type ⇒ profile is just k ∈ {0,...,m}
    • Per-profile: generators ⊂ Sym^k(W) where dim W ≤ w+1
    • Total: (m+1) × (m+w+1)^w ≤ (m+w+1)^(w+1)

    The paper's Lemma 32 gives this bound specifically for compiled polynomials
    under the NF–SPDP compiler with radius-1 locality, finite local alphabet,
    and interface-anonymous profile compression.

    **Important**: This is NOT a generic product bound. It relies on compiler
    structure (bounded normal forms, O(1) interface types, profile compression).
    A naive product bound for m factors of width w would give C(m,κ) generators,
    which is exponential for κ = Θ(log n) and m = Θ(n).

    The compiled polynomial bound uses:
    - R = O((log n)^c) live interfaces (NOT m = n factors)
    - O(1) interface types (from finite local monoid)
    - Profile compression: |H| ≤ R^O(1) (independent of κ)
    - Per-profile dim ≤ R^O(1) (via Sym^{h(σ)}(W_σ), dim W_σ = O(1))
    - Total: R^O(1) = (log n)^O(1) = n^O(1)

    Regime: (κ, ℓ) = Θ(log n). The axiom bakes in κ ≥ 5 and ℓ = κ,
    matching the proof's parameter choice. -/

-- ═══════════════════════════════════════════════════════════════════════
-- Rename infrastructure for axiom elimination
-- ═══════════════════════════════════════════════════════════════════════

/-- pderiv at a variable not in range(f) kills rename f p. -/
theorem pderiv_rename_zero {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (v : Fin m) (hv : v ∉ Set.range f)
    (p : MvPolynomial (Fin n) F) :
    MvPolynomial.pderiv v (MvPolynomial.rename f p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.pderiv_C]
  | add p q hp hq =>
    rw [map_add, map_add (MvPolynomial.pderiv v), hp, hq, add_zero]
  | mul_X p j ih =>
    have hne : v ≠ f j := fun h => hv ⟨j, h.symm⟩
    have h1 : MvPolynomial.rename f (p * MvPolynomial.X j) =
      MvPolynomial.rename f p * MvPolynomial.X (f j) := by
      rw [map_mul, MvPolynomial.rename_X]
    rw [h1]
    have hx : MvPolynomial.pderiv v (MvPolynomial.X (f j) : MvPolynomial (Fin m) F) = 0 := by
      rw [MvPolynomial.pderiv_X]; simp [Pi.single, Function.update, hne.symm]
    rw [MvPolynomial.pderiv_mul, hx, mul_zero, add_zero, ih, zero_mul]

/-- iterDerivList of rename at variables not in range gives 0.
    Proof by induction on S: at each step, either the head is outside range(f)
    (killed by pderiv_rename_zero) or inside (pushed through by pderiv_rename). -/
theorem iterDerivList_rename_zero {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (S : List (Fin m)) (hS : ∃ v ∈ S, v ∉ Set.range f)
    (p : MvPolynomial (Fin n) F) :
    iterDerivList S (MvPolynomial.rename f p) = 0 := by
  obtain ⟨v, hv_mem, hv_range⟩ := hS
  -- Induction on S, carrying v ∈ S and v ∉ range(f), generalizing p
  induction S generalizing p with
  | nil => simp at hv_mem
  | cons a rest ih =>
    show iterDerivList rest (MvPolynomial.pderiv a (MvPolynomial.rename f p)) = 0
    rcases List.mem_cons.mp hv_mem with rfl | hv_rest
    · -- v = a ∉ range(f): pderiv kills rename
      rw [pderiv_rename_zero f hf v hv_range p]
      unfold iterDerivList; exact foldl_pderiv_zero' rest
    · -- v ∈ rest
      by_cases ha : a ∈ Set.range f
      · -- a = f i: push pderiv inside rename, recurse
        obtain ⟨i, rfl⟩ := ha
        rw [MvPolynomial.pderiv_rename hf i p]
        exact ih (MvPolynomial.pderiv i p) hv_rest
      · -- a ∉ range(f): pderiv kills rename, then foldl gives 0
        rw [pderiv_rename_zero f hf a ha p]
        unfold iterDerivList; exact foldl_pderiv_zero' rest

/-- iterDerivList of rename at mapped variables = rename of iterDerivList. -/
theorem iterDerivList_rename {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    iterDerivList (S.map f) (MvPolynomial.rename f p) =
    MvPolynomial.rename f (iterDerivList S p) := by
  induction S generalizing p with
  | nil => unfold iterDerivList; simp
  | cons a rest ih =>
    show iterDerivList (rest.map f) (MvPolynomial.pderiv (f a) (MvPolynomial.rename f p)) =
      MvPolynomial.rename f (iterDerivList rest (MvPolynomial.pderiv a p))
    rw [MvPolynomial.pderiv_rename hf a p]; exact ih _

/-- IsMultilinear is preserved by mapDomain with injective f. -/
private theorem isMultilinear_mapDomain_iff {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (s : Fin n →₀ ℕ) :
    Finsupp.IsMultilinear (Finsupp.mapDomain f s) ↔ Finsupp.IsMultilinear s := by
  constructor
  · -- mapDomain f s multilinear → s multilinear
    intro h i
    have h1 : Finsupp.mapDomain f s (f i) ≤ 1 := h (f i)
    rwa [Finsupp.mapDomain_apply hf] at h1
  · -- s multilinear → mapDomain f s multilinear
    intro h j
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      have : Finsupp.mapDomain f s (f i) = s i := Finsupp.mapDomain_apply hf s i
      rw [this]; exact h i
    · have : Finsupp.mapDomain f s j = 0 := Finsupp.mapDomain_notin_range s j hj
      simp [this]

/-- mlProj commutes with rename for injective f.
    mlProj = Finsupp.filter IsMultilinear, and rename f maps monomials via
    mapDomain f. Since IsMultilinear is preserved by injective mapDomain,
    the filter and mapDomain commute. -/
private theorem mlProj_rename_monomial {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (s : Fin n →₀ ℕ) (a : F) :
    mlProj (MvPolynomial.rename f (MvPolynomial.monomial s a)) =
    MvPolynomial.rename f (mlProj (MvPolynomial.monomial s a)) := by
  rw [MvPolynomial.rename_monomial, mlProj_monomial, mlProj_monomial,
    isMultilinear_mapDomain_iff f hf s]
  split
  · exact (MvPolynomial.rename_monomial f s a).symm
  · exact (map_zero (MvPolynomial.rename f)).symm

theorem mlProj_rename {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (p : MvPolynomial (Fin n) F) :
    mlProj (MvPolynomial.rename f p) = MvPolynomial.rename f (mlProj p) := by
  -- Both mlProj (= mlProjHom) and rename f are additive.
  -- Reduce to monomials via as_sum.
  -- Both mlProj and rename f are additive. Reduce to monomials.
  -- Use: p = ∑ s ∈ support, monomial s (coeff s p)
  -- Then mlProj(rename f p) = ∑ mlProj(rename f (mono s)) = ∑ rename f(mlProj(mono s)) = rename f(mlProj p)
  let g := fun s => MvPolynomial.monomial s (MvPolynomial.coeff s p)
  have hp : p = p.support.sum g := MvPolynomial.as_sum p
  -- LHS: mlProj(rename f p) = mlProjHom F (rename f (∑ g)) = mlProjHom F (∑ rename f ∘ g)
  -- = ∑ mlProjHom F (rename f (g s)) = ∑ mlProj(rename f (g s))
  -- RHS: rename f (mlProj p) = rename f (mlProjHom F (∑ g))
  -- = rename f (∑ mlProjHom F (g s)) = ∑ rename f (mlProj(g s))
  change mlProjHom F (MvPolynomial.rename f p) =
    MvPolynomial.rename f (mlProjHom F p)
  rw [hp, map_sum (MvPolynomial.rename f), map_sum (mlProjHom F),
    map_sum (mlProjHom F), map_sum (MvPolynomial.rename f)]
  exact Finset.sum_congr rfl fun s _ => mlProj_rename_monomial f hf s _

/-- If all elements of S are in range(f), we can extract a preimage list. -/
private lemma preimage_list {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (S : List (Fin m)) (hS : ∀ v ∈ S, v ∈ Set.range f) :
    ∃ S' : List (Fin n), S'.map f = S := by
  induction S with
  | nil => exact ⟨[], rfl⟩
  | cons a rest ih =>
    have ha : a ∈ Set.range f := hS a (by simp)
    obtain ⟨i, rfl⟩ := ha
    have ih' := ih (fun v hv => hS v (by simp [hv]))
    obtain ⟨rest', hrest'⟩ := ih'
    exact ⟨i :: rest', by rw [List.map_cons, hrest']⟩

/-- If mult.vars ⊆ range(f), then rename f (restrictPoly mult) = mult. -/
private lemma rename_restrictPoly_of_vars_range {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (mult : MvPolynomial (Fin m) F) (h : ↑mult.vars ⊆ Set.range f) :
    MvPolynomial.rename f (restrictPoly F f hf mult) = mult := by
  -- rename f ∘ restrictPoly agrees with id on vars(mult)
  -- Use: aeval_eq_aeval_of_forall_mem_vars or direct computation
  -- Show the two AlgHoms agree on X j for j ∈ vars(mult)
  -- comp(rename f, restrictPoly) vs AlgHom.id
  -- Then use MvPolynomial.algHom_ext or funext on support
  -- Use aeval_ite_mem_eq_self: aeval (fun j => if j ∈ s then X j else 0) p = p when vars ⊆ s
  -- First show rename f ∘ restrictPoly = aeval (fun j => if j ∈ range f then X j else 0)
  -- as AlgHoms:
  have heq : ((MvPolynomial.rename f).comp (restrictPoly F f hf)) =
      MvPolynomial.aeval (fun j => if (j ∈ Set.range f) then MvPolynomial.X j else (0 : MvPolynomial (Fin m) F)) := by
    ext j
    simp only [AlgHom.comp_apply, restrictPoly_X, MvPolynomial.aeval_X]
    by_cases hj : ∃ i, f i = j
    · rw [dif_pos hj, MvPolynomial.rename_X, if_pos ⟨hj.choose, hj.choose_spec⟩]
      simp [hj.choose_spec]
    · rw [dif_neg hj, map_zero]
      rw [if_neg]; intro ⟨i, hi⟩; exact hj ⟨i, hi⟩
  rw [show MvPolynomial.rename f (restrictPoly F f hf mult) =
    ((MvPolynomial.rename f).comp (restrictPoly F f hf)) mult from rfl, heq]
  exact MvPolynomial.aeval_ite_mem_eq_self mult h

/-- Block admissibility pulls back along injective maps. -/
private lemma isBlockAdmissible_pullback {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : BlockPartition m) (S' : List (Fin n))
    (hadm : isBlockAdmissible B (S'.map f)) :
    isBlockAdmissible (pullbackPartition B f) S' := by
  constructor
  · -- Nodup: S'.map f nodup + f injective → S' nodup
    exact ((List.nodup_map_iff hf).mp (And.left hadm))
  · intro b
    -- Filter S' for block b in pullback = filter (S'.map f) for block b in B
    have hfm : (S'.filter (fun i => (pullbackPartition B f).assign i = b)) =
      (S'.filter (fun i => B.assign (f i) = b)) := by rfl
    rw [hfm]
    -- (S'.map f).filter(P) = (S'.filter(P∘f)).map f, so same length
    have hlen : ∀ (L : List (Fin n)), ((L.map f).filter (fun j => B.assign j = b)).length =
        (L.filter (fun i => B.assign (f i) = b)).length := by
      intro L; induction L with
      | nil => simp
      | cons a rest ih =>
        simp only [List.map_cons, List.filter_cons]
        by_cases h : B.assign (f a) = b <;> simp [h, ih]
    rw [← hlen]; exact And.right hadm b

/-- restrictPoly preserves vars within preimage of range(f). -/
private lemma restrictPoly_vars_subset {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (mult : MvPolynomial (Fin m) F) (S' : List (Fin n))
    (hvars : mult.vars ⊆ (S'.map f).toFinset) :
    (restrictPoly F f hf mult).vars ⊆ S'.toFinset := by
  -- Strategy: show i ∈ vars(restrictPoly mult) → f i ∈ vars(mult) → f i ∈ (S'.map f).toFinset
  -- → i ∈ S'.toFinset (by injectivity)
  -- For the first step: rename f (restrictPoly mult) = mult (by rename_restrictPoly_of_vars_range)
  -- and vars(rename f q) ⊆ vars(q).image f, so mult.vars ⊆ (restrictPoly mult).vars.image f
  -- Reverse: i ∈ vars(q) → f i ∈ vars(rename f q) for injective f
  -- We prove this by showing support maps injectively
  intro i hi
  -- We know rename f (restrictPoly mult) = mult
  have h_range : ↑mult.vars ⊆ Set.range f := by
    intro v hv; obtain ⟨j, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (hvars (Finset.mem_coe.mpr hv)))
    exact ⟨j, rfl⟩
  have h_eq := rename_restrictPoly_of_vars_range f hf mult h_range
  -- i ∈ vars(restrictPoly mult), so coeff of some monomial with i > 0 is nonzero
  -- After rename f, f(i) must appear in vars(mult)
  -- Use: vars_rename gives (rename f q).vars ⊆ q.vars.image f
  -- For the reverse with injective f, use rename_injective + support
  -- Simpler: use that restrictPoly mult = restrictPoly (rename f (restrictPoly mult))
  -- = restrictPoly mult. Not helpful.
  -- Direct approach: show f i ∈ mult.vars from h_eq
  -- rename f maps support injectively, so f i ∈ (rename f (restrictPoly mult)).vars
  -- = mult.vars
  have h_fi_mem : f i ∈ mult.vars := by
    rw [← h_eq]
    -- Need: i ∈ q.vars → f i ∈ (rename f q).vars for injective f
    -- This follows from: support(rename f q) = support(q).map (mapDomain f) injectively
    -- and vars = degrees = biUnion of support
    rw [MvPolynomial.mem_vars] at hi ⊢
    obtain ⟨d, hd_supp, hd_i⟩ := hi
    refine ⟨Finsupp.mapDomain f d, ?_, ?_⟩
    · rw [MvPolynomial.mem_support_iff]
      rw [show MvPolynomial.coeff (Finsupp.mapDomain f d) (MvPolynomial.rename f (restrictPoly F f hf mult)) =
        MvPolynomial.coeff d (restrictPoly F f hf mult) from
        MvPolynomial.coeff_rename_mapDomain f hf _ d]
      rwa [← MvPolynomial.mem_support_iff]
    · rw [Finsupp.mem_support_iff]
      rw [Finsupp.mapDomain_apply hf]
      rwa [← Finsupp.mem_support_iff]
  -- Now f i ∈ mult.vars ⊆ (S'.map f).toFinset
  have h_fi_S := hvars h_fi_mem
  rw [List.mem_toFinset, List.mem_map] at h_fi_S
  obtain ⟨j, hj_mem, hj_eq⟩ := h_fi_S
  rw [List.mem_toFinset]
  exact hf hj_eq ▸ hj_mem

/-- The B-subspace of rename(f,p) embeds into image of pullback-subspace under rename f. -/
private lemma mlBlockedSpdpSubspace_rename_le_map {n m : ℕ} {F : Type*} [Field F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : BlockPartition m) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspace B κ ℓ (MvPolynomial.rename f p) ≤
    Submodule.map (MvPolynomial.rename f).toLinearMap
      (mlBlockedSpdpSubspace (pullbackPartition B f) κ ℓ p) := by
  rw [mlBlockedSpdpSubspace, Submodule.span_le]
  intro q hq
  obtain ⟨S, mult, hlen, hdeg, hvars, hadm, hq_eq⟩ := hq
  -- Case split: is every element of S in range(f)?
  by_cases h_all : ∀ v ∈ S, v ∈ Set.range f
  · -- All in range(f): construct preimage, lift to pullback generator
    obtain ⟨S', hS'⟩ := preimage_list f hf S h_all
    -- Rewrite iterDerivList using S' and iterDerivList_rename
    have h_iter : iterDerivList S (MvPolynomial.rename f p) =
        MvPolynomial.rename f (iterDerivList S' p) := by
      rw [← hS', iterDerivList_rename f hf S' p]
    -- mult.vars ⊆ S.toFinset = (S'.map f).toFinset
    have hvars' : mult.vars ⊆ (S'.map f).toFinset := by
      have : S = S'.map f := hS'.symm; subst this; exact hvars
    -- rename f (restrictPoly mult) = mult
    have h_mult : MvPolynomial.rename f (restrictPoly F f hf mult) = mult :=
      rename_restrictPoly_of_vars_range f hf mult (by
        intro v hv
        have hv_S : v ∈ (S'.map f).toFinset := hvars' (Finset.mem_coe.mpr hv)
        rw [List.mem_toFinset] at hv_S
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv_S
        exact ⟨i, rfl⟩)
    -- q = mlProj(mult * rename f (iterDerivList S' p))
    --   = mlProj(rename f (restrictPoly mult) * rename f (iterDerivList S' p))
    --   = mlProj(rename f (restrictPoly mult * iterDerivList S' p))
    --   = rename f (mlProj(restrictPoly mult * iterDerivList S' p))
    rw [hq_eq, h_iter, ← h_mult, ← map_mul (MvPolynomial.rename f),
      mlProj_rename f hf]
    -- Now show the preimage is in the pullback subspace
    apply Submodule.mem_map_of_mem
    apply Submodule.subset_span
    refine ⟨S', restrictPoly F f hf mult, ?_, ?_, ?_, ?_, rfl⟩
    · -- length preserved
      rw [← hS', List.length_map] at hlen; exact hlen
    · -- degree bound
      exact le_trans (restrictPoly_totalDegree_le F f hf mult) hdeg
    · -- vars subset
      exact restrictPoly_vars_subset f hf mult S' hvars'
    · -- admissibility
      exact isBlockAdmissible_pullback f hf B S' (hS' ▸ hadm)
  · -- Some element outside range(f): generator = 0
    push_neg at h_all
    obtain ⟨v, hv, hv_range⟩ := h_all
    rw [hq_eq, iterDerivList_rename_zero f hf S ⟨v, hv, hv_range⟩ p,
      mul_zero, mlProj_zero]
    exact Submodule.zero_mem _

theorem mlBlockedSpdpRank_rename_le {n m : ℕ} {F : Type*} [Field F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : BlockPartition m) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRank B κ ℓ (MvPolynomial.rename f p) ≤
    mlBlockedSpdpRank (pullbackPartition B f) κ ℓ p := by
  unfold mlBlockedSpdpRank
  calc Module.finrank F (mlBlockedSpdpSubspace B κ ℓ (MvPolynomial.rename f p))
      ≤ Module.finrank F (Submodule.map (MvPolynomial.rename f).toLinearMap
          (mlBlockedSpdpSubspace (pullbackPartition B f) κ ℓ p)) :=
        Submodule.finrank_mono (mlBlockedSpdpSubspace_rename_le_map f hf B κ ℓ p)
    _ ≤ Module.finrank F (mlBlockedSpdpSubspace (pullbackPartition B f) κ ℓ p) :=
        Submodule.finrank_map_le _ _

-- Compiled SPDP rank bound (paper's Lemma 32)
-- Decomposed into: profile count (Lemma 29) + per-profile dim (Lemma 31)
-- Both require compiler-structural properties: radius-1 locality,
-- finite local monoid, bounded normal forms.
-- Profile count: |H| ≤ n^5 (from O(1) types, R = O(log n))
-- Per-profile dim: ≤ n^5 (from Sym^{h(σ)}(W_σ), dim W_σ = O(1))
-- Together: rank ≤ n^10 ≤ n^25

/-- Profile decomposition of the compiled verifier sheet (paper's Lemmas 29+31).

    This axiom packages the paper's two key compiler-structural results:
    - **Lemma 29 (Profile count)**: The number of realizable interface-anonymous
      profiles is ≤ R^O(1) where R = O((log n)^c). Uses: finite local monoid
      (P2), bounded normal forms (Lemma 25), stars-and-bars on R interfaces
      with O(1) types. Profile = histogram h : Σ^{≤q} → ℕ with Σ h ≤ R.
    - **Lemma 31 (Per-profile dimension)**: Each profile subspace V_h has
      dim ≤ (log n)^O(1). Uses: per-interface space W_σ of constant dimension
      d₀ (P5), Sym^{h(σ)}(W_σ) dimension bound, product over O(1) types.

    The SPDP rank bound follows by subadditivity:
      Γ ≤ Σ_h dim(V_h) ≤ |H| × max dim(V_h) ≤ n^5 × n^5 = n^10.

    Both require compiler properties not yet formalized in Lean:
    (P1) radius-1 locality: each operation touches O(1) interfaces,
    (P2) finite local alphabet: |Σ| = O(1),
    (P3) R = O((log n)^c) live interfaces,
    (P5) constant-dim per-interface space W_σ,
    (P7) bounded normal forms via finite local monoid.

    NOTE: This axiom CANNOT be stated as a generic product bound.
    Counterexample: p = ∏ X_i (m=100, w=1, κ=50) gives
    C(100,50) ≈ 10^29 generators, far exceeding any polynomial bound.
    The bound holds ONLY for compiled polynomials with the above
    compiler-structural properties.

## Partition equivalence: pullback(compiled, witnessInclusion) ↔ tseitinPartition

The compiledPartition on witness vars mirrors tseitinPartition exactly.
Both use the same condition (v ≥ base ∧ v - base < clauses.length) and
produce the same block assignment. The compiled partition has an extra
conjunct (v < npNumVars) which is always true for witness vars.

This bidirectional refinement means the SPDP ranks are equal.

Reverse refinement: tseitin → pullback(compiled). -/
theorem tseitinPartition_refines_pullback (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (i j : Fin (npNumVars n))
    (h_eq : (tseitinPartition n).assign i = (tseitinPartition n).assign j) :
    (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)).assign i =
    (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)).assign j := by
  -- pullback.assign i = compiledPartition.assign ⟨i.val, _⟩
  -- compiledPartition has: if v≥base ∧ v-base<clauses ∧ v<npNumVars then ... else ...
  -- For witness vars, v<npNumVars always holds, so condition = tseitin condition
  unfold pullbackPartition witnessInclusion compiledPartition
  unfold tseitinPartition IdentityMinor.tseitinPartition at h_eq
  simp only at h_eq ⊢
  have hi_np : i.val < npNumVars n := i.isLt
  have hj_np : j.val < npNumVars n := j.isLt
  -- The compiled dite has 3 conjuncts; 3rd is always true for witness vars
  -- So compiled condition ↔ tseitin condition
  by_cases hi : i.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
    i.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length
  · have hi3 : i.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
      i.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length ∧
      i.val < npNumVars n := ⟨hi.1, hi.2, hi_np⟩
    simp only [dif_pos hi3, dif_pos hi, Fin.mk.injEq] at h_eq ⊢
    by_cases hj : j.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
      j.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length
    · have hj3 : j.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
        j.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length ∧
        j.val < npNumVars n := ⟨hj.1, hj.2, hj_np⟩
      simp only [dif_pos hj3, dif_pos hj, Fin.mk.injEq] at h_eq ⊢; omega
    · simp only [dif_neg hj, Fin.mk.injEq] at h_eq; omega
  · have hi3 : ¬(i.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
      i.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length ∧
      i.val < npNumVars n) := by intro ⟨a, b, _⟩; exact hi ⟨a, b⟩
    simp only [dif_neg hi3, dif_neg hi, Fin.mk.injEq] at h_eq ⊢
    by_cases hj : j.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
      j.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length
    · simp only [dif_pos hj, Fin.mk.injEq] at h_eq; omega
    · have hj3 : ¬(j.val ≥ (tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length ∧
        j.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) < (tseitinAt n).clauses.length ∧
        j.val < npNumVars n) := by intro ⟨a, b, _⟩; exact hj ⟨a, b⟩
      simp only [dif_neg hj3]

/-- SPDP rank monotonicity: pullback(compiled) rank ≤ tseitin rank.
    Uses: tseitin refines pullback (same assign function on witness vars),
    so pullback-admissible lists are also tseitin-admissible,
    hence pullback subspace ⊆ tseitin subspace.
    Note: this is a one-way inequality, not equality. The paper's extraction
    argument uses rank non-increase, not rank equality. -/
theorem spdpRank_pullback_le_tseitin (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (κ ℓ : ℕ) :
    mlBlockedSpdpRank (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
      κ ℓ (tseitinPoly ℚ n) ≤
    mlBlockedSpdpRank (tseitinPartition n) κ ℓ (tseitinPoly ℚ n) :=
  -- tseitin refines pullback → subspace(pullback) ⊆ subspace(tseitin)
  Submodule.finrank_mono
    (mlBlockedSpdpSubspace_mono_partition _ _ κ ℓ _
      (tseitinPartition_refines_pullback M n h_le))

/-! ## Tseitin SPDP rank bound (§9 Profile Compression)

The tseitinPoly = ∏_c (1 - X(z_c) · gadget_c) has product structure where:
- Each selector z_c is in its own block (block c+1)
- All clause variables are in block 0
- Each factor has width ≤ 4

For block-admissible S with κ ≤ log₂(n) elements:
- Each derivative hits at most one factor (selectors in distinct blocks)
- The per-factor derivative is 1-dimensional (just -gadget_c)
- Profile compression collapses the combinatorics

Bound: mlBlockedSpdpRank ≤ n^10 for matching logarithmic parameters. -/

/-- Admissible SPDP parameter regime: matching parameters (κ = ℓ),
    both bounded by log₂(n), with κ ≥ 5 for the low-degree elimination.
    This is the regime where the paper's Width⇒Rank bound applies. -/
def AdmissibleSpdpParams (n κ : ℕ) : Prop :=
  κ ≥ 5 ∧ κ ≤ Nat.log 2 n

/-! ## Profile Space Construction (Paper §9.1 Def 19)

For the Tseitin product p = ∏_c (1 - z_c · g_c), each SPDP generator
mlProj(m × ∂^S p) has the factored form (by iterDeriv_cvProd_eq):
  mlProj(m × (-1)^κ × ∏_{hit} g_c × ∏_{unhit} (1 - z_c · g_c))

The profile space V_h captures the algebraic structure of generators
with a fixed profile h (histogram of clause types).

We construct V_h as the span of a FINITE set of "profile basis polynomials"
and show every generator lies in the appropriate V_h. -/

/-- A block-admissible selector list determines a "hit set" of clauses.
    For the Tseitin partition, selectors are in 1-1 correspondence with clauses.
    An admissible list of κ selectors corresponds to κ distinct clauses. -/
private theorem tseitinPartition_nonzero_block_is_selector (n : ℕ)
    (v : Fin (npNumVars n))
    (hv : ((tseitinPartition n).assign v).val ≠ 0) :
    ∃ c : Fin (tseitinAt n).clauses.length, v = selectorIdx (tseitinAt n) c := by
  simp only [tseitinPartition, IdentityMinor.tseitinPartition] at hv
  split at hv
  · rename_i h
    refine ⟨⟨v.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length), h.2⟩, ?_⟩
    apply Fin.ext
    simp [selectorIdx]
    omega
  · simp at hv

private noncomputable def tseitinSelectorInv (n : ℕ) (v : Fin (npNumVars n))
    (hv : ((tseitinPartition n).assign v).val ≠ 0) :
    Fin (tseitinAt n).clauses.length :=
  (tseitinPartition_nonzero_block_is_selector n v hv).choose

private theorem tseitinSelectorInv_spec (n : ℕ) (v : Fin (npNumVars n))
    (hv : ((tseitinPartition n).assign v).val ≠ 0) :
    v = selectorIdx (tseitinAt n) (tseitinSelectorInv n v hv) :=
  (tseitinPartition_nonzero_block_is_selector n v hv).choose_spec

noncomputable def hitClausesOf (n : ℕ)
    (S : List (Fin (npNumVars n)))
    (hadm : isBlockAdmissible (tseitinPartition n) S) :
    Finset (Fin (tseitinAt n).clauses.length) :=
  ((S.filter (fun v => ((tseitinPartition n).assign v).val ≠ 0)).attach.map
    (fun ⟨v, hv⟩ =>
      tseitinSelectorInv n v (by
        have hv' := (List.mem_filter.mp hv).2
        simpa using hv'))).toFinset

/- Legacy near-variable/profile-compression block archived from active route. -/

/-!
NOTE (active route):
The old theorem pair
  * `compiled_spdp_rank_bound`
  * `pside_full_ml_rank_bound`
was tied to a stale mixed encoding route (product-form object on the P-side).
For paper-consistent active development, the P-side upper bound is treated as part
of the restriction/depth-collapse obligation in `RestrictionPipeline.depth_collapse_L171`.
-/

/-- §34 Compiler extraction: NP-side rank ≤ P-side rank.

    Paper-faithful proof chain using fullCompiledPoly = verifierSheet + tableau:
    1. restriction_rank_monotone on fullCompiledPoly
    2. restrictPoly(fullCompiled) = tseitin + restrictPoly(tableau)
       [by map_add + restrictPoly_rename]
    3. mlBlockedSpdpRank_add_lowDeg: remove low-degree remainder (degree ≤ 4 < κ)
    4. mlBlockedSpdpRank_coarsen: identity pullback refines tseitin partition
    5. Chain: Γ(tseitin) ≤ Γ(pullback) ≤ Γ(compiled) -/
theorem extraction_rank_monotone (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (M : DTM) (hsolves : True) (hn : n ≥ 32) :
    ∀ (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) (κ ℓ : ℕ),
      κ ≥ 5 →
      mlBlockedSpdpRank (tseitinPartition n) κ ℓ (tseitinPoly F n) ≤
      mlBlockedSpdpRank (compiledPartition M n) κ ℓ
        (fullCompiledPoly F M n h_le) := by
  intro h_le κ ℓ hκ
  let f := witnessInclusion M n h_le
  have hf_inj := witnessInclusion_injective M n h_le
  -- Step 1: restriction_rank_monotone on fullCompiledPoly
  have h_restrict := restriction_rank_monotone F f hf_inj (compiledPartition M n) κ ℓ
    (fullCompiledPoly F M n h_le)
  -- Step 2: restrictPoly(fullCompiled) = tseitin + restrictPoly(tableau)
  have h_add : restrictPoly F f hf_inj (fullCompiledPoly F M n h_le) =
      restrictPoly F f hf_inj (verifierSheetOf F M n h_le) +
      restrictPoly F f hf_inj (violationPolyOf F M n) := by
    unfold fullCompiledPoly
    exact map_add (restrictPoly F f hf_inj) _ _
  have h_sheet : restrictPoly F f hf_inj (verifierSheetOf F M n h_le) =
      tseitinPoly F n := by
    unfold verifierSheetOf
    exact restrictPoly_rename F f hf_inj (tseitinPoly F n)
  rw [h_add, h_sheet] at h_restrict
  -- Step 3: remove low-degree remainder (degree ≤ 4 < κ ≥ 5)
  let h_pullback := pullbackPartition (compiledPartition M n) f
  have h_lowdeg := tableau_restriction_lowDeg F M n h_le
  rw [mlBlockedSpdpRank_add_lowDeg F h_pullback κ ℓ (tseitinPoly F n) _ (by linarith)]
    at h_restrict
  -- Step 4: coarsen — pullback of template partition refines tseitin partition
  have h_coarsen := mlBlockedSpdpRank_coarsen F h_pullback (tseitinPartition n) κ ℓ
    (tseitinPoly F n) (by
      intro i j h_eq
      change (compiledPartition M n).assign (f i) = (compiledPartition M n).assign (f j) at h_eq
      exact compiledPartition_refines_tseitin M n h_le i j h_eq)
  linarith

/-! ## Paper-faithful inclusive-κ port of the rank chain

Ports the existing strict-κ chain theorems to the inclusive-κ variant
`mlBlockedSpdpSubspaceInc`. The strict-κ `mlBlockedSpdpRank_add_lowDeg`
does **not** survive the port — it is falsifiable under `≤ κ` (see
`GadgetSubspaceFactoringCounterexample`). We replace it with the
paper-correct triangle-inequality form
`mlBlockedSpdpRankInc_add_le` that gives
`rank_inc(p+q) ≤ rank_inc(p) + rank_inc(q)`.

All theorems below are axiom-free. -/

/-- **Inclusive-κ partition monotonicity.** If B₂ is coarser than B₁,
then the B₂-subspace ⊆ B₁-subspace. Ports
`mlBlockedSpdpSubspace_mono_partition`. -/
theorem mlBlockedSpdpSubspaceInc_mono_partition {n : ℕ} {F : Type*} [CommRing F]
    (B₁ B₂ : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (hrefine : ∀ i j : Fin n, B₁.assign i = B₁.assign j → B₂.assign i = B₂.assign j) :
    mlBlockedSpdpSubspaceInc B₂ κ ℓ p ≤ mlBlockedSpdpSubspaceInc B₁ κ ℓ p := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  apply Submodule.subset_span
  exact ⟨S, m, hlen, hdeg, hvars,
    isBlockAdmissible_coarsen B₁ B₂ S hrefine hadm, hq⟩

/-- **Inclusive-κ coarsen rank bound.** Port of
`mlBlockedSpdpRank_coarsen`. -/
theorem mlBlockedSpdpRankInc_coarsen {n : ℕ} (F : Type*) [Field F] [Nontrivial F]
    (B₁ B₂ : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (hrefine : ∀ i j : Fin n, B₁.assign i = B₁.assign j → B₂.assign i = B₂.assign j) :
    mlBlockedSpdpRankInc B₂ κ ℓ p ≤ mlBlockedSpdpRankInc B₁ κ ℓ p := by
  unfold mlBlockedSpdpRankInc
  apply Submodule.finrank_mono
  apply mlBlockedSpdpSubspaceInc_mono_partition
  exact hrefine

/-- **Inclusive-κ restriction preimage in the big-side subspace.**
Port of `mlBlockedSpdpSubspace_restrict_le_map`. -/
theorem mlBlockedSpdpSubspaceInc_restrict_le_map {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : BlockPartition m) (κ ℓ : ℕ) (p : MvPolynomial (Fin m) F) :
    mlBlockedSpdpSubspaceInc (pullbackPartition B f) κ ℓ
      (restrictPoly F f hf p) ≤
    Submodule.map (restrictPolyLinearMap F f hf)
      (mlBlockedSpdpSubspaceInc B κ ℓ p) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, mul, hlen, hdeg, hvars, hadm, hq⟩
  simp only [Submodule.mem_map, SetLike.mem_coe]
  let S' := S.map f
  let q' := iterDerivList S' p
  let mul' := MvPolynomial.rename f mul
  refine ⟨mlProj (mul' * q'), ?_, ?_⟩
  · apply Submodule.subset_span
    refine ⟨S', mul', by simp [S', hlen], ?_, ?_, ?_, rfl⟩
    · exact le_trans (MvPolynomial.totalDegree_rename_le f mul) hdeg
    · show (MvPolynomial.rename f mul).vars ⊆ (S.map f).toFinset
      intro v hv
      have hsub := MvPolynomial.vars_rename f mul
      have hv' := hsub hv
      simp only [Finset.mem_image] at hv'
      obtain ⟨w, hw, rfl⟩ := hv'
      rw [List.mem_toFinset]
      have hwS : w ∈ S := List.mem_toFinset.mp (hvars hw)
      exact List.mem_map.mpr ⟨w, hwS, rfl⟩
    · constructor
      · exact List.Nodup.map hf hadm.1
      · intro b
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
        exact hadm.2 b
  · rw [show restrictPolyLinearMap F f hf (mlProj (mul' * q')) =
      restrictPoly F f hf (mlProj (mul' * q')) from rfl]
    rw [← mlProj_restrictPoly F f hf]
    rw [restrictPoly_mul_rename F f hf mul q']
    rw [← iterDerivList_restrictPoly F f hf S p]
    rw [hq]

/-- **Inclusive-κ restriction rank monotonicity.** Port of
`restriction_rank_monotone` for the paper-faithful inclusive
subspace. -/
theorem restriction_rank_monotone_inc (F : Type*) [Field F] [Nontrivial F]
    {n m : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : BlockPartition m) (κ ℓ : ℕ) (p : MvPolynomial (Fin m) F) :
    mlBlockedSpdpRankInc (pullbackPartition B f) κ ℓ
      (restrictPoly F f hf p) ≤
    mlBlockedSpdpRankInc B κ ℓ p := by
  unfold mlBlockedSpdpRankInc
  calc Module.finrank F
        (mlBlockedSpdpSubspaceInc (pullbackPartition B f) κ ℓ
          (restrictPoly F f hf p))
      ≤ Module.finrank F
          (Submodule.map (restrictPolyLinearMap F f hf)
            (mlBlockedSpdpSubspaceInc B κ ℓ p)) :=
        Submodule.finrank_mono
          (mlBlockedSpdpSubspaceInc_restrict_le_map f hf B κ ℓ p)
    _ ≤ Module.finrank F (mlBlockedSpdpSubspaceInc B κ ℓ p) :=
        Submodule.finrank_map_le _ _

/-- **Inclusive-κ add containment (triangle inequality).**

Under `mlBlockedSpdpSubspaceInc`, adding a polynomial `q` to `p` gives
a subspace contained in the SUM of the two individual subspaces:
`mlBlockedSpdpSubspaceInc (p+q) ⊆ mlBlockedSpdpSubspaceInc p +
                                   mlBlockedSpdpSubspaceInc q`.

This is the paper-correct replacement for the (falsifiable under ≤ κ)
`mlBlockedSpdpRank_add_lowDeg`. The inequality is tight: even if q is
low-degree, its |S|=0, |S|=1, ..., generators contribute, so we can't
claim exact preservation. -/
theorem mlBlockedSpdpSubspaceInc_add_le {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p q : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspaceInc B κ ℓ (p + q) ≤
    (mlBlockedSpdpSubspaceInc B κ ℓ p + mlBlockedSpdpSubspaceInc B κ ℓ q :
      Submodule F (MvPolynomial (Fin n) F)) := by
  apply Submodule.span_le.mpr
  intro r ⟨S, m, hlen, hdeg, hvars, hadm, hr⟩
  have h_deriv : iterDerivList S (p + q) =
                 iterDerivList S p + iterDerivList S q :=
    iterDerivList_add S p q
  rw [hr, h_deriv, mul_add, mlProj_add]
  have hp : mlProj (m * iterDerivList S p) ∈ mlBlockedSpdpSubspaceInc B κ ℓ p :=
    Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  have hq : mlProj (m * iterDerivList S q) ∈ mlBlockedSpdpSubspaceInc B κ ℓ q :=
    Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  rw [Submodule.add_eq_sup]
  exact Submodule.add_mem_sup hp hq

/-- **Inclusive-κ add rank bound (triangle inequality).**
Paper-correct replacement for `mlBlockedSpdpRank_add_lowDeg` (which
was falsifiable under `≤ κ`). -/
theorem mlBlockedSpdpRankInc_add_le {n : ℕ} (F : Type*) [Field F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p q : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRankInc B κ ℓ (p + q) ≤
    mlBlockedSpdpRankInc B κ ℓ p + mlBlockedSpdpRankInc B κ ℓ q := by
  unfold mlBlockedSpdpRankInc
  -- Step 1: the (p + q) subspace ≤ the ⊔-sup of p and q subspaces.
  have hle_sup : mlBlockedSpdpSubspaceInc B κ ℓ (p + q) ≤
      ((mlBlockedSpdpSubspaceInc B κ ℓ p ⊔
        mlBlockedSpdpSubspaceInc B κ ℓ q :
        Submodule F (MvPolynomial (Fin n) F))) := by
    have hadd := mlBlockedSpdpSubspaceInc_add_le (F := F) B κ ℓ p q
    rw [Submodule.add_eq_sup] at hadd
    exact hadd
  -- Step 2: finrank is monotone on this containment.
  have h1 : Module.finrank F (mlBlockedSpdpSubspaceInc B κ ℓ (p + q)) ≤
            Module.finrank F
              ((mlBlockedSpdpSubspaceInc B κ ℓ p ⊔
                mlBlockedSpdpSubspaceInc B κ ℓ q :
                Submodule F (MvPolynomial (Fin n) F))) :=
    Submodule.finrank_mono hle_sup
  -- Step 3: finrank(p ⊔ q) ≤ finrank p + finrank q.
  have h2 : Module.finrank F
              ((mlBlockedSpdpSubspaceInc B κ ℓ p ⊔
                mlBlockedSpdpSubspaceInc B κ ℓ q :
                Submodule F (MvPolynomial (Fin n) F))) ≤
            Module.finrank F (mlBlockedSpdpSubspaceInc B κ ℓ p) +
            Module.finrank F (mlBlockedSpdpSubspaceInc B κ ℓ q) :=
    Submodule.finrank_add_le_finrank_add_finrank _ _
  exact le_trans h1 h2

/-- iterDerivList distributes over negation (from iterDerivList_add). -/
private theorem iterDerivList_neg_helper {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    iterDerivList S (-p) = -iterDerivList S p := by
  have h0 : iterDerivList S (p + (-p)) =
            iterDerivList S p + iterDerivList S (-p) :=
    iterDerivList_add S p (-p)
  have hzero : p + (-p) = (0 : MvPolynomial (Fin n) F) := by ring
  rw [hzero] at h0
  have hder0 : iterDerivList S (0 : MvPolynomial (Fin n) F) = 0 := by
    unfold iterDerivList
    exact foldl_pderiv_zero' S
  rw [hder0] at h0
  -- 0 = ∂p + ∂(-p) → ∂(-p) = -∂p
  linear_combination -h0

/-- mlProj of a negation. Uses additive hom from `mlProjHom`. -/
private theorem mlProj_neg_helper {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) : mlProj (-p) = -mlProj p := by
  change (mlProjHom F) (-p) = -(mlProjHom F) p
  exact map_neg _ p

/-- Negation preserves the inclusive-κ subspace exactly. -/
theorem mlBlockedSpdpSubspaceInc_neg {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspaceInc B κ ℓ (-p) =
    mlBlockedSpdpSubspaceInc B κ ℓ p := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro r ⟨S, m, hlen, hdeg, hvars, hadm, hr⟩
    rw [hr, iterDerivList_neg_helper]
    have hneg : m * (-iterDerivList S p) = -(m * iterDerivList S p) := by ring
    rw [hneg, mlProj_neg_helper]
    have hgen : mlProj (m * iterDerivList S p) ∈
        mlBlockedSpdpSubspaceInc B κ ℓ p :=
      Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
    exact (mlBlockedSpdpSubspaceInc B κ ℓ p).neg_mem hgen
  · apply Submodule.span_le.mpr
    rintro r ⟨S, m, hlen, hdeg, hvars, hadm, hr⟩
    rw [hr]
    have hid : (m * iterDerivList S p) = -(m * iterDerivList S (-p)) := by
      rw [iterDerivList_neg_helper]; ring
    rw [hid, mlProj_neg_helper]
    have hgen : mlProj (m * iterDerivList S (-p)) ∈
        mlBlockedSpdpSubspaceInc B κ ℓ (-p) :=
      Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
    exact (mlBlockedSpdpSubspaceInc B κ ℓ (-p)).neg_mem hgen

/-- Negation preserves the inclusive-κ rank. -/
theorem mlBlockedSpdpRankInc_neg {n : ℕ} (F : Type*) [Field F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRankInc B κ ℓ (-p) = mlBlockedSpdpRankInc B κ ℓ p := by
  unfold mlBlockedSpdpRankInc
  rw [mlBlockedSpdpSubspaceInc_neg]

/-- Symmetric triangle inequality: `rank(p) ≤ rank(p+q) + rank(q)`. -/
theorem mlBlockedSpdpRankInc_le_add_le {n : ℕ} (F : Type*) [Field F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p q : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRankInc B κ ℓ p ≤
    mlBlockedSpdpRankInc B κ ℓ (p + q) + mlBlockedSpdpRankInc B κ ℓ q := by
  have heq : p = (p + q) + (-q) := by ring
  conv_lhs => rw [heq]
  have := mlBlockedSpdpRankInc_add_le F B κ ℓ (p + q) (-q)
  rw [mlBlockedSpdpRankInc_neg] at this
  exact this

/-- **Paper-faithful extraction rank monotonicity.**

Ports `extraction_rank_monotone` to the inclusive-κ variant. Uses
`mlBlockedSpdpRankInc_add_le` (triangle inequality) instead of the
falsifiable `_add_lowDeg`, so the final bound has a `+ rank(violation)`
slack term accounting for the low-degree remainder contribution.

For the paper's final separation, one needs to show the violation
polynomial's contribution is polynomial in N (which follows from its
bounded degree), preserving the overall asymptotics. -/
theorem extraction_rank_monotone_inc (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (M : DTM) (hsolves : True) (hn : n ≥ 32) :
    ∀ (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) (κ ℓ : ℕ),
      κ ≥ 5 →
      mlBlockedSpdpRankInc (tseitinPartition n) κ ℓ (tseitinPoly F n) ≤
      mlBlockedSpdpRankInc (compiledPartition M n) κ ℓ
        (fullCompiledPoly F M n h_le) +
      mlBlockedSpdpRankInc (pullbackPartition (compiledPartition M n)
        (witnessInclusion M n h_le)) κ ℓ
        (restrictPoly F (witnessInclusion M n h_le)
          (witnessInclusion_injective M n h_le) (violationPolyOf F M n)) := by
  intro h_le κ ℓ _
  let f := witnessInclusion M n h_le
  have hf_inj := witnessInclusion_injective M n h_le
  let h_pullback := pullbackPartition (compiledPartition M n) f
  -- Step 1: restriction_rank_monotone_inc on fullCompiledPoly
  have h_restrict := restriction_rank_monotone_inc F f hf_inj
    (compiledPartition M n) κ ℓ (fullCompiledPoly F M n h_le)
  -- Step 2: restrictPoly(fullCompiled) = tseitin + restrictPoly(violation)
  have h_add : restrictPoly F f hf_inj (fullCompiledPoly F M n h_le) =
      tseitinPoly F n +
      restrictPoly F f hf_inj (violationPolyOf F M n) := by
    unfold fullCompiledPoly
    rw [map_add (restrictPoly F f hf_inj)]
    congr 1
    unfold verifierSheetOf
    exact restrictPoly_rename F f hf_inj (tseitinPoly F n)
  rw [h_add] at h_restrict
  -- Step 3: coarsen — pullback of compiledPartition refines tseitin
  have h_coarsen := mlBlockedSpdpRankInc_coarsen F h_pullback
    (tseitinPartition n) κ ℓ (tseitinPoly F n) (by
      intro i j h_eq
      change (compiledPartition M n).assign (f i) =
             (compiledPartition M n).assign (f j) at h_eq
      exact compiledPartition_refines_tseitin M n h_le i j h_eq)
  -- Step 4: symmetric triangle inequality on tseitin = (tseitin + restrictVio) - restrictVio
  have h_sym_triangle := mlBlockedSpdpRankInc_le_add_le F h_pullback κ ℓ
    (tseitinPoly F n) (restrictPoly F f hf_inj (violationPolyOf F M n))
  -- Chain: rank(tseitin) ≤ rank(pullback, tseitin) ≤ rank(pullback, tseitin+restrictVio) + rank(restrictVio)
  --                     ≤ rank(compiled, fullCompiled) + rank(restrictVio)
  calc mlBlockedSpdpRankInc (tseitinPartition n) κ ℓ (tseitinPoly F n)
      ≤ mlBlockedSpdpRankInc h_pullback κ ℓ (tseitinPoly F n) := h_coarsen
    _ ≤ mlBlockedSpdpRankInc h_pullback κ ℓ
          (tseitinPoly F n +
            restrictPoly F f hf_inj (violationPolyOf F M n)) +
        mlBlockedSpdpRankInc h_pullback κ ℓ
          (restrictPoly F f hf_inj (violationPolyOf F M n)) :=
        h_sym_triangle
    _ ≤ mlBlockedSpdpRankInc (compiledPartition M n) κ ℓ
          (fullCompiledPoly F M n h_le) +
        mlBlockedSpdpRankInc h_pullback κ ℓ
          (restrictPoly F f hf_inj (violationPolyOf F M n)) :=
        Nat.add_le_add_right h_restrict _

/-- **Strict ⊆ inclusive rank bridge.**

The strict-κ rank is bounded above by the inclusive-κ rank at the
same parameters. Via `Submodule.finrank_mono` applied to the
subspace containment `mlBlockedSpdpSubspace_le_inc`.

This is the key bridge that lets paper-faithful (inclusive) theorems
be used in contexts that still use `mlBlockedSpdpRank` (strict),
such as `Theorem207Witness` fields. -/
theorem mlBlockedSpdpRank_le_mlBlockedSpdpRankInc
    {n : ℕ} {F : Type*} [Field F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRank B κ ℓ p ≤ mlBlockedSpdpRankInc B κ ℓ p := by
  unfold mlBlockedSpdpRank mlBlockedSpdpRankInc
  exact Submodule.finrank_mono (mlBlockedSpdpSubspace_le_inc B κ ℓ p)

/-! ## Axiom-freeness checks for the paper-faithful inclusive port -/

#print axioms linearIndependent_of_kronecker_dual
#print axioms finrank_ge_of_kronecker_dual
#print axioms identity_minor_projected_kronecker_delta
#print axioms identity_minor_projected_diagonal_coeff
#print axioms identity_minor_projected_diagonal_coeff_unit
#print axioms identity_minor_projected_offdiag_coeff_zero
#print axioms identity_minor_projected_row_ne_zero
#print axioms identity_minor_projected_rows_linearIndependent
#print axioms identity_minor_projected_rows_span_finrank
#print axioms projectedIdentityMinorSpan_finite
#print axioms projectedIdentityMinorBasis
#print axioms projectedIdentityMinorBasis_apply
#print axioms projectedIdentityMinorBasis_eq_mlProj_signed_gadgetProd_mul_remaining
#print axioms coeff_body_projectedIdentityMinorBasis_eq_signed_gadgetProd
#print axioms coeff_tagMono_projectedIdentityMinorBasis_kronecker
#print axioms coeff_tagMono_projectedIdentityMinorBasis_self_eq_subsetSign
#print axioms projectedIdentityMinorBasis_mem_mlSubspace
#print axioms projectedIdentityMinorBasis_mem_canonical_mlSubspace
#print axioms subsetSign_mul_self
#print axioms projectedIdentityMinorDual
#print axioms projectedIdentityMinorDual_basis_apply
#print axioms projectedIdentityMinorDual_eq_basis_repr_coord
#print axioms projectedIdentityMinor_dual_reconstruction
#print axioms projectedIdentityMinor_coeff_eq_signed_repr_coord
#print axioms projectedIdentityMinor_repr_coord_eq_signed_coeff
#print axioms projectedIdentityMinorSignEquiv
#print axioms projectedIdentityMinorTagCoeffEquiv
#print axioms projectedIdentityMinorTagCoeffEquiv_apply
#print axioms projectedIdentityMinorTagCoeffEquiv_injective
#print axioms projectedIdentityMinorTagCoeffEquiv_symm_apply
#print axioms projectedIdentityMinorTagCoeffEquiv_apply_symm
#print axioms coeff_tagMono_projectedIdentityMinor_signed_basis_sum
#print axioms projectedIdentityMinor_coeff_reconstruction
#print axioms projectedIdentityMinor_eq_zero_of_forall_tag_coeff_zero
#print axioms projectedIdentityMinor_ext_of_forall_tag_coeff_eq
#print axioms projectedIdentityMinor_forall_tag_coeff_zero_iff
#print axioms identity_minor_projected_rows_span_le_mlSubspace
#print axioms identity_minor_projected_rows_span_le_mlSubspaceInc
#print axioms identity_minor_projected_rank_lower_from_span
#print axioms identity_minor_projected_rank_lower_inc_from_span
#print axioms coupledVerifier_projected_identity_minor_span_le_mlSubspace
#print axioms coupledVerifier_projected_identity_minor_span_le_mlSubspaceInc
#print axioms coupledVerifier_projected_identity_minor_span_finrank
#print axioms tseitinAt_projected_identity_minor_subspace_certificate
#print axioms tseitinAt_projected_identity_minor_subspace_certificate_inc
#print axioms tseitinAt_projected_identity_minor_subspace_superpoly_certificate
#print axioms tseitinAt_projected_identity_minor_subspace_superpoly_certificate_inc
#print axioms rank_lower_of_finite_subspace_certificate
#print axioms tseitinAt_projected_identity_minor_finite_subspace_certificate
#print axioms tseitinAt_projected_identity_minor_finite_subspace_certificate_inc
#print axioms tseitinAt_coupledVerifier_projected_rank_lower_choose_div30_from_finite_subspace_certificate
#print axioms tseitinAt_coupledVerifier_projected_rank_lower_choose_div30_inc_from_finite_subspace_certificate
#print axioms tseitinAt_projected_identity_minor_finite_subspace_superpoly_certificate
#print axioms tseitinAt_projected_identity_minor_finite_subspace_superpoly_certificate_inc
#print axioms tseitinAt_coupledVerifier_projected_rank_lower_superpoly_from_finite_subspace_certificate
#print axioms tseitinAt_coupledVerifier_projected_rank_lower_superpoly_inc_from_finite_subspace_certificate
#print axioms coupledVerifier_projected_finite_subspace_superpoly_certificate
#print axioms coupledVerifier_projected_finite_subspace_superpoly_certificate_inc
#print axioms coupledVerifier_projected_rank_lower_superpoly_from_asymptotic_finite_subspace_certificate
#print axioms coupledVerifier_projected_rank_lower_superpoly_inc_from_asymptotic_finite_subspace_certificate
#print axioms IdentityMinorPaperFaithful.tagMono_finsupp_isMultilinear
#print axioms IdentityMinorPaperFaithful.monomial_tagMono_isMultilinear
#print axioms IdentityMinorPaperFaithful.identity_minor_components_columns_multilinear
#print axioms identity_minor_components_kronecker_after_mlProj
#print axioms identity_minor_projected_rank_lower
#print axioms identity_minor_projected_rank_lower_inc
#print axioms coupledVerifier_projected_identity_minor_rank_lower
#print axioms coupledVerifier_projected_identity_minor_rank_lower_inc
#print axioms tseitinAt_coupledVerifier_projected_rank_lower_choose_div30
#print axioms tseitinAt_coupledVerifier_projected_rank_lower_choose_div30_inc
#print axioms coupledVerifier_projected_rank_lower_superpoly
#print axioms coupledVerifier_projected_rank_lower_superpoly_inc
#print axioms coupledVerifier_projected_rank_lower_superpoly_concrete
#print axioms coupledVerifier_projected_rank_lower_superpoly_concrete_inc
#print axioms mlBlockedSpdpSubspace_le_inc
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms mlBlockedSpdpSubspaceInc_eq_iSup
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms mlBlockedSpdpSubspaceInc_mono_partition
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms mlBlockedSpdpRankInc_coarsen
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms mlBlockedSpdpSubspaceInc_restrict_le_map
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms restriction_rank_monotone_inc
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms mlBlockedSpdpSubspaceInc_add_le
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms mlBlockedSpdpRankInc_add_le
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms mlBlockedSpdpSubspaceInc_neg
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms mlBlockedSpdpRankInc_neg
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms mlBlockedSpdpRankInc_le_add_le
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms extraction_rank_monotone_inc
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms mlBlockedSpdpRank_le_mlBlockedSpdpRankInc
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).

end MultilinearSPDP
