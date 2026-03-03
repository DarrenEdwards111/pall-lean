/-
  SpdpPaperKeyLemmas.lean — Key deep-sorry lemmas from Pall paper.
-/
import Mathlib

open scoped BigOperators
open Submodule

namespace SpdpPaper

/-! ## 0. Helpers: finrank bounds for finite sups -/

section FinrankSup
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

lemma finrank_finset_sup_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (W : ι → Submodule F V)
    [∀ i, FiniteDimensional F (W i)] :
    Module.finrank F ↥(s.sup W) ≤ ∑ i ∈ s, Module.finrank F ↥(W i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' has ih =>
    rw [Finset.sup_insert, Finset.sum_insert has]
    exact le_trans (Submodule.finrank_add_le_finrank_add_finrank (K := F) _ _)
                   (Nat.add_le_add_left ih _)

lemma finrank_le_sum_of_le_sup {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (U : ι → Submodule F V)
    (W : Submodule F V) (hW : W ≤ s.sup U)
    [∀ i, FiniteDimensional F (U i)] :
    Module.finrank F ↥W ≤ ∑ i ∈ s, Module.finrank F ↥(U i) :=
  le_trans (Submodule.finrank_mono hW) (finrank_finset_sup_le s U)

end FinrankSup

/-! ## 2. Theorem 5.16 (Width⇒Rank): profile-partition bound -/

section WidthToRank
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]

theorem width_to_rank_bound {Profile : Type*} [DecidableEq Profile]
    (Rows : Set V) (H : Finset Profile)
    (Vh : Profile → Submodule F V)
    (hcover : span F Rows ≤ H.sup Vh)
    (d : Nat)
    (hd : ∀ h ∈ H, Module.finrank F ↥(Vh h) ≤ d)
    [∀ h, FiniteDimensional F (Vh h)] :
    Module.finrank F ↥(span F Rows) ≤ H.card * d := by
  have h1 := finrank_le_sum_of_le_sup H Vh _ hcover
  have h2 : ∑ h ∈ H, Module.finrank F ↥(Vh h) ≤ ∑ _h ∈ H, d :=
    Finset.sum_le_sum (fun h hh => hd h hh)
  exact le_trans h1 (le_trans h2 (by simp [Finset.sum_const, Nat.smul_one_eq_cast]))

end WidthToRank

/-! ## 3. Theorem 9.3: dual-functional linear independence → rank lower bound -/

section IdentityMinor
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Dual-functionals Kronecker delta test ⇒ linear independence. -/
theorem linearIndependent_of_dual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → V) (φ : ι → V →ₗ[F] F)
    (hδ : ∀ i j, φ i (v j) = if i = j then (1 : F) else 0) :
    LinearIndependent F v := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congr_arg (φ i) hg
  simp only [map_sum, map_smul, LinearMap.map_zero] at h
  simp only [smul_eq_mul, hδ] at h
  simp only [mul_ite, mul_one, mul_zero] at h
  rwa [Finset.sum_ite_eq s i, if_pos hi] at h

/-- Identity-minor lower bound: Kronecker-separated vectors span ≥ card ι dimensions. -/
theorem finrank_span_ge_card_of_dual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → V) (φ : ι → V →ₗ[F] F)
    (hδ : ∀ i j, φ i (v j) = if i = j then (1 : F) else 0) :
    Fintype.card ι ≤ Module.finrank F ↥(span F (Set.range v)) := by
  have hv := linearIndependent_of_dual v φ hδ
  exact le_of_eq (finrank_span_eq_card hv).symm

end IdentityMinor

/-! ## 4. Theorem 12.2: extraction pipeline (abstract) -/

section Extraction
variable {Obj : Type*}

theorem extraction_rank_monotone (rank : Obj → Nat)
    (proj restrict relabel gauge : Obj → Obj)
    (hproj : ∀ X, rank (proj X) ≤ rank X)
    (hres : ∀ X, rank (restrict X) ≤ rank X)
    (hrel : ∀ X, rank (relabel X) ≤ rank X)
    (hgau : ∀ X, rank (gauge X) ≤ rank X) :
    ∀ X, rank (gauge (relabel (restrict (proj X)))) ≤ rank X :=
  fun X => le_trans (hgau _) (le_trans (hrel _) (le_trans (hres _) (hproj _)))

end Extraction

end SpdpPaper
