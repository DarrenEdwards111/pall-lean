import PallLean.SPDPDefs
import PallLean.RestrictionRank
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Variables
/-!
# Rename with injective f cannot increase SPDP rank
-/

namespace SPDP.Rename

open SPDP MvPolynomial

variable {F : Type*} [CommRing F] [Nontrivial F]
variable {n m : ℕ}

/-- pderiv j of rename f q is 0 when j ∉ range f -/
theorem pderiv_rename_zero (f : Fin n → Fin m) (j : Fin m)
    (hj : j ∉ Set.range f) (q : MvPolynomial (Fin n) F) :
    (pderiv j) (rename f q) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hmem
  obtain ⟨i, _, hi⟩ := mem_vars_rename f q hmem
  exact hj ⟨i, hi⟩

/-- iterDerivList commutes with rename for injective f -/
theorem iterDerivList_rename (f : Fin n → Fin m) (hf : Function.Injective f)
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    iterDerivList (indices.map f) (rename f p) =
      rename f (iterDerivList indices p) := by
  induction indices generalizing p with
  | nil => simp [iterDerivList]
  | cons j rest ih =>
    simp only [iterDerivList, List.foldl_cons, List.map_cons]
    rw [pderiv_rename hf j p]
    exact ih (pderiv j p)

/-- If some index ∉ range f, iterDerivList on rename f gives 0 -/
theorem iterDerivList_rename_zero_of_mem_not_range (f : Fin n → Fin m)
    (hf : Function.Injective f)
    (indices : List (Fin m)) (p : MvPolynomial (Fin n) F)
    (j : Fin m) (hj_mem : j ∈ indices) (hj_range : j ∉ Set.range f) :
    iterDerivList indices (rename f p) = 0 := by
  induction indices generalizing p with
  | nil => simp at hj_mem
  | cons k rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    rcases List.mem_cons.mp hj_mem with rfl | hj_rest
    · -- k = j, not in range, kills it
      rw [pderiv_rename_zero f j hj_range p, foldl_pderiv_zero]
    · -- k ≠ j (or k = j handled above)
      by_cases hk : k ∉ Set.range f
      · rw [pderiv_rename_zero f k hk p, foldl_pderiv_zero]
      · push_neg at hk
        obtain ⟨i, rfl⟩ := hk
        rw [pderiv_rename hf i p]
        exact ih (pderiv i p) hj_rest

/-- Pullback list through f using choice -/
noncomputable def pullbackList (f : Fin n → Fin m)
    (indices : List (Fin m)) (h_all : ∀ j ∈ indices, j ∈ Set.range f) :
    List (Fin n) :=
  match indices, h_all with
  | [], _ => []
  | j :: rest, h =>
    (h j (List.mem_cons.mpr (Or.inl rfl))).choose ::
      pullbackList f rest (fun k hk => h k (List.mem_cons.mpr (Or.inr hk)))

theorem pullbackList_map (f : Fin n → Fin m)
    (indices : List (Fin m)) (h_all : ∀ j ∈ indices, j ∈ Set.range f) :
    (pullbackList f indices h_all).map f = indices := by
  induction indices with
  | nil => simp [pullbackList]
  | cons j rest ih =>
    simp only [pullbackList, List.map_cons, List.cons.injEq]
    exact ⟨(h_all j (List.mem_cons.mpr (Or.inl rfl))).choose_spec,
      ih (fun k hk => h_all k (List.mem_cons.mpr (Or.inr hk)))⟩

theorem pullbackList_length (f : Fin n → Fin m)
    (indices : List (Fin m)) (h_all : ∀ j ∈ indices, j ∈ Set.range f) :
    (pullbackList f indices h_all).length = indices.length := by
  induction indices with
  | nil => simp [pullbackList]
  | cons j rest ih =>
    simp only [pullbackList, List.length_cons]
    congr 1
    exact ih (fun k hk => h_all k (List.mem_cons.mpr (Or.inr hk)))

/-- V_κ(rename f p) ⊆ image of V_κ(p) under rename f -/
theorem spdpSubspace_rename_le (f : Fin n → Fin m) (hf : Function.Injective f)
    (κ : ℕ) (p : MvPolynomial (Fin n) F) :
    spdpSubspace κ (rename f p) ≤
      (spdpSubspace κ p).map (rename f).toLinearMap := by
  apply Submodule.span_le.mpr
  intro q hq
  simp only [Set.mem_setOf_eq] at hq
  obtain ⟨indices, hlen, rfl⟩ := hq
  by_cases h_all : ∀ j ∈ indices, j ∈ Set.range f
  · -- All in range: pull back
    let pb := pullbackList f indices h_all
    rw [show iterDerivList indices (rename f p) =
        iterDerivList (pb.map f) (rename f p) from by
      rw [pullbackList_map f indices h_all]]
    rw [iterDerivList_rename f hf pb p]
    apply Submodule.mem_map.mpr
    exact ⟨iterDerivList pb p, Submodule.subset_span ⟨pb,
      by rw [pullbackList_length]; exact hlen, rfl⟩, rfl⟩
  · -- Some index not in range → generator is 0
    push_neg at h_all
    obtain ⟨j, hj_mem, hj_range⟩ := h_all
    rw [iterDerivList_rename_zero_of_mem_not_range f hf indices p j hj_mem hj_range]
    exact Submodule.zero_mem _

/-- Image of V_κ(p) under rename f ≤ V_κ(rename f p) -/
theorem spdpSubspace_rename_ge (f : Fin n → Fin m) (hf : Function.Injective f)
    (κ : ℕ) (p : MvPolynomial (Fin n) F) :
    (spdpSubspace κ p).map (rename f).toLinearMap ≤
      spdpSubspace κ (rename f p) := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  intro q hq
  simp only [Set.mem_setOf_eq] at hq
  obtain ⟨indices, hlen, rfl⟩ := hq
  apply Submodule.mem_comap.mpr
  simp only [AlgHom.toLinearMap_apply]
  rw [← iterDerivList_rename f hf indices p]
  apply Submodule.subset_span
  exact ⟨indices.map f, by simp [hlen], rfl⟩

/-- **R3: rename with injective f cannot increase SPDP rank — PROVED** -/
theorem rank_rename_le (f : Fin n → Fin m) (hf : Function.Injective f)
    (κ : ℕ) (p : MvPolynomial (Fin n) F) :
    spdpRank κ (rename f p) ≤ spdpRank κ p := by
  unfold spdpRank
  calc Module.finrank F ↥(spdpSubspace κ (rename f p))
      ≤ Module.finrank F ↥((spdpSubspace κ p).map (rename f).toLinearMap) :=
        Submodule.finrank_mono (spdpSubspace_rename_le f hf κ p)
      _ ≤ Module.finrank F ↥(spdpSubspace κ p) :=
        Submodule.finrank_map_le _ _

end SPDP.Rename
