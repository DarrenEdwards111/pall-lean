import PallLean.SPDPDefs
import PallLean.PDerivEval
import Mathlib.Tactic
/-!
# R1: Variable Restriction Cannot Increase SPDP Rank — PROVED
-/

namespace SPDP.Restriction

open SPDP PDerivEval MvPolynomial

variable {F : Type*} [CommRing F] [Nontrivial F]
variable {n : ℕ}

/-- If i ∈ indices, then iterDerivList kills evalAt i c p -/
theorem iterDerivList_evalAt_eq_zero_of_mem (i : Fin n) (c : F)
    (indices : List (Fin n)) (hi : i ∈ indices)
    (p : MvPolynomial (Fin n) F) :
    iterDerivList indices (evalAt i c p) = 0 := by
  induction indices generalizing p with
  | nil => simp at hi
  | cons j rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    by_cases hji : j = i
    · subst hji; rw [pderiv_evalAt_self]; exact foldl_pderiv_zero rest
    · rw [pderiv_comm_evalAt i j hji c p]
      exact ih (by rcases List.mem_cons.mp hi with h | h; exact absurd h.symm hji; exact h)
        (pderiv j p)

/-- If i ∉ indices, iterDerivList commutes with evalAt -/
theorem iterDerivList_comm_evalAt_of_not_mem (i : Fin n) (c : F)
    (indices : List (Fin n)) (hi : i ∉ indices)
    (p : MvPolynomial (Fin n) F) :
    iterDerivList indices (evalAt i c p) =
      evalAt i c (iterDerivList indices p) := by
  induction indices generalizing p with
  | nil => simp [iterDerivList]
  | cons j rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    have hji : j ≠ i := by intro h; exact hi (List.mem_cons.mpr (Or.inl h.symm))
    rw [pderiv_comm_evalAt i j hji c p]
    exact ih (by intro h; exact hi (List.mem_cons.mpr (Or.inr h))) (pderiv j p)

/-- evalAt i c as an F-linear map -/
noncomputable def evalAtLM (i : Fin n) (c : F) :
    MvPolynomial (Fin n) F →ₗ[F] MvPolynomial (Fin n) F where
  toFun := evalAt i c
  map_add' := map_add (evalAt i c)
  map_smul' := fun r x => by
    simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
    congr 1; exact evalAt_C i c r

/-- The generating set of spdpSubspace is finite (at most n^κ elements) -/
theorem spdpSubspace_generating_set_finite (κ : ℕ) (p : MvPolynomial (Fin n) F) :
    Set.Finite { q | ∃ (indices : List (Fin n)),
        indices.length = κ ∧ q = iterDerivList indices p } := by
  apply Set.Finite.subset
    (Set.finite_range (fun f : Fin κ → Fin n => iterDerivList (List.ofFn f) p))
  intro x ⟨indices, hlen, hx⟩
  simp only [Set.mem_range]
  subst hlen; subst hx
  exact ⟨fun i => indices.get i, by simp [List.ofFn_get]⟩

/-- spdpSubspace is finitely generated -/
theorem spdpSubspace_fg (κ : ℕ) (p : MvPolynomial (Fin n) F) :
    (spdpSubspace κ p).FG :=
  Submodule.fg_def.mpr ⟨_, spdpSubspace_generating_set_finite κ p, rfl⟩

/-- Module.Finite instance for spdpSubspace -/
instance spdpSubspace_moduleFinite (κ : ℕ) (p : MvPolynomial (Fin n) F) :
    Module.Finite F ↥(spdpSubspace κ p) :=
  Module.Finite.iff_fg.mpr (spdpSubspace_fg κ p)

/-- V_κ(evalAt i c p) ≤ V_κ(p).map (evalAt i c) -/
theorem spdpSubspace_evalAt_le (κ : ℕ) (p : MvPolynomial (Fin n) F)
    (i : Fin n) (c : F) :
    spdpSubspace κ (evalAt i c p) ≤
      (spdpSubspace κ p).map (evalAtLM i c) := by
  apply Submodule.span_le.mpr
  intro q hq
  simp only [Set.mem_setOf_eq] at hq
  obtain ⟨indices, hlen, rfl⟩ := hq
  by_cases hi : i ∈ indices
  · rw [iterDerivList_evalAt_eq_zero_of_mem i c indices hi p]
    exact Submodule.zero_mem _
  · rw [iterDerivList_comm_evalAt_of_not_mem i c indices hi p]
    exact Submodule.mem_map.mpr
      ⟨iterDerivList indices p, Submodule.subset_span ⟨indices, hlen, rfl⟩, rfl⟩

/-- **R1: restriction cannot increase rank — PROVED** -/
theorem restriction_rank_le (κ : ℕ) (p : MvPolynomial (Fin n) F)
    (i : Fin n) (c : F) :
    spdpRank κ (evalAt i c p) ≤ spdpRank κ p := by
  unfold spdpRank
  calc Module.finrank F ↥(spdpSubspace κ (evalAt i c p))
      ≤ Module.finrank F ↥((spdpSubspace κ p).map (evalAtLM i c)) :=
        Submodule.finrank_mono (spdpSubspace_evalAt_le κ p i c)
      _ ≤ Module.finrank F ↥(spdpSubspace κ p) :=
        Submodule.finrank_map_le (evalAtLM i c) (spdpSubspace κ p)

end SPDP.Restriction
