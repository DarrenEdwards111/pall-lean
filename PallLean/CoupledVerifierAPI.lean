/-
  CoupledVerifierAPI.lean — Bridge lemmas for the coupled identity minor proof.
  Hides Finsupp/List/Finset API friction from the main theorem.
-/
import PallLean.CoupledVerifier
import Mathlib.Tactic

open MvPolynomial CoupledVerifier

namespace CoupledVerifierAPI

variable {N L : ℕ} (dcs : DisjointClauseSystem N L)

-- Tag monomial uses only block variables, NOT selector variables.
-- Because: dcs.tag C has support ⊆ blocks C ⊆ Fin N (block vars).
-- Selector vars have index ≥ N. So selector vars are not in tag support.
theorem tagMon_support_not_selector (T : Finset (Fin L)) (C : Fin L) (v : Fin (N + L))
    (hv : v ∈ (dcs.tag C).support) : v.val < N := by
  have := dcs.tag_support C v hv
  obtain ⟨i, hvi, _⟩ := this
  rw [hvi]; exact i.isLt

theorem tagSum_support_not_selector (T : Finset (Fin L))
    (v : Fin (N + L)) (hv : v ∈ (T.sum dcs.tag).support) : v.val < N := by
  rw [Finsupp.mem_support_iff] at hv
  by_contra h; push_neg at h
  have : (T.sum dcs.tag) v = 0 := by
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro C _
    by_contra hne
    have hmem : v ∈ (dcs.tag C).support := Finsupp.mem_support_iff.mpr hne
    have := tagMon_support_not_selector dcs T C v hmem
    omega
  exact hv this

-- Selector variable index ≥ N.
theorem selectorVarIdx_ge_N (C : Fin L) : (selectorVarIdx N L C).val ≥ N := by
  unfold selectorVarIdx; omega

-- Tag support condition for coeff_iterDerivList_zero:
-- For each selector var z_C in selList T, (tagMon T) z_C = 0.
-- Because tagMon uses block vars (index < N), selectors have index ≥ N.
theorem tag_zero_at_selector (T : Finset (Fin L)) (C : Fin L) :
    (T.sum dcs.tag) (selectorVarIdx N L C) = 0 := by
  by_contra h
  have hmem := Finsupp.mem_support_iff.mpr h
  have hlt := tagSum_support_not_selector dcs T (selectorVarIdx N L C) hmem
  have hge := selectorVarIdx_ge_N C
  omega

-- selList mapped has nodup when selectorVarIdx is injective
theorem selList_nodup (T : Finset (Fin L)) :
    (T.val.toList.map (selectorVarIdx N L)).Nodup := by
  apply List.Nodup.map
  · intro a b hab; simp [selectorVarIdx, Fin.ext_iff] at hab; exact Fin.ext hab
  · exact T.nodup_toList

-- Tag condition for coeff_iterDerivList_zero: tagMon is zero at all selector vars
theorem tag_zero_at_selList (T : Finset (Fin L)) :
    ∀ s ∈ T.val.toList.map (selectorVarIdx N L), (T.sum dcs.tag) s = 0 := by
  intro s hs
  obtain ⟨C, _, rfl⟩ := List.mem_map.mp hs
  exact tag_zero_at_selector dcs T C

end CoupledVerifierAPI

-- Coupled factors have disjoint variable sets.
-- Factor C uses {z_C} ∪ B_C. Different C → disjoint blocks + different selectors.
theorem coupledFactor_vars_disjoint (i j : Fin L) (hij : i ≠ j) :
    Disjoint (coupledFactor N L dcs i).vars (coupledFactor N L dcs j).vars := by
  sorry -- From: dcs.disjoint + selectorVarIdx injective

-- Coefficient of product of disjoint-variable coupled factors.
-- Q.coeff(m) = ∏_C (coupledFactor C).coeff(m restricted to C's vars)
-- For our specific monomial: this gives (-1)^κ ∏ tag_coeff.
-- Uses coeff_prod_disjoint (PROVED in IdentityMinorProof).
theorem coupledPoly_coeff_factored (m : (Fin (N + L)) →₀ ℕ) :
    (coupledPoly N L dcs).coeff m = ∏ C : Fin L, (coupledFactor N L dcs C).coeff (sorry : (Fin (N + L)) →₀ ℕ) := by
  sorry -- From coeff_prod_disjoint

