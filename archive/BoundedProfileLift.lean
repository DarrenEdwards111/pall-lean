import PallLean.ProductTransport
import PallLean.ProductProfileSlices
import PallLean.Profile

/-!
# BoundedProfileLift

This file proves the bounded-profile lift for verifier allocation generators.

For the coupled verifier factors `1 - z_c * V_c`, every factor has variable width
at most 4 (one selector plus three clause-body variables). Therefore any
allocation that sends more than 4 derivatives to a factor is either:

* impossible in the relevant case (by block-admissibility / width bound), or
* yields the zero generator (because some derivative falls outside the factor vars).

This is the bridge from the raw allocation span to the bounded profile-slice cover.
-/

namespace BoundedProfileLift

open SPDP
open MultilinearSPDP
open ProductTransport
open ProductProfileSlices
open Tseitin
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Each verifier factor uses at most 4 variables: one selector + at most 3 body vars. -/
theorem verifierFactor_vars_card_le_four
    (Φ : TseitinFormula)
    (c : Fin Φ.clauses.length) :
    (verifierFactor (F := F) Φ c).vars.card ≤ 4 := by
  unfold verifierFactor
  have hmul := MvPolynomial.vars_mul (MvPolynomial.X (selectorIdx Φ c)) (clauseGadget F Φ c)
  have hsub := MvPolynomial.vars_sub_subset (p := (1 : MvPolynomial _ F))
    (q := MvPolynomial.X (selectorIdx Φ c) * clauseGadget F Φ c)
  rw [MvPolynomial.vars_one] at hsub
  have hcg : (clauseGadget F Φ c).vars.card ≤ 3 := by
    have hsubset := clauseGadget_vars_subset F Φ c
    calc
      (clauseGadget F Φ c).vars.card ≤ ({let cl := Φ.clauses.get c
        let hpos : tseitinNumVars Φ > 0 := by unfold tseitinNumVars; have := c.isLt; omega
        let v1 : Fin (tseitinNumVars Φ) := ⟨cl.var1 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
        let v2 : Fin (tseitinNumVars Φ) := ⟨cl.var2 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
        let v3 : Fin (tseitinNumVars Φ) := ⟨cl.var3 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
        v1, (let cl := Φ.clauses.get c
        let hpos : tseitinNumVars Φ > 0 := by unfold tseitinNumVars; have := c.isLt; omega
        let v1 : Fin (tseitinNumVars Φ) := ⟨cl.var1 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
        let v2 : Fin (tseitinNumVars Φ) := ⟨cl.var2 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
        let v3 : Fin (tseitinNumVars Φ) := ⟨cl.var3 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
        v2), (let cl := Φ.clauses.get c
        let hpos : tseitinNumVars Φ > 0 := by unfold tseitinNumVars; have := c.isLt; omega
        let v1 : Fin (tseitinNumVars Φ) := ⟨cl.var1 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
        let v2 : Fin (tseitinNumVars Φ) := ⟨cl.var2 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
        let v3 : Fin (tseitinNumVars Φ) := ⟨cl.var3 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
        v3)} : Finset _).card := Finset.card_le_card (hsubset)
      _ ≤ 3 := by simp [Finset.card_insert_le]
  have hprodvars : (MvPolynomial.X (selectorIdx Φ c) * clauseGadget F Φ c).vars.card ≤ 4 := by
    calc
      (MvPolynomial.X (selectorIdx Φ c) * clauseGadget F Φ c).vars.card
          ≤ ({selectorIdx Φ c} ∪ (clauseGadget F Φ c).vars).card :=
            Finset.card_le_card (by
              intro x hx
              exact (Finset.mem_union.mpr ((MvPolynomial.vars_mul _ _ hx).elim
                (fun hxX => Or.inl hxX) (fun hxC => Or.inr hxC))))
      _ ≤ ({selectorIdx Φ c} : Finset _).card + (clauseGadget F Φ c).vars.card :=
            Finset.card_union_le _ _
      _ ≤ 1 + 3 := by simp [hcg]
      _ = 4 := by norm_num
  calc
    (verifierFactor (F := F) Φ c).vars.card
        ≤ (MvPolynomial.X (selectorIdx Φ c) * clauseGadget F Φ c).vars.card :=
          Finset.card_le_card (by
            intro x hx
            exact hsub hx)
    _ ≤ 4 := hprodvars

/-- The selected derivative variable is a member of `allocatedDerivs`. -/
theorem mem_allocatedDerivs_of_eq
    {κ m : ℕ}
    (S : List (Fin n)) (hS : S.length = κ)
    (α : DerivAlloc κ m) (i : Fin m) (j : Fin κ)
    (hji : α j = i) :
    S.get (j.cast (by omega)) ∈ allocatedDerivs (n := n) S hS α i := by
  unfold allocatedDerivs
  apply List.mem_filterMap.mpr
  refine ⟨j, ?_, ?_⟩
  · simp
  · simp [hji]

/-- If one factor in an allocation product vanishes, the whole allocation product vanishes. -/
theorem allocProduct_eq_zero_of_factor_eq_zero
    {κ m : ℕ}
    (factor : Fin m → MvPolynomial (Fin n) F)
    (S : List (Fin n)) (hS : S.length = κ)
    (α : DerivAlloc κ m) (i : Fin m)
    (hz : iterDerivList (allocatedDerivs (n := n) S hS α i) (factor i) = 0) :
    allocProduct (F := F) factor S hS α = 0 := by
  unfold allocProduct
  have hprod : (∏ k : Fin m, iterDerivList (allocatedDerivs (n := n) S hS α k) (factor k)) =
      iterDerivList (allocatedDerivs (n := n) S hS α i) (factor i) *
        ∏ k in Finset.univ.erase i, iterDerivList (allocatedDerivs (n := n) S hS α k) (factor k) := by
    symm
    exact Finset.mul_prod_erase (s := Finset.univ)
      (f := fun k => iterDerivList (allocatedDerivs (n := n) S hS α k) (factor k))
      (a := i) (by simp)
  rw [hprod, hz, zero_mul]

/-- Any unbounded allocation for verifier factors yields the zero shifted generator. -/
theorem shiftedAllocGenerator_eq_zero_of_unbounded
    {κ : ℕ}
    (Φ : TseitinFormula)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ))) (hS : S.length = κ)
    (hS_nodup : S.Nodup)
    (α : DerivAlloc κ Φ.clauses.length)
    (i : Fin Φ.clauses.length)
    (hbad : allocProfile α i > 4) :
    shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α = 0 := by
  have h_not_relevant : ¬ ∀ j : Fin κ,
      S.get (j.cast (by omega)) ∈ (verifierFactor (F := F) Φ (α j)).vars := by
    intro hrel
    have hle := allocProfile_le_of_width_bound (n := tseitinNumVars Φ)
      (F := F) (S := S) (hS := hS) (α := α)
      (factor := verifierFactor (F := F) Φ) (width := 4)
      (hfactor_width := verifierFactor_vars_card_le_four (F := F) Φ)
      (h_relevant := hrel) (hS_nodup := hS_nodup) i
    omega
  push_neg at h_not_relevant
  obtain ⟨j, hj_notin⟩ := h_not_relevant
  have hmem : S.get (j.cast (by omega)) ∈ allocatedDerivs (n := tseitinNumVars Φ) S hS α (α j) :=
    mem_allocatedDerivs_of_eq (n := tseitinNumVars Φ) S hS α (α j) j rfl
  have hzero_factor :
      iterDerivList (allocatedDerivs (n := tseitinNumVars Φ) S hS α (α j))
        (verifierFactor (F := F) Φ (α j)) = 0 := by
    apply iterDerivList_eq_zero_of_exists_not_in_vars
    exact ⟨S.get (j.cast (by omega)), hmem, hj_notin⟩
  have hzero_prod := allocProduct_eq_zero_of_factor_eq_zero
    (F := F) (factor := verifierFactor (F := F) Φ) (S := S) (hS := hS)
    (α := α) (i := α j) hzero_factor
  unfold shiftedAllocGenerator
  rw [hzero_prod, mul_zero, mlProj_zero]

/-- Every verifier allocation generator belongs to the width-4 bounded allocation span. -/
theorem shiftedAllocGenerator_mem_boundedAllocSpan_verifier
    {κ : ℕ}
    (Φ : TseitinFormula)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ))) (hS : S.length = κ)
    (hS_nodup : S.Nodup)
    (α : DerivAlloc κ Φ.clauses.length) :
    shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α ∈
      boundedAllocSpan (F := F) (w := 4) shift (verifierFactor (F := F) Φ) S hS := by
  by_cases hbounded : ∀ i, allocProfile α i ≤ 4
  · apply Submodule.subset_span
    exact ⟨α, hbounded, rfl⟩
  · push_neg at hbounded
    obtain ⟨i, hi⟩ := hbounded
    rw [shiftedAllocGenerator_eq_zero_of_unbounded (F := F) (κ := κ) Φ shift S hS hS_nodup α i hi]
    exact Submodule.zero_mem _

/-- The raw verifier allocation span is contained in the bounded width-4 allocation span. -/
theorem verifierAllocSpan_le_boundedAllocSpan
    {κ : ℕ}
    (Φ : TseitinFormula)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ))) (hS : S.length = κ)
    (hS_nodup : S.Nodup) :
    verifierAllocSpan (F := F) (κ := κ) Φ shift S hS ≤
      boundedAllocSpan (F := F) (w := 4) shift (verifierFactor (F := F) Φ) S hS := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨α, rfl⟩
  exact shiftedAllocGenerator_mem_boundedAllocSpan_verifier
    (F := F) (κ := κ) Φ shift S hS hS_nodup α

/-- Bounded profile-cover lift for verifier allocation generators. -/
theorem verifierAllocSpan_le_profileSlices
    {κ : ℕ}
    (Φ : TseitinFormula)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ))) (hS : S.length = κ)
    (hS_nodup : S.Nodup) :
    verifierAllocSpan (F := F) (κ := κ) Φ shift S hS ≤
      ⨆ ρ : ProfileIndex Φ.clauses.length 4,
        profileSliceSubspace (F := F) (w := 4) shift (verifierFactor (F := F) Φ) S hS ρ := by
  exact le_trans
    (verifierAllocSpan_le_boundedAllocSpan (F := F) (κ := κ) Φ shift S hS hS_nodup)
    (boundedAllocSpan_le_iSup_profileSlices (F := F) (κ := κ) (m := Φ.clauses.length)
      (w := 4) shift (verifierFactor (F := F) Φ) S hS)

end BoundedProfileLift
