import PallLean.Profile

/-! # Layer 3: Within-profile dimension bound -/

namespace SPDP

open MvPolynomial Finset

variable {n : ℕ} {F : Type*} [CommRing F]

/-! ## Commutativity of partial derivatives -/

/-- Partial derivatives commute. -/
theorem pderiv_comm (i j : Fin n) (p : MvPolynomial (Fin n) F) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  suffices h : ∀ (s : Fin n →₀ ℕ) (a : F),
      pderiv i (pderiv j (monomial s a)) = pderiv j (pderiv i (monomial s a)) by
    conv_lhs => rw [MvPolynomial.as_sum p]
    conv_rhs => rw [MvPolynomial.as_sum p]
    simp only [map_sum]
    exact Finset.sum_congr rfl (fun s _ => h s (p.coeff s))
  intro s a
  simp only [pderiv_monomial]
  -- After two applications of pderiv_monomial:
  -- LHS = monomial (s - δj - δi) ((a * s j) * (s - δj) i)
  -- RHS = monomial (s - δi - δj) ((a * s i) * (s - δi) j)
  -- where (s - δj) i means the Finsupp function applied to i
  -- We need: exponents equal ∧ coefficients equal
  -- Exponent equality: s - δj - δi = s - δi - δj (Nat subtraction commutes pointwise)
  -- Coeff equality: (a * s j) * (s-δj) i = (a * s i) * (s-δi) j
  --   When i ≠ j: (s-δj) i = s i and (s-δi) j = s j, so both = a * s j * s i ✓
  --   When i = j: trivially equal ✓
  by_cases hij : i = j
  · subst hij; rfl
  · -- Need to show monomial equality
    -- The coefficient uses DFunLike coercion for (s - δj) i
    -- Use: Finsupp.tsub_apply and Finsupp.single_apply
    have h_exp : s - Finsupp.single j 1 - Finsupp.single i 1 =
                 s - Finsupp.single i 1 - Finsupp.single j 1 := by
      ext k; simp only [Finsupp.tsub_apply, Finsupp.single_apply]; omega
    -- For coefficients, we need that applying the finsupp gives the right nat
    have h_sji : DFunLike.coe (s - Finsupp.single j 1) i = s i := by
      simp only [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hij)]; omega
    have h_sij : DFunLike.coe (s - Finsupp.single i 1) j = s j := by
      simp only [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hij]; omega
    rw [h_exp, h_sji, h_sij]; ring

/-! ## Iterated derivatives and permutations -/

theorem iterDerivList_swap (a b : Fin n) (S : List (Fin n))
    (p : MvPolynomial (Fin n) F) :
    iterDerivList (a :: b :: S) p = iterDerivList (b :: a :: S) p := by
  unfold iterDerivList; simp only [List.foldl_cons]; congr 1; exact pderiv_comm b a p

theorem iterDerivList_perm (S T : List (Fin n)) (p : MvPolynomial (Fin n) F)
    (hperm : S.Perm T) : iterDerivList S p = iterDerivList T p := by
  induction hperm generalizing p with
  | nil => rfl
  | cons x _ ih => unfold iterDerivList; simp only [List.foldl_cons]; exact ih (pderiv x p)
  | swap x y S' => exact iterDerivList_swap y x S' p
  | trans _ _ ih1 ih2 => exact (ih1 p).trans (ih2 p)

/-! ## Allocated derivatives: structural properties -/

/-- Allocated derivatives are Nodup when S is Nodup. -/
theorem allocatedDerivs_nodup {κ : ℕ}
    (S : List (Fin n)) (hS : S.length = κ)
    (α : DerivAlloc κ m) (hS_nodup : S.Nodup) (i : Fin m) :
    (allocatedDerivs S hS α i).Nodup := by
  unfold allocatedDerivs
  apply List.Nodup.filterMap _ (List.nodup_finRange κ)
  intro a a' b hba hba'
  rw [Option.mem_def] at hba hba'
  -- hba : (if α a = i then some (S.get ...) else none) = some b
  -- hba' : (if α a' = i then some (S.get ...) else none) = some b
  have ha : α a = i := by
    by_contra h; simp only [if_neg h] at hba; exact absurd hba nofun
  have ha' : α a' = i := by
    by_contra h; simp only [if_neg h] at hba'; exact absurd hba' nofun
  simp only [if_pos ha, Option.some.injEq] at hba
  simp only [if_pos ha', Option.some.injEq] at hba'
  -- hba : S.get ... = b, hba' : S.get ... = b
  have h_eq : S.get (Fin.cast (by omega) a) = S.get (Fin.cast (by omega) a') := by
    exact hba.trans hba'.symm
  have := hS_nodup.get_inj_iff.mp h_eq
  exact Fin.ext (by simp [Fin.ext_iff] at this; exact this)

/-- All elements of allocatedDerivs are in the factor's vars. -/
theorem allocatedDerivs_subset_vars {κ : ℕ}
    (S : List (Fin n)) (hS : S.length = κ)
    (α : DerivAlloc κ m)
    (factor : Fin m → MvPolynomial (Fin n) F)
    (h_relevant : ∀ j : Fin κ, S.get (j.cast (by omega)) ∈ (factor (α j)).vars)
    (i : Fin m) :
    ∀ v ∈ allocatedDerivs S hS α i, v ∈ (factor i).vars := by
  intro v hv
  unfold allocatedDerivs at hv
  simp only [List.mem_filterMap, List.mem_finRange, true_and] at hv
  obtain ⟨j, hj⟩ := hv
  -- hj : v ∈ (if α j = i then some (...) else none)
  have hα : α j = i := by
    by_contra h; simp only [if_neg h] at hj; exact absurd hj nofun
  simp only [if_pos hα, Option.mem_def, Option.some.injEq] at hj
  rw [← hj, ← hα]; exact h_relevant j

/-- |allocatedDerivs toFinset for factor i| ≤ width. -/
theorem allocatedDerivs_toFinset_card_le {κ : ℕ}
    (S : List (Fin n)) (hS : S.length = κ)
    (α : DerivAlloc κ m) (hS_nodup : S.Nodup)
    (factor : Fin m → MvPolynomial (Fin n) F)
    (width : ℕ)
    (hfactor_width : ∀ i, (factor i).vars.card ≤ width)
    (h_relevant : ∀ j : Fin κ, S.get (j.cast (by omega)) ∈ (factor (α j)).vars)
    (i : Fin m) :
    (allocatedDerivs S hS α i).toFinset.card ≤ width := by
  have hsub : (allocatedDerivs S hS α i).toFinset ⊆ (factor i).vars := by
    intro v hv
    exact allocatedDerivs_subset_vars S hS α factor h_relevant i v (List.mem_toFinset.mp hv)
  exact le_trans (Finset.card_le_card hsub) (hfactor_width i)

end SPDP
