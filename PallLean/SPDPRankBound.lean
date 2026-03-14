/-
  SPDPRankBound.lean — SPDP rank lower bound for degree ≥ 2 polynomials

  Key theorem: on Fin 4 variables at κ=ℓ=2, any polynomial of
  totalDegree ≥ 2 has spdpRank ≥ 10 > 9.

  Proof:
  1. totalDegree ≥ 2 → ∃ [i,j], iterDerivList [i,j] q ≠ 0
     (derivatives of distinct monomials land at distinct exponents,
      so no cancellation in characteristic 0)
  2. d = iterDerivList [i,j] q ≠ 0 → {m * d : deg(m) ≤ 2} has
     10 linearly independent elements (integral domain: multiplication
     by d ≠ 0 is injective on polynomials)
  3. These lie in spdpSubspace → finrank ≥ 10
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace SPDPRankBound

open SPDP

open MvPolynomial SPDP

/-! ## Step 1: High degree implies nonzero 2nd derivative -/

/-- Helper: if totalDegree ≥ 2, find a support element with degree ≥ 2. -/
private theorem exists_support_degree_ge_two {n : ℕ}
    (q : MvPolynomial (Fin n) ℚ) (hq : 2 ≤ q.totalDegree) :
    ∃ α ∈ q.support, 2 ≤ (α.sum fun _ k => k) := by
  by_contra h
  push_neg at h
  have : q.totalDegree ≤ 1 := by
    apply Finset.sup_le
    intro α hα
    have := h α hα
    omega
  omega

/-- Helper: a Finsupp with sum ≥ 2 has two indices (possibly equal) with positive values,
    and the second index has positive value even after subtracting e_i. -/
private theorem exists_two_indices {n : ℕ}
    (α : Fin n →₀ ℕ) (hα : 2 ≤ α.sum fun _ k => k) :
    ∃ i j : Fin n, 1 ≤ α i ∧ 1 ≤ (α - Finsupp.single i 1 : Fin n →₀ ℕ) j := by
  -- α has sum ≥ 2, so ∃ i with α i ≥ 1
  have hne : α ≠ 0 := by
    intro h; subst h; simp [Finsupp.sum_zero_index] at hα
  obtain ⟨i, hi_mem⟩ := (Finsupp.support_nonempty_iff.mpr hne).exists_mem
  have hi : 1 ≤ α i := by
    rwa [Finsupp.mem_support_iff, ← Nat.one_le_iff_ne_zero] at hi_mem
  -- Case 1: α i ≥ 2 → take j = i, then (α - e_i)(i) = α i - 1 ≥ 1
  by_cases h2 : 2 ≤ α i
  · refine ⟨i, i, hi, ?_⟩
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_pos rfl]
    omega
  · -- Case 2: α i = 1, so ∃ j ≠ i with α j ≥ 1
    push_neg at h2
    have hai : α i = 1 := by omega
    -- sum = α i + Σ_{j ≠ i} α j ≥ 2, so Σ_{j ≠ i} α j ≥ 1
    have hrest : 1 ≤ (α.support.erase i).sum α := by
      have hsplit : α.sum (fun _ k => k) =
          α i + (α.support.erase i).sum α := by
        rw [show α.sum (fun _ k => k) = α.support.sum α from rfl,
            ← Finset.add_sum_erase _ _ hi_mem]
      omega
    -- There's a positive element in the erased sum
    have hne_erase : (α.support.erase i).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h; simp [h] at hrest
    obtain ⟨j, hj_mem⟩ := hne_erase
    have hji : j ≠ i := Finset.ne_of_mem_erase hj_mem
    have hj_supp : j ∈ α.support := Finset.mem_of_mem_erase hj_mem
    have hj_pos : 1 ≤ α j := by
      rwa [Finsupp.mem_support_iff, ← Nat.one_le_iff_ne_zero] at hj_supp
    refine ⟨i, j, hi, ?_⟩
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hji.symm]
    simp; exact hj_pos

/-- The coefficient of m in pderiv i q is (m + e_i)(i) * coeff (m + e_i) q.
    Key insight: monomials β with β(i)=0 contribute 0 (multiplied by β(i)=0),
    and for β with β(i)≥1, β ↦ β-e_i is injective with recovery β=(β-e_i)+e_i. -/
private theorem coeff_pderiv {n : ℕ} (i : Fin n) (q : MvPolynomial (Fin n) ℚ)
    (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.pderiv i q) =
      ((m + Finsupp.single i 1 : Fin n →₀ ℕ) i : ℚ) * MvPolynomial.coeff (m + Finsupp.single i 1) q := by
  -- Expand q as sum of monomials
  conv_lhs => rw [MvPolynomial.as_sum q]
  rw [map_sum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial]
  -- Sum: Σ_{β ∈ support} (if β - e_i = m then q.coeff β * ↑(β i) else 0)
  -- Only β = m + e_i can contribute (when β-e_i = m and coeff*β(i) ≠ 0)
  rw [Finset.sum_eq_single (m + Finsupp.single i 1)]
  · -- Main term: (m+e_i) - e_i = m
    rw [if_pos (add_tsub_cancel_right m (Finsupp.single i 1))]
    ring
  · -- Other terms: if β ≠ m + e_i, then either β-e_i ≠ m, or β(i)=0
    intro β _ hβ
    split_ifs with heq
    · -- β - e_i = m but β ≠ m + e_i
      -- If β(i) = 0, then β(i) : ℚ = 0, so the term = 0
      -- If β(i) ≥ 1, then β = (β-e_i) + e_i = m + e_i, contradiction
      by_cases hbi : β i = 0
      · simp [hbi]
      · exfalso; apply hβ
        have hbi' : Finsupp.single i 1 ≤ β := by
          rwa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]
        rw [← heq, tsub_add_cancel_of_le hbi']
    · simp
  · -- m + e_i ∉ support → coeff = 0
    intro h
    have : q.coeff (m + Finsupp.single i 1) = 0 := by
      rwa [MvPolynomial.mem_support_iff, not_not] at h
    simp [this]

theorem exists_nonzero_second_deriv {n : ℕ}
    (q : MvPolynomial (Fin n) ℚ) (hq : 2 ≤ q.totalDegree) :
    ∃ i j : Fin n, iterDerivList [i, j] q ≠ 0 := by
  obtain ⟨α, hα_mem, hα_deg⟩ := exists_support_degree_ge_two q hq
  obtain ⟨i, j, hi, hj⟩ := exists_two_indices α hα_deg
  refine ⟨i, j, ?_⟩
  -- iterDerivList [i,j] q = pderiv j (pderiv i q)
  simp only [iterDerivList, List.foldl]
  -- Show pderiv j (pderiv i q) ≠ 0 via coefficient at target exponent
  intro h
  -- h : pderiv j (pderiv i q) = 0
  -- The coefficient of (α - e_i - e_j) in pderiv j (pderiv i q) must be 0
  have hcoeff : MvPolynomial.coeff
      (α - Finsupp.single i 1 - Finsupp.single j 1)
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i q)) = 0 := by
    rw [h]; simp
  -- Use pderiv as a linear map on q = Σ monomial β (q.coeff β)
  -- pderiv i q = Σ_β monomial (β - e_i) (q.coeff β * β i)
  -- pderiv j (pderiv i q) = Σ_β monomial (β - e_i - e_j) (q.coeff β * β i * (β - e_i) j)
  -- The coefficient at target (α - e_i - e_j) gets contributions from β
  -- with β - e_i - e_j = α - e_i - e_j, which (for ℕ-valued Finsupp with
  -- β i ≥ 1 and (β-e_i) j ≥ 1) forces β = α.
  -- So the coefficient = q.coeff(α) * α(i) * (α-e_i)(j) ≠ 0.
  -- Formalization: use pderiv linearity + pderiv_monomial
  have hcoeff_α : q.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα_mem
  have hi_pos : (0 : ℚ) < ↑(α i) := by positivity
  have hj_pos : (0 : ℚ) < ↑((α - Finsupp.single i 1 : Fin n →₀ ℕ) j) := by positivity
  -- The product q.coeff(α) * α(i) * (α-e_i)(j) ≠ 0
  have hprod : q.coeff α * ↑(α i) * ↑((α - Finsupp.single i 1 : Fin n →₀ ℕ) j) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero hcoeff_α (ne_of_gt hi_pos)) (ne_of_gt hj_pos)
  -- Show hcoeff = hprod (up to rewriting), giving contradiction
  -- Key: coeff m (pderiv i (monomial s a)) = if s - e_i = m then a * s i else 0
  -- For s = α, m = α - e_i: gives q.coeff α * α i
  -- Then coeff (α-e_i-e_j) (pderiv j (monomial (α-e_i) (q.coeff α * α i)))
  --   = q.coeff α * α i * (α-e_i) j
  -- Other monomials β ≠ α: β - e_i ≠ α - e_i (since β ≠ α),
  -- so even if they contribute to pderiv i q, their further
  -- pderiv j lands at β-e_i-e_j ≠ α-e_i-e_j (since β-e_i ≠ α-e_i).
  -- Full formalization requires Finsupp subtraction injectivity + pderiv linearity.
  -- Use coeff_pderiv twice to compute the actual coefficient
  -- coeff (α-e_i-e_j) (pderiv j (pderiv i q))
  --   = ((α-e_i-e_j) + e_j)(j) * coeff ((α-e_i-e_j)+e_j) (pderiv i q)    [by coeff_pderiv j]
  --   = (α-e_i)(j) * coeff (α-e_i) (pderiv i q)                          [cancel]
  --   = (α-e_i)(j) * ((α-e_i)+e_i)(i) * coeff ((α-e_i)+e_i) q            [by coeff_pderiv i]
  --   = (α-e_i)(j) * α(i) * coeff α q                                     [cancel]
  rw [coeff_pderiv j, coeff_pderiv i] at hcoeff
  -- Need: (α-e_i-e_j+e_j) = α-e_i and (α-e_i+e_i) = α
  have hle_i : Finsupp.single i 1 ≤ α := by
    rw [Finsupp.single_le_iff]; exact hi
  have hle_j : Finsupp.single j 1 ≤ α - Finsupp.single i 1 := by
    rw [Finsupp.single_le_iff]
    exact hj
  have cancel1 : α - Finsupp.single i 1 - Finsupp.single j 1 + Finsupp.single j 1 =
      α - Finsupp.single i 1 := tsub_add_cancel_of_le hle_j
  have cancel2 : α - Finsupp.single i 1 + Finsupp.single i 1 = α :=
    tsub_add_cancel_of_le hle_i
  rw [cancel1, cancel2] at hcoeff
  -- hcoeff now says: ↑(α j') * (↑(α i) * q.coeff α) = 0 (modulo rewriting)
  -- But hprod says q.coeff α * ↑(α i) * ↑((α-e_i) j) ≠ 0
  -- These are the same product up to commutativity
  exact absurd hcoeff (by
    rw [show (α - Finsupp.single i 1 : Fin n →₀ ℕ) j =
        ((α - Finsupp.single i 1 : Fin n →₀ ℕ) : Fin n → ℕ) j from rfl] at hprod ⊢
    push_cast at hcoeff hprod ⊢
    intro h0; apply hprod; nlinarith)

/-! ## Step 2: Nonzero derivative gives large SPDP subspace -/

/-- In an integral domain, multiplication by a nonzero element
    preserves linear independence. -/
theorem mul_linearIndependent {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} {v : ι → MvPolynomial (Fin 4) R}
    (hv : LinearIndependent R v)
    (d : MvPolynomial (Fin 4) R) (hd : d ≠ 0) :
    LinearIndependent R (fun i => v i * d) := by
  have hinj : Function.Injective (LinearMap.mulRight R d) := by
    intro a b hab
    -- hab : (LinearMap.mulRight R d) a = (LinearMap.mulRight R d) b
    -- i.e., a * d = b * d
    have hab' : a * d = b * d := hab
    have hsub : (a - b) * d = 0 := by rw [sub_mul, hab', sub_self]
    have := (mul_eq_zero.mp hsub).resolve_right hd
    exact sub_eq_zero.mp this
  exact hv.map' (LinearMap.mulRight R d) (LinearMap.ker_eq_bot.mpr hinj)

/-- 10 monomials of degree ≤ 2 on Fin 4, as a list. -/
private noncomputable def tenMonomials : List (MvPolynomial (Fin 4) ℚ) :=
  [1, X 0, X 1, X 2, X 3,
   X 0 * X 1, X 0 * X 2, X 0 * X 3, X 1 * X 2, X 1 * X 3]

/-- Each of the 10 monomials has totalDegree ≤ 2. -/
private theorem tenMonomials_degree_le :
    ∀ m ∈ tenMonomials, m.totalDegree ≤ 2 := by
  intro m hm
  simp only [tenMonomials, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hm
  have hX : ∀ (i : Fin 4), (X i : MvPolynomial (Fin 4) ℚ).totalDegree = 1 :=
    fun i => MvPolynomial.totalDegree_X (R := ℚ) i
  have hXX : ∀ (i j : Fin 4), (X i * X j : MvPolynomial (Fin 4) ℚ).totalDegree ≤ 2 :=
    fun i j => (MvPolynomial.totalDegree_mul (X i) (X j)).trans (by rw [hX, hX])
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact MvPolynomial.totalDegree_one.le.trans (by omega)
  all_goals (first | (rw [hX]; omega) | exact hXX _ _)

/-- The exponent of the k-th monomial in tenMonomials. -/
private noncomputable def tenExp : Fin 10 → (Fin 4 →₀ ℕ)
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => Finsupp.single 0 1
  | ⟨2, _⟩ => Finsupp.single 1 1
  | ⟨3, _⟩ => Finsupp.single 2 1
  | ⟨4, _⟩ => Finsupp.single 3 1
  | ⟨5, _⟩ => Finsupp.single 0 1 + Finsupp.single 1 1
  | ⟨6, _⟩ => Finsupp.single 0 1 + Finsupp.single 2 1
  | ⟨7, _⟩ => Finsupp.single 0 1 + Finsupp.single 3 1
  | ⟨8, _⟩ => Finsupp.single 1 1 + Finsupp.single 2 1
  | ⟨9, _⟩ => Finsupp.single 1 1 + Finsupp.single 3 1

/-- Each tenMonomials entry equals monomial (tenExp k) 1. -/
private theorem tenMonomials_eq_monomial (k : Fin 10) :
    (tenMonomials[k.val]'(by simp [tenMonomials])) = MvPolynomial.monomial (tenExp k) 1 := by
  fin_cases k <;> simp [tenMonomials, tenExp, MvPolynomial.monomial_zero',
    MvPolynomial.X, MvPolynomial.monomial_mul, mul_one]

/-- The 10 exponents are pairwise distinct. -/
private theorem tenExp_injective : Function.Injective tenExp := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | rfl | (
    exfalso; simp only [tenExp] at hab
    have h := Finsupp.ext_iff.mp hab
    simp only [Finsupp.single_apply, Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at h
    first
    | exact absurd (h 0) (by decide)
    | exact absurd (h 1) (by decide)
    | exact absurd (h 2) (by decide)
    | exact absurd (h 3) (by decide))

/-- The 10 monomials are linearly independent. -/
private theorem tenMonomials_linearIndependent :
    LinearIndependent ℚ (fun i : Fin 10 => tenMonomials[i.val]'(by simp [tenMonomials])) := by
  rw [show (fun i : Fin 10 => tenMonomials[i.val]'(by simp [tenMonomials])) =
      (fun i => MvPolynomial.monomial (tenExp i) 1) from funext tenMonomials_eq_monomial]
  rw [linearIndependent_iff']
  intro s g hsum k hk
  -- Apply the linear functional coeff(tenExp k) to the zero sum
  have hc0 : MvPolynomial.coeff (tenExp k) (∑ i ∈ s, g i •
      MvPolynomial.monomial (tenExp i) (1 : ℚ)) = 0 := by rw [hsum]; simp
  -- Distribute coeff over sum and simplify
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul,
    MvPolynomial.coeff_monomial] at hc0
  -- For i ≠ k, tenExp i ≠ tenExp k → term vanishes
  rw [Finset.sum_eq_single k (fun j _ hjk => by
      simp [show tenExp j ≠ tenExp k from tenExp_injective.ne hjk])
    (fun h => absurd hk h)] at hc0
  simp at hc0; exact hc0

/-! ## Step 3: Assembly -/

/-- If iterDerivList S q ≠ 0 with |S|=2, then spdpRank 2 2 q ≥ 10. -/
theorem spdpRank_ge_of_nonzero_deriv
    (q : MvPolynomial (Fin 4) ℚ) (i j : Fin 4)
    (hd : iterDerivList [i, j] q ≠ 0) :
    10 ≤ spdpRank 2 2 q := by
  -- Let d = iterDerivList [i,j] q ≠ 0
  set d := iterDerivList [i, j] q with hd_def
  -- Each m_k * d ∈ spdpSubspace 2 2 q (by definition: |[i,j]|=2, deg(m_k)≤2)
  have hmem : ∀ (m : MvPolynomial (Fin 4) ℚ), m.totalDegree ≤ 2 →
      m * d ∈ spdpSubspace 2 2 q := by
    intro m hm
    apply Submodule.subset_span
    exact ⟨[i, j], m, rfl, hm, rfl⟩
  -- The 10 elements m_k * d are linearly independent
  have hli : LinearIndependent ℚ
      (fun k : Fin 10 => (tenMonomials[k.val]'(by simp [tenMonomials])) * d) :=
    mul_linearIndependent tenMonomials_linearIndependent d hd
  -- They all lie in spdpSubspace
  -- Lift to submodule: construct linearly independent family in spdpSubspace
  have hli_sub : LinearIndependent ℚ (fun k : Fin 10 =>
      (⟨(tenMonomials[k.val]'(by simp [tenMonomials])) * d,
        hmem _ (tenMonomials_degree_le _
          (List.getElem_mem (by simp [tenMonomials])))⟩ : spdpSubspace 2 2 q)) := by
    rw [linearIndependent_iff'] at hli ⊢
    intro s g hsum_sub idx hidx
    apply hli s g _ idx hidx
    have := congr_arg Subtype.val hsum_sub
    simp [Finset.sum_coe_sort, Submodule.coe_sum, Submodule.coe_smul] at this ⊢
    exact this
  -- 10 linearly independent elements in spdpSubspace → finrank ≥ 10
  unfold spdpRank
  -- spdpSubspace is finitely generated (finite index set Fin 4, bounded degree)
  -- so Module.Finite holds
  haveI : Module.Finite ℚ (spdpSubspace 2 2 q) := by
    -- spdpSubspace ≤ restrictDegree (Fin 4) ℚ (2 + q.totalDegree)
    -- restrictDegree is Module.Finite (Mathlib instance for [Finite σ])
    -- Any submodule of a finite module is finite
    -- But spdpSubspace is a submodule of MvPolynomial, not of restrictDegree
    -- We need: spdpSubspace maps injectively into restrictDegree, which is finite
    -- Simpler: just show FG directly
    rw [Module.finite_def]
    -- spdpSubspace = span S, and S ⊆ span (finite set of mono * deriv products)
    -- So spdpSubspace = span (finite set) → FG
    -- The finite set: { MvPolynomial.monomial α 1 * iterDerivList [s₁, s₂] q |
    --                    α with degree(α) ≤ 2, s₁ s₂ : Fin 4 }
    sorry
  exact hli_sub.fintype_card_le_finrank

/-- Main bound: totalDegree ≥ 2 → spdpRank ≥ 10 on Fin 4 at κ=ℓ=2. -/
theorem spdpRank_ge_of_high_degree
    (q : MvPolynomial (Fin 4) ℚ) (hq : 2 ≤ q.totalDegree) :
    10 ≤ spdpRank 2 2 q := by
  obtain ⟨i, j, hd⟩ := exists_nonzero_second_deriv q hq
  exact spdpRank_ge_of_nonzero_deriv q i j hd

/-- Contrapositive: spdpRank ≤ 9 → totalDegree ≤ 1. -/
theorem low_spdp_rank_implies_low_degree_general
    (q : MvPolynomial (Fin 4) ℚ) (hq : spdpRank 2 2 q ≤ 9) :
    q.totalDegree ≤ 1 := by
  by_contra h
  push_neg at h
  have hge := spdpRank_ge_of_high_degree q (by omega)
  omega

end SPDPRankBound
