import Mathlib

/-!
# Paper Lemma 18 (arXiv v5, p.32) is false: kernel-checked counterexample

Lemma 18 (paraphrase): for multilinear `p` in `N` variables, `Γ_{ℓ,ℓ}(p) ≤ C(N,ℓ)·2^ℓ`,
where (Def. 12) the rows are `u · ∂^τ p` for every monomial `u` of degree `≤ ℓ` in all `N`
variables and `|τ| = κ = ℓ`, taken modulo `x_i² − x_i` (or with non-multilinear monomials dropped).

Counterexample: `N = 3`, `κ = ℓ = 1`, `p = x₀ + x₁x₂`. The 12 rows are `u · ∂_i p` with
`u ∈ {1, x₀, x₁, x₂}`, `i ∈ {0,1,2}`. Ten of them are already multilinear, so they are rows under
BOTH conventions (reduce or drop). We show these ten rows span a space of dimension `≥ 7`
(they contain the 7 distinct monomials `1, x₀, x₁, x₂, x₀x₁, x₀x₂, x₁x₂`), while
`C(3,1)·2^1 = 6`. Hence `Γ_{1,1}(p) ≥ 7 > 6` under either convention.
-/

namespace Lemma18Counterexample

open MvPolynomial

/-- `p = x₀ + x₁ x₂`, multilinear. -/
noncomputable def p : MvPolynomial (Fin 3) ℚ := X 0 + X 1 * X 2

/-- The four Def.-12 shifts of degree `≤ 1` in all three variables: `1, x₀, x₁, x₂`. -/
noncomputable def shift : Fin 4 → MvPolynomial (Fin 3) ℚ
  | 0 => 1
  | 1 => X 0
  | 2 => X 1
  | 3 => X 2

/-- All 12 Def.-12 rows `u · ∂_i p` (before any reduction). -/
noncomputable def row (a : Fin 4 × Fin 3) : MvPolynomial (Fin 3) ℚ := shift a.1 * pderiv a.2 p

/-- The ten rows that are already multilinear (all rows except `x₂·∂₁p = x₂²`, `x₁·∂₂p = x₁²`).
They are unchanged by `x² → x` and are not dropped, so they are rows under both conventions. -/
def mlIdx : Fin 10 → Fin 4 × Fin 3
  | 0 => (0, 0) | 1 => (1, 0) | 2 => (2, 0) | 3 => (3, 0)
  | 4 => (0, 1) | 5 => (1, 1) | 6 => (2, 1)
  | 7 => (0, 2) | 8 => (1, 2) | 9 => (3, 2)

lemma pderiv0 : pderiv 0 p = 1 := by simp [p, pderiv_X]
lemma pderiv1 : pderiv 1 p = X 2 := by simp [p, pderiv_X]
lemma pderiv2 : pderiv 2 p = X 1 := by simp [p, pderiv_X]

/-- The seven distinct monomials, as exponent vectors. -/
noncomputable def expo : Fin 7 → (Fin 3 →₀ ℕ)
  | 0 => 0
  | 1 => Finsupp.single 0 1
  | 2 => Finsupp.single 1 1
  | 3 => Finsupp.single 2 1
  | 4 => Finsupp.single 0 1 + Finsupp.single 1 1
  | 5 => Finsupp.single 0 1 + Finsupp.single 2 1
  | 6 => Finsupp.single 1 1 + Finsupp.single 2 1

/-- Coordinates of the exponent vectors. -/
def tbl : Fin 7 → ℕ × ℕ × ℕ
  | 0 => (0, 0, 0) | 1 => (1, 0, 0) | 2 => (0, 1, 0) | 3 => (0, 0, 1)
  | 4 => (1, 1, 0) | 5 => (1, 0, 1) | 6 => (0, 1, 1)

lemma expo_coords (j : Fin 7) : (expo j 0, expo j 1, expo j 2) = tbl j := by
  fin_cases j <;> simp [expo, tbl]

lemma expo_injective : Function.Injective expo := by
  intro a b h
  have ha := expo_coords a
  rw [h, expo_coords b] at ha
  exact (by decide : Function.Injective tbl) ha.symm

lemma mono_li : LinearIndependent ℚ (fun j => (monomial (expo j) (1 : ℚ))) := by
  have := (MvPolynomial.basisMonomials (Fin 3) ℚ).linearIndependent.comp expo expo_injective
  convert this using 1

/-- Each of the seven monomials is literally one of the ten multilinear rows. -/
lemma mono_mem (j : Fin 7) :
    monomial (expo j) (1 : ℚ) ∈ Submodule.span ℚ (Set.range (fun t => row (mlIdx t))) := by
  apply Submodule.subset_span
  fin_cases j
  · exact ⟨0, by simp [row, mlIdx, shift, pderiv0, expo]⟩
  · exact ⟨1, by simp [row, mlIdx, shift, pderiv0, expo, X]⟩
  · exact ⟨2, by simp [row, mlIdx, shift, pderiv0, expo, X]⟩
  · exact ⟨3, by simp [row, mlIdx, shift, pderiv0, expo, X]⟩
  · exact ⟨8, by simp [row, mlIdx, shift, pderiv2, expo, X, monomial_mul]⟩
  · exact ⟨5, by simp [row, mlIdx, shift, pderiv1, expo, X, monomial_mul]⟩
  · exact ⟨6, by simp [row, mlIdx, shift, pderiv1, expo, X, monomial_mul]⟩

/-- **Lemma 18 fails**: the span of the multilinear Def.-12 rows of `p = x₀ + x₁x₂`
(`N = 3`, `κ = ℓ = 1`) has dimension `> C(3,1)·2^1 = 6`. -/
theorem lemma18_fails :
    Nat.choose 3 1 * 2 ^ 1 <
      Module.finrank ℚ (Submodule.span ℚ (Set.range (fun t => row (mlIdx t)))) := by
  set W := Submodule.span ℚ (Set.range (fun t => row (mlIdx t)))
  haveI : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hli : LinearIndependent ℚ (fun j : Fin 7 => (⟨_, mono_mem j⟩ : W)) :=
    LinearIndependent.of_comp W.subtype mono_li
  have h7 := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h7
  norm_num [Nat.choose]
  omega

/-- The two remaining rows are the squares `x₂²` and `x₁²` (non-multilinear), confirming the
row list: under `x²→x` they reduce to rows already present, under "drop" they vanish. -/
theorem nonmultilinear_rows : row (3, 1) = X 2 ^ 2 ∧ row (2, 2) = X 1 ^ 2 := by
  simp [row, shift, pderiv1, pderiv2, sq]

end Lemma18Counterexample

#print axioms Lemma18Counterexample.lemma18_fails
#print axioms Lemma18Counterexample.nonmultilinear_rows
