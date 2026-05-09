import PallLean.Paper93.DeepMath.PathB.RouteBTouchedUntouchedBackgroundKR

/-!
# Route B touched/background KR product composition

This file proves the algebraic Khatri--Rao composition step: if a touched local
piece lies in a finite local span and the untouched background lies in a finite
profile/normal-form span, then their multilinear projected product lies in the
span of all pairwise projected products.

This is deliberately only a composition theorem.  The background profile basis
must still be constructed from the paper §9.3 local-monoid normal forms; we do
not replace it by a global ambient monomial span.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Pairwise projected-product generators for a touched local basis and an
untouched background basis. -/
noncomputable def mlProjProductBasis {N : ℕ}
    (A B : Finset (MvPolynomial (Fin N) ℚ)) :
    Finset (MvPolynomial (Fin N) ℚ) :=
  (A.product B).image (fun ab => MultilinearSPDP.mlProj (ab.1 * ab.2))

/-- The projected-product basis has at most `|A| * |B|` generators. -/
theorem mlProjProductBasis_card_le {N : ℕ}
    (A B : Finset (MvPolynomial (Fin N) ℚ)) :
    (mlProjProductBasis A B).card ≤ A.card * B.card := by
  classical
  unfold mlProjProductBasis
  exact (Finset.card_image_le).trans (by simp [Finset.card_product])

/-- Product-basis count after inserting separate local/background budgets. -/
theorem mlProjProductBasis_card_le_mul_budget {N LA LB : ℕ}
    (A B : Finset (MvPolynomial (Fin N) ℚ))
    (hA : A.card ≤ LA) (hB : B.card ≤ LB) :
    (mlProjProductBasis A B).card ≤ LA * LB := by
  exact (mlProjProductBasis_card_le A B).trans (Nat.mul_le_mul hA hB)

/-- If the local side costs `n^200` and the background side costs `n^C`, the
pairwise product basis costs `n^(200+C)`. -/
theorem mlProjProductBasis_card_le_pow_add_budget {N n C : ℕ}
    (A B : Finset (MvPolynomial (Fin N) ℚ))
    (hA : A.card ≤ n ^ 200) (hB : B.card ≤ n ^ C) :
    (mlProjProductBasis A B).card ≤ n ^ (200 + C) := by
  have hmul := mlProjProductBasis_card_le_mul_budget A B hA hB
  rw [pow_add]
  exact hmul

/-- Multilinear projection may be applied to the left factor before a final
multilinear projection of the product.  Non-multilinear monomials in the left
factor cannot become multilinear after multiplying by the right factor because
exponents only increase. -/
theorem mlProj_mul_left_mlProj {N : ℕ}
    (p q : MvPolynomial (Fin N) ℚ) :
    MultilinearSPDP.mlProj (MultilinearSPDP.mlProj p * q) =
      MultilinearSPDP.mlProj (p * q) := by
  classical
  ext α
  rw [WithinProfileBound.coeff_mlProj, WithinProfileBound.coeff_mlProj]
  by_cases hα : MultilinearSPDP.Finsupp.IsMultilinear α
  · simp [hα]
    rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_antidiagonal] at hx
    rw [WithinProfileBound.coeff_mlProj]
    have hxsum : α = x.1 + x.2 := hx.symm
    have hx1 : MultilinearSPDP.Finsupp.IsMultilinear x.1 := by
      intro i
      have hi := hα i
      rw [hxsum] at hi
      simp only [Finsupp.coe_add, Pi.add_apply] at hi
      omega
    simp [hx1]
  · simp [hα]

/-- Multilinear projection may likewise be applied to the right factor before
the final projection of a product. -/
theorem mlProj_mul_right_mlProj {N : ℕ}
    (p q : MvPolynomial (Fin N) ℚ) :
    MultilinearSPDP.mlProj (p * MultilinearSPDP.mlProj q) =
      MultilinearSPDP.mlProj (p * q) := by
  classical
  rw [mul_comm p q, mul_comm p (MultilinearSPDP.mlProj q)]
  exact mlProj_mul_left_mlProj q p

/-- If `p ∈ span A` and `q ∈ span B`, then `mlProj (p*q)` lies in the span of
the pairwise projected-product basis. -/
theorem mlProj_mul_mem_span_productBasis {N : ℕ}
    (A B : Finset (MvPolynomial (Fin N) ℚ))
    {p q : MvPolynomial (Fin N) ℚ}
    (hp : p ∈ Submodule.span ℚ (↑A : Set (MvPolynomial (Fin N) ℚ)))
    (hq : q ∈ Submodule.span ℚ (↑B : Set (MvPolynomial (Fin N) ℚ))) :
    MultilinearSPDP.mlProj (p * q) ∈
      Submodule.span ℚ (↑(mlProjProductBasis A B) : Set (MvPolynomial (Fin N) ℚ)) := by
  classical
  let W : Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
    Submodule.span ℚ (↑(mlProjProductBasis A B) : Set (MvPolynomial (Fin N) ℚ))
  refine Submodule.span_induction
    (s := (↑A : Set (MvPolynomial (Fin N) ℚ)))
    (p := fun p _hp => ∀ q, q ∈ Submodule.span ℚ (↑B : Set (MvPolynomial (Fin N) ℚ)) →
      MultilinearSPDP.mlProj (p * q) ∈ W) ?base ?zero ?add ?smul hp q hq
  · intro a ha q hq
    refine Submodule.span_induction
      (s := (↑B : Set (MvPolynomial (Fin N) ℚ)))
      (p := fun q _hq => MultilinearSPDP.mlProj (a * q) ∈ W) ?baseB ?zeroB ?addB ?smulB hq
    · intro b hb
      change MultilinearSPDP.mlProj (a * b) ∈ W
      apply Submodule.subset_span
      unfold mlProjProductBasis
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
    · change MultilinearSPDP.mlProj (a * 0) ∈ W
      simp [W]
    · intro y z _hy _hz hyW hzW
      change MultilinearSPDP.mlProj (a * (y + z)) ∈ W
      rw [mul_add, MultilinearSPDP.mlProj_add]
      exact Submodule.add_mem W hyW hzW
    · intro c y _hy hyW
      change MultilinearSPDP.mlProj (a * (c • y)) ∈ W
      rw [mul_smul_comm, MultilinearSPDP.mlProj_smul]
      exact Submodule.smul_mem W c hyW
  · intro q _hq
    change MultilinearSPDP.mlProj (0 * q) ∈ W
    simp [W]
  · intro x y _hx _hy hxW hyW q hq
    change MultilinearSPDP.mlProj ((x + y) * q) ∈ W
    rw [add_mul, MultilinearSPDP.mlProj_add]
    exact Submodule.add_mem W (hxW q hq) (hyW q hq)
  · intro c x _hx hxW q hq
    change MultilinearSPDP.mlProj ((c • x) * q) ∈ W
    rw [smul_mul_assoc, MultilinearSPDP.mlProj_smul]
    exact Submodule.smul_mem W c (hxW q hq)

/-- Projected-left variant of `mlProj_mul_mem_span_productBasis`.  This is the
version needed for touched rows: the touched local factor is first reduced to
its row-window multilinear normal form, while the untouched background remains
explicit and unlocalized. -/
theorem mlProj_mul_mem_span_productBasis_of_leftProjected {N : ℕ}
    (A B : Finset (MvPolynomial (Fin N) ℚ))
    {p q : MvPolynomial (Fin N) ℚ}
    (hp : MultilinearSPDP.mlProj p ∈
      Submodule.span ℚ (↑A : Set (MvPolynomial (Fin N) ℚ)))
    (hq : q ∈ Submodule.span ℚ (↑B : Set (MvPolynomial (Fin N) ℚ))) :
    MultilinearSPDP.mlProj (p * q) ∈
      Submodule.span ℚ (↑(mlProjProductBasis A B) : Set (MvPolynomial (Fin N) ℚ)) := by
  rw [← mlProj_mul_left_mlProj p q]
  exact mlProj_mul_mem_span_productBasis A B hp hq

/-- Both-projected variant: the final product row only depends on the
multilinear normal forms of each factor. -/
theorem mlProj_mul_mem_span_productBasis_of_bothProjected {N : ℕ}
    (A B : Finset (MvPolynomial (Fin N) ℚ))
    {p q : MvPolynomial (Fin N) ℚ}
    (hp : MultilinearSPDP.mlProj p ∈
      Submodule.span ℚ (↑A : Set (MvPolynomial (Fin N) ℚ)))
    (hq : MultilinearSPDP.mlProj q ∈
      Submodule.span ℚ (↑B : Set (MvPolynomial (Fin N) ℚ))) :
    MultilinearSPDP.mlProj (p * q) ∈
      Submodule.span ℚ (↑(mlProjProductBasis A B) : Set (MvPolynomial (Fin N) ℚ)) := by
  rw [← mlProj_mul_right_mlProj p q]
  exact mlProj_mul_mem_span_productBasis_of_leftProjected A B hp hq

/-- Abstract untouched-background finite profile data for a fixed row.

`B` is not arbitrary: in the final proof it must be supplied by the paper §9.3
local-monoid/profile normal-form construction for the explicit
`untouchedBackgroundProduct`.  This record only states the exact algebraic
output that the product-composition theorem consumes. -/
def UntouchedBackgroundProfileSpanData
    (N : ℕ) (background : MvPolynomial (Fin N) ℚ) : Prop :=
  ∃ B : Finset (MvPolynomial (Fin N) ℚ),
    background ∈ Submodule.span ℚ (↑B : Set (MvPolynomial (Fin N) ℚ))

/-- Combining a touched-local basis with an untouched-background profile basis
spans the exact monomial split row. -/
theorem touchedMonomialSplitRow_mem_productBasis_of_localAndBackgroundSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S.toList → alloc i = [])
    (A B : Finset (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))
    (hA : MultilinearSPDP.mlProj (touchedShiftMonomial T *
        touchedAllocatedProductOnly M n hn2 htb hns S.toList alloc) ∈
      Submodule.span ℚ (↑A : Set (MvPolynomial
        (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)))
    (hB : untouchedBackgroundProduct M n hn2 htb hns S.toList ∈
      Submodule.span ℚ (↑B : Set (MvPolynomial
        (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))) :
    touchedMonomialSplitRow M n hn2 htb hns S.toList T alloc ∈
      Submodule.span ℚ
        (↑(mlProjProductBasis A B) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  classical
  rw [touchedMonomialSplitRow_eq_mlProj_local_mul_background
    M n hn2 htb hns S.toList T alloc hout]
  exact mlProj_mul_mem_span_productBasis_of_leftProjected A B hA hB

/-- Count bound for the concrete row-window/background product basis at paper
scale, for touched rows of length at most `log n`. -/
theorem rowWindowProductBasis_card_le_pow_add_budget
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hS : S.card ≤ Nat.log 2 n)
    (B : Finset (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))
    {C : ℕ} (hB : B.card ≤ n ^ C) :
    (mlProjProductBasis
      (MlProjFar.mlMonomialBasis
        (cookLevinRowLocalWindow M n hn2 htb hns S.toList)) B).card ≤
      n ^ (200 + C) := by
  have hA :
      (MlProjFar.mlMonomialBasis
        (cookLevinRowLocalWindow M n hn2 htb hns S.toList)).card ≤ n ^ 200 :=
    touchedRowWindowMonomialBasis_card_le_n_pow_200 M n hn hn2 htb hns S hS
  exact mlProjProductBasis_card_le_pow_add_budget
    (N := (cookLevinTableau M n hn2 htb hns).numVars) (n := n) (C := C)
    (MlProjFar.mlMonomialBasis
      (cookLevinRowLocalWindow M n hn2 htb hns S.toList)) B hA hB

/-- Concrete seam when the untouched background is supplied by a projected
normal-form span.  This is the shape needed by the profile/monoid compression:
it is enough to span `mlProj background`, because the outer product row may
project each factor before the final multilinear projection. -/
theorem touchedMonomialSplitRow_mem_rowWindowProductBasis_of_projectedBackgroundSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S)
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S.toList → alloc i = [])
    (B : Finset (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))
    (hB : MultilinearSPDP.mlProj
        (untouchedBackgroundProduct M n hn2 htb hns S.toList) ∈
      Submodule.span ℚ (↑B : Set (MvPolynomial
        (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))) :
    touchedMonomialSplitRow M n hn2 htb hns S.toList T alloc ∈
      Submodule.span ℚ
        (↑(mlProjProductBasis
          (MlProjFar.mlMonomialBasis
            (cookLevinRowLocalWindow M n hn2 htb hns S.toList)) B) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  rw [touchedMonomialSplitRow_eq_mlProj_local_mul_background
    M n hn2 htb hns S.toList T alloc hout]
  exact mlProj_mul_mem_span_productBasis_of_bothProjected
    (MlProjFar.mlMonomialBasis
      (cookLevinRowLocalWindow M n hn2 htb hns S.toList)) B
    (mlProj_touchedMonomialLocalPart_mem_rowWindowMonomialSpan
      M n hn2 htb hns S T alloc hT)
    hB

/-- Concrete touched-local/product-composition seam: the exact split row is
spanned by pairwise products of the row-window monomial basis and any supplied
paper-faithful untouched-background profile basis. -/
theorem touchedMonomialSplitRow_mem_rowWindowProductBasis_of_backgroundSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S)
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S.toList → alloc i = [])
    (B : Finset (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))
    (hB : untouchedBackgroundProduct M n hn2 htb hns S.toList ∈
      Submodule.span ℚ (↑B : Set (MvPolynomial
        (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))) :
    touchedMonomialSplitRow M n hn2 htb hns S.toList T alloc ∈
      Submodule.span ℚ
        (↑(mlProjProductBasis
          (MlProjFar.mlMonomialBasis
            (cookLevinRowLocalWindow M n hn2 htb hns S.toList)) B) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  exact touchedMonomialSplitRow_mem_productBasis_of_localAndBackgroundSpan
    M n hn2 htb hns S T alloc hout
    (MlProjFar.mlMonomialBasis
      (cookLevinRowLocalWindow M n hn2 htb hns S.toList)) B
    (mlProj_touchedMonomialLocalPart_mem_rowWindowMonomialSpan
      M n hn2 htb hns S T alloc hT)
    hB

/-! ## Axiom audit anchors -/

#print axioms mlProjProductBasis_card_le
#print axioms mlProjProductBasis_card_le_mul_budget
#print axioms mlProjProductBasis_card_le_pow_add_budget
#print axioms rowWindowProductBasis_card_le_pow_add_budget
#print axioms mlProj_mul_left_mlProj
#print axioms mlProj_mul_right_mlProj
#print axioms mlProj_mul_mem_span_productBasis
#print axioms mlProj_mul_mem_span_productBasis_of_leftProjected
#print axioms mlProj_mul_mem_span_productBasis_of_bothProjected
#print axioms touchedMonomialSplitRow_mem_productBasis_of_localAndBackgroundSpan
#print axioms touchedMonomialSplitRow_mem_rowWindowProductBasis_of_projectedBackgroundSpan
#print axioms touchedMonomialSplitRow_mem_rowWindowProductBasis_of_backgroundSpan

end PallLean.Paper93.DeepMath.PathB
