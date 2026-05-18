import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedCookLevinAssemblyReduction

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

private theorem zeroProfileBooleanExponent_single_two_add_eq_single_one_add
    {n : Nat} (i : Fin n) (α : Fin n →₀ Nat) :
    zeroProfileBooleanExponent (Finsupp.single i 2 + α) =
      zeroProfileBooleanExponent (Finsupp.single i 1 + α) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [zeroProfileBooleanExponent_apply]
  · by_cases hα : α j = 0
    · have hs2 : j ∉ (Finsupp.single i 2 + α).support := by
        simp [Finsupp.mem_support_iff, Finsupp.single_eq_of_ne hji, hα]
      have hs1 : j ∉ (Finsupp.single i 1 + α).support := by
        simp [Finsupp.mem_support_iff, Finsupp.single_eq_of_ne hji, hα]
      simp [zeroProfileBooleanExponent_apply, hs2, hs1]
    · have hs2 : j ∈ (Finsupp.single i 2 + α).support := by
        simp [Finsupp.mem_support_iff, Finsupp.single_eq_of_ne hji, hα]
      have hs1 : j ∈ (Finsupp.single i 1 + α).support := by
        simp [Finsupp.mem_support_iff, Finsupp.single_eq_of_ne hji, hα]
      simp [zeroProfileBooleanExponent_apply, hs2, hs1]

private theorem zeroProfileBooleanNormalize_square_residual_mul_monomial
    {n : Nat} (i : Fin n) (α : Fin n →₀ Nat) (c : ℚ) :
    zeroProfileBooleanNormalize
      (((X i * X i - X i : MvPolynomial (Fin n) ℚ) * monomial α c)) = 0 := by
  rw [sub_mul, zeroProfileBooleanNormalize_sub]
  change zeroProfileBooleanNormalize
      ((monomial (Finsupp.single i 1) (1 : ℚ) *
          monomial (Finsupp.single i 1) (1 : ℚ)) * monomial α c) -
    zeroProfileBooleanNormalize
      (monomial (Finsupp.single i 1) (1 : ℚ) * monomial α c) = 0
  rw [monomial_mul, monomial_mul, monomial_mul]
  rw [zeroProfileBooleanNormalize_monomial, zeroProfileBooleanNormalize_monomial]
  have htwo : (Finsupp.single i 1 + Finsupp.single i 1 : Fin n →₀ Nat) =
      Finsupp.single i 2 := by
    ext j
    by_cases hji : j = i
    · subst j; simp
    · simp [Finsupp.single_eq_of_ne hji]
  have hsum : ((Finsupp.single i 1 + Finsupp.single i 1) + α : Fin n →₀ Nat) =
      Finsupp.single i 2 + α := by
    rw [htwo]
  rw [hsum]
  rw [zeroProfileBooleanExponent_single_two_add_eq_single_one_add]
  simp

theorem zeroProfileBooleanExponent_add_left_normalized
    {n : Nat} (α β : Fin n →₀ Nat) :
    zeroProfileBooleanExponent (zeroProfileBooleanExponent α + β) =
      zeroProfileBooleanExponent (α + β) := by
  ext i
  by_cases hα : α i = 0
  · by_cases hβ : β i = 0
    · have hleft : i ∉ (zeroProfileBooleanExponent α + β).support := by
        simp [Finsupp.mem_support_iff, zeroProfileBooleanExponent_apply, hα, hβ]
      have hright : i ∉ (α + β).support := by
        simp [Finsupp.mem_support_iff, hα, hβ]
      simp [zeroProfileBooleanExponent_apply, hleft, hright]
    · have hleft : i ∈ (zeroProfileBooleanExponent α + β).support := by
        simp [Finsupp.mem_support_iff, zeroProfileBooleanExponent_apply, hα, hβ]
      have hright : i ∈ (α + β).support := by
        simp [Finsupp.mem_support_iff, hα, hβ]
      simp [zeroProfileBooleanExponent_apply, hleft, hright]
  · have hleft : i ∈ (zeroProfileBooleanExponent α + β).support := by
      simp [Finsupp.mem_support_iff, zeroProfileBooleanExponent_apply, hα]
    have hright : i ∈ (α + β).support := by
      simp [Finsupp.mem_support_iff, hα]
    simp [zeroProfileBooleanExponent_apply, hleft, hright]

theorem zeroProfileBooleanNormalize_normalized_monomial_mul_monomial
    {n : Nat} (α β : Fin n →₀ Nat) (c d : ℚ) :
    zeroProfileBooleanNormalize
      ((zeroProfileBooleanNormalize (monomial α c)) * monomial β d) =
    zeroProfileBooleanNormalize ((monomial α c : MvPolynomial (Fin n) ℚ) * monomial β d) := by
  rw [zeroProfileBooleanNormalize_monomial]
  rw [monomial_mul, monomial_mul]
  rw [zeroProfileBooleanNormalize_monomial, zeroProfileBooleanNormalize_monomial]
  rw [zeroProfileBooleanExponent_add_left_normalized]

/-- Multiples of the Boolean square residual vanish under Boolean normalization.
This is the key quotient-algebra fact needed to peel Booleanity factors off the
Cook--Levin product: `(Xᵢ²-Xᵢ) q` is zero in the Boolean quotient. -/
theorem zeroProfileBooleanNormalize_square_residual_mul
    {n : Nat} (i : Fin n) (q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize
      (((X i * X i - X i : MvPolynomial (Fin n) ℚ) * q)) = 0 := by
  classical
  rw [show q = q.support.sum (fun α => monomial α (coeff α q)) from MvPolynomial.as_sum q]
  rw [Finset.mul_sum]
  change zeroProfileBooleanNormalizeLinearMap
      (∑ x ∈ q.support, (X i * X i - X i) * monomial x (coeff x q)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro α hα
  exact zeroProfileBooleanNormalize_square_residual_mul_monomial i α (coeff α q)

/-- Left-multiplication by one Booleanity factor is invisible after Boolean
normalization. -/
theorem zeroProfileBooleanNormalize_boolFactor_mul
    {n : Nat} (i : Fin n) (q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize (SymmetricPower.boolFactor n i * q) =
      zeroProfileBooleanNormalize q := by
  unfold SymmetricPower.boolFactor
  rw [show
      ((1 : MvPolynomial (Fin n) ℚ) - X i * (1 - X i)) =
        1 + (X i * X i - X i) by ring]
  rw [add_mul, zeroProfileBooleanNormalize_add]
  rw [one_mul, zeroProfileBooleanNormalize_square_residual_mul]
  simp

/-- Any list product of Booleanity factors is invisible after Boolean
normalization. -/
theorem zeroProfileBooleanNormalize_boolFactor_listProd_mul
    {n : Nat} (L : List (Fin n)) (q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize (((L.map (SymmetricPower.boolFactor n)).prod) * q) =
      zeroProfileBooleanNormalize q := by
  induction L generalizing q with
  | nil => simp
  | cons v rest ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [mul_assoc]
      rw [zeroProfileBooleanNormalize_boolFactor_mul]
      exact ih q

/-- Any list product of exposed Cook--Levin Booleanity factors is invisible after
Boolean normalization. -/
theorem zeroProfileBooleanNormalize_cookLevinBooleanFactor_listProd_mul
    {n : Nat} (L : List (Fin n)) (q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize (((L.map (cookLevinBooleanFactor n)).prod) * q) =
      zeroProfileBooleanNormalize q := by
  simpa [cookLevinBooleanFactor, SymmetricPower.boolFactor]
    using zeroProfileBooleanNormalize_boolFactor_listProd_mul (n := n) L q

/-- Any finite product of exposed Cook--Levin Booleanity factors is invisible
after Boolean normalization. -/
theorem zeroProfileBooleanNormalize_cookLevinBooleanFactor_finsetProd_mul
    {n : Nat} (s : Finset (Fin n)) (q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize ((s.prod (cookLevinBooleanFactor n)) * q) =
      zeroProfileBooleanNormalize q := by
  classical
  induction s using Finset.induction_on generalizing q with
  | empty => simp
  | insert v s hvs ih =>
      rw [Finset.prod_insert hvs]
      rw [mul_assoc]
      rw [show cookLevinBooleanFactor n v = SymmetricPower.boolFactor n v by
        simp [cookLevinBooleanFactor, SymmetricPower.boolFactor]]
      rw [zeroProfileBooleanNormalize_boolFactor_mul]
      exact ih q

/-- The exposed Cook--Levin Booleanity product is invisible after Boolean
normalization. -/
theorem zeroProfileBooleanNormalize_cookLevinBooleanFactorProd_mul
    (n : Nat) (q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize (cookLevinBooleanFactorProd n * q) =
      zeroProfileBooleanNormalize q := by
  rw [cookLevinBooleanFactorProd_eq_finRange]
  exact zeroProfileBooleanNormalize_cookLevinBooleanFactor_listProd_mul
    (List.finRange n) q

/-- Boolean normalization erases the untouched Booleanity factors left after a
nodup derivative of the Booleanity product.  This is the exact quotient-level
slice used by the factored Cook--Levin Leibniz assembly. -/
theorem zeroProfileBooleanNormalize_iterDerivList_cookLevinBooleanFactorProd_mul
    (n : Nat) (S : List (Fin n)) (hS : S.Nodup)
    (q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize (iterDerivList S (cookLevinBooleanFactorProd n) * q) =
      zeroProfileBooleanNormalize
        (((S.map (fun v => MvPolynomial.pderiv v (cookLevinBooleanFactor n v))).prod) * q) := by
  rw [iterDerivList_cookLevinBooleanFactorProd n S hS]
  let head := (S.map (fun v => MvPolynomial.pderiv v (cookLevinBooleanFactor n v))).prod
  let tail := ((Finset.univ : Finset (Fin n)) \ S.toFinset).prod
      (cookLevinBooleanFactor n)
  change zeroProfileBooleanNormalize ((head * tail) * q) =
    zeroProfileBooleanNormalize (head * q)
  have hcomm : (head * tail) * q = tail * (head * q) := by ring
  rw [hcomm]
  exact zeroProfileBooleanNormalize_cookLevinBooleanFactor_finsetProd_mul
    ((Finset.univ : Finset (Fin n)) \ S.toFinset) (head * q)

/-- Special case: the whole exposed Booleanity product normalizes to `1`. -/
theorem zeroProfileBooleanNormalize_cookLevinBooleanFactorProd
    (n : Nat) :
    zeroProfileBooleanNormalize (cookLevinBooleanFactorProd n) =
      (1 : MvPolynomial (Fin n) ℚ) := by
  simpa using zeroProfileBooleanNormalize_cookLevinBooleanFactorProd_mul n
    (1 : MvPolynomial (Fin n) ℚ)

/-! ## Axiom audit anchors -/
#print axioms zeroProfileBooleanExponent_add_left_normalized
#print axioms zeroProfileBooleanNormalize_normalized_monomial_mul_monomial
#print axioms zeroProfileBooleanNormalize_square_residual_mul
#print axioms zeroProfileBooleanNormalize_boolFactor_mul
#print axioms zeroProfileBooleanNormalize_boolFactor_listProd_mul
#print axioms zeroProfileBooleanNormalize_cookLevinBooleanFactor_listProd_mul
#print axioms zeroProfileBooleanNormalize_cookLevinBooleanFactor_finsetProd_mul
#print axioms zeroProfileBooleanNormalize_cookLevinBooleanFactorProd_mul
#print axioms zeroProfileBooleanNormalize_iterDerivList_cookLevinBooleanFactorProd_mul
#print axioms zeroProfileBooleanNormalize_cookLevinBooleanFactorProd

end PallLean.Paper93.DeepMath.PathC
