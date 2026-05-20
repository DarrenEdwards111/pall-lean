import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedCookLevinAssemblyReduction

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
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

/-- Monomial-left version of quotient product stability. -/
theorem zeroProfileBooleanNormalize_normalized_monomial_mul
    {n : Nat} (α : Fin n →₀ Nat) (c : ℚ) (q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize
      ((zeroProfileBooleanNormalize (monomial α c)) * q) =
    zeroProfileBooleanNormalize ((monomial α c : MvPolynomial (Fin n) ℚ) * q) := by
  classical
  rw [show q = q.support.sum (fun β => monomial β (coeff β q)) from MvPolynomial.as_sum q]
  rw [Finset.mul_sum, Finset.mul_sum]
  change zeroProfileBooleanNormalizeLinearMap
      (∑ β ∈ q.support, zeroProfileBooleanNormalize (monomial α c) * monomial β (coeff β q)) =
    zeroProfileBooleanNormalizeLinearMap
      (∑ β ∈ q.support, (monomial α c : MvPolynomial (Fin n) ℚ) * monomial β (coeff β q))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  exact zeroProfileBooleanNormalize_normalized_monomial_mul_monomial α β c (coeff β q)

/-- Boolean normalization of the left factor is invisible under a final Boolean
normalization after multiplication.  This is the quotient-algebra associativity
fact used to move between raw products and normalized representatives. -/
theorem zeroProfileBooleanNormalize_left_normalized_mul
    {n : Nat} (p q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize (zeroProfileBooleanNormalize p * q) =
      zeroProfileBooleanNormalize (p * q) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
      exact zeroProfileBooleanNormalize_normalized_monomial_mul α c q
  | add p r hp hr =>
      rw [zeroProfileBooleanNormalize_add]
      rw [add_mul, add_mul]
      rw [zeroProfileBooleanNormalize_add, zeroProfileBooleanNormalize_add]
      rw [hp, hr]

/-- Boolean normalization of the right factor is invisible under a final Boolean
normalization after multiplication. -/
theorem zeroProfileBooleanNormalize_mul_right_normalized
    {n : Nat} (p q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize (p * zeroProfileBooleanNormalize q) =
      zeroProfileBooleanNormalize (p * q) := by
  rw [mul_comm p (zeroProfileBooleanNormalize q), mul_comm p q]
  exact zeroProfileBooleanNormalize_left_normalized_mul q p

/-- Full quotient-algebra product law: normalizing both factors before
multiplication does not change the final Boolean normal form. -/
theorem zeroProfileBooleanNormalize_mul_normalized
    {n : Nat} (p q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize (zeroProfileBooleanNormalize p * zeroProfileBooleanNormalize q) =
      zeroProfileBooleanNormalize (p * q) := by
  rw [zeroProfileBooleanNormalize_left_normalized_mul p (zeroProfileBooleanNormalize q)]
  rw [zeroProfileBooleanNormalize_mul_right_normalized p q]

/-- Boolean normalization commutes with replacing every factor in a finite list
by its Boolean normal representative, up to the final normal form.  This is the
finite quotient-product law needed when product assembly first normalizes local
factors and only then multiplies them. -/
theorem zeroProfileBooleanNormalize_list_prod_map_normalized
    {n : Nat} (L : List (MvPolynomial (Fin n) ℚ)) :
    zeroProfileBooleanNormalize ((L.map zeroProfileBooleanNormalize).prod) =
      zeroProfileBooleanNormalize L.prod := by
  induction L with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.prod_cons]
      calc
        zeroProfileBooleanNormalize (zeroProfileBooleanNormalize p * (ps.map zeroProfileBooleanNormalize).prod)
            = zeroProfileBooleanNormalize (p * (ps.map zeroProfileBooleanNormalize).prod) := by
              rw [zeroProfileBooleanNormalize_left_normalized_mul]
        _ = zeroProfileBooleanNormalize (p * zeroProfileBooleanNormalize ((ps.map zeroProfileBooleanNormalize).prod)) := by
              rw [zeroProfileBooleanNormalize_mul_right_normalized]
        _ = zeroProfileBooleanNormalize (p * zeroProfileBooleanNormalize ps.prod) := by
              rw [ih]
        _ = zeroProfileBooleanNormalize (p * ps.prod) := by
              rw [zeroProfileBooleanNormalize_mul_right_normalized]

/-- Finset form of the finite quotient-product law. -/
theorem zeroProfileBooleanNormalize_finset_prod_normalized
    {n : Nat} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize (s.prod (fun i => zeroProfileBooleanNormalize (p i))) =
      zeroProfileBooleanNormalize (s.prod p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.prod_insert has]
      calc
        zeroProfileBooleanNormalize (zeroProfileBooleanNormalize (p a) *
            s.prod (fun i => zeroProfileBooleanNormalize (p i)))
            = zeroProfileBooleanNormalize (p a *
                s.prod (fun i => zeroProfileBooleanNormalize (p i))) := by
              rw [zeroProfileBooleanNormalize_left_normalized_mul]
        _ = zeroProfileBooleanNormalize (p a *
                zeroProfileBooleanNormalize (s.prod (fun i => zeroProfileBooleanNormalize (p i)))) := by
              rw [zeroProfileBooleanNormalize_mul_right_normalized]
        _ = zeroProfileBooleanNormalize (p a * zeroProfileBooleanNormalize (s.prod p)) := by
              rw [ih]
        _ = zeroProfileBooleanNormalize (p a * s.prod p) := by
              rw [zeroProfileBooleanNormalize_mul_right_normalized]


/-! ## Normalization-aware derivative algebra -/

/-- For multilinear polynomials, ordinary derivative commutes with Boolean
normalization.  This is the precise positive form of the derivative-commutation
principle: the obstruction only appears once repeated exponents are present. -/
theorem zeroProfileBooleanNormalize_pderiv_of_isMultilinear
    {n : Nat} (p : MvPolynomial (Fin n) ℚ)
    (hp : IsMultilinear p) (i : Fin n) :
    MvPolynomial.pderiv i (zeroProfileBooleanNormalize p) =
      zeroProfileBooleanNormalize (MvPolynomial.pderiv i p) := by
  rw [zeroProfileBooleanNormalize_of_support_isMultilinear p hp]
  rw [zeroProfileBooleanNormalize_of_support_isMultilinear
    (MvPolynomial.pderiv i p) (isMultilinear_pderiv p hp i)]

/-- For multilinear polynomials, any iterated derivative commutes with Boolean
normalization.  This gives an actual algebraic discharge of the normalized-row
commutation step on the multilinear slice. -/
theorem zeroProfileBooleanNormalize_iterDerivList_of_isMultilinear
    {n : Nat} (S : List (Fin n)) (p : MvPolynomial (Fin n) ℚ)
    (hp : IsMultilinear p) :
    iterDerivList S (zeroProfileBooleanNormalize p) =
      zeroProfileBooleanNormalize (iterDerivList S p) := by
  rw [zeroProfileBooleanNormalize_of_support_isMultilinear p hp]
  rw [zeroProfileBooleanNormalize_of_support_isMultilinear
    (iterDerivList S p) (isMultilinear_iterDerivList S p hp)]

/-- Formal differentiation after Boolean normalization of a monomial.  The
coefficient records only whether the variable occurs in the original support,
because Boolean normalization first collapses every positive exponent to `1`.
This is the local algebra behind the corrected product synthesis: differentiated
Boolean representatives use support-incidence coefficients, not raw
multiplicities. -/
theorem pderiv_zeroProfileBooleanNormalize_monomial
    {n : Nat} (i : Fin n) (α : Fin n →₀ Nat) (c : ℚ) :
    MvPolynomial.pderiv i (zeroProfileBooleanNormalize (MvPolynomial.monomial α c)) =
      MvPolynomial.monomial (zeroProfileBooleanExponent α - Finsupp.single i 1)
        (c * zeroProfileBooleanExponent α i) := by
  simp [MvPolynomial.pderiv_monomial]

/-- Boolean normalization after ordinary formal differentiation of a monomial.
Compared with `pderiv_zeroProfileBooleanNormalize_monomial`, this retains the
raw multiplicity `α i`.  The mismatch between these two coefficients is exactly
why the old commutation target
`∂(booleanNormalize p) = booleanNormalize(∂p)` is false for repeated variables
(e.g. `p = Xᵢ²`). -/
theorem zeroProfileBooleanNormalize_pderiv_monomial
    {n : Nat} (i : Fin n) (α : Fin n →₀ Nat) (c : ℚ) :
    zeroProfileBooleanNormalize (MvPolynomial.pderiv i (MvPolynomial.monomial α c)) =
      MvPolynomial.monomial (zeroProfileBooleanExponent (α - Finsupp.single i 1))
        (c * α i) := by
  simp [MvPolynomial.pderiv_monomial]

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
#print axioms zeroProfileBooleanNormalize_normalized_monomial_mul
#print axioms zeroProfileBooleanNormalize_left_normalized_mul
#print axioms zeroProfileBooleanNormalize_mul_right_normalized
#print axioms zeroProfileBooleanNormalize_mul_normalized
#print axioms zeroProfileBooleanNormalize_list_prod_map_normalized
#print axioms zeroProfileBooleanNormalize_finset_prod_normalized
#print axioms zeroProfileBooleanNormalize_pderiv_of_isMultilinear
#print axioms zeroProfileBooleanNormalize_iterDerivList_of_isMultilinear
#print axioms pderiv_zeroProfileBooleanNormalize_monomial
#print axioms zeroProfileBooleanNormalize_pderiv_monomial
#print axioms zeroProfileBooleanNormalize_square_residual_mul
#print axioms zeroProfileBooleanNormalize_boolFactor_mul
#print axioms zeroProfileBooleanNormalize_boolFactor_listProd_mul
#print axioms zeroProfileBooleanNormalize_cookLevinBooleanFactor_listProd_mul
#print axioms zeroProfileBooleanNormalize_cookLevinBooleanFactor_finsetProd_mul
#print axioms zeroProfileBooleanNormalize_cookLevinBooleanFactorProd_mul
#print axioms zeroProfileBooleanNormalize_iterDerivList_cookLevinBooleanFactorProd_mul
#print axioms zeroProfileBooleanNormalize_cookLevinBooleanFactorProd

end PallLean.Paper93.DeepMath.PathC
