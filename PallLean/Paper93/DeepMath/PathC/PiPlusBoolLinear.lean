import PallLean.Paper93.DeepMath.PathC.PiPlusBoolOps

/-!
# Linear maps in the Boolean paper ambient

Layer 2b of the Boolean-ambient refactor.  `BoolPoly` is already a normal-form
commutative ring; here we add the explicit `ℚ`-module structure and package the
canonical lift, `mlProjBool`, and Boolean-ambient `Pi+` as linear maps.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

namespace BoolPoly

/-- Scalar multiplication in the Boolean ambient: multiply by the scalar
constant and normalize. -/
noncomputable def smul {n : ℕ} (a : ℚ) (p : BoolPoly n) : BoolPoly n :=
  liftToBool ((MvPolynomial.C a : MvPolynomial (Fin n) ℚ) *
    (p : MvPolynomial (Fin n) ℚ))

noncomputable instance {n : ℕ} : SMul ℚ (BoolPoly n) := ⟨smul⟩

@[simp] theorem coe_smul {n : ℕ} (a : ℚ) (p : BoolPoly n) :
    ((a • p : BoolPoly n) : MvPolynomial (Fin n) ℚ) =
      (MvPolynomial.C a : MvPolynomial (Fin n) ℚ) *
        (p : MvPolynomial (Fin n) ℚ) := by
  change zeroProfileBooleanNormalize
      ((MvPolynomial.C a : MvPolynomial (Fin n) ℚ) *
        (p : MvPolynomial (Fin n) ℚ)) =
    (MvPolynomial.C a : MvPolynomial (Fin n) ℚ) *
      (p : MvPolynomial (Fin n) ℚ)
  rw [MvPolynomial.C_mul']
  calc
    zeroProfileBooleanNormalize (a • (p : MvPolynomial (Fin n) ℚ)) =
        a • zeroProfileBooleanNormalize (p : MvPolynomial (Fin n) ℚ) := by
          exact map_smul zeroProfileBooleanNormalizeLinearMap a
            (p : MvPolynomial (Fin n) ℚ)
    _ = a • (p : MvPolynomial (Fin n) ℚ) := by
          rw [p.normal]

@[simp] theorem one_smul_bool {n : ℕ} (p : BoolPoly n) :
    (1 : ℚ) • p = p := by
  apply BoolPoly.ext
  rw [coe_smul]
  simp

@[simp] theorem zero_smul_bool {n : ℕ} (p : BoolPoly n) :
    (0 : ℚ) • p = 0 := by
  apply BoolPoly.ext
  rw [coe_smul]
  simp

@[simp] theorem smul_zero_bool {n : ℕ} (a : ℚ) :
    a • (0 : BoolPoly n) = 0 := by
  apply BoolPoly.ext
  rw [coe_smul]
  simp

theorem mul_smul_bool {n : ℕ} (a b : ℚ) (p : BoolPoly n) :
    (a * b) • p = a • (b • p) := by
  apply BoolPoly.ext
  rw [coe_smul, coe_smul, coe_smul]
  simp [mul_assoc]

theorem smul_add_bool {n : ℕ} (a : ℚ) (p q : BoolPoly n) :
    a • (p + q) = a • p + a • q := by
  apply BoolPoly.ext
  rw [coe_smul, coe_add, coe_add, coe_smul, coe_smul]
  rw [mul_add]

theorem add_smul_bool {n : ℕ} (a b : ℚ) (p : BoolPoly n) :
    (a + b) • p = a • p + b • p := by
  apply BoolPoly.ext
  rw [coe_smul, coe_add, coe_smul, coe_smul]
  rw [MvPolynomial.C_add, add_mul]

noncomputable instance {n : ℕ} : Module ℚ (BoolPoly n) where
  one_smul := one_smul_bool
  mul_smul := mul_smul_bool
  smul_zero := smul_zero_bool
  smul_add := smul_add_bool
  add_smul := add_smul_bool
  zero_smul := zero_smul_bool

/-- Canonical Boolean-normal quotient map as a linear map. -/
noncomputable def liftToBoolLinearMap (n : ℕ) :
    MvPolynomial (Fin n) ℚ →ₗ[ℚ] BoolPoly n where
  toFun := liftToBool
  map_add' p q := by
    apply BoolPoly.ext
    change zeroProfileBooleanNormalize (p + q) =
      ((liftToBool p + liftToBool q : BoolPoly n) : MvPolynomial (Fin n) ℚ)
    rw [coe_add, zeroProfileBooleanNormalize_add]
    rfl
  map_smul' a p := by
    apply BoolPoly.ext
    change zeroProfileBooleanNormalize (a • p) =
      ((a • liftToBool p : BoolPoly n) : MvPolynomial (Fin n) ℚ)
    rw [coe_smul]
    rw [MvPolynomial.C_mul']
    exact map_smul zeroProfileBooleanNormalizeLinearMap a p

@[simp] theorem liftToBoolLinearMap_apply {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    liftToBoolLinearMap n p = liftToBool p := rfl

/-- Paper-faithful `mlProjBool` as a linear map.  This is intentionally the
Boolean quotient-normalization map, not the legacy full-ring `mlProj`. -/
noncomputable def mlProjBoolLinearMap (n : ℕ) :
    MvPolynomial (Fin n) ℚ →ₗ[ℚ] BoolPoly n :=
  liftToBoolLinearMap n

@[simp] theorem mlProjBoolLinearMap_apply {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    mlProjBoolLinearMap n p = mlProjBool p := rfl

/-- Legacy bridge: old full-ring `mlProj`, followed by Boolean-normal ambient
entry, packaged as a linear map. -/
noncomputable def legacyMlProjBoolLinearMap (n : ℕ) :
    MvPolynomial (Fin n) ℚ →ₗ[ℚ] BoolPoly n :=
  (liftToBoolLinearMap n).comp (mlProjLinearMap (Fin n) ℚ)

@[simp] theorem legacyMlProjBoolLinearMap_apply {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    legacyMlProjBoolLinearMap n p = legacyMlProjBool p := rfl

/-- Boolean-ambient `Pi+` as a linear map induced by an existing full-ring SAT
gauge. -/
noncomputable def piPlusBoolLinearMap
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) :
    BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars →ₗ[ℚ]
      BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars where
  toFun := piPlusBool piP
  map_add' p q := by
    apply BoolPoly.ext
    change zeroProfileBooleanNormalize (piP.gauge
        ((p + q : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars) :
          MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)) =
      ((piPlusBool piP p + piPlusBool piP q :
        BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars) :
          MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    rw [coe_add, coe_add, map_add, zeroProfileBooleanNormalize_add]
    rfl
  map_smul' a p := by
    apply BoolPoly.ext
    change zeroProfileBooleanNormalize (piP.gauge
        ((a • p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars) :
          MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)) =
      ((a • piPlusBool piP p :
        BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars) :
          MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    rw [coe_smul, coe_smul]
    rw [MvPolynomial.C_mul']
    rw [map_smul]
    rw [MvPolynomial.C_mul']
    exact map_smul zeroProfileBooleanNormalizeLinearMap a
      (piP.gauge (p : MvPolynomial
        (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))

@[simp] theorem piPlusBoolLinearMap_apply
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars) :
    piPlusBoolLinearMap piP p = piPlusBool piP p := rfl

/-! ## Axiom audit anchors -/

#print axioms coe_smul
#print axioms liftToBoolLinearMap
#print axioms legacyMlProjBoolLinearMap
#print axioms piPlusBoolLinearMap
#print axioms piPlusBoolLinearMap_apply

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
