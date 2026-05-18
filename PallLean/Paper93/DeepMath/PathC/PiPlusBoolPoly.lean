import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanAmbient

/-!
# Normal-form Boolean polynomial wrapper

Layer 1 of the paper-ambient refactor.  `BoolPoly n` is a type-level marker for
polynomials represented in Boolean normal form.  It keeps the existing
`MvPolynomial` infrastructure available through coercion, but all constructors
enter through `liftToBool`, i.e. Boolean normalization.

This is deliberately parallel to the old full-ring infrastructure: no existing
Route-C file is rewritten here.  New paper-faithful statements can now quantify
over `BoolPoly n` instead of raw `MvPolynomial (Fin n) ℚ`.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Boolean-normal polynomial representative for the paper ambient. -/
structure BoolPoly (n : ℕ) where
  poly : MvPolynomial (Fin n) ℚ
  normal : zeroProfileBooleanNormalize poly = poly

namespace BoolPoly

instance {n : ℕ} : Coe (BoolPoly n) (MvPolynomial (Fin n) ℚ) where
  coe p := p.poly

@[ext] theorem ext {n : ℕ} {p q : BoolPoly n}
    (h : (p : MvPolynomial (Fin n) ℚ) = q) : p = q := by
  cases p
  cases q
  simp at h
  subst h
  rfl

@[simp] theorem normal_coe {n : ℕ} (p : BoolPoly n) :
    zeroProfileBooleanNormalize (p : MvPolynomial (Fin n) ℚ) = p :=
  p.normal

/-- Apply Boolean normalization twice. -/
theorem normalize_idempotent_apply {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize (zeroProfileBooleanNormalize p) =
      zeroProfileBooleanNormalize p := by
  change ((zeroProfileBooleanNormalizeLinearMap (n := n)).comp
      zeroProfileBooleanNormalizeLinearMap) p =
    zeroProfileBooleanNormalizeLinearMap p
  rw [zeroProfileBooleanNormalizeLinearMap_idempotent]

/-- Canonical lift from the full polynomial ring into the Boolean-normal
paper ambient. -/
noncomputable def liftToBool {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) : BoolPoly n where
  poly := zeroProfileBooleanNormalize p
  normal := normalize_idempotent_apply p

@[simp] theorem coe_liftToBool {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    (liftToBool p : MvPolynomial (Fin n) ℚ) =
      zeroProfileBooleanNormalize p := rfl

/-- Soundness/retraction: lifting an already Boolean-normal representative is
identity. -/
@[simp] theorem liftToBool_coe {n : ℕ} (p : BoolPoly n) :
    liftToBool (p : MvPolynomial (Fin n) ℚ) = p := by
  ext
  simp [p.normal]

/-- Two raw representatives lift to the same Boolean polynomial exactly when
they are equal in the paper Boolean ambient. -/
theorem liftToBool_eq_liftToBool_iff {n : ℕ}
    (p q : MvPolynomial (Fin n) ℚ) :
    liftToBool p = liftToBool q ↔ p ≈ᵦ q := by
  constructor
  · intro h
    change zeroProfileBooleanNormalize p = zeroProfileBooleanNormalize q
    simpa using congrArg (fun r : BoolPoly n => (r : MvPolynomial (Fin n) ℚ)) h
  · intro h
    apply BoolPoly.ext
    exact h

/-- Zero in the Boolean ambient. -/
noncomputable def zero {n : ℕ} : BoolPoly n :=
  liftToBool 0

/-- One in the Boolean ambient. -/
noncomputable def one {n : ℕ} : BoolPoly n :=
  liftToBool 1

/-- Addition in the Boolean ambient. -/
noncomputable def add {n : ℕ} (p q : BoolPoly n) : BoolPoly n :=
  liftToBool ((p : MvPolynomial (Fin n) ℚ) + q)

/-- Negation in the Boolean ambient. -/
noncomputable def neg {n : ℕ} (p : BoolPoly n) : BoolPoly n :=
  liftToBool (-(p : MvPolynomial (Fin n) ℚ))

/-- Multiplication in the Boolean ambient: multiply representatives and reduce
back to Boolean normal form. -/
noncomputable def mul {n : ℕ} (p q : BoolPoly n) : BoolPoly n :=
  liftToBool ((p : MvPolynomial (Fin n) ℚ) * q)

noncomputable instance {n : ℕ} : Zero (BoolPoly n) := ⟨zero⟩
noncomputable instance {n : ℕ} : One (BoolPoly n) := ⟨one⟩
noncomputable instance {n : ℕ} : Add (BoolPoly n) := ⟨add⟩
noncomputable instance {n : ℕ} : Neg (BoolPoly n) := ⟨neg⟩
noncomputable instance {n : ℕ} : Mul (BoolPoly n) := ⟨mul⟩

@[simp] theorem coe_zero {n : ℕ} :
    ((0 : BoolPoly n) : MvPolynomial (Fin n) ℚ) = 0 := by
  change zeroProfileBooleanNormalize (0 : MvPolynomial (Fin n) ℚ) = 0
  simp

@[simp] theorem coe_one {n : ℕ} :
    ((1 : BoolPoly n) : MvPolynomial (Fin n) ℚ) = 1 := by
  change zeroProfileBooleanNormalize (1 : MvPolynomial (Fin n) ℚ) = 1
  simp

@[simp] theorem coe_add {n : ℕ} (p q : BoolPoly n) :
    ((p + q : BoolPoly n) : MvPolynomial (Fin n) ℚ) =
      (p : MvPolynomial (Fin n) ℚ) + (q : MvPolynomial (Fin n) ℚ) := by
  change zeroProfileBooleanNormalize
      ((p : MvPolynomial (Fin n) ℚ) + (q : MvPolynomial (Fin n) ℚ)) =
    (p : MvPolynomial (Fin n) ℚ) + (q : MvPolynomial (Fin n) ℚ)
  rw [zeroProfileBooleanNormalize_add, p.normal, q.normal]

@[simp] theorem coe_neg {n : ℕ} (p : BoolPoly n) :
    ((-p : BoolPoly n) : MvPolynomial (Fin n) ℚ) =
      -(p : MvPolynomial (Fin n) ℚ) := by
  change zeroProfileBooleanNormalize (-(p : MvPolynomial (Fin n) ℚ)) =
    -(p : MvPolynomial (Fin n) ℚ)
  rw [zeroProfileBooleanNormalize_neg, p.normal]

@[simp] theorem coe_mul {n : ℕ} (p q : BoolPoly n) :
    ((p * q : BoolPoly n) : MvPolynomial (Fin n) ℚ) =
      zeroProfileBooleanNormalize
        ((p : MvPolynomial (Fin n) ℚ) * (q : MvPolynomial (Fin n) ℚ)) := rfl

/-- Boolean ambient multiplication, viewed through coercion, is the same as the
`*ᵦ` operation on representatives. -/
theorem coe_mul_eq_booleanAmbientMul {n : ℕ} (p q : BoolPoly n) :
    ((p * q : BoolPoly n) : MvPolynomial (Fin n) ℚ) =
      (p : MvPolynomial (Fin n) ℚ) *ᵦ (q : MvPolynomial (Fin n) ℚ) := rfl

@[simp] theorem add_zero_bool {n : ℕ} (p : BoolPoly n) : p + 0 = p := by
  apply BoolPoly.ext
  simp

@[simp] theorem zero_add_bool {n : ℕ} (p : BoolPoly n) : 0 + p = p := by
  apply BoolPoly.ext
  simp

@[simp] theorem neg_add_cancel_bool {n : ℕ} (p : BoolPoly n) : -p + p = 0 := by
  apply BoolPoly.ext
  simp

theorem add_comm_bool {n : ℕ} (p q : BoolPoly n) : p + q = q + p := by
  apply BoolPoly.ext
  change ((p + q : BoolPoly n) : MvPolynomial (Fin n) ℚ) =
    ((q + p : BoolPoly n) : MvPolynomial (Fin n) ℚ)
  rw [coe_add, coe_add, add_comm]

theorem add_assoc_bool {n : ℕ} (p q r : BoolPoly n) :
    (p + q) + r = p + (q + r) := by
  apply BoolPoly.ext
  change (((p + q) + r : BoolPoly n) : MvPolynomial (Fin n) ℚ) =
    ((p + (q + r) : BoolPoly n) : MvPolynomial (Fin n) ℚ)
  rw [coe_add, coe_add, coe_add, coe_add, add_assoc]

@[simp] theorem one_mul_bool {n : ℕ} (p : BoolPoly n) : 1 * p = p := by
  apply BoolPoly.ext
  change zeroProfileBooleanNormalize
      (zeroProfileBooleanNormalize (1 : MvPolynomial (Fin n) ℚ) *
        (p : MvPolynomial (Fin n) ℚ)) =
    (p : MvPolynomial (Fin n) ℚ)
  rw [zeroProfileBooleanNormalize_one, one_mul, p.normal]

@[simp] theorem mul_one_bool {n : ℕ} (p : BoolPoly n) : p * 1 = p := by
  apply BoolPoly.ext
  change zeroProfileBooleanNormalize
      ((p : MvPolynomial (Fin n) ℚ) *
        zeroProfileBooleanNormalize (1 : MvPolynomial (Fin n) ℚ)) =
    (p : MvPolynomial (Fin n) ℚ)
  rw [zeroProfileBooleanNormalize_one, mul_one, p.normal]

@[simp] theorem zero_mul_bool {n : ℕ} (p : BoolPoly n) : 0 * p = 0 := by
  apply BoolPoly.ext
  change zeroProfileBooleanNormalize
      ((0 : MvPolynomial (Fin n) ℚ) * (p : MvPolynomial (Fin n) ℚ)) = 0
  rw [zero_mul]
  simp

@[simp] theorem mul_zero_bool {n : ℕ} (p : BoolPoly n) : p * 0 = 0 := by
  apply BoolPoly.ext
  change zeroProfileBooleanNormalize
      ((p : MvPolynomial (Fin n) ℚ) * (0 : MvPolynomial (Fin n) ℚ)) = 0
  rw [mul_zero]
  simp

theorem mul_comm_bool {n : ℕ} (p q : BoolPoly n) : p * q = q * p := by
  apply BoolPoly.ext
  show zeroProfileBooleanNormalize
      ((p : MvPolynomial (Fin n) ℚ) * (q : MvPolynomial (Fin n) ℚ)) =
    zeroProfileBooleanNormalize
      ((q : MvPolynomial (Fin n) ℚ) * (p : MvPolynomial (Fin n) ℚ))
  rw [mul_comm]

theorem mul_assoc_bool {n : ℕ} (p q r : BoolPoly n) :
    (p * q) * r = p * (q * r) := by
  apply BoolPoly.ext
  calc
    zeroProfileBooleanNormalize
        (zeroProfileBooleanNormalize
          ((p : MvPolynomial (Fin n) ℚ) * (q : MvPolynomial (Fin n) ℚ)) *
            (r : MvPolynomial (Fin n) ℚ)) =
        zeroProfileBooleanNormalize
          (((p : MvPolynomial (Fin n) ℚ) * (q : MvPolynomial (Fin n) ℚ)) *
            (r : MvPolynomial (Fin n) ℚ)) := by
          exact zeroProfileBooleanNormalize_left_normalized_mul
            ((p : MvPolynomial (Fin n) ℚ) * (q : MvPolynomial (Fin n) ℚ))
            (r : MvPolynomial (Fin n) ℚ)
    _ = zeroProfileBooleanNormalize
        ((p : MvPolynomial (Fin n) ℚ) *
          ((q : MvPolynomial (Fin n) ℚ) * (r : MvPolynomial (Fin n) ℚ))) := by
          rw [mul_assoc]
    _ = zeroProfileBooleanNormalize
        ((p : MvPolynomial (Fin n) ℚ) *
          zeroProfileBooleanNormalize
            ((q : MvPolynomial (Fin n) ℚ) * (r : MvPolynomial (Fin n) ℚ))) := by
          symm
          exact zeroProfileBooleanNormalize_mul_right_normalized
            (p : MvPolynomial (Fin n) ℚ)
            ((q : MvPolynomial (Fin n) ℚ) * (r : MvPolynomial (Fin n) ℚ))

theorem left_distrib_bool {n : ℕ} (p q r : BoolPoly n) :
    p * (q + r) = p * q + p * r := by
  apply BoolPoly.ext
  change ((p * (q + r) : BoolPoly n) : MvPolynomial (Fin n) ℚ) =
    ((p * q + p * r : BoolPoly n) : MvPolynomial (Fin n) ℚ)
  rw [coe_mul, coe_add, coe_add, coe_mul, coe_mul]
  rw [left_distrib, zeroProfileBooleanNormalize_add]

theorem right_distrib_bool {n : ℕ} (p q r : BoolPoly n) :
    (p + q) * r = p * r + q * r := by
  apply BoolPoly.ext
  change (((p + q) * r : BoolPoly n) : MvPolynomial (Fin n) ℚ) =
    ((p * r + q * r : BoolPoly n) : MvPolynomial (Fin n) ℚ)
  rw [coe_mul, coe_add, coe_add, coe_mul, coe_mul]
  rw [right_distrib, zeroProfileBooleanNormalize_add]

noncomputable instance {n : ℕ} : CommRing (BoolPoly n) where
  zero := 0
  one := 1
  add := (· + ·)
  neg := Neg.neg
  mul := (· * ·)
  add_assoc := add_assoc_bool
  zero_add := zero_add_bool
  add_zero := add_zero_bool
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := neg_add_cancel_bool
  add_comm := add_comm_bool
  mul_assoc := mul_assoc_bool
  one_mul := one_mul_bool
  mul_one := mul_one_bool
  left_distrib := left_distrib_bool
  right_distrib := right_distrib_bool
  zero_mul := zero_mul_bool
  mul_zero := mul_zero_bool
  mul_comm := mul_comm_bool

/-- Boolean quotient fact as a typed equality in `BoolPoly`: `Xᵢ² = Xᵢ`. -/
theorem lift_X_mul_X_eq_lift_X {n : ℕ} (i : Fin n) :
    liftToBool ((X i * X i : MvPolynomial (Fin n) ℚ)) =
      liftToBool (X i : MvPolynomial (Fin n) ℚ) := by
  rw [liftToBool_eq_liftToBool_iff]
  exact booleanAmbient_X_mul_X_eq_X i

/-- Boolean square residual vanishes as a typed Boolean polynomial. -/
theorem lift_square_residual_eq_zero {n : ℕ} (i : Fin n) :
    liftToBool ((X i * X i - X i : MvPolynomial (Fin n) ℚ)) = 0 := by
  change liftToBool ((X i * X i - X i : MvPolynomial (Fin n) ℚ)) =
    liftToBool (0 : MvPolynomial (Fin n) ℚ)
  rw [liftToBool_eq_liftToBool_iff]
  exact booleanAmbient_square_residual_eq_zero i

/-! ## Axiom audit anchors -/

#print axioms liftToBool_coe
#print axioms liftToBool_eq_liftToBool_iff
#print axioms mul_assoc_bool
#print axioms left_distrib_bool
#print axioms lift_X_mul_X_eq_lift_X
#print axioms lift_square_residual_eq_zero

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
