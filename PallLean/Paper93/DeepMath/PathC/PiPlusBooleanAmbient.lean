import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanNormalizeProductLemmas

/-!
# Boolean quotient ambient for the paper-faithful Route C refactor

The paper works in the Boolean quotient ambient

`ℚ[x₁,…,xₙ] / ⟨xᵢ² - xᵢ⟩`,

where every positive power of a variable is represented by the same multilinear
monomial.  The current codebase still uses `MvPolynomial (Fin n) ℚ` as the
carrier, so this file makes the paper ambient explicit as a normal-form layer:

* equality in the paper ambient is equality after `zeroProfileBooleanNormalize`;
* multiplication in the paper ambient is multiplication followed by Boolean
  normalization;
* square residuals vanish in this equality;
* raw representatives can still be used, but all Route-C paper statements
  should be stated through this interface rather than raw `mlProj` equality.

This is intentionally a first refactor step: it gives a small API that can be
used to migrate the remaining Pi+ / SPDP payloads without replacing every
`MvPolynomial` occurrence at once.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Paper-ambient equality: two full-ring representatives are equal iff their
Boolean normal forms agree. -/
def BooleanAmbientEq {n : ℕ}
    (p q : MvPolynomial (Fin n) ℚ) : Prop :=
  zeroProfileBooleanNormalize p = zeroProfileBooleanNormalize q

infix:50 " ≈ᵦ " => BooleanAmbientEq

/-- Canonical representative of a full-ring polynomial in the paper Boolean
ambient. -/
noncomputable abbrev booleanAmbientNormal {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) : MvPolynomial (Fin n) ℚ :=
  zeroProfileBooleanNormalize p

/-- Multiplication in the paper Boolean ambient, represented back in the full
polynomial ring by Boolean normal form. -/
noncomputable def booleanAmbientMul {n : ℕ}
    (p q : MvPolynomial (Fin n) ℚ) : MvPolynomial (Fin n) ℚ :=
  zeroProfileBooleanNormalize (p * q)

infixl:70 " *ᵦ " => booleanAmbientMul

@[simp] theorem booleanAmbientEq_refl {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) : p ≈ᵦ p := rfl

theorem booleanAmbientEq_symm {n : ℕ}
    {p q : MvPolynomial (Fin n) ℚ} (h : p ≈ᵦ q) : q ≈ᵦ p := h.symm

theorem booleanAmbientEq_trans {n : ℕ}
    {p q r : MvPolynomial (Fin n) ℚ}
    (hpq : p ≈ᵦ q) (hqr : q ≈ᵦ r) : p ≈ᵦ r := hpq.trans hqr

@[simp] theorem booleanAmbientNormal_eq_normalize {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    booleanAmbientNormal p = zeroProfileBooleanNormalize p := rfl

@[simp] theorem booleanAmbientMul_eq {n : ℕ}
    (p q : MvPolynomial (Fin n) ℚ) :
    p *ᵦ q = zeroProfileBooleanNormalize (p * q) := rfl

/-- Boolean ambient multiplication respects normal representatives on the left. -/
theorem booleanAmbientMul_left_normal {n : ℕ}
    (p q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize (zeroProfileBooleanNormalize p * q) =
      p *ᵦ q := by
  rw [booleanAmbientMul_eq]
  exact zeroProfileBooleanNormalize_left_normalized_mul p q

/-- Boolean ambient multiplication respects normal representatives on the right. -/
theorem booleanAmbientMul_right_normal {n : ℕ}
    (p q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize (p * zeroProfileBooleanNormalize q) =
      p *ᵦ q := by
  rw [booleanAmbientMul_eq]
  exact zeroProfileBooleanNormalize_mul_right_normalized p q

/-- Boolean ambient multiplication is the quotient product law: normalizing both
inputs before multiplication gives the same normal representative. -/
theorem booleanAmbientMul_normalized {n : ℕ}
    (p q : MvPolynomial (Fin n) ℚ) :
    zeroProfileBooleanNormalize
        (zeroProfileBooleanNormalize p * zeroProfileBooleanNormalize q) =
      p *ᵦ q := by
  rw [booleanAmbientMul_eq]
  exact zeroProfileBooleanNormalize_mul_normalized p q

/-- The paper ambient validates `Xᵢ² = Xᵢ`. -/
theorem booleanAmbient_X_mul_X_eq_X {n : ℕ} (i : Fin n) :
    (X i * X i : MvPolynomial (Fin n) ℚ) ≈ᵦ X i := by
  rw [BooleanAmbientEq, zeroProfileBooleanNormalize_X_mul_X,
    zeroProfileBooleanNormalize_X]

/-- The Boolean square residual is zero in the paper ambient. -/
theorem booleanAmbient_square_residual_eq_zero {n : ℕ} (i : Fin n) :
    ((X i * X i - X i : MvPolynomial (Fin n) ℚ) ≈ᵦ 0) := by
  rw [BooleanAmbientEq, zeroProfileBooleanNormalize_square_residual]
  simp

/-- Boolean ambient equality is exactly equality of canonical representatives. -/
theorem booleanAmbientEq_iff_normal_eq {n : ℕ}
    (p q : MvPolynomial (Fin n) ℚ) :
    p ≈ᵦ q ↔ booleanAmbientNormal p = booleanAmbientNormal q := Iff.rfl

/-- If two representatives are equal in the ordinary full ring, they are equal
in the Boolean ambient. -/
theorem booleanAmbientEq_of_eq {n : ℕ}
    {p q : MvPolynomial (Fin n) ℚ} (h : p = q) : p ≈ᵦ q := by
  subst h
  rfl

/-- Raw multilinear projection is not the paper quotient operation; this named
predicate marks statements that are intentionally about Boolean normal forms
rather than `mlProj`. -/
def PaperBooleanAmbientStatement {n : ℕ}
    (P : MvPolynomial (Fin n) ℚ → Prop) : Prop :=
  ∀ p, P (booleanAmbientNormal p)

/-! ## Axiom audit anchors -/

#print axioms booleanAmbientMul_left_normal
#print axioms booleanAmbientMul_right_normal
#print axioms booleanAmbientMul_normalized
#print axioms booleanAmbient_X_mul_X_eq_X
#print axioms booleanAmbient_square_residual_eq_zero
#print axioms booleanAmbientEq_of_eq

end PallLean.Paper93.DeepMath.PathC
