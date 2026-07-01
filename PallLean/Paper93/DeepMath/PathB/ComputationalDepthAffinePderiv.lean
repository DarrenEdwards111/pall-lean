import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPFullProdLB

/-!
# The affine-automorphism chain rule: engine for the affine-product SPDP bound

`MOD_q`'s multilinear polynomial is the *affine product* `∏ᵢ(1 + (ω-1)Xᵢ)` (see `…SPDPRestricted`), and restricting it
outside an observer boundary leaves `∏_{visible}(1 + cXᵢ)` — again an affine product.  To prove such a product has
`SPDP.spdpRank κ 0 ≥ C(m, κ)` (the quantitative boundary robustness of `MOD_q`), the clean route is that the affine
map `φ = aeval (Xⱼ ↦ 1 + cXⱼ)` is an automorphism sending `∏Xᵢ ↦ ∏(1+cXᵢ)` and **preserving SPDP rank**, because
partial derivatives transform by a chain rule with a scalar `c`.  This file proves that engine — the part Mathlib
lacks:

  `pderiv_aeval_aff` — **`pderiv i (aeval (aff c) p) = C c · aeval (aff c) (pderiv i p)`** (the chain rule; Mathlib
        has no `pderiv`-under-`aeval` rule — proved by `induction_on` with `Derivation.leibniz`).
  `iterDerivList_aeval_aff` — the iterated form: `∂_L(aeval φ p) = C(c^{|L|}) · aeval φ (∂_L p)`.
  `aeval_aff_injective` — `φ` is injective (`c ≠ 0`), via the inverse `Xⱼ ↦ c⁻¹(Xⱼ-1)`.

## Status

The engine (chain rule + iterate + injectivity) is proved clean.  The remaining assembly that turns it into
`spdpRank κ 0 (∏(1+cXᵢ)) ≥ C(n,κ)` — either the `spdpSubspace`-map + `finrank`-transfer, or the direct
`C(n,κ)`-independent-family argument (mirroring `spdpRank_fullProd_choose_ge`, with `φ` carrying the linear
independence, since `∂_S(∏(1+cX)) = C(c^κ)·φ(∏_{i∉S}X)`) — is mechanical from here.  Composed with `…SPDPRestricted`'s
`restrictPoly (modqPoly c) = (unit)·∏_{visible}(1+cX)`, that gives the observer-boundary quantitative separation
`BoundarySPDP MOD_q m κ ≥ C(m,κ)` vs `BoundarySPDP ∏Xᵢ = 0`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial SPDP

variable {n : ℕ} {F : Type*} [Field F]

variable {n : ℕ} {F : Type*} [Field F]
noncomputable def aff (c : F) : Fin n → MvPolynomial (Fin n) F := fun j => 1 + C c * X j
theorem haff_self (c : F) (i : Fin n) : pderiv i (aff c i) = C c := by
  simp only [aff, map_add, pderiv_one, zero_add, pderiv_C_mul, pderiv_X_self, mul_one]
theorem haff_ne (c : F) (i j : Fin n) (h : j ≠ i) : pderiv i (aff c j) = 0 := by
  simp only [aff, map_add, pderiv_one, zero_add, pderiv_C_mul, pderiv_X_of_ne h, mul_zero]
theorem pderiv_aeval_aff (c : F) (i : Fin n) (p : MvPolynomial (Fin n) F) :
    pderiv i (aeval (aff c) p) = C c * aeval (aff c) (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add]
  | mul_X p j h =>
    rcases eq_or_ne j i with rfl | hji
    · rw [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, h, haff_self,
        pderiv_mul, map_add, map_mul, aeval_X, map_mul, pderiv_X_self]
      simp only [map_one, mul_one]; ring
    · rw [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, h, haff_ne c i j hji,
        pderiv_mul, map_add, map_mul, aeval_X, map_mul, pderiv_X_of_ne hji]
      simp only [map_zero, mul_zero, zero_mul, add_zero]; ring
theorem aeval_aff_injective (c : F) (hc : c ≠ 0) :
    Function.Injective (aeval (aff c) : MvPolynomial (Fin n) F → MvPolynomial (Fin n) F) := by
  have hid : (aeval (fun j => C c⁻¹ * (X j - 1))).comp (aeval (aff c))
      = AlgHom.id F (MvPolynomial (Fin n) F) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, aeval_X, aff, map_add, map_one, map_mul, aeval_C,
      AlgHom.id_apply, MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1]; ring
  exact Function.LeftInverse.injective (g := aeval (fun j => C c⁻¹ * (X j - 1)))
    (fun p => by rw [← AlgHom.comp_apply, hid, AlgHom.id_apply])
theorem iterDerivList_C_mul (c : F) (L : List (Fin n)) (q : MvPolynomial (Fin n) F) :
    iterDerivList L (C c * q) = C c * iterDerivList L q := by
  induction L generalizing q with
  | nil => rfl
  | cons k L' ih =>
    show iterDerivList L' (pderiv k (C c * q)) = C c * iterDerivList L' (pderiv k q)
    rw [pderiv_C_mul, ih]
theorem iterDerivList_aeval_aff (c : F) (L : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    iterDerivList L (aeval (aff c) p) = C (c ^ L.length) * aeval (aff c) (iterDerivList L p) := by
  induction L generalizing p with
  | nil => simp [iterDerivList]
  | cons k L' ih =>
    show iterDerivList L' (pderiv k (aeval (aff c) p)) = _
    rw [pderiv_aeval_aff, iterDerivList_C_mul, ih, ← mul_assoc, ← map_mul, ← pow_succ',
      List.length_cons]
    rfl

end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.pderiv_aeval_aff
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.aeval_aff_injective
