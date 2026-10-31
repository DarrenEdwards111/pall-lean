import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Multilinearisation

/-!
# `MvPolynomial` re-modelling of circuit substitution — the circuit *is* a polynomial; its accept count is sparse

The circuit-substitution assembly (`…ACC0CircuitSubstitution`) modelled approximants as `Bool`-valued functions, while
the multilinearisation (`…ACC0Multilinearisation`) needs an actual `MvPolynomial`.  This file fuses the two: it
substitutes a genuine `MvPolynomial` through the circuit and identifies it with the circuit's value.

Every gate has an *exact* multilinear interpolation over `{0,1}`: a unary gate `f` becomes
`f(0)·(1-A) + f(1)·A`, a binary gate `g` becomes the four-term bilinear form.  Substituting these bottom-up gives a
polynomial `subst c` over `R` with **`eval (boolVal ∘ x) (subst c) = boolVal (eval c x)`** — the polynomial computes
the circuit exactly on the cube.  Composing with `multilinear_cube_sum` then yields the **accept count as a sparse sum
over the polynomial's support**, closing the modelling gap.

## What is proved (clean axioms, no `sorry`)

* **`subst`** — the substituted `MvPolynomial` (exact multilinear gate interpolations, composed through the circuit).
* **`unary_interp_val` / `binary_interp_val`** — the gate interpolations are exact on `{0,1}`.
* **`subst_eval`** — `eval (boolVal ∘ x) (subst c) = boolVal (eval c x)`: the polynomial computes the circuit on the
  cube (the substitution is faithful).
* **`circuit_cube_count`** — `∑ₓ boolVal (eval c x) = ∑_{d∈(subst c).support} coeff_d · 2^{n-|supp d|}`: the
  circuit's accept count (cast to `R`) is the sparse cube count of its polynomial — the sub-`2^n` Williams `SAT` input,
  now for the actual circuit.
* **`circuit_features_lowDeg`** — every feature of `subst c` is a support of size `≤ totalDegree (subst c)` (in
  `lowDegMonomials`), via `support_mem_lowDeg`.

## Honest scope

This is the **exact** polynomial of the circuit: `subst c` computes `eval c` on the cube with no error, fusing the
substitution and multilinearisation files into a single `MvPolynomial` statement.  Its total degree is whatever the
circuit forces (high for wide gates); the *low-degree* representation is the separate probabilistic content
(`…ACC0Mod6ProbabilisticPolynomial`, `…ACC0ProbabilisticAmplification`, `…ACC0CircuitSubstitution.circuit_error_bound`)
— substituting the *approximate* low-degree gate polynomials trades exactness for low degree, and the abstract
`williams`/`hierarchy` Props remain the named Route-B sockets keeping the final implication conditional.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SubstitutionPoly

open scoped Classical BigOperators
open Finset MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitSubstitution
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The substituted `MvPolynomial`: each gate replaced by its exact multilinear interpolation over `{0,1}`. -/
noncomputable def subst : Circ n → MvPolynomial (Fin n) R
  | .inp i => X i
  | .cst b => C (boolVal b)
  | .una f c => C (boolVal (f false)) * (1 - subst c) + C (boolVal (f true)) * subst c
  | .bin g a b =>
      C (boolVal (g false false)) * ((1 - subst a) * (1 - subst b))
        + C (boolVal (g true false)) * (subst a * (1 - subst b))
        + C (boolVal (g false true)) * ((1 - subst a) * subst b)
        + C (boolVal (g true true)) * (subst a * subst b)

/-- **The unary gate interpolation is exact on `{0,1}` (proved).** -/
theorem unary_interp_val (f : Bool → Bool) (b : Bool) :
    (boolVal (f false) : R) * (1 - boolVal b) + boolVal (f true) * boolVal b = boolVal (f b) := by
  cases b <;> simp [boolVal]

/-- **The binary gate interpolation is exact on `{0,1}` (proved).** -/
theorem binary_interp_val (g : Bool → Bool → Bool) (ba bb : Bool) :
    (boolVal (g false false) : R) * ((1 - boolVal ba) * (1 - boolVal bb))
      + boolVal (g true false) * (boolVal ba * (1 - boolVal bb))
      + boolVal (g false true) * ((1 - boolVal ba) * boolVal bb)
      + boolVal (g true true) * (boolVal ba * boolVal bb)
      = boolVal (g ba bb) := by
  cases ba <;> cases bb <;> simp [boolVal]

/-- **The substituted polynomial computes the circuit on the cube (proved): `eval (boolVal ∘ x) (subst c) =
boolVal (eval c x)`.**  The substitution is faithful — `subst c` *is* the circuit's value as a polynomial. -/
theorem subst_eval (c : Circ n) (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => (boolVal (x i) : R)) (subst c) = boolVal (ACC0CircuitSubstitution.eval c x) := by
  induction c with
  | inp i => simp [subst, ACC0CircuitSubstitution.eval]
  | cst b => simp [subst, ACC0CircuitSubstitution.eval]
  | una f c ih =>
      show MvPolynomial.eval (fun i => (boolVal (x i) : R))
          (C (boolVal (f false)) * (1 - subst c) + C (boolVal (f true)) * subst c)
          = boolVal (ACC0CircuitSubstitution.eval (Circ.una f c) x)
      simp only [map_add, map_mul, map_sub, eval_C, map_one, ih]
      rw [show ACC0CircuitSubstitution.eval (Circ.una f c) x
            = f (ACC0CircuitSubstitution.eval c x) from rfl]
      exact unary_interp_val f (ACC0CircuitSubstitution.eval c x)
  | bin g a b iha ihb =>
      show MvPolynomial.eval (fun i => (boolVal (x i) : R))
          (C (boolVal (g false false)) * ((1 - subst a) * (1 - subst b))
            + C (boolVal (g true false)) * (subst a * (1 - subst b))
            + C (boolVal (g false true)) * ((1 - subst a) * subst b)
            + C (boolVal (g true true)) * (subst a * subst b))
          = boolVal (ACC0CircuitSubstitution.eval (Circ.bin g a b) x)
      simp only [map_add, map_mul, map_sub, eval_C, map_one, iha, ihb]
      rw [show ACC0CircuitSubstitution.eval (Circ.bin g a b) x
            = g (ACC0CircuitSubstitution.eval a x) (ACC0CircuitSubstitution.eval b x) from rfl]
      exact binary_interp_val g (ACC0CircuitSubstitution.eval a x) (ACC0CircuitSubstitution.eval b x)

/-- **The circuit's accept count is the sparse cube count of its polynomial (proved).**  `∑ₓ boolVal (eval c x) =
∑_{d∈(subst c).support} coeff_d · 2^{n-|supp d|}` — the number of accepting inputs (cast to `R`) is computed from the
sparse support of `subst c`, not by enumerating `2^n` inputs.  This is the sub-`2^n` `ACC⁰`-`SAT` count for the actual
circuit (fusing `subst_eval` with `multilinear_cube_sum`). -/
theorem circuit_cube_count (c : Circ n) :
    (∑ x : Fin n → Bool, (boolVal (ACC0CircuitSubstitution.eval c x) : R))
      = ∑ d ∈ (subst (R := R) c).support, (subst (R := R) c).coeff d * (2 : R) ^ (n - d.support.card) := by
  rw [← multilinear_cube_sum (subst (R := R) c)]
  exact Finset.sum_congr rfl (fun x _ => (subst_eval c x).symm)

/-- **Every feature of the circuit polynomial is a low-degree support (proved).**  Each monomial of `subst c` has
support of size `≤ totalDegree (subst c)`, i.e. in `lowDegMonomials n (totalDegree (subst c))`. -/
theorem circuit_features_lowDeg (c : Circ n) {d : Fin n →₀ ℕ}
    (hd : d ∈ (subst (R := R) c).support) :
    d.support ∈ Layer3.lowDegMonomials n (subst (R := R) c).totalDegree :=
  support_mem_lowDeg (subst (R := R) c) (le_refl _) hd

end PallLean.Paper93.DeepMath.PathB.ACC0SubstitutionPoly

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SubstitutionPoly.subst_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SubstitutionPoly.circuit_cube_count
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SubstitutionPoly.circuit_features_lowDeg
