/-
  PallLean/Paper93/Bridge/AmbientInterfaceSpace.lean

  Bridge module: lift Agent A's real W_σ
  `PallLean.Paper93.realInterfaceSpace : Submodule ℚ (MvPolynomial (Fin 4) ℚ)`
  (defined in `PallLean.Paper93.CookLevinWSigma`, commit `6818c78`) to an
  ambient `MvPolynomial (Fin n) ℚ` space with `n ≥ 4`, along a canonical
  embedding `σ : Fin 4 ↪ Fin n` of coordinate indices.

  At this abstraction level we take the embedding `σ` as a hypothesis
  (later files can supply a canonical one, e.g. `Fin.castLE`). The lift is
  the image of `realInterfaceSpace` under `MvPolynomial.rename σ.toFun`
  viewed as a ℚ-linear map.

  This is the canonical "Route C ⇒ Route A" ambient construction:
  we take the concrete (non-vacuous) dim ≤ 3 subspace from Agent A and
  present it as a submodule of the ambient polynomial ring indexed by
  `Fin n`, suitable for gluing into the `cookLevinQ`-style constructions
  that natively live in `MvPolynomial (Fin n) ℚ`.

  What this file provides:

    * `ambientInterfaceSpace n hn σ : Submodule ℚ (MvPolynomial (Fin n) ℚ)`
      the ambient W_σ obtained by `.map` along `(rename σ.toFun).toLinearMap`.

    * `instance : Module.Finite ℚ (ambientInterfaceSpace n hn σ)`
      finite-dimensionality, inherited from the finite-dimensionality of
      `realInterfaceSpace` via `Module.Finite.map`.

  No axioms are introduced beyond the Lean kernel's; no `sorry` occurs.
-/
import PallLean.Paper93.CookLevinWSigma

namespace PallLean.Paper93.Bridge

open MvPolynomial

/-- **Ambient W_σ.** Lift Agent A's real per-type interface space
`PallLean.Paper93.realInterfaceSpace` (a concrete dim ≤ 3 subspace of
`MvPolynomial (Fin 4) ℚ`) to the ambient polynomial ring
`MvPolynomial (Fin n) ℚ` along a given coordinate embedding
`σ : Fin 4 ↪ Fin n`.

The lift is the image under the linear map underlying the algebra
homomorphism `MvPolynomial.rename σ.toFun`. -/
noncomputable def ambientInterfaceSpace (n : ℕ) (_hn : n ≥ 4)
    (σ : Fin 4 ↪ Fin n) : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  PallLean.Paper93.realInterfaceSpace.map
    (MvPolynomial.rename σ.toFun).toLinearMap

/-- `realInterfaceSpace` is finite-dimensional (Agent A's
`realInterfaceSpace_finite`), exposed as an instance so that
`Module.Finite.map` fires automatically for `ambientInterfaceSpace`. -/
instance : Module.Finite ℚ ↥PallLean.Paper93.realInterfaceSpace :=
  PallLean.Paper93.realInterfaceSpace_finite

/-- The ambient W_σ is finite-dimensional as a ℚ-module.
Inherited from the finite-dimensionality of the underlying
`realInterfaceSpace` via `Module.Finite.map`. -/
instance ambientInterfaceSpace_finite
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    Module.Finite ℚ ↥(ambientInterfaceSpace n hn σ) := by
  unfold ambientInterfaceSpace
  infer_instance

end PallLean.Paper93.Bridge
