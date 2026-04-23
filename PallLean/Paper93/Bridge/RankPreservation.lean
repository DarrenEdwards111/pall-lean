/-
  RankPreservation.lean — Rank preservation under injective variable
  substitution of multivariate polynomials.

  Agent F3 of 10 (parallel) — paper §9 Lemma 31 bridge-layer
  preparatory step.

  ## Scope

  For an embedding `σ : Fin m ↪ Fin n`, the algebra homomorphism
  `MvPolynomial.rename σ.toFun` is injective on the whole polynomial
  ring, and hence injective on every submodule image. Consequently,
  pushing a submodule `W ≤ MvPolynomial (Fin m) ℚ` forward through
  `rename σ.toFun` preserves its `ℚ`-finrank; in particular the bound
  `finrank W ≤ 3` used by the paper's rank-route analysis is preserved
  under arbitrary variable embeddings `Fin m ↪ Fin n`.

  The proof reuses Mathlib's
  - `MvPolynomial.rename_injective` (injectivity of `rename` along an
    injective variable map), and
  - `Submodule.equivMapOfInjective` together with `LinearEquiv.finrank_eq`
    (finrank is invariant under linear equivalences of submodules).

  Nothing in this file depends on the concrete Cook-Levin compilation;
  it is a purely algebraic statement about `MvPolynomial` over `ℚ`.
-/
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Logic.Embedding.Basic

namespace PallLean
namespace Paper93
namespace Bridge

open MvPolynomial

/--
**Rename-along-embedding injectivity.**

For any embedding `σ : Fin m ↪ Fin n`, the induced algebra homomorphism
`MvPolynomial.rename σ.toFun : MvPolynomial (Fin m) ℚ →ₐ[ℚ]
MvPolynomial (Fin n) ℚ` is injective as a function on the ambient
polynomial ring. This is a direct specialisation of
`MvPolynomial.rename_injective` to the injective variable map
underlying `σ`.
-/
theorem rename_injective_of_embedding {m n : ℕ} (σ : Fin m ↪ Fin n) :
    Function.Injective
      (MvPolynomial.rename σ.toFun :
        MvPolynomial (Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ) := by
  -- Injectivity of `rename f` reduces to injectivity of the variable
  -- map `f`. For `f := σ.toFun` this is the tautological embedding
  -- injectivity `σ.injective`.
  have hσ : Function.Injective (σ.toFun : Fin m → Fin n) := σ.injective
  -- `MvPolynomial.rename_injective` packages this reduction.
  simpa using
    (MvPolynomial.rename_injective (R := ℚ) (σ.toFun) hσ)

/--
**Linear-map form of `rename_injective_of_embedding`.**

The underlying `ℚ`-linear map of `rename σ.toFun` is injective on the
full polynomial ring. This is the form used by the submodule pushforward
constructions below.
-/
theorem rename_toLinearMap_injective {m n : ℕ} (σ : Fin m ↪ Fin n) :
    Function.Injective
      ((MvPolynomial.rename σ.toFun :
          MvPolynomial (Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ).toLinearMap) := by
  -- The `toLinearMap` of an `AlgHom` has the same underlying function
  -- as the `AlgHom` itself, so injectivity of the one transfers to
  -- injectivity of the other.
  intro p q hpq
  exact rename_injective_of_embedding σ hpq

/--
**Finrank preservation under injective rename.**

If `W ≤ MvPolynomial (Fin m) ℚ` is a `ℚ`-finite submodule, then pushing
`W` forward through `rename σ.toFun` produces a submodule of the same
`ℚ`-finrank. This follows because `rename σ.toFun` is globally injective
(and thus a fortiori injective on `W`), and an injective linear map
induces a linear equivalence between `W` and `W.map`, under which
`finrank` is preserved.
-/
theorem rename_finrank_preserved {m n : ℕ} (σ : Fin m ↪ Fin n)
    (W : Submodule ℚ (MvPolynomial (Fin m) ℚ)) [Module.Finite ℚ W] :
    Module.finrank ℚ
        (W.map (MvPolynomial.rename σ.toFun :
          MvPolynomial (Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ).toLinearMap)
      = Module.finrank ℚ W := by
  -- Injectivity of the underlying linear map.
  have hinj := rename_toLinearMap_injective σ
  -- The canonical linear equivalence `W ≃ₗ[ℚ] W.map f` for injective
  -- `f` (Mathlib's `Submodule.equivMapOfInjective`).
  let e :
      (W : Submodule ℚ (MvPolynomial (Fin m) ℚ))
        ≃ₗ[ℚ]
      W.map (MvPolynomial.rename σ.toFun :
        MvPolynomial (Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ).toLinearMap :=
    Submodule.equivMapOfInjective
      ((MvPolynomial.rename σ.toFun :
        MvPolynomial (Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ).toLinearMap)
      hinj W
  -- `finrank` is invariant under linear equivalence.
  exact (LinearEquiv.finrank_eq e).symm

/--
**Preservation of the `≤ 3` finrank bound under injective rename.**

Specialisation of `rename_finrank_preserved` to the `≤ 3` regime used by
the paper's rank-route analysis: if `finrank W ≤ 3` then the pushforward
`W.map (rename σ.toFun).toLinearMap` also has finrank `≤ 3`, for any
embedding `σ : Fin m ↪ Fin n`.
-/
theorem rename_finrank_le_three {m n : ℕ} (σ : Fin m ↪ Fin n)
    (W : Submodule ℚ (MvPolynomial (Fin m) ℚ)) [Module.Finite ℚ W]
    (h : Module.finrank ℚ W ≤ 3) :
    Module.finrank ℚ
        (W.map (MvPolynomial.rename σ.toFun :
          MvPolynomial (Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ).toLinearMap)
      ≤ 3 := by
  -- Directly rewrite the target finrank using the exact preservation
  -- lemma, then apply the hypothesis.
  rw [rename_finrank_preserved σ W]
  exact h

end Bridge
end Paper93
end PallLean
