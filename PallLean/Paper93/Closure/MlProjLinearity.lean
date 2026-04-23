/-
  PallLean/Paper93/Closure/MlProjLinearity.lean

  Agent I2 of 10 (parallel) — Paper §9.3 closure layer.

  ## Scope

  This file provides the ℚ-linearity packaging of the multilinear
  projection `mlProj` together with the submodule-image rank bound.
  Concretely:

  * `mlProjLM` exposes `MultilinearSPDP.mlProjLinearMap (Fin N) ℚ` — the
    multilinear projection on `MvPolynomial (Fin N) ℚ` — as a ℚ-linear
    endomorphism under the short name required by downstream Paper §9.3
    closure lemmas.  No new content is introduced at this layer beyond
    the definitional unfolding into the pre-existing `MultilinearSPDP`
    construction: `mlProj_add` and `mlProj_smul` are already established
    in `PallLean/MultilinearSPDP.lean` and `mlProjLinearMap` packages
    them into a `LinearMap`.

  * `mlProjLM_map_finrank_le` witnesses that the ℚ-finrank of the
    image `W.map mlProjLM` of any finite-dimensional ℚ-submodule
    `W ⊆ MvPolynomial (Fin N) ℚ` is bounded by the finrank of `W` itself.
    This is the rank-monotonicity specialisation of Mathlib's general
    `Submodule.finrank_map_le` to the linear endomorphism `mlProjLM`.

  Both results are obtained from standard Mathlib infrastructure:

  * `MultilinearSPDP.mlProjLinearMap` — already in the repo — provides
    the `LinearMap` packaging; `mlProj_add` and `mlProj_smul` are the
    underlying additivity and ℚ-homogeneity witnesses. No wrapping is
    therefore needed.

  * `Submodule.finrank_map_le` — Mathlib
    `Mathlib.LinearAlgebra.Dimension.Constructions` — is the generic
    rank-monotonicity of pushforwards under linear maps.

  This file is a kernel-only, axiom-free bridge layer: nothing is
  introduced except the definitional renaming of a pre-existing
  `LinearMap` together with one specialised instance of Mathlib's
  `Submodule.finrank_map_le`. It does not depend on any other file
  under `PallLean/Paper93/Closure/`.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import PallLean.MultilinearSPDP

namespace PallLean
namespace Paper93
namespace Closure

open MvPolynomial

variable {N : ℕ}

/--
**`mlProj` as a ℚ-linear endomorphism.**

This is the short-name alias consumed by Paper §9.3 closure lemmas: it
is definitionally `MultilinearSPDP.mlProjLinearMap (Fin N) ℚ`, i.e. the
`LinearMap` packaging of the multilinear projection
`MultilinearSPDP.mlProj` on `MvPolynomial (Fin N) ℚ` (the Finsupp-level
filter retaining only multilinear monomials).  Linearity is provided by
`MultilinearSPDP.mlProj_add` and `MultilinearSPDP.mlProj_smul`, which
are already established in `PallLean/MultilinearSPDP.lean`; no extra
wrapping is required here.
-/
noncomputable def mlProjLM :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ :=
  MultilinearSPDP.mlProjLinearMap (Fin N) ℚ

/--
**`mlProjLM` coincides with `MultilinearSPDP.mlProj` on elements.**

A convenience rewriting lemma: applying the `LinearMap` `mlProjLM` to a
polynomial is the same as applying the raw Finsupp-level multilinear
projection `MultilinearSPDP.mlProj`. This is a direct unfolding of the
`LinearMap` packaging from `MultilinearSPDP.mlProjLinearMap`.
-/
@[simp]
theorem mlProjLM_apply (p : MvPolynomial (Fin N) ℚ) :
    mlProjLM (N := N) p = MultilinearSPDP.mlProj p := rfl

/--
**ℚ-additivity of `mlProjLM`.**

Immediate consequence of `mlProjLM` being a `LinearMap`; stated
explicitly for downstream convenience and to double-check the
additivity witness coming from `MultilinearSPDP.mlProj_add`.
-/
theorem mlProjLM_add (p q : MvPolynomial (Fin N) ℚ) :
    mlProjLM (N := N) (p + q) = mlProjLM (N := N) p + mlProjLM (N := N) q :=
  map_add (mlProjLM (N := N)) p q

/--
**ℚ-homogeneity of `mlProjLM`.**

Immediate consequence of `mlProjLM` being a `LinearMap`; stated
explicitly for downstream convenience and to double-check the
homogeneity witness coming from `MultilinearSPDP.mlProj_smul`.
-/
theorem mlProjLM_smul (c : ℚ) (p : MvPolynomial (Fin N) ℚ) :
    mlProjLM (N := N) (c • p) = c • mlProjLM (N := N) p :=
  map_smul (mlProjLM (N := N)) c p

/--
**Image of a finite-dimensional submodule is finite-dimensional.**

If `W ⊆ MvPolynomial (Fin N) ℚ` is a `ℚ`-finite submodule, then the
pushforward `W.map mlProjLM` is again a `ℚ`-finite submodule.  This is
the direct specialisation of Mathlib's `Submodule.Module.Finite.map`
instance to the linear map `mlProjLM`.
-/
instance mlProjLM_map_finite
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ))
    [Module.Finite ℚ W] :
    Module.Finite ℚ (W.map (mlProjLM (N := N))) :=
  Module.Finite.map W (mlProjLM (N := N))

/--
**Rank bound for the image of a finite-dimensional submodule.**

For any ℚ-finite submodule `W ⊆ MvPolynomial (Fin N) ℚ`,
```
  finrank ℚ (W.map mlProjLM)  ≤  finrank ℚ W.
```
This is the rank-monotonicity specialisation of Mathlib's general
`Submodule.finrank_map_le` to the linear endomorphism `mlProjLM`: no
extra hypotheses on `mlProjLM` (e.g. injectivity or surjectivity) are
required for the `≤` direction, since `finrank_map_le` holds for every
linear map.
-/
theorem mlProjLM_map_finrank_le
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ))
    [Module.Finite ℚ W] :
    Module.finrank ℚ (W.map (mlProjLM (N := N)))
      ≤ Module.finrank ℚ W :=
  Submodule.finrank_map_le (mlProjLM (N := N)) W

end Closure
end Paper93
end PallLean
