/-
# Paper §9.3 — Multilinear-projection closure (the multilinear projection
`mlProj` is a ℚ-linear map on `MvPolynomial (Fin N) ℚ`, and the image of a
finite-dimensional submodule is again finite-dimensional with bounded rank).

This file isolates the elementary module-theoretic content needed for the
"multilinear-projection closure" step of Paper §9.3: the multilinear
projection, viewed as a linear map `mlProjLM : MvPolynomial (Fin N) ℚ →ₗ[ℚ]
MvPolynomial (Fin N) ℚ`, sends every finite-dimensional submodule
`W ⊆ MvPolynomial (Fin N) ℚ` to a finite-dimensional submodule
`W.map mlProjLM`, with
```
  finrank ℚ (W.map mlProjLM)  ≤  finrank ℚ W.
```

The underlying facts are standard Mathlib content:

* `MultilinearSPDP.mlProjLinearMap` packages multilinear projection as a
  `ℚ`-linear endomorphism of `MvPolynomial (Fin N) ℚ`;
* `Submodule.Module.Finite.map` (instance) witnesses that the pushforward of a
  finite submodule under a linear map is finite;
* `Submodule.finrank_map_le` witnesses the rank inequality.

Agent I4 (of 10, parallel) owns this file exclusively; no other file is
touched. The local alias `mlProjLM` matches the name consumed by downstream
closure composition steps and the parallel Agent I2 `mlProjLM` bridge: once
Agent I2 lands, its `mlProjLM` and this file's `mlProjLM` are definitionally
equal (both unfold to `MultilinearSPDP.mlProjLinearMap (Fin N) ℚ`), so no
interface breakage occurs.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
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
**The multilinear projection as a ℚ-linear endomorphism.**

This is the local alias for Agent I2's `mlProjLM`. At the bridge layer it is
definitionally `MultilinearSPDP.mlProjLinearMap (Fin N) ℚ`, which is the
linear-map packaging of `MultilinearSPDP.mlProj` (the Finsupp-level filter
that retains only multilinear monomials). It is a `ℚ`-linear endomorphism of
`MvPolynomial (Fin N) ℚ` — this is the only fact required for the closure
result below.
-/
noncomputable def mlProjLM :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ :=
  MultilinearSPDP.mlProjLinearMap (Fin N) ℚ

/--
**The `mlProj`-closure submodule.**

For a `ℚ`-submodule `W ⊆ MvPolynomial (Fin N) ℚ`, `mlProjClosure W` is the
pushforward of `W` under the linear endomorphism `mlProjLM`.
-/
noncomputable def mlProjClosure
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ)) :
    Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  W.map (mlProjLM (N := N))

@[simp]
theorem mlProjClosure_def
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ)) :
    mlProjClosure (N := N) W = W.map (mlProjLM (N := N)) := rfl

/--
**Finite-dimensionality is preserved under `mlProjClosure`.**

If `W ⊆ MvPolynomial (Fin N) ℚ` is a finite-dimensional `ℚ`-submodule, then
`mlProjClosure W = W.map mlProjLM` is again finite-dimensional. This is a
direct instance of the general Mathlib fact `Submodule.Module.Finite.map`
applied to the linear map `mlProjLM`.
-/
instance mlProjClosure_finite
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ))
    [Module.Finite ℚ W] :
    Module.Finite ℚ (mlProjClosure (N := N) W) :=
  Module.Finite.map W (mlProjLM (N := N))

/--
**Rank does not increase under `mlProjClosure`.**

For any finite-dimensional `ℚ`-submodule `W ⊆ MvPolynomial (Fin N) ℚ`,
```
  finrank ℚ (mlProjClosure W)  ≤  finrank ℚ W.
```
This is the rank monotonicity of `Submodule.finrank_map_le` specialised to
the linear map `mlProjLM`.
-/
theorem mlProjClosure_finrank_le
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ))
    [Module.Finite ℚ W] :
    Module.finrank ℚ (mlProjClosure (N := N) W)
      ≤ Module.finrank ℚ W :=
  Submodule.finrank_map_le (mlProjLM (N := N)) W

end Closure
end Paper93
end PallLean
