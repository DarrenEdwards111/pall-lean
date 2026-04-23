/-
# Paper §9.3 — Shift-multiplication closure (multiplication by a fixed polynomial
is a ℚ-linear map on `MvPolynomial (Fin n) ℚ`).

This file isolates the elementary module-theoretic content needed for the
"shift-multiplication closure" step: multiplication by a fixed polynomial
`m : MvPolynomial (Fin n) ℚ` is a `ℚ`-linear endomorphism of
`MvPolynomial (Fin n) ℚ`, and the image of any finite-dimensional
`ℚ`-submodule under this map is again finite-dimensional, with rank at most
that of the source.

The underlying facts are standard Mathlib content:

* `LinearMap.mulRight` supplies right-multiplication-by-`m` as a linear map
  on any `Algebra`;
* `Submodule.Module.Finite.map` (instance) witnesses that the pushforward of a
  finite submodule under a linear map is finite;
* `Submodule.finrank_map_le` witnesses the rank inequality.

Agent I1 (of 10, parallel) owns this file exclusively; no other file is
touched.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat

namespace PallLean
namespace Paper93
namespace Closure

open MvPolynomial

variable {n : ℕ}

/--
**Shift-multiplication as a linear map.**

For any fixed polynomial `m : MvPolynomial (Fin n) ℚ`, right-multiplication
by `m` (i.e. `p ↦ p * m`) is a `ℚ`-linear endomorphism of
`MvPolynomial (Fin n) ℚ`. This is the Mathlib `LinearMap.mulRight`
specialised to the commutative algebra `MvPolynomial (Fin n) ℚ` over `ℚ`.
-/
noncomputable def mulByPoly
    (m : MvPolynomial (Fin n) ℚ) :
    MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ :=
  LinearMap.mulRight ℚ m

@[simp]
theorem mulByPoly_apply
    (m p : MvPolynomial (Fin n) ℚ) :
    mulByPoly (n := n) m p = p * m := rfl

/--
**Finite-dimensionality is preserved under pushforward by `mulByPoly m`.**

If `W ⊆ MvPolynomial (Fin n) ℚ` is a finite-dimensional `ℚ`-submodule, then
its image `W.map (mulByPoly m)` under right-multiplication by `m` is again
finite-dimensional. This is a direct instance of the general Mathlib fact
`Submodule.Module.Finite.map` applied to the linear map `mulByPoly m`.
-/
instance mulByPoly_map_finite
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    [Module.Finite ℚ W]
    (m : MvPolynomial (Fin n) ℚ) :
    Module.Finite ℚ (W.map (mulByPoly (n := n) m)) :=
  Module.Finite.map W (mulByPoly (n := n) m)

/--
**Rank does not increase under pushforward by `mulByPoly m`.**

For any finite-dimensional `ℚ`-submodule `W ⊆ MvPolynomial (Fin n) ℚ`,
```
  finrank ℚ (W.map (mulByPoly m))  ≤  finrank ℚ W.
```
This is the rank monotonicity of `Submodule.finrank_map_le` specialised to
the linear map `mulByPoly m`.
-/
theorem mulByPoly_map_finrank_le
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    [Module.Finite ℚ W]
    (m : MvPolynomial (Fin n) ℚ) :
    Module.finrank ℚ (W.map (mulByPoly (n := n) m))
      ≤ Module.finrank ℚ W :=
  Submodule.finrank_map_le (mulByPoly (n := n) m) W

end Closure
end Paper93
end PallLean
