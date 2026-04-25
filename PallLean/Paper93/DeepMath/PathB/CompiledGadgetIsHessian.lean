import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# `compiledGadget` as a Tikhonov-regularised kinetic-term Hessian

This file connects round-70's `compiledGadget α n` to the kinetic term
of the N-Frame Lagrangian `S_NF`. The kinetic term

  `S_kin(α, Φ) := α · ∑_{u, v ∈ E_{K_n}} (Φ_u − Φ_v)²`

(summing over the edge set `E_{K_n}` of the complete graph) has Hessian
matrix

  `∂²S_kin / ∂Φ_i ∂Φ_j = 2 α · L_{K_n}`,

where `L_{K_n} = laplacian (completeAdj n)` is the graph Laplacian of
`K_n`.  We package this as `kineticTermHessian α n := 2 α · L_{K_n}` and
relate it to `compiledGadget α n = α • I + L_{K_n}` by exhibiting the
Tikhonov-regularisation decomposition

  `compiledGadget α n = α • I + (½ • kineticTermHessian 1 n)`,

i.e.  `compiledGadget α n` is the sum of an `α • I` ridge term (the
"Tikhonov" / mass term) plus the kinetic-Hessian half-coupling
`L_{K_n}` (the kinetic term Hessian at `α = ½`).  At `α = 0` the gadget
collapses to the bare Laplacian.

These lemmas are *structural*: they keep the proof kernel-only and make
the connection between the §28.3 compiled gadget and the kinetic-term
Hessian explicit at the matrix level.  Constants are normalised so that
the structural identity holds with rfl-grade simplifications.

## Main results

* `kineticTermHessian` — the Hessian of the K_n kinetic term at coupling
  `α`, defined as `(2 * α) • L_{K_n}`.
* `kineticTermHessian_eq` — the unfolding identity for
  `kineticTermHessian`.
* `compiledGadget_eq_alpha_smul_one_plus_kinetic` — Tikhonov
  decomposition: `compiledGadget α n = α • I + (½) • kineticTermHessian 1 n`.
* `compiledGadget_kinetic_decomposition` — `compiledGadget α n` is the
  sum of the ridge `α • I` and the bare Laplacian `L_{K_n}`.
* `compiledGadget_zero_alpha` — at `α = 0`, `compiledGadget 0 n = L_{K_n}`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-- **Kinetic-term Hessian for the N-Frame Lagrangian on `K_n`.**

The kinetic term of `S_NF` is
`S_kin(α, Φ) := α · ∑_{(u, v) ∈ E_{K_n}} (Φ_u − Φ_v)²`. Its Hessian
matrix `(∂²S_kin / ∂Φ_i ∂Φ_j)_{i, j}` equals `2 α · L_{K_n}`, where
`L_{K_n} = laplacian (completeAdj n)` is the graph Laplacian of `K_n`.

We define `kineticTermHessian α n` as exactly this matrix `2 α · L_{K_n}`.
This is the discrete-Laplacian Hessian of the harmonic energy on `K_n`.
-/
def kineticTermHessian (α : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 * α) • laplacian (completeAdj n)

/-- **Unfolding lemma for `kineticTermHessian`.**

By construction `kineticTermHessian α n = (2 α) • L_{K_n}`. -/
theorem kineticTermHessian_eq (α : ℝ) (n : ℕ) :
    kineticTermHessian α n = (2 * α) • laplacian (completeAdj n) := rfl

/-- **Compiled gadget as Tikhonov + half kinetic-Hessian.**

`compiledGadget α n = α • I + L_{K_n}` admits the structural
decomposition

  `compiledGadget α n = α • I + (½) • kineticTermHessian 1 n`

since `kineticTermHessian 1 n = 2 • L_{K_n}` and `½ • (2 • L_{K_n}) = L_{K_n}`.

This exhibits `compiledGadget α n` explicitly as a *Tikhonov-regularised*
form of the kinetic-term Hessian: the `α • I` is the ridge / mass term
and `½ • kineticTermHessian 1 n = L_{K_n}` is the Hessian of the
kinetic energy at unit coupling. -/
theorem compiledGadget_eq_alpha_smul_one_plus_kinetic (α : ℝ) (n : ℕ) :
    compiledGadget α n
      = α • (1 : Matrix (Fin n) (Fin n) ℝ)
          + ((1 : ℝ) / 2) • kineticTermHessian 1 n := by
  -- Unfold both definitions and reduce to a smul–smul identity on
  -- `laplacian (completeAdj n)`.
  unfold compiledGadget kineticTermHessian
  -- It suffices to prove
  --   `laplacian (completeAdj n) = ((1 : ℝ) / 2) • ((2 * 1) • laplacian (completeAdj n))`.
  congr 1
  -- Reduce the scalar coefficient to `1`.
  have hsmul_smul :
      ((1 : ℝ) / 2) • ((2 * (1 : ℝ)) • laplacian (completeAdj n))
        = (((1 : ℝ) / 2) * (2 * (1 : ℝ))) • laplacian (completeAdj n) := by
    rw [smul_smul]
  rw [hsmul_smul]
  have hcoeff : ((1 : ℝ) / 2) * (2 * (1 : ℝ)) = 1 := by ring
  rw [hcoeff, one_smul]

/-- **Compiled gadget = Tikhonov ridge + bare Laplacian.**

The compiled gadget decomposes as the sum of the Tikhonov ridge term
`α • I` and the bare Laplacian `L_{K_n}`:

  `compiledGadget α n = α • I + L_{K_n}`.

This is by definition of `compiledGadget`, but we record it as a named
theorem to emphasise the *structural* role of the two summands: the
first is the regularisation (mass) term, the second is the (half)
kinetic-term Hessian `½ · ∂²S_kin / ∂Φ²` at unit coupling. -/
theorem compiledGadget_kinetic_decomposition (α : ℝ) (n : ℕ) :
    compiledGadget α n
      = α • (1 : Matrix (Fin n) (Fin n) ℝ) + laplacian (completeAdj n) := rfl

/-- **`compiledGadget` at zero coupling is the bare Laplacian.**

When the Tikhonov coupling vanishes (`α = 0`), the compiled gadget
reduces to the bare graph Laplacian `L_{K_n} = laplacian (completeAdj n)`
of the complete graph. In view of `compiledGadget_eq_alpha_smul_one_plus_kinetic`,
this exhibits the gadget as a pure (half) kinetic-Hessian at unit
kinetic coupling, with no mass / regularisation term. -/
theorem compiledGadget_zero_alpha (n : ℕ) :
    compiledGadget 0 n = laplacian (completeAdj n) := by
  unfold compiledGadget
  rw [zero_smul, zero_add]

/-- **Compiled gadget is half the kinetic Hessian plus a ridge.**

A second packaging of the Tikhonov decomposition: `compiledGadget α n`
is exactly the ridge `α • I` plus *one half* of the unit-coupling
kinetic Hessian. -/
theorem compiledGadget_as_ridge_plus_half_kinetic (α : ℝ) (n : ℕ) :
    compiledGadget α n
      = α • (1 : Matrix (Fin n) (Fin n) ℝ)
          + ((1 : ℝ) / 2) • kineticTermHessian 1 n :=
  compiledGadget_eq_alpha_smul_one_plus_kinetic α n

end PallLean.Paper93.DeepMath.PathB
