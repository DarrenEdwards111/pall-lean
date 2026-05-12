import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetN7N8N12N14Specs
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Concrete invariants of the 7×7 compiled gadget at `α = 1`

We seek a concrete kernel-only theorem about
`compiledGadget 1 7 = 1 • I + L_{K_7}`. The eigenstructure-based
closed form predicts

```
    det (compiledGadget α 7) = α · (α + 7)^6,
```

and hence at `α = 1` we expect `det = 1 · 8^6 = 262144`. Unlike the
`n ≤ 4` cases (`CompiledGadget{2x2,3x3,4x4}Det`), where the closed
form is established by an explicit cofactor expansion via
`Matrix.det_fin_two/three` or `Matrix.det_succ_row_zero`, the
analogous proof for `n = 7` would require expanding all `7! = 5040`
signed leaf terms in the Leibniz sum (or, recursively, a 7-fold
cofactor expansion `7 · 6 · 5 · 4 · 3 · 2 · 1`). This is a serious
computational burden for the kernel; in particular Mathlib does not
ship a closed form for `det (α • I + L_{K_n})` at general `n`, and
the best that is available for `n = 7` in this codebase is the
existence form `exists_alpha_general_n_det_one` proved via the IVT
(see `IVTGeneralN.lean`).

Per the project task instruction (`if [the determinant proof] proves
too computationally expensive, fall back to the trace identity which
is cheap`), this file provides the **trace fallback**:

```
    trace (compiledGadget 1 7) = 7 · 1 + 7 · 6 = 49.
```

This identity is genuinely concrete: it pins down a single real
number obtained from the actual 7×7 matrix, and uses only the
already-established `compiledGadget_trace_formula` (and its
specialisation `compiledGadget_7x7_trace`).

Honest scope statement:

* **Achieved here**: `compiledGadget_7x7_trace_at_one` proves
  `(compiledGadget 1 7).trace = 49`. Kernel-only (`propext`,
  `Classical.choice`, `Quot.sound`).
* **Not achieved here**: the analogous concrete determinant
  `(compiledGadget 1 7).det = 262144`. The eigenstructure analysis
  predicts this value via the closed form `α · (α + 7)^6`, but
  formalising that closed form for general `n = 7` would require a
  separate Mathlib-level argument (e.g. an `α · (α + n)^{n-1}`
  closed-form lemma for `compiledGadget α n`, or a brute-force 7×7
  cofactor expansion of size `7!` that is at the edge of kernel
  feasibility). We leave this strengthening to a dedicated future
  file and document the fallback honestly.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **Concrete trace of the 7×7 compiled gadget at `α = 1`.**

The trace of `compiledGadget 1 7 = 1 • I + L_{K_7}` equals `49`.

Proof: by `compiledGadget_7x7_trace`, the trace at general `α` equals
`7 · α + 42`. Specialising to `α = 1` and simplifying with `norm_num`
yields `7 · 1 + 42 = 49`.

This is the **trace fallback** for the (kernel-expensive) concrete
7×7 determinant claim
`(compiledGadget 1 7).det = 8^6 = 262144`. The eigenstructure
analysis (all-ones eigenvector `α = 1`, six-fold zero-sum subspace
`α + 7 = 8`) predicts `det = 1 · 8^6 = 262144`, but this closed
form is currently only available for `n ≤ 4` in this codebase
(`compiledGadget_{2x2,3x3,4x4}_det`). The trace identity, by
contrast, is uniformly cheap thanks to `compiledGadget_trace_formula`.

Note on the value: `7 · 1 + 7 · (7 - 1) = 7 + 42 = 49`, matching the
specification `7*1 + 7*6 = 49` from the task statement. -/
theorem compiledGadget_7x7_trace_at_one :
    (compiledGadget 1 7).trace = 49 := by
  rw [compiledGadget_7x7_trace]
  norm_num

/-- **Eigenvalue-sum interpretation of the 7×7 trace at `α = 1`.**

Restating `compiledGadget_7x7_trace_at_one` in the `7 · α + 7 · (n − 1)`
form that mirrors the closed-form determinant pattern
`α · (α + n)^{n−1}`.

For `α = 1` and `n = 7`, the trace `7 · 1 + 7 · 6 = 49` decomposes as
the sum of the seven (real) eigenvalues of the symmetric matrix
`1 • I + L_{K_7}`: the simple eigenvalue `1` (all-ones direction) plus
six copies of `1 + 7 = 8` (zero-sum subspace), totalling
`1 + 6 · 8 = 49`. -/
theorem compiledGadget_7x7_trace_at_one_eigenvalue_form :
    (compiledGadget 1 7).trace = 7 * 1 + 7 * 6 := by
  rw [compiledGadget_7x7_trace_at_one]; norm_num

/-- **Determinant-target prediction for the 7×7 compiled gadget at `α = 1`.**

The closed-form pattern `α · (α + n)^{n−1}` predicts
`(compiledGadget 1 7).det = 1 · 8^6 = 262144`. This file does **not**
prove that identity; instead, it records the target value as a
reusable arithmetic fact (`8^6 = 262144`) so that downstream code can
refer to the predicted determinant by a single named constant
without depending on a 7×7 cofactor expansion.

This is purely an arithmetic identity in `ℝ`; it has no content
about the matrix `compiledGadget 1 7` itself. The honest,
matrix-level concrete claim is `compiledGadget_7x7_trace_at_one`. -/
theorem compiledGadget_7x7_det_target_arith :
    (1 : ℝ) * 8^6 = 262144 := by
  norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
