import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetEigenvalueAlpha
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetOrthogonalEigenvec
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Bundled spectrum facts for the compiled gadget

This file packages the four core spectrum/eigenvalue/trace/diagonal
identities for the §28.3 compiled gadget matrix
`compiledGadget α n = α • I + L_{K_n}` into a single bundled theorem
`compiledGadget_spectrum_bundle`. The four conjuncts are exactly the
statements of the existing lemmas:

1. **All-ones eigenvector with eigenvalue `α`** — see
   `compiledGadget_mulVec_one` (in
   `PallLean.Paper93.DeepMath.PathB.CompiledGadgetEigenvalueAlpha`):
   `(compiledGadget α n).mulVec (fun _ => 1) = (fun _ => α)`.

2. **Sum-zero eigenvectors with eigenvalue `α + n`** — see
   `compiledGadget_mulVec_sumZero` (in
   `PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetOrthogonalEigenvec`):
   for any `v : Fin n → ℝ` with `∑ i, v i = 0`,
   `(compiledGadget α n).mulVec v = (α + n) • v`.

3. **Trace formula** — see `compiledGadget_trace_formula` (in
   `PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula`):
   `trace (compiledGadget α n) = n * α + n * (n - 1)`.

4. **Diagonal entry formula** — see `compiledGadget_diagonal` (in
   `PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal`):
   for every `i : Fin n`, `(compiledGadget α n) i i = α + (n - 1)`.

The bundle is universally quantified over `α : ℝ` and `n : ℕ`, and
each conjunct is supplied by the corresponding existing lemma via the
`⟨..., ..., ..., ...⟩` anonymous-constructor form.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

/-- **Compiled-gadget spectrum bundle.**

A single statement bundling the four core spectrum/eigenvalue
identities for `compiledGadget α n = α • I + L_{K_n}`:

* the all-ones vector is an `α`-eigenvector;
* every sum-zero vector is an `(α + n)`-eigenvector;
* the trace equals `n α + n (n - 1)`;
* every diagonal entry equals `α + (n - 1)`.

Each conjunct is exactly the statement of an existing lemma; the proof
is the anonymous tuple of those lemmas.
-/
theorem compiledGadget_spectrum_bundle :
    (∀ α : ℝ, ∀ n : ℕ,
        (compiledGadget α n).mulVec (fun _ : Fin n => (1 : ℝ))
          = (fun _ : Fin n => α)) ∧
    (∀ α : ℝ, ∀ n : ℕ, ∀ v : Fin n → ℝ, ∑ i, v i = 0 →
        (compiledGadget α n).mulVec v = (α + (n : ℝ)) • v) ∧
    (∀ α : ℝ, ∀ n : ℕ,
        (compiledGadget α n).trace
          = (n : ℝ) * α + (n : ℝ) * ((n : ℝ) - 1)) ∧
    (∀ α : ℝ, ∀ n : ℕ, ∀ i : Fin n,
        compiledGadget α n i i = α + ((n : ℝ) - 1)) :=
  ⟨fun α n => compiledGadget_mulVec_one α n,
   fun α n v hv => compiledGadget_mulVec_sumZero α n v hv,
   fun α n => compiledGadget_trace_formula α n,
   fun α n i => compiledGadget_diagonal α n i⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
