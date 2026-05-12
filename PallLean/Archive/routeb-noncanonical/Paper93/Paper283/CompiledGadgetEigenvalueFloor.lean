import PallLean.Paper93.Paper283.RouteBBridgeAConcreteSpectralFloor
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetIsHermitian

/-!
# Eigenvalue floor for the compiled gadget via its `IsHermitian` proof

This file packages the spectral-floor inequality

  `∀ i, α ≤ (compiledGadget_isHermitian α n).eigenvalues i`

for the compiled gadget `compiledGadget α n` at positive coupling
`α > 0`, expressed directly in terms of the dedicated `IsHermitian`
proof `compiledGadget_isHermitian α n` from
`Paper93/DeepMath/PathB/Positroid/CompiledGadgetIsHermitian.lean`.

This is the variant of the spectral floor consumed by Codex's
`RouteBRicherGaugeSpectralWindowBudget.eigenvalue_floor` field at
`A := compiledGadget α n`, `lambdaFloor := α`, `S := Finset.univ`.

## Strategy

The structural identity
`compiledGadget α n = α • I + L_{K_n}` (with `L_{K_n}` PSD as the
complete-graph Laplacian) is already used by
`PallLean.Paper93.Paper283.compiledGadget_eigenvalue_floor` to derive
the floor from a `PosSemidef` proof. That theorem produces

  `∀ i, α ≤ hA.1.eigenvalues i`

where `hA : (compiledGadget α n).PosSemidef` and `hA.1` extracts the
`IsHermitian` proof.

Since `Matrix.IsHermitian A` is the proposition `Aᴴ = A`, Lean 4
proof irrelevance makes any two `IsHermitian` proofs of the same matrix
definitionally equal as `Prop`-valued terms. In particular,
`compiledGadget_isHermitian α n` and `hA.1` are equal, and we can
transfer the floor inequality between them with a `rfl`-rewrite.

## Output

`compiledGadget_isHermitian_eigenvalue_floor` states the floor
inequality directly against `(compiledGadget_isHermitian α n).eigenvalues`,
which is the exact form expected by the spectral-window budget package.
-/

namespace PallLean.Paper93.Paper283

open PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Eigenvalue floor for `compiledGadget α n` at positive `α`,
expressed via the `compiledGadget_isHermitian` Hermitian proof.**

For all `α : ℝ` with `α > 0` and all `n : ℕ` with `1 ≤ n`,
every eigenvalue of `compiledGadget α n` (as computed from the
canonical Hermitian proof `compiledGadget_isHermitian α n`) is at
least `α`.

Mathematically the spectrum of `compiledGadget α n = α • I + L_{K_n}`
consists of `α` (with multiplicity 1, from the all-ones eigenvector)
and `α + n` (with multiplicity `n - 1`, from sum-zero
eigenvectors). For `α > 0` and `n ≥ 1` both `α` and `α + n` are at
least `α`, so the spectral floor is `α`.

The proof reuses the `PosSemidef`-based floor theorem
`PallLean.Paper93.Paper283.compiledGadget_eigenvalue_floor`, which
proves the same inequality against `hA.1.eigenvalues` for any
`hA : (compiledGadget α n).PosSemidef`. Since `Matrix.IsHermitian` is
a `Prop` (defined as `Aᴴ = A`), the two `IsHermitian` proofs
`compiledGadget_isHermitian α n` and `hA.1` are definitionally equal
by Lean 4 proof irrelevance. The transfer is therefore a single
`rfl`-rewrite (encoded as `Subsingleton.elim`, which discharges
immediately because all `IsHermitian` proofs of the same matrix are
equal). -/
theorem compiledGadget_isHermitian_eigenvalue_floor
    (α : ℝ) (n : ℕ) (hα : 0 < α) (_hn : 1 ≤ n) :
    ∀ i, α ≤ (compiledGadget_isHermitian α n).eigenvalues i := by
  -- Step 1: assemble the `PosSemidef` proof for `compiledGadget α n`
  -- at positive coupling, via the structural identity
  -- `compiledGadget α n = α • I + L_{K_n}` plus `L_{K_n}` PSD.
  intro i
  have hPSD : (compiledGadget α n).PosSemidef :=
    compiledGadget_posSemidef_of_positive_coupling α hα
  -- Step 2: invoke the existing PosSemidef-based floor theorem to
  -- obtain `α ≤ hPSD.1.eigenvalues i` for every index `i`.
  have hfloor : ∀ j, α ≤ hPSD.1.eigenvalues j :=
    compiledGadget_eigenvalue_floor (eta := α) (N := n) hα hPSD
  -- Step 3: the canonical Hermitian proof and the one extracted from
  -- `hPSD` are equal as terms of the proposition
  -- `(compiledGadget α n).IsHermitian` (which is just
  -- `(compiledGadget α n)ᴴ = compiledGadget α n` and hence a
  -- subsingleton).  We use `Subsingleton.elim` rather than `rfl` to
  -- be robust against any future definitional changes to
  -- `IsHermitian`.
  have hH_eq : (compiledGadget_isHermitian α n) = hPSD.1 :=
    Subsingleton.elim _ _
  rw [hH_eq]
  exact hfloor i

/-- **Restatement: every eigenvalue of `compiledGadget α n` at
positive `α` is at least `α`.**

This is the `Prop`-form most directly consumed by
`RouteBRicherGaugeSpectralWindowBudget.eigenvalue_floor` when the
spectral window `S` is `Finset.univ`: it asserts that for every
index `i ∈ Finset.univ`, the lambda-floor `α` is dominated by the
`i`-th eigenvalue of `compiledGadget α n` under the canonical
Hermitian proof. -/
theorem compiledGadget_isHermitian_eigenvalue_floor_univ
    (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) :
    ∀ i ∈ (Finset.univ : Finset (Fin n)),
      α ≤ (compiledGadget_isHermitian α n).eigenvalues i := by
  intro i _hi
  exact compiledGadget_isHermitian_eigenvalue_floor α n hα hn i

/-! ## Axiom audit anchors -/

#print axioms compiledGadget_isHermitian_eigenvalue_floor
#print axioms compiledGadget_isHermitian_eigenvalue_floor_univ

end PallLean.Paper93.Paper283
