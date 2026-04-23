/-
  PallLean/Paper93/Spanning/DerivativeClosure.lean

  Agent H4 (of 10, parallel) — Derivative-closure submodules.

  ## Scope

  The compiled `allBoundedProfilePostSpan` post-span contains generators
  of the form `mlProj (shift * iterDerivList S g)` where `g` ranges over
  factors and `S : List (Fin n)` is a list of tape variables. Previous
  spanning scaffolds (Agents G1–G3) supplied per-factor per-type ambient
  membership `g ∈ W τ`, but Agent G4's review flagged that this is
  strictly weaker than the per-derivative statement actually consumed
  by the composition pipeline: one needs the iterated partial derivative
  `iterDerivList S g` (not just `g`) to live in an appropriate ambient
  sub-module.

  This file supplies the purely linear-algebraic closure statement that
  lets G1–G3's per-factor membership bridge to the per-derivative form:

    * `derivSubmodule W i`   := `W.map (pderiv i).toLinearMap`
        — the ambient sub-module consisting of `∂_i f` for `f ∈ W`.
    * `iterDerivSubmodule W S` := iterated `derivSubmodule`
        along the list `S`, using the same left-fold convention as
        `SPDPDefs.iterDerivList` (see `SPDPDefs.lean`).
    * `derivSubmodule_finrank_le` (and its iterated version)
        — `Submodule.map` never increases finrank.
    * `iterDerivList_mem_iterDerivSubmodule`
        — the transport lemma: if `f ∈ W` then
          `iterDerivList S f ∈ iterDerivSubmodule W S`.

  ## Faithfulness

  All content is standard finite-dimensional linear algebra over ℚ.
  `MvPolynomial.pderiv i` is a `ℚ`-linear map (via the underlying
  `Derivation`), and `Submodule.map` preserves finiteness and
  never increases finrank. The iterated statements follow by a
  straight induction on the list `S`, matching the left-fold
  convention of `iterDerivList` (`foldl` with function
  `fun q i => pderiv i q`).

  ## Axiom trace

  Kernel-only: this file uses no `sorry`, no custom `axiom`, and no
  `SolveByElim`-style tactical magic. All conclusions route through
  existing Mathlib lemmas (`Submodule.mem_map_of_mem`,
  `Submodule.finrank_map_le`, `Submodule.Module.Finite.map`).
-/

import PallLean.SPDPDefs

open Module
open scoped BigOperators

namespace PallLean
namespace Paper93
namespace Spanning

open MvPolynomial SPDP

/-- **Single-step derivative closure.**

The sub-module consisting of all `∂_i f` for `f ∈ W`. By definition,
`derivSubmodule W i = W.map (pderiv i).toLinearMap`. -/
noncomputable def derivSubmodule {n : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ)) (i : Fin n) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  W.map (MvPolynomial.pderiv (R := ℚ) i).toLinearMap

/-- `derivSubmodule` packaging of `Submodule.mem_map_of_mem`:
    if `f ∈ W` then `pderiv i f ∈ derivSubmodule W i`. -/
theorem pderiv_mem_derivSubmodule {n : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ)) (i : Fin n)
    {f : MvPolynomial (Fin n) ℚ} (hf : f ∈ W) :
    MvPolynomial.pderiv (R := ℚ) i f ∈ derivSubmodule W i := by
  -- Unfold and apply `Submodule.mem_map_of_mem`.
  -- Note `((pderiv i).toLinearMap) f = pderiv i f` definitionally.
  exact Submodule.mem_map_of_mem hf

/-- `Submodule.map` never increases finrank, specialised to `derivSubmodule`. -/
theorem derivSubmodule_finrank_le {n : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ)) [Module.Finite ℚ W] (i : Fin n) :
    Module.finrank ℚ (derivSubmodule W i) ≤ Module.finrank ℚ W := by
  -- `derivSubmodule W i = W.map (pderiv i).toLinearMap`, so this is
  -- exactly `Submodule.finrank_map_le`.
  exact Submodule.finrank_map_le _ W

/-- Finite-ness is preserved under `derivSubmodule` (it is a `Submodule.map`). -/
instance derivSubmodule_finite {n : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ)) [Module.Finite ℚ W] (i : Fin n) :
    Module.Finite ℚ (derivSubmodule W i) := by
  -- `Submodule.Module.Finite.map` instance applies verbatim.
  unfold derivSubmodule
  infer_instance

/-- **Iterated derivative closure.**

Iterated `derivSubmodule`, matching the left-fold convention of
`SPDPDefs.iterDerivList`:
`iterDerivList S f = S.foldl (fun q i => pderiv i q) f`. Thus we use
`S.foldl` here with the same associativity: applying index `S.head`
first, then `S[1]`, etc. -/
noncomputable def iterDerivSubmodule {n : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ)) (S : List (Fin n)) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  S.foldl (fun W' i => derivSubmodule W' i) W

@[simp] theorem iterDerivSubmodule_nil {n : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ)) :
    iterDerivSubmodule W ([] : List (Fin n)) = W := rfl

@[simp] theorem iterDerivSubmodule_cons {n : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ)) (i : Fin n) (S : List (Fin n)) :
    iterDerivSubmodule W (i :: S) = iterDerivSubmodule (derivSubmodule W i) S := rfl

/-- Finite-ness propagates through `iterDerivSubmodule`. -/
theorem iterDerivSubmodule_finite {n : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ)) (S : List (Fin n))
    (_ : Module.Finite ℚ W) :
    Module.Finite ℚ (iterDerivSubmodule W S) := by
  -- Induction on `S`, carrying the finiteness instance through each
  -- `derivSubmodule` step.
  induction S generalizing W with
  | nil =>
    simpa [iterDerivSubmodule] using (inferInstance : Module.Finite ℚ W)
  | cons i rest ih =>
    -- `iterDerivSubmodule W (i :: rest) = iterDerivSubmodule (derivSubmodule W i) rest`.
    -- We have `Module.Finite ℚ (derivSubmodule W i)` from the single-step instance.
    have hW : Module.Finite ℚ W := ‹_›
    have hi : Module.Finite ℚ (derivSubmodule W i) := derivSubmodule_finite W i
    simpa [iterDerivSubmodule_cons] using ih (derivSubmodule W i) hi

/-- **Iterated finrank bound.** The iterated derivative closure has
finrank no larger than `W`. -/
theorem iterDerivSubmodule_finrank_le {n : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ)) [hW : Module.Finite ℚ W]
    (S : List (Fin n)) :
    Module.finrank ℚ (iterDerivSubmodule W S) ≤ Module.finrank ℚ W := by
  -- Induction on `S`. Each `derivSubmodule` step does not increase
  -- finrank (Mathlib `Submodule.finrank_map_le`), and finiteness is
  -- preserved so the inequality composes.
  induction S generalizing W with
  | nil =>
    -- `iterDerivSubmodule W [] = W`.
    simp
  | cons i rest ih =>
    -- `iterDerivSubmodule W (i :: rest) = iterDerivSubmodule (derivSubmodule W i) rest`.
    -- Step 1: IH gives `finrank (iterDerivSubmodule (derivSubmodule W i) rest)
    --           ≤ finrank (derivSubmodule W i)`.
    -- Step 2: `derivSubmodule_finrank_le` gives
    --           `finrank (derivSubmodule W i) ≤ finrank W`.
    -- Compose and transport along `iterDerivSubmodule_cons`.
    have hi : Module.Finite ℚ (derivSubmodule W i) := derivSubmodule_finite W i
    have h1 :
        Module.finrank ℚ (iterDerivSubmodule (derivSubmodule W i) rest)
          ≤ Module.finrank ℚ (derivSubmodule W i) :=
      ih (derivSubmodule W i)
    have h2 :
        Module.finrank ℚ (derivSubmodule W i) ≤ Module.finrank ℚ W :=
      derivSubmodule_finrank_le W i
    have hcomp :
        Module.finrank ℚ (iterDerivSubmodule (derivSubmodule W i) rest)
          ≤ Module.finrank ℚ W :=
      le_trans h1 h2
    simpa [iterDerivSubmodule_cons] using hcomp

/-- **Transport lemma (per-derivative membership).**

If `f ∈ W` then the iterated partial derivative `iterDerivList S f` lies in
the corresponding iterated derivative sub-module `iterDerivSubmodule W S`.

This is the key closure that upgrades Agents G1–G3's per-factor
`g ∈ W τ` deliverables to the per-derivative form
`iterDerivList S g ∈ iterDerivSubmodule (W τ) S` consumed by the
`allBoundedProfilePostSpan` machinery. -/
theorem iterDerivList_mem_iterDerivSubmodule {n : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (f : MvPolynomial (Fin n) ℚ) (hf : f ∈ W) (S : List (Fin n)) :
    iterDerivList S f ∈ iterDerivSubmodule W S := by
  -- Induction on `S`, generalising over both `W` and `f` so the
  -- `cons` step can apply the induction hypothesis to
  -- `(derivSubmodule W i, pderiv i f)`.
  induction S generalizing W f with
  | nil =>
    -- `iterDerivList [] f = f`, and `iterDerivSubmodule W [] = W`.
    simpa [iterDerivList, iterDerivSubmodule] using hf
  | cons i rest ih =>
    -- `iterDerivList (i :: rest) f = iterDerivList rest (pderiv i f)`
    -- and `iterDerivSubmodule W (i :: rest)
    --        = iterDerivSubmodule (derivSubmodule W i) rest`.
    -- So the goal reduces to
    --   `iterDerivList rest (pderiv i f) ∈ iterDerivSubmodule (derivSubmodule W i) rest`.
    -- We have `pderiv i f ∈ derivSubmodule W i` by `pderiv_mem_derivSubmodule`;
    -- the induction hypothesis finishes.
    have hpd : MvPolynomial.pderiv (R := ℚ) i f ∈ derivSubmodule W i :=
      pderiv_mem_derivSubmodule W i hf
    -- Reduce the goal to the IH form.
    have hrec :
        iterDerivList rest (MvPolynomial.pderiv (R := ℚ) i f)
          ∈ iterDerivSubmodule (derivSubmodule W i) rest :=
      ih (derivSubmodule W i) (MvPolynomial.pderiv (R := ℚ) i f) hpd
    -- Now identify the LHS with `iterDerivList (i :: rest) f` and the RHS
    -- with `iterDerivSubmodule W (i :: rest)` via `foldl`/`foldl`
    -- definitional unfolding.
    simpa [iterDerivList, iterDerivSubmodule, List.foldl_cons] using hrec

end Spanning
end Paper93
end PallLean
