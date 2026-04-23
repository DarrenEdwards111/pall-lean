/-
  PallLean/Paper93/Wiring/ConcreteW.lean

  Paper §9 Lemma 31 — concrete wiring of the ambient per-type interface
  space `W_σ(τ)` for any cookLevin instance, with `n ≥ 4`.

  Agent J1 of 3 (parallel).

  ## Scope

  This file exposes a concrete `concreteW` family that specialises Agent
  H2's abstract `ambientPerTypeSpace` family to Agent H1's concrete
  `perTypeInterfaceSpace`. Downstream chain wirings should consume
  `concreteW` rather than repeatedly supplying `perTypeInterfaceSpace`
  as an argument.

  Provides:

    * `concreteW n hn4 σ τ :
        Submodule ℚ (MvPolynomial (Fin n) ℚ)` — the ambient per-type
      `W_σ(τ)` specialised to H1's concrete per-type source space;
    * `concreteW_finite` — `Module.Finite ℚ (concreteW n hn4 σ τ)`
      discharged by `inferInstance` (via the local span-finite
      instance for `perTypeInterfaceSpace τ`);
    * `concreteW_finrank_le_three` — `finrank ≤ 3` uniformly in `τ`,
      obtained by composing H1's source-level bound with H2's rename
      preservation lemma.

  No `sorry`; no axioms beyond the Lean kernel's `propext`,
  `Classical.choice`, `Quot.sound`.
-/
import PallLean.Paper93.Bridge.AmbientPerType
import PallLean.Paper93.Bridge.EmbedPerType
import PallLean.Paper93.Bridge.PerTypeInterfaceSpace

namespace PallLean.Paper93.Wiring

open PallLean.Paper93.Bridge
open SymmetricPowerBound (ConstraintType)

attribute [local instance] Classical.dec

/-! ## `Module.Finite` instance for the concrete per-type source space

The concrete `perTypeInterfaceSpace τ` is either a span of a finite set
of polynomials (active branches) or the zero submodule
(`transitionRight`). In all four cases it is finitely generated as a
`ℚ`-module. We make this available as a local instance so that
`Module.Finite ℚ (concreteW n hn4 σ τ)` can be discharged by
`inferInstance` through H2's `ambientPerTypeSpace_finite` instance. -/

instance perTypeInterfaceSpace_finite (τ : ConstraintType) :
    Module.Finite ℚ ↥(perTypeInterfaceSpace τ) := by
  classical
  cases τ with
  | booleanity =>
      unfold perTypeInterfaceSpace
      exact Module.Finite.span_of_finite ℚ
        (Set.Finite.insert _
          (Set.Finite.insert _ (Set.finite_singleton _)))
  | adjacency =>
      unfold perTypeInterfaceSpace
      exact Module.Finite.span_of_finite ℚ
        (Set.Finite.insert _ (Set.finite_singleton _))
  | transitionLeft =>
      unfold perTypeInterfaceSpace
      exact Module.Finite.span_of_finite ℚ
        (Set.Finite.insert _ (Set.finite_singleton _))
  | transitionRight =>
      unfold perTypeInterfaceSpace
      -- `⊥` is the zero submodule, which is trivially finitely generated.
      infer_instance

/-! ## Concrete `W_σ(τ)` family

We specialise H2's `ambientPerTypeSpace` to H1's concrete
`perTypeInterfaceSpace`. This fixes the per-type source space once and
for all, giving a self-contained ambient family indexed by
`(n, hn4, σ, τ)`. -/

/-- **Concrete W_σ family.** For any cookLevin instance with `n ≥ 4`,
a coordinate embedding `σ : Fin 4 ↪ Fin n`, and a `ConstraintType τ`,
this is the ambient per-type interface space
`W_σ(τ) ⊆ MvPolynomial (Fin n) ℚ` obtained by `rename`-pushforward of
H1's concrete per-type source space along `σ`. -/
noncomputable def concreteW
    (n : ℕ) (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n) (τ : ConstraintType) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ τ

/-- **Finiteness of the concrete `W_σ(τ)`.** Discharged by
`inferInstance` via H2's `ambientPerTypeSpace_finite` instance together
with the local `perTypeInterfaceSpace_finite` instance above. -/
theorem concreteW_finite
    (n : ℕ) (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n) (τ : ConstraintType) :
    Module.Finite ℚ ↥(concreteW n hn4 σ τ) := by
  unfold concreteW
  infer_instance

/-- **Paper §9 Lemma 31 (concrete per-type W_σ form).** The concrete
ambient per-type interface space `concreteW n hn4 σ τ` has dimension
≤ 3 in `MvPolynomial (Fin n) ℚ`, uniformly in `τ : ConstraintType`.

Obtained by composing H1's source-level bound
`perTypeInterfaceSpace_finrank_le_three` with H2's rename-preservation
bound `ambientPerTypeSpace_finrank_le_three`. -/
theorem concreteW_finrank_le_three
    (n : ℕ) (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n) (τ : ConstraintType) :
    Module.finrank ℚ ↥(concreteW n hn4 σ τ) ≤ 3 :=
  ambientPerTypeSpace_finrank_le_three perTypeInterfaceSpace n hn4 σ τ
    (perTypeInterfaceSpace_finrank_le_three τ)

end PallLean.Paper93.Wiring
