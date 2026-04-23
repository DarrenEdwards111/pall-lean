/-
  PallLean/Paper93/Bridge/AmbientPerType.lean

  Paper §9 Lemma 31 — ambient (`Fin n`) version of the per-type
  interface space `W_σ(τ)` obtained by `rename`-pushforward of a
  per-type source space `perTypeInterfaceSpace τ` through a coordinate
  embedding `σ : Fin 4 ↪ Fin n`.

  Agent H2 of 10 (parallel).

  ## Scope

  This file composes

    * Agent H1's `perTypeInterfaceSpace :
        SymmetricPowerBound.ConstraintType →
        Submodule ℚ (MvPolynomial (Fin wSigmaArity) ℚ)`,
      a per-type source-space assignment with
      `perTypeInterfaceSpace_finrank_le_three` (dim ≤ 3 uniformly in τ)
      and `one_mem_perTypeInterfaceSpace` for `τ ≠ transitionRight`
      (the `1` constant lies in the per-type source for active types), and

    * Agent F3's `rename_finrank_le_three`
      (`PallLean.Paper93.Bridge.rename_finrank_le_three`), which lifts
      the ≤ 3 bound across an injective variable rename.

  into the **ambient** per-type interface space

      ambientPerTypeSpace n hn σ τ
        := (perTypeInterfaceSpace τ).map (rename σ.toFun).toLinearMap

  as a submodule of `MvPolynomial (Fin n) ℚ`, with:

    * `ambientPerTypeSpace_finrank_le_three` — the ≤ 3 bound preserved
      uniformly in `τ`, by composition of H1's source bound with F3's
      rename preservation;
    * a `Module.Finite ℚ` instance, via `Module.Finite.map`;
    * `one_mem_ambientPerTypeSpace` — the `1` constant lies in the
      ambient per-type space whenever `τ ≠ transitionRight`, by
      mapping H1's source membership through the algebra homomorphism
      `rename σ.toFun` (which preserves `1`).

  H1 is taken here as a set of hypotheses on an abstract
  `perTypeInterfaceSpace` family (see the `variable` block). When H1
  lands with a concrete definition and proofs of the three hypotheses
  below, downstream callers obtain concrete instances of the ambient
  lemmas simply by specialising. This keeps H2 independent of H1's
  exact chosen representation.

  No `sorry`; no axioms beyond `propext`, `Classical.choice`,
  `Quot.sound`.
-/
import PallLean.Paper93.Bridge.RankPreservation
import PallLean.Paper93.CookLevinWSigma
import PallLean.SymmetricPowerBound

namespace PallLean.Paper93.Bridge

open MvPolynomial
open PallLean.Paper93

attribute [local instance] Classical.dec

section AmbientPerType

-- Agent H1's per-type interface space: a per-`ConstraintType` family
-- of ℚ-submodules of `MvPolynomial (Fin wSigmaArity) ℚ`.
--
-- We take this as a hypothesis (variable) here so that H2 lands
-- independently of H1's concrete definition. H1 is expected to supply a
-- concrete `perTypeInterfaceSpace` along with the three hypotheses
-- `perTypeInterfaceSpace_finite`, `perTypeInterfaceSpace_finrank_le_three`,
-- and `one_mem_perTypeInterfaceSpace`, after which all results here
-- specialise automatically.
variable
  (perTypeInterfaceSpace :
    SymmetricPowerBound.ConstraintType →
      Submodule ℚ (MvPolynomial (Fin wSigmaArity) ℚ))

/-- **Ambient per-type W_σ.** Lift Agent H1's per-type interface space
`perTypeInterfaceSpace τ` to the ambient polynomial ring
`MvPolynomial (Fin n) ℚ` along a given coordinate embedding
`σ : Fin 4 ↪ Fin n`.

The lift is the image under the linear map underlying the algebra
homomorphism `MvPolynomial.rename σ.toFun`. This is the natural
ambient form used downstream by the cookLevinQ-compiled spanning
lemmas, which live in `MvPolynomial (Fin n) ℚ`. -/
noncomputable def ambientPerTypeSpace
    (n : ℕ) (_hn : n ≥ 4) (σ : Fin 4 ↪ Fin n)
    (τ : SymmetricPowerBound.ConstraintType) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  (perTypeInterfaceSpace τ).map
    (MvPolynomial.rename (σ.toFun :
      Fin wSigmaArity → Fin n) :
        MvPolynomial (Fin wSigmaArity) ℚ
          →ₐ[ℚ] MvPolynomial (Fin n) ℚ).toLinearMap

/-- The ambient per-type W_σ is finite-dimensional as a ℚ-module,
given that the source per-type space is finite-dimensional (Agent H1).

Inherited from the finite-dimensionality of `perTypeInterfaceSpace τ`
via `Module.Finite.map`. -/
instance ambientPerTypeSpace_finite
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n)
    (τ : SymmetricPowerBound.ConstraintType)
    [Module.Finite ℚ ↥(perTypeInterfaceSpace τ)] :
    Module.Finite ℚ
      ↥(ambientPerTypeSpace perTypeInterfaceSpace n hn σ τ) := by
  unfold ambientPerTypeSpace
  infer_instance

/-- **Paper §9 Lemma 31 (ambient per-type W_σ form).** The ambient
per-type interface space `ambientPerTypeSpace n hn σ τ` has
dimension ≤ 3 in `MvPolynomial (Fin n) ℚ`, uniformly in
`τ : ConstraintType`, provided Agent H1's source-level bound
`Module.finrank ℚ (perTypeInterfaceSpace τ) ≤ 3` holds.

Proof strategy: unfolding the definition, the ambient space is the
image of `perTypeInterfaceSpace τ` (a dim ≤ 3 source submodule by the
H1 hypothesis `h_src`) under the linear map
`(rename σ.toFun).toLinearMap`. Because `σ` is an embedding (hence
`σ.toFun` is injective), Agent F3's `rename_finrank_le_three`
transports the ≤ 3 bound across the rename, giving the conclusion. -/
theorem ambientPerTypeSpace_finrank_le_three
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n)
    (τ : SymmetricPowerBound.ConstraintType)
    [Module.Finite ℚ ↥(perTypeInterfaceSpace τ)]
    (h_src : Module.finrank ℚ ↥(perTypeInterfaceSpace τ) ≤ 3) :
    Module.finrank ℚ
      ↥(ambientPerTypeSpace perTypeInterfaceSpace n hn σ τ) ≤ 3 := by
  classical
  -- Preservation of the ≤ 3 bound under injective rename (Agent F3).
  -- `wSigmaArity = 4` definitionally, so this applies directly to σ.
  have h_push :
      Module.finrank ℚ
          ((perTypeInterfaceSpace τ).map
            (MvPolynomial.rename (σ.toFun :
              Fin wSigmaArity → Fin n) :
                MvPolynomial (Fin wSigmaArity) ℚ
                  →ₐ[ℚ] MvPolynomial (Fin n) ℚ).toLinearMap)
        ≤ 3 :=
    rename_finrank_le_three (m := wSigmaArity) (n := n)
      σ (perTypeInterfaceSpace τ) h_src
  -- Unfold H2's definition to reveal the push-forward shape.
  simpa [ambientPerTypeSpace] using h_push

/-- Restatement with the paper constant `d₀ = 3`. -/
theorem ambientPerTypeSpace_finrank_le_d₀
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n)
    (τ : SymmetricPowerBound.ConstraintType)
    [Module.Finite ℚ ↥(perTypeInterfaceSpace τ)]
    (h_src : Module.finrank ℚ ↥(perTypeInterfaceSpace τ) ≤ 3) :
    Module.finrank ℚ
      ↥(ambientPerTypeSpace perTypeInterfaceSpace n hn σ τ) ≤ 3 :=
  ambientPerTypeSpace_finrank_le_three perTypeInterfaceSpace n hn σ τ h_src

/-- **Ambient `1` membership for active constraint types.** If Agent
H1 supplies `(1 : MvPolynomial (Fin wSigmaArity) ℚ) ∈
perTypeInterfaceSpace τ` for every active `τ ≠ transitionRight`, then
the constant `1` also lies in the ambient per-type space
`ambientPerTypeSpace n hn σ τ`, because the algebra homomorphism
`MvPolynomial.rename σ.toFun` preserves `1`.

This is the canonical "`1` is in ambient W_σ" fact needed by the
Spanning-family cookLevinQ compilations (see e.g.
`PallLean.Paper93.Spanning.BooleanityCase.booleanity_factor_mem_ambient`,
which takes the analogous hypothesis for the shared-target
`ambientInterfaceSpace`). -/
theorem one_mem_ambientPerTypeSpace
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n)
    (τ : SymmetricPowerBound.ConstraintType)
    (hτ : τ ≠ SymmetricPowerBound.ConstraintType.transitionRight)
    (h_one_src :
      (1 : MvPolynomial (Fin wSigmaArity) ℚ)
        ∈ perTypeInterfaceSpace τ) :
    (1 : MvPolynomial (Fin n) ℚ)
      ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn σ τ := by
  classical
  -- `rename σ.toFun` is an algebra homomorphism and preserves `1`.
  have h_map_one :
      (MvPolynomial.rename (σ.toFun :
          Fin wSigmaArity → Fin n) :
            MvPolynomial (Fin wSigmaArity) ℚ
              →ₐ[ℚ] MvPolynomial (Fin n) ℚ)
        (1 : MvPolynomial (Fin wSigmaArity) ℚ)
        = (1 : MvPolynomial (Fin n) ℚ) := map_one _
  -- Exhibit `1` as the image of the source `1` under the pushforward.
  refine ⟨(1 : MvPolynomial (Fin wSigmaArity) ℚ), h_one_src, ?_⟩
  -- The `.map`-membership is stated in terms of the underlying
  -- linear map of the algebra hom, whose action on `1` agrees with
  -- `map_one` above.
  simpa [ambientPerTypeSpace] using h_map_one

-- Keep `hτ` formally bound in the signature; it is not used in the
-- proof of `one_mem_ambientPerTypeSpace` above because the hypothesis
-- `h_one_src` already encodes the activity condition at the source
-- level (Agent H1 is expected to only supply `h_one_src` for
-- `τ ≠ transitionRight`). The `hτ` parameter makes the intended usage
-- explicit to downstream callers.
attribute [nolint unusedArguments] one_mem_ambientPerTypeSpace

end AmbientPerType

end PallLean.Paper93.Bridge
