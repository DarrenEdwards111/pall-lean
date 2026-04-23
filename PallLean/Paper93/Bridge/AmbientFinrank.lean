/-
  PallLean/Paper93/Bridge/AmbientFinrank.lean

  Paper §9 Lemma 31 — ambient dimension bound for the real interface
  space `W_σ` after the `Fin 4 ↪ Fin n` coordinate lift.

  Context. Agent F4 (`AmbientInterfaceSpace.lean`) defines

      ambientInterfaceSpace n hn σ :=
        realInterfaceSpace.map (MvPolynomial.rename σ.toFun).toLinearMap

  as a submodule of `MvPolynomial (Fin n) ℚ`, and supplies a
  finite-dimensionality instance. Agent A (`CookLevinWSigma.lean`)
  proves that the source `realInterfaceSpace` satisfies

      Module.finrank ℚ realInterfaceSpace ≤ 3

  via `realInterfaceSpace_finrank_le_three`. Agent F3
  (`RankPreservation.lean`) packages the preservation of the ≤ 3 bound
  under injective rename as `rename_finrank_le_three`.

  This file combines those three inputs into the ambient bound:

      Module.finrank ℚ (ambientInterfaceSpace n hn σ) ≤ 3.

  Proof. `ambientInterfaceSpace n hn σ` is definitionally the image of
  `realInterfaceSpace` under `(rename σ.toFun).toLinearMap`. Agent F3's
  `rename_finrank_le_three` lifts the source bound (≤ 3) through the
  injective rename to the target bound (≤ 3).

  No axioms beyond `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
-/
import PallLean.Paper93.Bridge.AmbientInterfaceSpace
import PallLean.Paper93.Bridge.RankPreservation

namespace PallLean.Paper93.Bridge

open MvPolynomial
open PallLean.Paper93

attribute [local instance] Classical.dec

/-- **Paper §9 Lemma 31 (ambient W_σ form).** The ambient lifted
interface space `ambientInterfaceSpace n hn σ` (Agent F4) has
dimension ≤ 3 in `MvPolynomial (Fin n) ℚ`, for every `n ≥ 4` and every
coordinate embedding `σ : Fin 4 ↪ Fin n`.

Proof strategy.  Unfolding Agent F4's definition, the ambient space is
the image of `realInterfaceSpace` (a dim ≤ 3 subspace of
`MvPolynomial (Fin 4) ℚ`, by Agent A's
`realInterfaceSpace_finrank_le_three`) under the linear map
`(rename σ.toFun).toLinearMap`.  Because `σ` is an embedding (hence
`σ.toFun` is injective), Agent F3's `rename_finrank_le_three`
transports the ≤ 3 bound across the rename, giving the conclusion. -/
theorem ambientInterfaceSpace_finrank_le_three
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    Module.finrank ℚ (ambientInterfaceSpace n hn σ) ≤ 3 := by
  classical
  -- Source submodule is finite-dimensional (Agent A).
  haveI : Module.Finite ℚ (realInterfaceSpace :
      Submodule ℚ (MvPolynomial (Fin wSigmaArity) ℚ)) :=
    realInterfaceSpace_finite
  -- Source ≤ 3 bound (Agent A).
  have h_src :
      Module.finrank ℚ (realInterfaceSpace :
          Submodule ℚ (MvPolynomial (Fin wSigmaArity) ℚ)) ≤ 3 :=
    realInterfaceSpace_finrank_le_three
  -- Preservation of the ≤ 3 bound under injective rename (Agent F3).
  -- `wSigmaArity = 4` definitionally, so this applies directly to σ.
  have h_push :
      Module.finrank ℚ
          (realInterfaceSpace.map
            (MvPolynomial.rename (σ.toFun :
              Fin wSigmaArity → Fin n) :
                MvPolynomial (Fin wSigmaArity) ℚ
                  →ₐ[ℚ] MvPolynomial (Fin n) ℚ).toLinearMap)
        ≤ 3 :=
    rename_finrank_le_three (m := wSigmaArity) (n := n)
      σ realInterfaceSpace h_src
  -- Unfold Agent F4's definition to reveal the push-forward shape.
  simpa [ambientInterfaceSpace] using h_push

/-- Restatement with the paper constant `d₀ = 3`. -/
theorem ambientInterfaceSpace_finrank_le_d₀
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    Module.finrank ℚ (ambientInterfaceSpace n hn σ) ≤ 3 :=
  ambientInterfaceSpace_finrank_le_three n hn σ

end PallLean.Paper93.Bridge
