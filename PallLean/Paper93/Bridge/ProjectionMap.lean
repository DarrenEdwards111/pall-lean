/-
  PallLean/Paper93/Bridge/ProjectionMap.lean

  Paper §9.3.1 — rank-monotone projection map bridge.

  Paper text: the canonicalization of §9.3.1 supplies a projection map
  `π` from the ambient polynomial space `MvPolynomial (Fin N) ℚ` onto
  the compiled-basis image ("FiniteDim target"). Under the compiled
  coefficient basis `U^B_{≤ℓ}` the columns of `M^B_{κ,ℓ}` are indexed
  by a finite family of block-admissible shift monomials, so the image
  is a finite-dimensional submodule of the ambient polynomial space.

  This file (Agent F2 of 10) ships only the abstract bridge interface:

    * `compiledTarget N B ℓ` — a submodule of `MvPolynomial (Fin N) ℚ`
      playing the role of the "compiled-basis target space". In this
      minimal abstract bridge we model it as the full submodule `⊤`,
      which is the smallest claim compatible with the downstream
      consumer (`π_range : LinearMap.range π ≤ compiledTarget`). Any
      later concretisation (e.g. the span of `compiledCoefficientBasis
      B ℓ` from `Paper93.CompiledCoefficientBasis`) is a submodule of
      `⊤`, so strengthening `compiledTarget` refines the bridge without
      breaking downstream callers.

    * `π B ℓ` — the projection map. We use `LinearMap.id` as the
      concrete model, per the task's explicit allowance ("use
      `LinearMap.id` or truncation as concrete model if full projection
      is too complex"). This keeps the bridge kernel-only (no `sorry`,
      no bespoke axioms) while preserving the two downstream API
      contracts:

        - `π_range` : `LinearMap.range (π B ℓ) ≤ compiledTarget N B ℓ`
        - `π_rank_le` : `Module.finrank ℚ (Submodule.map (π B ℓ) W) ≤
                        Module.finrank ℚ W`

      In particular, `π` is rank-nonincreasing on every submodule `W`
      of `MvPolynomial (Fin N) ℚ`. This is the rank-monotonicity
      property referenced in §9.3.1's canonicalization argument, and
      is what the Route C ⇒ Route A truncation bridge needs to invoke.

  All proofs are elementary (they reduce to `Submodule.finrank_map_le`
  or to `le_top`/`LinearMap.range_id`), so the whole file is
  kernel-only:

      #print axioms ⟹ [propext, Classical.choice, Quot.sound]

  Rules:
    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic
import PallLean.SPDPDefs

namespace PallLean
namespace Paper93
namespace Bridge

open MvPolynomial

/-! ## Compiled-basis target submodule

For a block partition `B : SPDP.BlockPartition N` and a degree bound
`ℓ : ℕ`, the compiled-basis target is a submodule of the ambient
polynomial space `MvPolynomial (Fin N) ℚ`. At the bridge level we take
it to be the full submodule `⊤`; a downstream refinement will identify
it with the span of the compiled column family `U^B_{≤ℓ}` (see
`Paper93.CompiledCoefficientBasis.compiledCoefficientBasis`). -/
def compiledTarget (N : ℕ) (B : SPDP.BlockPartition N) (ℓ : ℕ) :
    Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  let _ := B
  let _ := ℓ
  (⊤ : Submodule ℚ (MvPolynomial (Fin N) ℚ))

/-! ## The projection map `π`

Paper §9.3.1 specifies a rank-monotone projection onto the compiled
basis. At this bridge layer we model `π` as `LinearMap.id`. This
satisfies the two downstream API contracts (range containment and
rank-monotonicity on every submodule) and is kernel-only. -/
noncomputable def π {N : ℕ} (B : SPDP.BlockPartition N) (ℓ : ℕ) :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ :=
  -- Silence unused-argument linter: the bridge-layer model does not
  -- use `B` or `ℓ`, but they are part of the interface.
  let _ := B
  let _ := ℓ
  LinearMap.id

/-! ## Range containment: `π` lands in the compiled target -/

/-- The range of `π` is contained in the compiled target submodule.
Since `compiledTarget N B ℓ = ⊤` at this bridge layer, this is the
trivial `le_top` inequality. -/
theorem π_range {N : ℕ} {B : SPDP.BlockPartition N} {ℓ : ℕ} :
    LinearMap.range (π B ℓ) ≤ compiledTarget N B ℓ := by
  -- `compiledTarget` is definitionally `⊤`; everything sits below `⊤`.
  exact le_top

/-! ## Rank monotonicity on submodules -/

/-- **Rank monotonicity of `π` (Paper §9.3.1).**

For any submodule `W ⊆ MvPolynomial (Fin N) ℚ`, the image submodule
`Submodule.map (π B ℓ) W` has finrank at most that of `W`. This is
the rank-monotonicity property stated in the paper's canonicalization
§9.3.1 and invoked by the Route C ⇒ Route A truncation bridge.

Proof: every linear map is rank-nonincreasing on every submodule
(`Submodule.finrank_map_le`). -/
theorem π_rank_le {N : ℕ} {B : SPDP.BlockPartition N} {ℓ : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ)) [Module.Finite ℚ W] :
    Module.finrank ℚ (Submodule.map (π (B := B) (ℓ := ℓ)) W) ≤
      Module.finrank ℚ W := by
  -- Standard mathlib fact: linear maps are rank-nonincreasing on
  -- finite submodules.
  exact Submodule.finrank_map_le (π (B := B) (ℓ := ℓ)) W

/-! ## Additional sanity lemmas (kernel-only, useful for downstream callers) -/

/-- `π` is rank-nonincreasing on any **finite-dimensional** submodule.
This is just `π_rank_le` with the `Module.Finite` hypothesis named
rather than instance-resolved, useful at call sites where the
finiteness witness is derived manually. -/
theorem π_rank_le_of_finite {N : ℕ} {B : SPDP.BlockPartition N} {ℓ : ℕ}
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ)) (hW : Module.Finite ℚ W) :
    Module.finrank ℚ (Submodule.map (π (B := B) (ℓ := ℓ)) W) ≤
      Module.finrank ℚ W := by
  letI : Module.Finite ℚ W := hW
  exact π_rank_le (B := B) (ℓ := ℓ) W

/-- The compiled target is (at this bridge layer) the full submodule.
This equation is what lets downstream refinements replace
`compiledTarget` by a concrete compiled-basis span without touching
the interface. -/
theorem compiledTarget_eq_top {N : ℕ} (B : SPDP.BlockPartition N) (ℓ : ℕ) :
    compiledTarget N B ℓ = (⊤ : Submodule ℚ (MvPolynomial (Fin N) ℚ)) :=
  rfl

/-- `π` is definitionally `LinearMap.id` at the bridge layer. -/
theorem π_eq_id {N : ℕ} (B : SPDP.BlockPartition N) (ℓ : ℕ) :
    π (B := B) (ℓ := ℓ) =
      (LinearMap.id : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ) :=
  rfl

end Bridge
end Paper93
end PallLean
