import PallLean.Paper93.DeepMath.NFrame.NegLogConvex
import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.DetFinOne
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Pi

/-!
# N-Frame: convexity of the 1×1 barrier on `{A : A 0 0 > 0}`

For 1×1 matrices, the barrier `B(A) = -log(det A)` reduces to
`B(A) = -log(A 0 0)`. We prove this scalar map is convex on the
open half-space `{A : Matrix (Fin 1) (Fin 1) ℝ | 0 < A 0 0}`, as an
incremental step toward full `-log det` convexity on the PosDef cone.

The proof factors the map through a linear extraction
`A ↦ A 0 0` (a composition of two coordinate projections, each a linear
`LinearMap.proj`) and applies `ConvexOn.comp_linearMap` to
`neg_log_convexOn_Ioi`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- For 1×1 matrices, `barrier A = -log(A 0 0)`, which is convex on `{A : A 0 0 > 0}`.
    This is a specific convexity statement in the finite-dim case n=1, as an
    incremental step toward the full `-log det` convexity on the PosDef cone. -/
theorem barrier_fin_one_convex_on_pos :
    ConvexOn ℝ
      ({A : Matrix (Fin 1) (Fin 1) ℝ | 0 < A 0 0})
      (fun A => barrier A) := by
  -- barrier A = -log A.det = -log (A 0 0)
  have h_eq : (fun A : Matrix (Fin 1) (Fin 1) ℝ => barrier A) =
              (fun A : Matrix (Fin 1) (Fin 1) ℝ => -Real.log (A 0 0)) := by
    funext A
    unfold barrier
    rw [Matrix.det_fin_one]
  rw [h_eq]
  -- Build the linear extraction `A ↦ A 0 0` as a composition of two
  -- `LinearMap.proj` coordinate projections.
  -- Outer projection: `(Fin 1 → ℝ) →ₗ[ℝ] ℝ` picks entry `0`.
  let projOuter : (Fin 1 → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0
  -- Inner projection: `Matrix (Fin 1) (Fin 1) ℝ →ₗ[ℝ] (Fin 1 → ℝ)` picks row `0`.
  -- Here `Matrix (Fin 1) (Fin 1) ℝ` unfolds to `Fin 1 → Fin 1 → ℝ`.
  let projInner : Matrix (Fin 1) (Fin 1) ℝ →ₗ[ℝ] (Fin 1 → ℝ) :=
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => (Fin 1 → ℝ)) 0
  -- Full extraction `g A = A 0 0`.
  let g : Matrix (Fin 1) (Fin 1) ℝ →ₗ[ℝ] ℝ := projOuter.comp projInner
  -- `g` acts as `fun A => A 0 0`.
  have hg_apply : ∀ A : Matrix (Fin 1) (Fin 1) ℝ, g A = A 0 0 := by
    intro A; rfl
  -- `neg_log_convexOn_Ioi` gives convexity of `fun x => -Real.log x` on `(0, ∞)`.
  have hneg : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => -Real.log x) :=
    neg_log_convexOn_Ioi
  -- Apply `ConvexOn.comp_linearMap` to transport convexity through `g`.
  have hcomp :
      ConvexOn ℝ (g ⁻¹' Set.Ioi (0 : ℝ))
        ((fun x => -Real.log x) ∘ g) :=
    hneg.comp_linearMap g
  -- Identify the preimage set with `{A | 0 < A 0 0}`.
  have hset :
      (g ⁻¹' Set.Ioi (0 : ℝ)) =
        ({A : Matrix (Fin 1) (Fin 1) ℝ | 0 < A 0 0}) := by
    ext A
    simp [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq, hg_apply]
  -- Identify the composed function with `fun A => -Real.log (A 0 0)`.
  have hfun :
      ((fun x => -Real.log x) ∘ g) =
        (fun A : Matrix (Fin 1) (Fin 1) ℝ => -Real.log (A 0 0)) := by
    funext A
    show -Real.log (g A) = -Real.log (A 0 0)
    rw [hg_apply]
  rw [hset, hfun] at hcomp
  exact hcomp

end PallLean.Paper93.DeepMath.NFrame
