import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LayerCompose

/-!
# Per-point composition: the composed polynomial computes the gate of the subgate values

`…ACC0LayerCompose` built `compPoly P σ` (the boosted `OR`-layer over subgate approximants `P_j`) and bounded its
degree.  This file discharges the **per-point composition** — the `hcomp` hypothesis of `…ACC0ErrorAccumulation`: if
each subgate polynomial `P_j` computes its Boolean subgate `h_j` at the point `x`, then the composed polynomial
evaluates to the boosted `OR` of the subgate *values* `(h_1(x), …, h_k(x))`.

So correctness composes exactly where the subgates are correct: `eval (compPoly P σ) x = OR`-predictor`(h_·(x))`.
This is the bridge between the *degree* composition (`…ACC0LayerCompose`), the *error* composition
(`…ACC0ErrorAccumulation`), and the actual Boolean computation — it lets the abstract error-accumulation lemma apply
to the real polynomial substitution.

## What is proved (clean axioms, no `sorry`)

* `boost_formula` — `1 − ∏_l (1 − pv w (σ l)) = boolToZMod 2 (boostPredict σ w)` for any subgate-output vector `w`.
* `eval_compPoly_of_subgates` — if `∀ j, eval (P_j) x = boolToZMod 2 (h_j x)`, then
  `eval (compPoly P σ) x = boolToZMod 2 (boostPredict σ (fun j => h_j x))`: the composed polynomial computes the
  boosted `OR` of the subgate values.

## Honest scope

This is the per-point composition for an `OR` layer (the `AND` layer is the affine dual, `…ACC0AndBasisBridge`).  It
discharges the structural `hcomp` hypothesis: the composed polynomial really computes the gate of the subgate values.
Combined with degree composition (`…ACC0LayerCompose`) and error accumulation (`…ACC0ErrorAccumulation`), the three
give one layer of the Razborov–Smolensky depth composition.  The full inductive assembly over a constant-depth
circuit — and the per-gate boosting that makes the error small, and the `MOD` layer — remain the rest of the
Beigel–Tarui/Yao front half, **Wall 1**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositionCorrect

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm
open PallLean.Paper93.DeepMath.PathB.ACC0BasisBridge
open PallLean.Paper93.DeepMath.PathB.ACC0LayerCompose

variable {n k t : ℕ}

/-- **The boosting formula (proved): `1 − ∏_l (1 − pv w (σ l)) = boolToZMod 2 (boostPredict σ w)`** — both sides are
`eval (boostPoly σ)` at `w`. -/
theorem boost_formula (w : Fin k → Bool) (σ : Fin t → Finset (Fin k)) :
    1 - ∏ l, (1 - pv w (σ l)) = boolToZMod 2 (boostPredict σ w) :=
  (eval_boostPoly w σ).symm.trans (eval_boostPoly_eq w σ)

/-- **Per-point composition (proved): the composed polynomial computes the boosted `OR` of the subgate values.**  If
each subgate poly `P_j` computes `h_j` at `x`, then `compPoly P σ` evaluates to the boosted `OR`-predictor on
`(h_1(x), …, h_k(x))`. -/
theorem eval_compPoly_of_subgates (x : Fin n → Bool) (P : Fin k → MvPolynomial (Fin n) (ZMod 2))
    (h : Fin k → (Fin n → Bool) → Bool)
    (hP : ∀ j, eval (fun i => boolToZMod 2 (x i)) (P j) = boolToZMod 2 (h j x))
    (σ : Fin t → Finset (Fin k)) :
    eval (fun i => boolToZMod 2 (x i)) (compPoly P σ)
      = boolToZMod 2 (boostPredict σ (fun j => h j x)) := by
  rw [eval_compPoly]
  have hsum : ∀ l, (∑ j ∈ σ l, eval (fun i => boolToZMod 2 (x i)) (P j))
      = pv (fun j => h j x) (σ l) := by
    intro l
    show (∑ j ∈ σ l, eval (fun i => boolToZMod 2 (x i)) (P j))
        = ∑ j ∈ σ l, (if h j x then (1 : ZMod 2) else 0)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hP j]
    rfl
  rw [Finset.prod_congr rfl (fun l _ => by rw [hsum l])]
  exact boost_formula (fun j => h j x) σ

end PallLean.Paper93.DeepMath.PathB.ACC0CompositionCorrect

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositionCorrect.boost_formula
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositionCorrect.eval_compPoly_of_subgates
