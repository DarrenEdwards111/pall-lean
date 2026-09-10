import GodMoveCircuitNormalization
import PallLean.PiStarConcrete

/-!
# Boolean face restriction and injective variable embedding

These helpers connect the existing constant-substitution map to its exact
Boolean semantics. Fixing coordinates to Boolean constants evaluates the
original polynomial on the corresponding face of the Boolean cube. An
injective renaming preserves multilinearity, and evaluation of a renamed
polynomial is evaluation on the pulled-back assignment.

No SAT correctness, efficiency, or rank premise is inserted into these
algebraic identities. Rank transport requires its separate hypotheses.
-/

namespace GodMoveBooleanFace

open MvPolynomial MultilinearSPDP PiStarConcrete GodMoveBooleanInterpolation

/-- Evaluation of the concrete substitution is evaluation on the designated
Boolean face. The source polynomial need not be multilinear. -/
theorem eval_piSubst_boolean {n : ℕ}
    (keep : Fin n → Prop) [DecidablePred keep]
    (fixed : Assignment n) (p : Poly n) (a : Assignment n) :
    eval (booleanPoint a) (piSubst keep (fun j => bit (fixed j)) p) =
      eval (booleanPoint (fun j => if keep j then a j else fixed j)) p := by
  change (aeval (booleanPoint a) : Poly n →ₐ[ℚ] ℚ)
      (aeval (substFn keep (fun j => bit (fixed j))) p) = _
  rw [comp_aeval_apply]
  change aeval (fun j => (aeval (booleanPoint a) : Poly n →ₐ[ℚ] ℚ)
      (substFn keep (fun j => bit (fixed j)) j)) p =
    aeval (booleanPoint (fun j => if keep j then a j else fixed j)) p
  apply congrArg (fun point : Fin n → ℚ => aeval point p)
  funext j
  by_cases hj : keep j <;> simp [substFn, booleanPoint, hj]

/-- Fixed points of multilinear projection are exactly the multilinear
polynomials. -/
theorem mlProj_eq_self_iff {n : ℕ} (p : Poly n) :
    mlProj p = p ↔ IsMultilinear p := by
  classical
  constructor
  · intro h a ha i
    have ha' : a ∈ (mlProj p).support := by rwa [h]
    change a ∈ (Finsupp.filter Finsupp.IsMultilinear p).support at ha'
    rw [Finsupp.support_filter] at ha'
    exact (Finset.mem_filter.mp ha').2 i
  · exact mlProj_of_isMultilinear p

/-- An injective embedding of variables does not identify two exponents,
so it preserves multilinearity. -/
theorem isMultilinear_rename {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (p : Poly n) (hp : IsMultilinear p) :
    IsMultilinear (rename f p) := by
  apply (mlProj_eq_self_iff _).mp
  rw [mlProj_rename f hf, mlProj_of_isMultilinear p hp]

/-- Renaming variables evaluates the original polynomial on the assignment
pulled back along that renaming; injectivity is not needed for evaluation. -/
theorem eval_rename_boolean {n m : ℕ}
    (f : Fin n → Fin m) (p : Poly n) (a : Assignment m) :
    eval (booleanPoint a) (rename f p) =
      eval (booleanPoint (fun i => a (f i))) p := by
  exact eval_rename f (booleanPoint a) p

end GodMoveBooleanFace

#print axioms GodMoveBooleanFace.eval_piSubst_boolean
#print axioms GodMoveBooleanFace.mlProj_eq_self_iff
#print axioms GodMoveBooleanFace.isMultilinear_rename
#print axioms GodMoveBooleanFace.eval_rename_boolean
