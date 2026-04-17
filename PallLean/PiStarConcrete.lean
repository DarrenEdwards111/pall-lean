/-
  PiStarConcrete.lean — concrete variable-substitution gauge
  ============================================================

  ## Goal

  Construct a concrete ℚ-linear endomorphism `piSubst` on
  `MvPolynomial (Fin N) ℚ` and verify it satisfies structural
  properties (idempotency, ℚ-linearity). This is the simplest nontrivial
  candidate for Π⋆ from paper Definition 6:

    > "ΠΦ ... (i) restricting administrative/tableau blocks v to fixed
    >  constants, (ii) projecting to the clause-sheet blocks u, (iii)
    >  applying a fixed block-local relabeling/basis normalization."

  We implement (i) — variable substitution — via MvPolynomial.aeval.

  ## Structure

  Given:
  - A predicate `keep : Fin N → Prop` identifying which variables to keep
  - A substitution value `val : Fin N → ℚ` for variables not kept

  The gauge `piSubst keep val` evaluates each X_i to:
  - X_i if `keep i` holds
  - C (val i) if `keep i` fails

  This is a ℚ-algebra homomorphism; its underlying ℚ-linear map is our
  candidate gauge endomorphism.

  ## Status: ON-CHAIN, axiom-free, no sorry.
-/

import PallLean.MultilinearSPDP
import PallLean.GaugeMonotonicity
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

namespace PiStarConcrete

open MvPolynomial

variable {N : ℕ}

/-! ## Section 1: The substitution algebra homomorphism -/

/-- **Substitution map**: `i ↦ X i` if `keep i` else `C (val i)`. -/
noncomputable def substFn (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) (i : Fin N) :
    MvPolynomial (Fin N) ℚ :=
  if keep i then X i else C (val i)

/-- **Substitution gauge** (algebra homomorphism form): replace each
non-kept variable by a constant. -/
noncomputable def substAlgHom (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) :
    MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  aeval (substFn keep val)

/-- **Substitution gauge** (ℚ-linear map form): the underlying ℚ-linear
endomorphism of `substAlgHom`. -/
noncomputable def piSubst (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ :=
  (substAlgHom keep val).toLinearMap

/-! ## Section 2: Basic properties -/

/-- `piSubst` evaluates `X i` to either `X i` or `C (val i)`. -/
theorem piSubst_X (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) (i : Fin N) :
    piSubst keep val (X i) = if keep i then X i else C (val i) := by
  unfold piSubst substAlgHom substFn
  rw [AlgHom.toLinearMap_apply, aeval_X]

/-- `piSubst keep val (C c) = C c` (constants are fixed). -/
theorem piSubst_C (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) (c : ℚ) :
    piSubst keep val (C c) = C c := by
  unfold piSubst substAlgHom
  rw [AlgHom.toLinearMap_apply, aeval_C]
  rfl

/-- **`piSubst keep val = id` when all variables are kept.** -/
theorem piSubst_all_kept (keep : Fin N → Prop) [DecidablePred keep] (hall : ∀ i, keep i) (val : Fin N → ℚ) :
    piSubst keep val = LinearMap.id := by
  unfold piSubst substAlgHom substFn
  have : (fun i : Fin N => if keep i then (X i : MvPolynomial (Fin N) ℚ) else C (val i)) =
      X := by
    funext i
    simp [hall i]
  rw [this]
  rw [show (aeval X : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ) =
        AlgHom.id ℚ _ from aeval_X_left]
  rfl

/-- **`substAlgHom` is idempotent as an algebra homomorphism.** -/
theorem substAlgHom_idempotent (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) :
    (substAlgHom keep val).comp (substAlgHom keep val) = substAlgHom keep val := by
  apply MvPolynomial.algHom_ext
  intro i
  -- Both sides applied to X i.
  unfold substAlgHom
  simp only [AlgHom.comp_apply, aeval_X]
  -- Goal: aeval (substFn keep val) (substFn keep val i) = substFn keep val i
  unfold substFn
  by_cases hi : keep i
  · simp [hi]
  · simp [hi]

/-- **`piSubst keep val` is idempotent** (a projection gauge).
Substituting twice is the same as substituting once, because after the
first substitution, each non-kept variable is replaced by a constant,
and constants are fixed by subsequent substitutions. -/
theorem piSubst_idempotent (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) :
    (piSubst keep val) ∘ₗ (piSubst keep val) = piSubst keep val := by
  apply LinearMap.ext
  intro p
  -- Goal: (piSubst keep val) ((piSubst keep val) p) = piSubst keep val p
  show (substAlgHom keep val).toLinearMap ((substAlgHom keep val).toLinearMap p)
        = (substAlgHom keep val).toLinearMap p
  have h := substAlgHom_idempotent keep val
  have : (substAlgHom keep val) ((substAlgHom keep val) p) = substAlgHom keep val p :=
    congrArg (fun f : _ →ₐ[ℚ] _ => f p) h
  simpa [AlgHom.toLinearMap_apply] using this

/-- **`piSubst keep val` is a projection gauge.** -/
theorem piSubst_isProjectionGauge (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) :
    GaugeMonotonicity.IsProjectionGauge (piSubst keep val) :=
  ⟨piSubst_idempotent keep val⟩

end PiStarConcrete
