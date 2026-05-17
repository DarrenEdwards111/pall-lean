import PallLean.Paper93.DeepMath.PathC.PiPlusPayloadCloseout

/-!
# Local warning for the sharp NP-window inclusion

The remaining NP payload is not a harmless monotonicity fact.  A two-variable
Boolean-local calculation shows the naive expectation can fail: a source
one-derivative row can contain the mixed `X₀X₁`/`X₀` direction while the
Boolean-projected target rows for the transformed local product live in the
`1, X₁` span.

This does **not** refute the full Cook--Levin paper-scale theorem, because that
still has global coordinate/block structure.  It records the precise local shape
that any real proof of the NP inclusion must overcome; the proof cannot be by a
formal same-window span argument alone.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP

attribute [local instance] Classical.dec

/-- The expanded local row produced by differentiating the Boolean pair-product
in `X₀`, shifting by `X₀`, and multilinear-projecting.  The point of recording
it separately is that it visibly contains an `X₀`/`X₀X₁` component. -/
noncomputable def localExpandedSourceNPRow : MvPolynomial (Fin 2) ℚ :=
  (-2 : ℚ) • (X (0 : Fin 2) * X (1 : Fin 2)) +
    (2 : ℚ) • X (0 : Fin 2) + X (1 : Fin 2) - 1

/-- The expanded source row is not in the two-dimensional span `⟨1, X₁⟩`.
Evaluating at `(X₀,X₁)=(0,0)` and `(1,0)` separates it from every polynomial
independent of `X₀`. -/
theorem localExpandedSourceNPRow_not_mem_one_X_one_span :
    ¬ ∃ c d : ℚ,
      localExpandedSourceNPRow =
        (C c + C d * X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ) := by
  rintro ⟨c, d, h⟩
  have h0 := congrArg
    (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (0 : ℚ) else 0)) h
  have h1 := congrArg
    (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1 : ℚ) else 0)) h
  simp [localExpandedSourceNPRow] at h0 h1
  linarith

/-! ## Axiom audit anchors -/

#print axioms localExpandedSourceNPRow_not_mem_one_X_one_span

end PallLean.Paper93.DeepMath.PathC
