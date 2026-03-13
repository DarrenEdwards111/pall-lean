/-
  BoolEval.lean — Boolean evaluation of multivariate polynomials

  Defines how a polynomial over ℚ with variables in Fin n computes
  a Boolean function: evaluate at Boolean inputs (0/1), then threshold.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

namespace BoolEval

open MvPolynomial

/-- Evaluate a polynomial at a Boolean input (mapping Bool to ℚ). -/
def boolToRat : Bool → ℚ
  | false => 0
  | true => 1

/-- Evaluate polynomial p at Boolean input x. -/
noncomputable def evalBool {n : ℕ} (p : MvPolynomial (Fin n) ℚ)
    (x : Fin n → Bool) : ℚ :=
  MvPolynomial.eval (fun i => boolToRat (x i)) p

/-- A polynomial p computes Boolean function f if:
    for all Boolean inputs x, evalBool p x = boolToRat (f x). -/
def computes {n : ℕ} (p : MvPolynomial (Fin n) ℚ)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, evalBool p x = boolToRat (f x)

/-- Two polynomials that compute the same function agree on all
    Boolean inputs. -/
theorem computes_unique {n : ℕ} {p q : MvPolynomial (Fin n) ℚ}
    {f : (Fin n → Bool) → Bool}
    (hp : computes p f) (hq : computes q f) :
    ∀ x, evalBool p x = evalBool q x :=
  fun x => by rw [hp x, hq x]

/-- If p computes f and q computes g, and f ≠ g, then p and q
    disagree on some Boolean input. -/
theorem computes_disagree {n : ℕ} {p q : MvPolynomial (Fin n) ℚ}
    {f g : (Fin n → Bool) → Bool}
    (hp : computes p f) (hq : computes q g) (hfg : f ≠ g) :
    ∃ x, evalBool p x ≠ evalBool q x := by
  by_contra h
  push_neg at h
  apply hfg
  funext x
  have := h x
  rw [hp x, hq x] at this
  unfold boolToRat at this
  cases hf : f x <;> cases hg : g x <;> simp_all

end BoolEval
