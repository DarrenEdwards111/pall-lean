import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.Rename

open MvPolynomial

noncomputable def myG (j : Fin 3) : MvPolynomial (Fin 2) ℤ :=
  if h : ∃ i : Fin 2, (Fin.castSucc i) = j then X h.choose else 0

example (s : Fin 3 →₀ ℕ) :
    (s.prod (fun j k => myG j ^ k) = 0) ∨
    (∃ t : Fin 2 →₀ ℕ, s.prod (fun j k => myG j ^ k) = monomial t 1) := by
  induction s using Finsupp.induction with
  | zero => right; exact ⟨0, by simp [Finsupp.prod_zero_index]⟩
  | single_add j b s hjs hb ih =>
    -- What does the goal look like here?
    sorry
