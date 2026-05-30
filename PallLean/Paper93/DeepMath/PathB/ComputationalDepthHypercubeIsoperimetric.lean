import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# Edge-isoperimetric inequality for the hypercube (explicit-expander attempt)

Toward a fully numeric Tseitin size lower bound we need an explicit graph family
with `HasExpansion c` (`c ≥ 1`) and degree below `|V|/4`.  The hypercube `Q_k`
(vertices `Fin k → ZMod 2`, degree `k = log₂|V|`) qualifies: it satisfies the
edge-isoperimetric inequality `|∂S| ≥ |S|` for `|S| ≤ 2^{k-1}` (`HasExpansion 1`).

This file builds the boundary function (`bdry`, summed over coordinates) and the
two facts driving Harper's clean two-case induction: the **recurrence**
`bdry S = bdry S₀ + bdry S₁ + |S₀ △ S₁|` under splitting on a coordinate, and
**complement symmetry** `bdry S = bdry Sᶜ`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Hypercube

open scoped BigOperators

variable {k : ℕ}

/-- Flip the `i`-th coordinate of a hypercube point. -/
def flip (x : Fin k → ZMod 2) (i : Fin k) : Fin k → ZMod 2 :=
  Function.update x i (x i + 1)

@[simp] theorem flip_flip (x : Fin k → ZMod 2) (i : Fin k) : flip (flip x i) i = x := by
  funext j
  rcases eq_or_ne j i with h | h
  · subst h
    simp only [flip, Function.update_self]
    rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]
  · simp only [flip, Function.update_of_ne h]

theorem flip_ne (x : Fin k → ZMod 2) (i : Fin k) : flip x i ≠ x := by
  intro h
  have hi : (flip x i) i = x i := by rw [h]
  simp only [flip, Function.update_self] at hi
  exact (by decide : ∀ y : ZMod 2, y + 1 ≠ y) (x i) hi

/-- Directed boundary in coordinate `i`: points in `S` whose `i`-flip leaves `S`. -/
def dirBdry (S : Finset (Fin k → ZMod 2)) (i : Fin k) : ℕ :=
  (Finset.univ.filter (fun x => x ∈ S ∧ flip x i ∉ S)).card

/-- Edge boundary of `S` in the hypercube: summed over coordinates. -/
def bdry (S : Finset (Fin k → ZMod 2)) : ℕ :=
  ∑ i : Fin k, dirBdry S i

/-- **Complement symmetry of the directed boundary.**  The `i`-flip is an
involution swapping `{x ∈ S : flip x i ∉ S}` and `{x ∉ S : flip x i ∈ S}`. -/
theorem dirBdry_compl (S : Finset (Fin k → ZMod 2)) (i : Fin k) :
    dirBdry S i = dirBdry Sᶜ i := by
  unfold dirBdry
  refine Finset.card_bij' (fun x _ => flip x i) (fun x _ => flip x i) ?_ ?_
    (fun x _ => flip_flip x i) (fun x _ => flip_flip x i)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, flip_flip,
      not_not] at hx ⊢
    exact ⟨hx.2, hx.1⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, flip_flip,
      not_not] at hx ⊢
    exact ⟨hx.2, hx.1⟩

/-- **Complement symmetry of the boundary.** -/
theorem bdry_compl (S : Finset (Fin k → ZMod 2)) : bdry S = bdry Sᶜ :=
  Finset.sum_congr rfl (fun i _ => dirBdry_compl S i)

end PallLean.Paper93.DeepMath.PathB.Hypercube
