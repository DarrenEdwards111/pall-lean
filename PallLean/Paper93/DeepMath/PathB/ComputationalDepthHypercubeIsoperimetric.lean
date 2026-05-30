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

/-! ## Splitting on the first coordinate (toward the recurrence) -/

theorem flip_cons_zero (b : ZMod 2) (y : Fin k → ZMod 2) :
    flip (Fin.cons b y) 0 = Fin.cons (b + 1) y := by
  unfold flip; rw [Fin.cons_zero, Fin.update_cons_zero]

theorem flip_cons_succ (b : ZMod 2) (y : Fin k → ZMod 2) (i : Fin k) :
    flip (Fin.cons b y) i.succ = Fin.cons b (flip y i) := by
  unfold flip; rw [Fin.cons_succ, ← Fin.cons_update]

/-- The `b`-half of `S`: the points `y` with `cons b y ∈ S`. -/
def half (S : Finset (Fin (k+1) → ZMod 2)) (b : ZMod 2) : Finset (Fin k → ZMod 2) :=
  Finset.univ.filter (fun y => Fin.cons b y ∈ S)

@[simp] theorem mem_half {S : Finset (Fin (k+1) → ZMod 2)} {b : ZMod 2} {y : Fin k → ZMod 2} :
    y ∈ half S b ↔ Fin.cons b y ∈ S := by
  simp [half]

/-- **The cons-bijection.**  Restricting to `x 0 = b` and taking tails is a bijection
onto the `Φ`-filtered points of `Q_k`. -/
theorem card_filter_x0 (b : ZMod 2) (Φ : (Fin k → ZMod 2) → Prop) [DecidablePred Φ] :
    (Finset.univ.filter (fun x : Fin (k+1) → ZMod 2 => x 0 = b ∧ Φ (Fin.tail x))).card
      = (Finset.univ.filter Φ).card := by
  refine Finset.card_bij' (fun x _ => Fin.tail x) (fun y _ => Fin.cons b y) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, hx.2.2⟩
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, Fin.cons_zero _ _, ?_⟩
    rw [Fin.tail_cons]; exact hy.2
  · intro x hx
    have hb : x 0 = b := (Finset.mem_filter.mp hx).2.1
    exact hb ▸ Fin.cons_self_tail x
  · intro y _
    simp only [Fin.tail_cons]

end PallLean.Paper93.DeepMath.PathB.Hypercube
