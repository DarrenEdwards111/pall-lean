import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

namespace List

variable {α β : Type*} [AddCommMonoid β]

theorem sum_map_eq_sum_fin_getElem (l : List α) (f : α → β) :
    (l.map f).sum = ∑ i : Fin l.length, f l[i] := by
  conv_lhs => rw [← List.ofFn_getElem_eq_map l f]
  rw [List.sum_ofFn]; rfl

theorem sum_map_eq_sum_fin_get (l : List α) (f : α → β) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  simp only [List.get_eq_getElem]; exact sum_map_eq_sum_fin_getElem l f

end List
