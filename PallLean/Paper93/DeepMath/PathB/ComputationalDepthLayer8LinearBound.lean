import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8GeneralCircuit
import Mathlib.Data.Finset.Card

/-!
# Layer 8 (general circuits, R2) — an explicit linear lower bound

The honest "R2" rung (`SCOPE_LAYER8_GENERAL_CIRCUITS.md`): an **explicit, concrete** lower bound against
general circuits — every function that depends on all `n` inputs needs size `≥ n`, instantiated for the
`n`-bit AND.

Unlike the Shannon bound (Layer 8 R1, *nonconstructive*), this is a bound on a **named** function.  But it
is only **linear**, and it is *not* the open frontier: the difficulty there is *super-polynomial* bounds,
which no technique reaches (see `SCOPE_LAYER8_EXPLICIT_LOWER_BOUND_FRONTIER.md`).  A linear bound like this
is the floor of explicit circuit complexity, far below `n·log n`, let alone super-poly.

* `inputsOf` / `inputsOf_card_le_size` — the variables occurring in a circuit; their count is `≤` its size.
* `eval_eq_of_agree` — a circuit's output depends only on the inputs occurring in it.
* `size_ge_of_depends_all` — if `c` computes a function depending on all `n` inputs, then `n ≤ c.size`.
* `andAll_needs_linear_size` — the explicit instance: any circuit computing the `n`-bit AND has size `≥ n`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer8

open Finset

/-- The set of input-variable indices occurring in a circuit. -/
def inputsOf {n : ℕ} : Circuit n → Finset (Fin n)
  | .input i => {i}
  | .const _ => ∅
  | .not c => inputsOf c
  | .and c d => inputsOf c ∪ inputsOf d
  | .or c d => inputsOf c ∪ inputsOf d

/-- The number of distinct input variables occurring in a circuit is at most its size. -/
theorem inputsOf_card_le_size {n : ℕ} (c : Circuit n) : (inputsOf c).card ≤ c.size := by
  induction c with
  | input i => simp [inputsOf, Circuit.size]
  | const b => simp [inputsOf, Circuit.size]
  | not c ih => simp only [inputsOf, Circuit.size]; omega
  | and c d ihc ihd =>
      simp only [inputsOf, Circuit.size]
      exact le_trans (Finset.card_union_le _ _) (by omega)
  | or c d ihc ihd =>
      simp only [inputsOf, Circuit.size]
      exact le_trans (Finset.card_union_le _ _) (by omega)

/-- A circuit's output depends only on the inputs occurring in it: two inputs agreeing on `inputsOf c`
yield the same output. -/
theorem eval_eq_of_agree {n : ℕ} (c : Circuit n) (x y : Fin n → Bool)
    (h : ∀ j ∈ inputsOf c, x j = y j) : c.eval x = c.eval y := by
  induction c with
  | input i => exact h i (Finset.mem_singleton_self i)
  | const b => rfl
  | not c ih => simp only [Circuit.eval]; rw [ih h]
  | and c d ihc ihd =>
      simp only [Circuit.eval]
      rw [ihc (fun j hj => h j (Finset.mem_union_left _ hj)),
          ihd (fun j hj => h j (Finset.mem_union_right _ hj))]
  | or c d ihc ihd =>
      simp only [Circuit.eval]
      rw [ihc (fun j hj => h j (Finset.mem_union_left _ hj)),
          ihd (fun j hj => h j (Finset.mem_union_right _ hj))]

/-- `f` **depends on** input `i`: two inputs agreeing off `i` give different outputs. -/
def DependsOn {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y

/-- **Explicit linear lower bound.**  Any circuit computing a function that depends on all `n` inputs has
size at least `n` (each relevant variable must occur as a leaf). -/
theorem size_ge_of_depends_all {n : ℕ} (f : (Fin n → Bool) → Bool) (c : Circuit n)
    (hc : Computes c f) (hdep : ∀ i, DependsOn f i) : n ≤ c.size := by
  have hall : ∀ i, i ∈ inputsOf c := by
    intro i
    by_contra hi
    obtain ⟨x, y, hagree, hfxy⟩ := hdep i
    have heq : c.eval x = c.eval y :=
      eval_eq_of_agree c x y (fun j hj => hagree j (by rintro rfl; exact hi hj))
    rw [hc x, hc y] at heq
    exact hfxy heq
  have hcard : (Finset.univ : Finset (Fin n)).card ≤ (inputsOf c).card :=
    Finset.card_le_card (fun i _ => hall i)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  exact le_trans hcard (inputsOf_card_le_size c)

/-- The `n`-bit AND function. -/
def andAll (n : ℕ) : (Fin n → Bool) → Bool := fun x => decide (∀ i, x i = true)

/-- The `n`-bit AND depends on every input. -/
theorem dependsOn_andAll {n : ℕ} (i : Fin n) : DependsOn (andAll n) i := by
  refine ⟨fun _ => true, Function.update (fun _ => true) i false, ?_, ?_⟩
  · intro j hj; simp [Function.update_apply, hj]
  · have h1 : andAll n (fun _ => true) = true := by simp [andAll]
    have h2 : andAll n (Function.update (fun _ => true) i false) = false := by
      simp only [andAll, decide_eq_false_iff_not, not_forall]
      exact ⟨i, by simp⟩
    rw [h1, h2]; decide

/-- **Explicit linear lower bound for AND.**  Any general circuit computing the `n`-bit AND has size `≥ n`.
(Concrete and explicit — but only linear; not the open super-polynomial frontier.) -/
theorem andAll_needs_linear_size {n : ℕ} (c : Circuit n) (hc : Computes c (andAll n)) : n ≤ c.size :=
  size_ge_of_depends_all (andAll n) c hc (fun i => dependsOn_andAll i)

end PallLean.Paper93.DeepMath.PathB.Layer8

#print axioms PallLean.Paper93.DeepMath.PathB.Layer8.size_ge_of_depends_all
#print axioms PallLean.Paper93.DeepMath.PathB.Layer8.andAll_needs_linear_size
