import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAndreevShrinkageRoute

/-!
# A non‑counting structural leaf bound — relevance / sensitivity

The Nečiporuk method is *counting* (distinct subfunctions).  A **non‑counting** structural argument instead says:
*every formula has a structural weakness, and the explicit function provably lacks it.*  This file formalizes the
base structural engine of that style — the **relevance** (sensitivity) leaf bound:

> a formula must contain a leaf reading every variable its function genuinely depends on.

So `leaves F ≥ #{variables relevant to F}` — a lower bound proved from the *structure* of the formula and the
*sensitivity* of the function, with **no counting of functions** anywhere.  It is the base case the Andreev /
Håstad shrinkage route (`…AndreevShrinkageRoute`) amplifies: a fully‑sensitive‑after‑restriction function
(a table lookup) keeps many relevant variables, and shrinkage turns that base bound into `n^{3-o(1)}`.

## What is proved (clean axioms, no `sorry`)

* `eval_eq_of_agree` — a formula's value depends only on the variables that appear in it.
* `vars_card_le_leaves` — `#(variables appearing) ≤ #leaves`.
* `relevant_mem_vars` — a variable the function is **sensitive to** must appear in the formula (else flipping it
  could not change the output).
* `leaves_ge_relevant_card` — **the non‑counting bound**: `#{relevant variables} ≤ leaves F`.
* `gAnd_all_relevant` / `gAnd_needs_n_leaves` — the `n`‑bit `AND` is sensitive to *every* variable, so any formula
  computing it has `≥ n` leaves.  (A clean, fully‑sensitive witness — "the explicit function lacks the weakness".)

## Honest scope

The relevance bound itself is *linear* (`≥ n` leaves for a fully‑sensitive function) — modest on its own, and the
`AND` example is tight.  Its value is being the **non‑counting structural core**: it lower‑bounds leaves by the
function's sensitivity, the property the shrinkage route amplifies.  The amplification (Håstad shrinkage `Γ=2` on
Andreev's lookup, raising the base bound to `n^{3-o(1)}`) is the cited deep step formalized structurally in
`…AndreevShrinkageRoute`; this file supplies the proved, non‑counting base it stands on.  It is a restricted
formula‑size technique, not a `P ≠ NP` argument.
-/

namespace PallLean.Paper93.DeepMath.PathB.RelevanceLeafBound

open Classical

/-- A Boolean formula over `n` variables (basis `{¬, ∧, ∨}` with constants). -/
inductive Formula (n : ℕ) where
  | var : Fin n → Formula n
  | tru : Formula n
  | fls : Formula n
  | neg : Formula n → Formula n
  | conj : Formula n → Formula n → Formula n
  | disj : Formula n → Formula n → Formula n

variable {n : ℕ}

/-- Evaluate a formula. -/
def eval : Formula n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .tru, _ => true
  | .fls, _ => false
  | .neg f, x => !(eval f x)
  | .conj f g, x => (eval f x) && (eval g x)
  | .disj f g, x => (eval f x) || (eval g x)

/-- The number of leaves (variable/constant occurrences). -/
def leaves : Formula n → ℕ
  | .var _ => 1
  | .tru => 1
  | .fls => 1
  | .neg f => leaves f
  | .conj f g => leaves f + leaves g
  | .disj f g => leaves f + leaves g

/-- The set of variables appearing in the formula. -/
def vars : Formula n → Finset (Fin n)
  | .var i => {i}
  | .tru => ∅
  | .fls => ∅
  | .neg f => vars f
  | .conj f g => vars f ∪ vars g
  | .disj f g => vars f ∪ vars g

/-- **A formula depends only on the variables that appear in it (proved).** -/
theorem eval_eq_of_agree (F : Formula n) :
    ∀ {x y : Fin n → Bool}, (∀ i ∈ vars F, x i = y i) → eval F x = eval F y := by
  induction F with
  | var i => intro x y h; simp only [eval]; exact h i (by simp [vars])
  | tru => intro x y _; rfl
  | fls => intro x y _; rfl
  | neg f ih => intro x y h; simp only [eval]; rw [ih h]
  | conj f g ihf ihg =>
      intro x y h
      simp only [eval]
      rw [ihf (fun i hi => h i (Finset.mem_union_left _ hi)),
          ihg (fun i hi => h i (Finset.mem_union_right _ hi))]
  | disj f g ihf ihg =>
      intro x y h
      simp only [eval]
      rw [ihf (fun i hi => h i (Finset.mem_union_left _ hi)),
          ihg (fun i hi => h i (Finset.mem_union_right _ hi))]

/-- **`#(appearing variables) ≤ #leaves` (proved).** -/
theorem vars_card_le_leaves (F : Formula n) : (vars F).card ≤ leaves F := by
  induction F with
  | var i => simp [vars, leaves]
  | tru => simp [vars, leaves]
  | fls => simp [vars, leaves]
  | neg f ih => simpa [vars, leaves] using ih
  | conj f g ihf ihg =>
      simp only [vars, leaves]
      exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add ihf ihg)
  | disj f g ihf ihg =>
      simp only [vars, leaves]
      exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add ihf ihg)

/-- Flip the `i`‑th bit. -/
def flipAt (a : Fin n → Bool) (i : Fin n) : Fin n → Bool := Function.update a i (!a i)

/-- Variable `i` is **relevant** to `g` if flipping it changes the output somewhere. -/
def relevantVar (g : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ a, g a ≠ g (flipAt a i)

/-- **A relevant variable must appear in the formula (proved).**  If `i` does not appear, the formula's value is
unchanged by flipping `i`, so `i` cannot be relevant. -/
theorem relevant_mem_vars (F : Formula n) (i : Fin n) (h : relevantVar (eval F) i) : i ∈ vars F := by
  by_contra hmem
  obtain ⟨a, ha⟩ := h
  apply ha
  apply eval_eq_of_agree
  intro j hj
  have hji : j ≠ i := fun e => hmem (e ▸ hj)
  rw [flipAt, Function.update_apply, if_neg hji]

/-- **The non‑counting structural leaf bound (proved): `#{relevant variables} ≤ leaves F`.**  Each variable the
function is sensitive to occupies a leaf; no counting of functions is used. -/
theorem leaves_ge_relevant_card (F : Formula n) :
    (Finset.univ.filter (fun i => relevantVar (eval F) i)).card ≤ leaves F := by
  classical
  calc (Finset.univ.filter (fun i => relevantVar (eval F) i)).card
      ≤ (vars F).card := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_filter] at hi
        exact relevant_mem_vars F i hi.2
    _ ≤ leaves F := vars_card_le_leaves F

/-- The `n`‑bit `AND` function. -/
def gAnd (n : ℕ) : (Fin n → Bool) → Bool := fun a => decide (∀ i, a i = true)

/-- **`AND` is sensitive to every variable (proved).**  At the all‑ones input, flipping any bit turns the output
from `true` to `false`. -/
theorem gAnd_all_relevant (i : Fin n) : relevantVar (gAnd n) i := by
  refine ⟨fun _ => true, ?_⟩
  have h1 : gAnd n (fun _ => true) = true := by simp [gAnd]
  have h2 : gAnd n (flipAt (fun _ => true) i) = false := by
    simp only [gAnd, decide_eq_false_iff_not, not_forall]
    exact ⟨i, by simp [flipAt]⟩
  rw [h1, h2]
  simp

/-- **`AND` needs `≥ n` leaves (proved), by sensitivity — a non‑counting bound.**  The explicit function provably
lacks the "ignores most variables" weakness: every variable is relevant, so any formula computing it has `≥ n`
leaves. -/
theorem gAnd_needs_n_leaves (F : Formula n) (hF : eval F = gAnd n) : n ≤ leaves F := by
  have h := leaves_ge_relevant_card F
  have hfull : (Finset.univ.filter (fun i => relevantVar (eval F) i)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    rw [hF]
    exact gAnd_all_relevant i
  rw [hfull, Finset.card_univ, Fintype.card_fin] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.RelevanceLeafBound

#print axioms PallLean.Paper93.DeepMath.PathB.RelevanceLeafBound.eval_eq_of_agree
#print axioms PallLean.Paper93.DeepMath.PathB.RelevanceLeafBound.leaves_ge_relevant_card
#print axioms PallLean.Paper93.DeepMath.PathB.RelevanceLeafBound.gAnd_needs_n_leaves
