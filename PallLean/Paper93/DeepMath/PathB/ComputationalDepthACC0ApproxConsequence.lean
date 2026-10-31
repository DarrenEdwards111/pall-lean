import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ResidueObserver

/-!
# Approximate vs exact: what an approximating `SYM∘AND` actually buys

The RS layer produces an *approximating* low-degree / `SYM∘AND` function `g` (agreeing with the target `f` on a
`1-ε` fraction), not an exact equal.  This file pins down, honestly, the gap between approximation and exact equality
for the SAT/search side:

* **Exact** (`disagreeSet f g = ∅`, i.e. `f = g` everywhere): SAT transfers — `Satisfiable f ↔ Satisfiable g`
  (`exact_sat_iff`).  This is the only regime where a searchable `g` decides `f`'s SAT.
* **Approximate** (disagreement set of size `≤ δ`): SAT does **not** transfer; one gets only a *size* bound —
  `f`'s satisfying set is within the disagreement of `g`'s (`sat_card_le_of_disagree`).  So an approximating `g` bounds
  the *number* of solutions of `f` (a sparsity/correlation consequence), but cannot decide `f`'s satisfiability.

That is exactly why the YBT *cash-out* needs the **exact** normal form (not the RS approximation) to give a SAT
algorithm — the searchability lane (`…ACC0SymmetricObserver` etc.) consumes an exact `SYM∘AND`.

## What is proved (clean axioms, no `sorry`)

* `disagreeSet` — the set of inputs where `f` and `g` differ.
* `sat_card_le_of_disagree` — `|{f = true}| ≤ |{g = true}| + |disagreeSet f g|` (approximation bounds the solution count).
* `exact_sat_iff` — exact agreement (`disagreeSet = ∅`) ⇒ `Satisfiable f ↔ Satisfiable g`.

## Honest scope

This delimits the approximate/exact boundary: only *exact* agreement transfers satisfiability, so the searchable
cash-out genuinely needs the exact `SYM∘AND` form; the RS approximation gives only a solution-count (correlation)
bound.  It does not close the gap (RS stays approximate) — it *names* why the gap matters.  The correlation side is
where RS lower bounds live (e.g. `parity_function_lower_bound`); the exact-form side is the open structural wall.
Still the cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ApproxConsequence

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup

variable {n : ℕ}

/-- The set of inputs on which `f` and `g` disagree. -/
def disagreeSet (f g : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => f x ≠ g x)

/-- **Approximation bounds the solution count (proved): `|{f = true}| ≤ |{g = true}| + |disagreeSet f g|`.**  An
approximating `g` controls the *number* of solutions of `f`, not its satisfiability. -/
theorem sat_card_le_of_disagree (f g : (Fin n → Bool) → Bool) :
    (Finset.univ.filter (fun x => f x = true)).card ≤
      (Finset.univ.filter (fun x => g x = true)).card + (disagreeSet f g).card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simp only [Finset.mem_union, Finset.mem_filter, disagreeSet, Finset.mem_univ, true_and]
  by_cases hg : g x = true
  · exact Or.inl hg
  · exact Or.inr (by rw [hx]; exact fun heq => hg heq.symm)

/-- **Exact agreement transfers SAT (proved): if `f` and `g` never disagree, `Satisfiable f ↔ Satisfiable g`.**  This
is the only regime where a searchable `g` decides `f`'s SAT. -/
theorem exact_sat_iff (f g : (Fin n → Bool) → Bool) (h : disagreeSet f g = ∅) :
    Satisfiable f ↔ Satisfiable g := by
  have hfg : ∀ x, f x = g x := by
    intro x
    by_contra hne
    have hx : x ∈ disagreeSet f g := by
      simp only [disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact hne
    rw [h] at hx
    simp at hx
  unfold Satisfiable
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x, by rw [← hfg x]; exact hx⟩
  · rintro ⟨x, hx⟩; exact ⟨x, by rw [hfg x]; exact hx⟩

end PallLean.Paper93.DeepMath.PathB.ACC0ApproxConsequence

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ApproxConsequence.sat_card_le_of_disagree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ApproxConsequence.exact_sat_iff
