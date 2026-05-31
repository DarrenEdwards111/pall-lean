import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3OneStepRestriction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCounting

/-!
# Canonical path selector for a single bottom clause (switching lemma, step 1)

**STATUS: REAL.  SINGLE-CLAUSE CASE; THE LIFT TO ΣΠΣ IS THE NEXT STEP.**

The switching-lemma encoding needs a *selection rule* `sel ρ` choosing which free
coordinates to fix — Razborov's canonical decision-tree path.  This file builds
and verifies that selector for a single bottom **clause** (OR of literals), the
narrow first case before the full depth-3 circuit.  It proves exactly the four
properties the counting scaffold (`SwitchingCounting`) consumes:

1. `canonicalSel_subset_freeVars` — the selector chooses only *free* coordinates;
2. `canonicalSel_forces` — fixing along the selector leaves the clause with **no
   surviving free literal**, i.e. fully decided;
3. `canonicalSel_card_le_width` — the path length is bounded by the bottom width;
4. `canonicalSel_label_bound` — the number of possible selector values for one
   clause is `≤ 2^width` (the combinatorial label bound).

Composing these across the terms of a ΣΠΣ circuit (giving `(2^w)^s`) is the next
brick; the full switching lemma then plugs into `card_bad_le_of_label_bound`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The variable a literal queries. -/
def litVar : Rung4Literal n → Fin n
  | .pos i => i
  | .neg i => i

/-- The variables occurring in a bottom clause. -/
def clauseVars (C : Clause n) : Finset (Fin n) :=
  (C.lits.map litVar).toFinset

/-- "free" for a literal is "free" for its variable. -/
theorem litFree_var (ρ : Restriction n) (ℓ : Rung4Literal n) :
    Depth3.litFree ρ ℓ = (ρ (litVar ℓ)).isNone := by
  cases ℓ with
  | pos i => cases h : ρ i <;> simp [Depth3.litFree, Depth3.litFixedVal, litVar, h]
  | neg i => cases h : ρ i <;> simp [Depth3.litFree, Depth3.litFixedVal, litVar, h]

/-- **The canonical selector:** the free coordinates occurring in the clause. -/
def canonicalSel (ρ : Restriction n) (C : Clause n) : Finset (Fin n) :=
  freeVars ρ ∩ clauseVars C

/-- **(1) The selector chooses only free coordinates.** -/
theorem canonicalSel_subset_freeVars (ρ : Restriction n) (C : Clause n) :
    canonicalSel ρ C ⊆ freeVars ρ :=
  Finset.inter_subset_left

/-- After fixing the canonical selector, every variable of the clause is fixed. -/
theorem clauseVars_fixed_after (ρ : Restriction n) (C : Clause n) (a : Fin n → Bool) :
    ∀ i ∈ clauseVars C, (fixOn ρ (canonicalSel ρ C) a) i ≠ none := by
  intro i hi
  by_cases hc : i ∈ canonicalSel ρ C
  · simp only [fixOn, if_pos hc]; exact Option.some_ne_none _
  · have hnf : i ∉ freeVars ρ := fun hf => hc (Finset.mem_inter.mpr ⟨hf, hi⟩)
    simp only [fixOn, if_neg hc]
    exact fun h => hnf (mem_freeVars.mpr h)

/-- **(2) Fixing along the selector forces the clause.**  No literal of the clause
survives as free, so the clause is decided (its restricted bottom is empty). -/
theorem canonicalSel_forces (ρ : Restriction n) (C : Clause n) (a : Fin n → Bool) :
    C.lits.filter (Depth3.litFree (fixOn ρ (canonicalSel ρ C) a)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro ℓ hℓ
  rw [litFree_var]
  have hv : litVar ℓ ∈ clauseVars C := List.mem_toFinset.mpr (List.mem_map.mpr ⟨ℓ, hℓ, rfl⟩)
  have hne : (fixOn ρ (canonicalSel ρ C) a) (litVar ℓ) ≠ none :=
    clauseVars_fixed_after ρ C a (litVar ℓ) hv
  simp [Option.isNone_iff_eq_none, hne]

/-- The number of clause variables is at most the bottom width. -/
theorem clauseVars_card_le_width (C : Clause n) : (clauseVars C).card ≤ C.width := by
  have h1 : (clauseVars C).card ≤ (C.lits.map litVar).length :=
    @List.toFinset_card_le (Fin n) _ (C.lits.map litVar)
  simpa [Clause.width] using h1

/-- **(3) The path length is bounded by the bottom width.** -/
theorem canonicalSel_card_le_width (ρ : Restriction n) (C : Clause n) :
    (canonicalSel ρ C).card ≤ C.width :=
  le_trans (Finset.card_le_card Finset.inter_subset_right) (clauseVars_card_le_width C)

/-- The selector value is a subset of the clause variables. -/
theorem canonicalSel_mem_powerset (ρ : Restriction n) (C : Clause n) :
    canonicalSel ρ C ∈ (clauseVars C).powerset :=
  Finset.mem_powerset.mpr Finset.inter_subset_right

/-- **(4) The label space for one clause is combinatorially bounded.**  Every
selector value lies in `(clauseVars C).powerset`, whose cardinality is `≤ 2^width`. -/
theorem canonicalSel_label_bound (C : Clause n) :
    (clauseVars C).powerset.card ≤ 2 ^ C.width := by
  rw [Finset.card_powerset]
  exact Nat.pow_le_pow_right (by norm_num) (clauseVars_card_le_width C)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonicalSel_forces
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonicalSel_card_le_width
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonicalSel_label_bound
