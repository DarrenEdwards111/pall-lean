import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCanonicalPath

/-!
# Canonical path through one term (AND of clauses) — switching lemma, step 2

**STATUS: REAL.  ONE-TERM CASE; THE LIFT TO THE OR OF TERMS IS NEXT.**

Lifts the single-clause canonical selector to a whole **term** (a conjunction of
clauses).  The path processes the clauses in order, fixing the free variables of
each clause as it is reached, accumulating a restriction.  Proves the four
properties the counting scaffold consumes at the term level:

1. `termSel_subset_freeVars` — every selected coordinate was free in the starting
   restriction (so the selector is admissible for the encoding);
2. `termPath_decides` — after the accumulated restriction, **every** clause of the
   term has no surviving free literal — the term is decided;
3. `termSel_card_le` — total selected coordinates `≤ numClauses · width`;
4. `termLabelSpace_card_le` (+ `termPathList_mem_labelSpace`) — the number of
   possible path labels is `≤ (2^width)^numClauses`.

Composing this across the OR of terms of a ΣΠΣ circuit is the final structural
brick; the full switching lemma then plugs into `card_bad_le_of_label_bound`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The accumulated restriction obtained by fixing each clause's free variables in
turn. -/
def termPath : Restriction n → List (Clause n) → (Fin n → Bool) → Restriction n
  | ρ, [], _ => ρ
  | ρ, C :: cs, a => termPath (fixOn ρ (canonicalSel ρ C) a) cs a

/-- The set of all coordinates selected along the term path. -/
def termSel : Restriction n → List (Clause n) → (Fin n → Bool) → Finset (Fin n)
  | _, [], _ => ∅
  | ρ, C :: cs, a => canonicalSel ρ C ∪ termSel (fixOn ρ (canonicalSel ρ C) a) cs a

/-- The ordered list of selected blocks (the path label). -/
def termPathList : Restriction n → List (Clause n) → (Fin n → Bool) → List (Finset (Fin n))
  | _, [], _ => []
  | ρ, C :: cs, a => canonicalSel ρ C :: termPathList (fixOn ρ (canonicalSel ρ C) a) cs a

/-- The space of possible path labels for a list of clauses. -/
def termLabelSpace : List (Clause n) → Finset (List (Finset (Fin n)))
  | [] => {[]}
  | C :: cs => ((clauseVars C).powerset ×ˢ termLabelSpace cs).image (fun p => p.1 :: p.2)

/-! ### Monotonicity helpers -/

theorem fixOn_preserves_fixed (ρ : Restriction n) (S : Finset (Fin n)) (a : Fin n → Bool)
    (i : Fin n) (h : ρ i ≠ none) : (fixOn ρ S a) i ≠ none := by
  show (if i ∈ S then some (a i) else ρ i) ≠ none
  by_cases hi : i ∈ S
  · rw [if_pos hi]; exact Option.some_ne_none _
  · rw [if_neg hi]; exact h

theorem termPath_preserves_fixed :
    ∀ (cs : List (Clause n)) (ρ : Restriction n) (a : Fin n → Bool) (i : Fin n),
      ρ i ≠ none → (termPath ρ cs a) i ≠ none := by
  intro cs
  induction cs with
  | nil => intro ρ a i h; exact h
  | cons C cs ih =>
    intro ρ a i h
    exact ih (fixOn ρ (canonicalSel ρ C) a) a i (fixOn_preserves_fixed ρ _ a i h)

theorem freeVars_fixOn_subset (ρ : Restriction n) (S : Finset (Fin n)) (a : Fin n → Bool) :
    freeVars (fixOn ρ S a) ⊆ freeVars ρ := by
  intro i hi
  rw [mem_freeVars] at hi ⊢
  by_cases h : i ∈ S
  · simp [fixOn, h] at hi
  · simpa [fixOn, h] using hi

/-! ### The four term-level properties -/

/-- **(1) Selected coordinates were free in the starting restriction.** -/
theorem termSel_subset_freeVars (cs : List (Clause n)) (ρ : Restriction n) (a : Fin n → Bool) :
    termSel ρ cs a ⊆ freeVars ρ := by
  induction cs generalizing ρ with
  | nil => simp [termSel]
  | cons C cs ih =>
    intro i hi
    simp only [termSel, Finset.mem_union] at hi
    rcases hi with h | h
    · exact canonicalSel_subset_freeVars ρ C h
    · exact freeVars_fixOn_subset ρ (canonicalSel ρ C) a (ih (fixOn ρ (canonicalSel ρ C) a) h)

/-- Every variable of every clause is fixed after the full term path. -/
theorem termPath_fixes_clauseVars :
    ∀ (cs : List (Clause n)) (ρ : Restriction n) (a : Fin n → Bool) (C : Clause n),
      C ∈ cs → ∀ i ∈ clauseVars C, (termPath ρ cs a) i ≠ none := by
  intro cs
  induction cs with
  | nil => intro ρ a C hC; exact absurd hC (by simp)
  | cons C0 cs ih =>
    intro ρ a C hC i hi
    rcases List.mem_cons.mp hC with h | h
    · exact termPath_preserves_fixed cs _ a i
        (clauseVars_fixed_after ρ C0 a i (h ▸ hi))
    · exact ih (fixOn ρ (canonicalSel ρ C0) a) a C h i hi

/-- A clause with all variables fixed has no surviving free literal. -/
theorem filter_litFree_nil_of_fixed (ρ' : Restriction n) (C : Clause n)
    (h : ∀ i ∈ clauseVars C, ρ' i ≠ none) :
    C.lits.filter (Depth3.litFree ρ') = [] := by
  rw [List.filter_eq_nil_iff]
  intro ℓ hℓ
  rw [litFree_var]
  have hv : litVar ℓ ∈ clauseVars C := List.mem_toFinset.mpr (List.mem_map.mpr ⟨ℓ, hℓ, rfl⟩)
  simp [Option.isNone_iff_eq_none, h (litVar ℓ) hv]

/-- **(2) The accumulated restriction decides the term:** every clause is left with
no surviving free literal. -/
theorem termPath_decides (ρ : Restriction n) (cs : List (Clause n)) (a : Fin n → Bool)
    (C : Clause n) (hC : C ∈ cs) :
    C.lits.filter (Depth3.litFree (termPath ρ cs a)) = [] :=
  filter_litFree_nil_of_fixed _ C (fun i hi => termPath_fixes_clauseVars cs ρ a C hC i hi)

/-- **(3) Total selected coordinates are at most `numClauses · width`.** -/
theorem termSel_card_le :
    ∀ (cs : List (Clause n)) (ρ : Restriction n) (a : Fin n → Bool) (w : ℕ),
      (∀ C ∈ cs, C.width ≤ w) → (termSel ρ cs a).card ≤ cs.length * w := by
  intro cs
  induction cs with
  | nil => intro ρ a w _; simp [termSel]
  | cons C cs ih =>
    intro ρ a w hw
    have h1 : (canonicalSel ρ C).card ≤ w :=
      le_trans (canonicalSel_card_le_width ρ C) (hw C (List.mem_cons.mpr (Or.inl rfl)))
    have h2 : (termSel (fixOn ρ (canonicalSel ρ C) a) cs a).card ≤ cs.length * w :=
      ih (fixOn ρ (canonicalSel ρ C) a) a w (fun C' hC' => hw C' (List.mem_cons.mpr (Or.inr hC')))
    calc (termSel ρ (C :: cs) a).card
        ≤ (canonicalSel ρ C).card + (termSel (fixOn ρ (canonicalSel ρ C) a) cs a).card :=
          Finset.card_union_le _ _
      _ ≤ w + cs.length * w := Nat.add_le_add h1 h2
      _ = (C :: cs).length * w := by rw [List.length_cons]; ring

/-- The path label lands in the label space. -/
theorem termPathList_mem_labelSpace :
    ∀ (cs : List (Clause n)) (ρ : Restriction n) (a : Fin n → Bool),
      termPathList ρ cs a ∈ termLabelSpace cs := by
  intro cs
  induction cs with
  | nil => intro ρ a; simp [termPathList, termLabelSpace]
  | cons C cs ih =>
    intro ρ a
    refine Finset.mem_image.mpr ⟨(canonicalSel ρ C,
      termPathList (fixOn ρ (canonicalSel ρ C) a) cs a), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨canonicalSel_mem_powerset ρ C,
      ih (fixOn ρ (canonicalSel ρ C) a) a⟩

/-- **(4) The number of possible path labels is at most `(2^width)^numClauses`.** -/
theorem termLabelSpace_card_le :
    ∀ (cs : List (Clause n)) (w : ℕ), (∀ C ∈ cs, C.width ≤ w) →
      (termLabelSpace cs).card ≤ (2 ^ w) ^ cs.length := by
  intro cs
  induction cs with
  | nil => intro w _; simp [termLabelSpace]
  | cons C cs ih =>
    intro w hw
    have hc : (clauseVars C).powerset.card ≤ 2 ^ w :=
      le_trans (canonicalSel_label_bound C)
        (Nat.pow_le_pow_right (by norm_num) (hw C (List.mem_cons.mpr (Or.inl rfl))))
    have hrec : (termLabelSpace cs).card ≤ (2 ^ w) ^ cs.length :=
      ih w (fun C' hC' => hw C' (List.mem_cons.mpr (Or.inr hC')))
    calc (termLabelSpace (C :: cs)).card
        ≤ ((clauseVars C).powerset ×ˢ termLabelSpace cs).card := Finset.card_image_le
      _ = (clauseVars C).powerset.card * (termLabelSpace cs).card := Finset.card_product _ _
      _ ≤ 2 ^ w * (2 ^ w) ^ cs.length := Nat.mul_le_mul hc hrec
      _ = (2 ^ w) ^ (C :: cs).length := by rw [List.length_cons, pow_succ]; ring

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termSel_subset_freeVars
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termPath_decides
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termSel_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termLabelSpace_card_le
