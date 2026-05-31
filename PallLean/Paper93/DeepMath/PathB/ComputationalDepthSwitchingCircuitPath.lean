import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingTermPath

/-!
# Canonical path through the whole ΣΠΣ circuit (switching lemma, step 3)

**STATUS: REAL.  FULL DEPTH-3 PATH; ASSEMBLY INTO THE SWITCHING BOUND IS NEXT.**

Lifts the term-level canonical path to the **OR of terms** — the full depth-3
ΣΠΣ circuit.  The path processes the terms in order, running each term's path and
accumulating.  Proves the four circuit-level properties, lifting the term-level
ones (`width` → `numClauses · width` → `numTerms · numClauses · width`; label
count multiplies across terms):

1. `circuitSel_subset_freeVars` — selected coordinates were free in the start;
2. `circuitPath_decides` — every clause of every term is decided after the path;
3. `circuitSel_card_le` — total selected `≤ numTerms · (m · w)` (`m` clauses/term,
   width `w`);
4. `circuitLabelSpace_card_le` (+ `circuitPathList_mem_labelSpace`) — label count
   `≤ ((2^w)^m)^numTerms`.

This completes the canonical-decision-tree path for the entire circuit; the
remaining brick assembles the bad-restriction count (`card_bad_le_of_label_bound`)
and discharges `Depth3CollapseModel.collapse`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The accumulated restriction from running each term's path in order. -/
def circuitPath : Restriction n → List (Term n) → (Fin n → Bool) → Restriction n
  | ρ, [], _ => ρ
  | ρ, T :: ts, a => circuitPath (termPath ρ T.clauses a) ts a

/-- All coordinates selected along the whole-circuit path. -/
def circuitSel : Restriction n → List (Term n) → (Fin n → Bool) → Finset (Fin n)
  | _, [], _ => ∅
  | ρ, T :: ts, a => termSel ρ T.clauses a ∪ circuitSel (termPath ρ T.clauses a) ts a

/-- The nested path label (a list of per-term path labels). -/
def circuitPathList : Restriction n → List (Term n) → (Fin n → Bool) →
    List (List (Finset (Fin n)))
  | _, [], _ => []
  | ρ, T :: ts, a => termPathList ρ T.clauses a :: circuitPathList (termPath ρ T.clauses a) ts a

/-- The space of possible circuit path labels. -/
def circuitLabelSpace : List (Term n) → Finset (List (List (Finset (Fin n))))
  | [] => {[]}
  | T :: ts => ((termLabelSpace T.clauses) ×ˢ circuitLabelSpace ts).image (fun p => p.1 :: p.2)

/-! ### Monotonicity helpers -/

theorem freeVars_termPath_subset :
    ∀ (cs : List (Clause n)) (ρ : Restriction n) (a : Fin n → Bool),
      freeVars (termPath ρ cs a) ⊆ freeVars ρ := by
  intro cs
  induction cs with
  | nil => intro ρ a i hi; exact hi
  | cons C cs ih =>
    intro ρ a i hi
    exact freeVars_fixOn_subset ρ (canonicalSel ρ C) a (ih (fixOn ρ (canonicalSel ρ C) a) a hi)

theorem circuitPath_preserves_fixed :
    ∀ (ts : List (Term n)) (ρ : Restriction n) (a : Fin n → Bool) (i : Fin n),
      ρ i ≠ none → (circuitPath ρ ts a) i ≠ none := by
  intro ts
  induction ts with
  | nil => intro ρ a i h; exact h
  | cons T ts ih =>
    intro ρ a i h
    exact ih (termPath ρ T.clauses a) a i (termPath_preserves_fixed T.clauses ρ a i h)

/-! ### The four circuit-level properties -/

/-- **(1) Selected coordinates were free in the starting restriction.** -/
theorem circuitSel_subset_freeVars (ts : List (Term n)) (ρ : Restriction n) (a : Fin n → Bool) :
    circuitSel ρ ts a ⊆ freeVars ρ := by
  induction ts generalizing ρ with
  | nil => simp [circuitSel]
  | cons T ts ih =>
    intro i hi
    simp only [circuitSel, Finset.mem_union] at hi
    rcases hi with h | h
    · exact termSel_subset_freeVars T.clauses ρ a h
    · exact freeVars_termPath_subset T.clauses ρ a (ih (termPath ρ T.clauses a) h)

/-- Every variable of every clause of every term is fixed after the circuit path. -/
theorem circuitPath_fixes_clauseVars :
    ∀ (ts : List (Term n)) (ρ : Restriction n) (a : Fin n → Bool) (T : Term n),
      T ∈ ts → ∀ C ∈ T.clauses, ∀ i ∈ clauseVars C, (circuitPath ρ ts a) i ≠ none := by
  intro ts
  induction ts with
  | nil => intro ρ a T hT; exact absurd hT (by simp)
  | cons T0 ts ih =>
    intro ρ a T hT C hC i hi
    rcases List.mem_cons.mp hT with h | h
    · exact circuitPath_preserves_fixed ts _ a i
        (termPath_fixes_clauseVars T0.clauses ρ a C (h ▸ hC) i hi)
    · exact ih (termPath ρ T0.clauses a) a T h C hC i hi

/-- **(2) The circuit path decides the circuit:** every clause of every term is left
with no surviving free literal. -/
theorem circuitPath_decides (ρ : Restriction n) (ts : List (Term n)) (a : Fin n → Bool)
    (T : Term n) (hT : T ∈ ts) (C : Clause n) (hC : C ∈ T.clauses) :
    C.lits.filter (Depth3.litFree (circuitPath ρ ts a)) = [] :=
  filter_litFree_nil_of_fixed _ C
    (fun i hi => circuitPath_fixes_clauseVars ts ρ a T hT C hC i hi)

/-- **(3) Total selected coordinates `≤ numTerms · (m · w)`.** -/
theorem circuitSel_card_le :
    ∀ (ts : List (Term n)) (ρ : Restriction n) (a : Fin n → Bool) (w m : ℕ),
      (∀ T ∈ ts, ∀ C ∈ T.clauses, C.width ≤ w) → (∀ T ∈ ts, T.clauses.length ≤ m) →
      (circuitSel ρ ts a).card ≤ ts.length * (m * w) := by
  intro ts
  induction ts with
  | nil => intro ρ a w m _ _; simp [circuitSel]
  | cons T ts ih =>
    intro ρ a w m hw hm
    have h1 : (termSel ρ T.clauses a).card ≤ m * w :=
      le_trans (termSel_card_le T.clauses ρ a w
          (fun C hC => hw T (List.mem_cons.mpr (Or.inl rfl)) C hC))
        (mul_le_mul_right' (hm T (List.mem_cons.mpr (Or.inl rfl))) w)
    have h2 : (circuitSel (termPath ρ T.clauses a) ts a).card ≤ ts.length * (m * w) :=
      ih (termPath ρ T.clauses a) a w m
        (fun T' hT' C hC => hw T' (List.mem_cons.mpr (Or.inr hT')) C hC)
        (fun T' hT' => hm T' (List.mem_cons.mpr (Or.inr hT')))
    calc (circuitSel ρ (T :: ts) a).card
        ≤ (termSel ρ T.clauses a).card + (circuitSel (termPath ρ T.clauses a) ts a).card :=
          Finset.card_union_le _ _
      _ ≤ m * w + ts.length * (m * w) := Nat.add_le_add h1 h2
      _ = (T :: ts).length * (m * w) := by rw [List.length_cons]; ring

/-- The circuit path label lands in the circuit label space. -/
theorem circuitPathList_mem_labelSpace :
    ∀ (ts : List (Term n)) (ρ : Restriction n) (a : Fin n → Bool),
      circuitPathList ρ ts a ∈ circuitLabelSpace ts := by
  intro ts
  induction ts with
  | nil => intro ρ a; simp [circuitPathList, circuitLabelSpace]
  | cons T ts ih =>
    intro ρ a
    refine Finset.mem_image.mpr ⟨(termPathList ρ T.clauses a,
      circuitPathList (termPath ρ T.clauses a) ts a), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨termPathList_mem_labelSpace T.clauses ρ a,
      ih (termPath ρ T.clauses a) a⟩

/-- **(4) The number of possible circuit path labels is `≤ ((2^w)^m)^numTerms`.** -/
theorem circuitLabelSpace_card_le :
    ∀ (ts : List (Term n)) (w m : ℕ),
      (∀ T ∈ ts, ∀ C ∈ T.clauses, C.width ≤ w) → (∀ T ∈ ts, T.clauses.length ≤ m) →
      (circuitLabelSpace ts).card ≤ ((2 ^ w) ^ m) ^ ts.length := by
  intro ts
  induction ts with
  | nil => intro w m _ _; simp [circuitLabelSpace]
  | cons T ts ih =>
    intro w m hw hm
    have hT : (termLabelSpace T.clauses).card ≤ (2 ^ w) ^ m :=
      le_trans (termLabelSpace_card_le T.clauses w
          (fun C hC => hw T (List.mem_cons.mpr (Or.inl rfl)) C hC))
        (Nat.pow_le_pow_right (Nat.one_le_pow w 2 (by norm_num))
          (hm T (List.mem_cons.mpr (Or.inl rfl))))
    have hrec : (circuitLabelSpace ts).card ≤ ((2 ^ w) ^ m) ^ ts.length :=
      ih w m (fun T' hT' C hC => hw T' (List.mem_cons.mpr (Or.inr hT')) C hC)
        (fun T' hT' => hm T' (List.mem_cons.mpr (Or.inr hT')))
    calc (circuitLabelSpace (T :: ts)).card
        ≤ ((termLabelSpace T.clauses) ×ˢ circuitLabelSpace ts).card := Finset.card_image_le
      _ = (termLabelSpace T.clauses).card * (circuitLabelSpace ts).card := Finset.card_product _ _
      _ ≤ (2 ^ w) ^ m * ((2 ^ w) ^ m) ^ ts.length := Nat.mul_le_mul hT hrec
      _ = ((2 ^ w) ^ m) ^ (T :: ts).length := by rw [List.length_cons, pow_succ]; ring

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.circuitSel_subset_freeVars
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.circuitPath_decides
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.circuitSel_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.circuitLabelSpace_card_le
