import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseInterface
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCanonicalPath
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHastad

/-!
# The OR/AND object adapter (switching DNF ↔ ΣΠΣ middle-layer CNF)

**STATUS: REAL.  THE DE MORGAN ADAPTER — A HONEST PREREQUISITE FOR THE COLLAPSE ASSEMBLY.**

The switching machinery (`SwitchingCounting`) operates on **DNF terms** — a `Clause`'s literals
read as an AND (`termSat`/`evalLits`), an `anyTermSat`/`any` over terms.  The ΣΠΣ depth-3
substrate (`Depth3.Circuit`) has the *dual* polarity at the middle layer: a `Term` is an **AND
of OR-clauses** (a CNF).  To apply switching to collapse the bottom of a ΣΠΣ circuit, one
negates: by De Morgan a middle `Term` (CNF) is the negation of a **DNF** whose terms are the
negated clauses — exactly the object the switching count handles.

This file builds that adapter cleanly:

* `litNeg` — literal negation, with `litNeg_eval : (litNeg ℓ).eval x = !(ℓ.eval x)` and
  `litVar_litNeg` (variable preserved, so the switching width/star structure is unchanged);
* `evalLits_map_litNeg` / `clauseEval_neg` — negating an OR-clause yields an AND-monomial:
  `evalLits (C.lits.map litNeg) x = !(C.eval x)`;
* `termEval_neg` — **the adapter**: a ΣΠΣ middle `Term` (CNF) negates to a DNF,
  `!(T.eval x) = (T.clauses.map (fun C => C.lits.map litNeg)).any (fun t => evalLits t x)`.

It does **not** discharge the collapse assembly (good restriction ⟹ short `LDeriv` refutation)
— that is the open gate.  It supplies the polarity bridge that assembly will need.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting Rung4DNFTerm

variable {n : ℕ}

/-- Literal negation: `pos ↔ neg` on the same variable. -/
def litNeg : Rung4Literal n → Rung4Literal n
  | .pos i => .neg i
  | .neg i => .pos i

@[simp] theorem litNeg_eval (ℓ : Rung4Literal n) (x : Fin n → Bool) :
    (litNeg ℓ).eval x = !(ℓ.eval x) := by
  cases ℓ <;> simp [litNeg, Rung4Literal.eval]

@[simp] theorem litVar_litNeg (ℓ : Rung4Literal n) : litVar (litNeg ℓ) = litVar ℓ := by
  cases ℓ <;> rfl

/-! ### Extension monotonicity (the gate-A correctness foundation)

The canonical decision tree's correctness rests on: a literal/term *forced true* by the partial
restriction `σ` stays true on every full assignment extending `σ`.  This is the semantic bridge
from the partial `σ` (where `termSat`/`litTrue` live) to the full-assignment DNF evaluation that
the DT computes — the honest foundation of gate A.  (Gate A itself — that the *shallow* canonical
tree, querying only the `s` path variables, computes the restricted DNF — is the switching
lemma's structural conclusion and holds only for good `ρ`; not faked.) -/

/-- A literal forced true by `σ` evaluates true on every extension of `σ`. -/
theorem litTrue_eval_extend {σ : Fin n → Option Bool} {ℓ : Rung4Literal n} {x : Fin n → Bool}
    (hlt : Depth3.litTrue σ ℓ = true) (hext : Rung4Restriction.Extends σ x) : ℓ.eval x = true := by
  cases ℓ with
  | pos i =>
    have hs : σ i = some true := by
      cases h : σ i with
      | none => simp [Depth3.litTrue, Depth3.litFixedVal, h] at hlt
      | some b => cases b with
        | false => simp [Depth3.litTrue, Depth3.litFixedVal, h] at hlt
        | true => rfl
    simp [Rung4Literal.eval, hext i true hs]
  | neg i =>
    have hs : σ i = some false := by
      cases h : σ i with
      | none => simp [Depth3.litTrue, Depth3.litFixedVal, h] at hlt
      | some b => cases b with
        | true => simp [Depth3.litTrue, Depth3.litFixedVal, h] at hlt
        | false => rfl
    simp [Rung4Literal.eval, hext i false hs]

/-- A list of literals all forced true by `σ` evaluates (as an AND) to true on every extension. -/
theorem evalLits_eq_true_of_all {x : Fin n → Bool} :
    ∀ lits : List (Rung4Literal n), (∀ ℓ ∈ lits, ℓ.eval x = true) → evalLits lits x = true
  | [], _ => rfl
  | a :: t, hall => by
    simp only [evalLits, hall a (List.mem_cons.mpr (Or.inl rfl)),
      evalLits_eq_true_of_all t (fun ℓ hℓ => hall ℓ (List.mem_cons.mpr (Or.inr hℓ))), Bool.and_self]

/-- **A term satisfied by `σ` stays satisfied on every extension.**  If `termSat σ T` (all of
`T`'s literals forced true by `σ`), then `evalLits T.lits x = true` for every `x` extending `σ` —
so the DNF is true there.  Extension monotonicity for the satisfied-term branch of the canonical
DT. -/
theorem termSat_eval_extend {σ : Fin n → Option Bool} {T : Clause n} {x : Fin n → Bool}
    (hsat : T.lits.all (Depth3.litTrue σ) = true) (hext : Rung4Restriction.Extends σ x) :
    evalLits T.lits x = true :=
  evalLits_eq_true_of_all T.lits
    (fun ℓ hℓ => litTrue_eval_extend ((List.all_eq_true.mp hsat) ℓ hℓ) hext)

/-- A literal forced *false* by `σ` evaluates false on every extension of `σ`. -/
theorem litFalse_eval_extend {σ : Fin n → Option Bool} {ℓ : Rung4Literal n} {x : Fin n → Bool}
    (hlf : SwitchingCounting.litFalse σ ℓ = true) (hext : Rung4Restriction.Extends σ x) :
    ℓ.eval x = false := by
  cases ℓ with
  | pos i =>
    have hs : σ i = some false := by
      cases h : σ i with
      | none => simp [SwitchingCounting.litFalse, Depth3.litFixedVal, h] at hlf
      | some b => cases b with
        | true => simp [SwitchingCounting.litFalse, Depth3.litFixedVal, h] at hlf
        | false => rfl
    simp [Rung4Literal.eval, hext i false hs]
  | neg i =>
    have hs : σ i = some true := by
      cases h : σ i with
      | none => simp [SwitchingCounting.litFalse, Depth3.litFixedVal, h] at hlf
      | some b => cases b with
        | false => simp [SwitchingCounting.litFalse, Depth3.litFixedVal, h] at hlf
        | true => rfl
    simp [Rung4Literal.eval, hext i true hs]

/-- If some literal of a list is false, the AND-monomial is false. -/
theorem evalLits_eq_false_of_mem {x : Fin n → Bool} :
    ∀ (lits : List (Rung4Literal n)) (ℓ : Rung4Literal n), ℓ ∈ lits → ℓ.eval x = false →
      evalLits lits x = false
  | a :: t, ℓ, hmem, hfalse => by
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · simp [evalLits, hfalse]
    · simp [evalLits, evalLits_eq_false_of_mem t ℓ hmem' hfalse]

/-- **A term falsified by `σ` stays false on every extension.**  Extension monotonicity for the
falsified branch of the canonical decision tree. -/
theorem termFalsified_eval_extend {σ : Fin n → Option Bool} {T : Clause n} {x : Fin n → Bool}
    (hf : SwitchingCounting.termFalsified σ T = true) (hext : Rung4Restriction.Extends σ x) :
    evalLits T.lits x = false := by
  rw [SwitchingCounting.termFalsified, List.any_eq_true] at hf
  obtain ⟨ℓ, hℓ, hlf⟩ := hf
  exact evalLits_eq_false_of_mem T.lits ℓ hℓ (litFalse_eval_extend hlf hext)

/-- The DNF's value on a full assignment: some term's literals are all true. -/
def dnfEval (cs : List (Clause n)) (x : Fin n → Bool) : Bool :=
  cs.any (fun T => evalLits T.lits x)

/-- **Canonical DT leaf decision (satisfied).**  If some term is satisfied by `σ`, the DNF is
true on every extension — the correct value at a `leaf true` of the canonical tree. -/
theorem dnfEval_true_of_anyTermSat {σ : Fin n → Option Bool} {cs : List (Clause n)}
    {x : Fin n → Bool} (hany : SwitchingCounting.anyTermSat cs σ = true)
    (hext : Rung4Restriction.Extends σ x) : dnfEval cs x = true := by
  rw [SwitchingCounting.anyTermSat, List.any_eq_true] at hany
  obtain ⟨T, hT, hsat⟩ := hany
  exact List.any_eq_true.mpr ⟨T, hT, termSat_eval_extend hsat hext⟩

/-- **Canonical DT leaf decision (all falsified).**  If every term is falsified by `σ`, the DNF
is false on every extension — the correct value at a `leaf false` of the canonical tree. -/
theorem dnfEval_false_of_all_falsified {σ : Fin n → Option Bool} {cs : List (Clause n)}
    {x : Fin n → Bool} (hall : ∀ T ∈ cs, SwitchingCounting.termFalsified σ T = true)
    (hext : Rung4Restriction.Extends σ x) : dnfEval cs x = false := by
  rw [dnfEval]
  by_contra h
  simp only [Bool.not_eq_false, List.any_eq_true] at h
  obtain ⟨T, hT, hev⟩ := h
  rw [termFalsified_eval_extend (hall T hT) hext] at hev
  exact absurd hev (by decide)

/-! ### The canonical stop-on-satisfied decision tree (gate-A core) -/

/-- Fix variable `i` to bit `b` in the restriction. -/
def fixVar (σ : Fin n → Option Bool) (i : Fin n) (b : Bool) : Fin n → Option Bool :=
  Function.update σ i (some b)

/-- Branch extension: if `x` extends `σ` and `x i = b`, then `x` extends `σ` with `i:=b`. -/
theorem extends_fixVar {σ : Fin n → Option Bool} {i : Fin n} {b : Bool} {x : Fin n → Bool}
    (hext : Rung4Restriction.Extends σ x) (hxi : x i = b) :
    Rung4Restriction.Extends (fixVar σ i b) x := by
  intro j c hjc
  by_cases hj : j = i
  · subst hj
    simp only [fixVar, Function.update_self, Option.some.injEq] at hjc
    rw [hxi]; exact hjc
  · rw [fixVar, Function.update_of_ne hj] at hjc; exact hext j c hjc

/-- Fixing a free variable strictly decreases the star count. -/
theorem stars_fixVar_lt {σ : Fin n → Option Bool} {i : Fin n} {b : Bool}
    (hi : σ i = none) : SwitchingCounting.stars (fixVar σ i b) < SwitchingCounting.stars σ := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i, SwitchingCounting.mem_freeVars.mpr hi, ?_⟩
    rw [SwitchingCounting.mem_freeVars, fixVar, Function.update_self]; simp
  · intro j hj
    rw [SwitchingCounting.mem_freeVars] at hj ⊢
    by_cases hji : j = i
    · subst hji; rw [fixVar, Function.update_self] at hj; simp at hj
    · rwa [fixVar, Function.update_of_ne hji] at hj

/-- The **canonical stop-on-satisfied decision tree** for a DNF `cs` under partial restriction
`σ`: if some term is already satisfied, output `true`; if all terms are falsified, output
`false`; otherwise query the active term's first free literal and recurse on both branches. -/
def canonicalDT (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → BoolDecisionTree n
  | 0, σ => if SwitchingCounting.anyTermSat cs σ then BoolDecisionTree.leaf true
            else BoolDecisionTree.leaf false
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then BoolDecisionTree.leaf true
    else match SwitchingCounting.activeTerm cs σ with
      | none => BoolDecisionTree.leaf false
      | some T => match (SwitchingCounting.freeLits σ T).head? with
        | none => BoolDecisionTree.leaf false
        | some ℓ => BoolDecisionTree.query (litVar ℓ)
            (canonicalDT cs fuel (fixVar σ (litVar ℓ) false))
            (canonicalDT cs fuel (fixVar σ (litVar ℓ) true))

/-- No free literals when the restriction is total (`stars = 0`). -/
theorem freeLits_nil_of_stars_zero {σ : Fin n → Option Bool} (h0 : SwitchingCounting.stars σ = 0)
    (T : Clause n) : SwitchingCounting.freeLits σ T = [] := by
  have hempty : SwitchingCounting.freeVars σ = ∅ := Finset.card_eq_zero.mp h0
  rw [SwitchingCounting.freeLits, List.filter_eq_nil_iff]
  intro ℓ _ hlf
  rw [SwitchingCounting.litFree_var] at hlf
  have : σ (litVar ℓ) = none := Option.isNone_iff_eq_none.mp hlf
  have := SwitchingCounting.mem_freeVars.mpr this
  rw [hempty] at this; simp at this

/-- If no term is satisfied, every term's `termSat` is false. -/
theorem not_termSat_of_not_any {cs : List (Clause n)} {σ : Fin n → Option Bool}
    (hany : SwitchingCounting.anyTermSat cs σ = false) {T : Clause n} (hT : T ∈ cs) :
    SwitchingCounting.termSat σ T = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  have : SwitchingCounting.anyTermSat cs σ = true := List.any_eq_true.mpr ⟨T, hT, hc⟩
  rw [this] at hany; exact absurd hany (by decide)

/-- All terms falsified, given no term satisfied and each term is either falsified or has no free
literal. -/
theorem all_falsified_general {cs : List (Clause n)} {σ : Fin n → Option Bool}
    (hany : SwitchingCounting.anyTermSat cs σ = false)
    (h : ∀ T ∈ cs, SwitchingCounting.termFalsified σ T = true ∨ SwitchingCounting.freeLits σ T = []) :
    ∀ T ∈ cs, SwitchingCounting.termFalsified σ T = true := by
  intro T hT
  rcases h T hT with hf | hnf
  · exact hf
  · exact SwitchingCounting.term_falsified_of_not_sat_no_free (not_termSat_of_not_any hany hT) hnf

/-- An active term has a first free literal, on a free variable. -/
theorem activeTerm_first_free {cs : List (Clause n)} {σ : Fin n → Option Bool} {T : Clause n}
    (hact : SwitchingCounting.activeTerm cs σ = some T) :
    ∃ ℓ, (SwitchingCounting.freeLits σ T).head? = some ℓ ∧ σ (litVar ℓ) = none := by
  have hns := SwitchingCounting.activeTerm_anyTermSat_false hact
  have hfind : cs.find? (fun T => !SwitchingCounting.termFalsified σ T &&
      decide (0 < (SwitchingCounting.freeLits σ T).length)) = some T :=
    SwitchingCounting.activeTerm_eq_find hns ▸ hact
  have hpred := List.find?_some hfind
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
  obtain ⟨_, hlen⟩ := hpred
  obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hlen)
  refine ⟨a, by rw [hat]; rfl, ?_⟩
  have ha : a ∈ SwitchingCounting.freeLits σ T := by rw [hat]; exact List.mem_cons.mpr (Or.inl rfl)
  have hlf := (List.mem_filter.mp ha).2
  rw [SwitchingCounting.litFree_var] at hlf
  exact Option.isNone_iff_eq_none.mp hlf

/-- **Gate-A core: the canonical decision tree computes the DNF on extensions.**  For every full
assignment `x` extending `σ`, with fuel at least the star count, the canonical tree evaluates to
the DNF value.  This is the switching lemma's decision-tree conclusion: querying the active
term's first free literal, recursing, and stopping on a satisfied/falsified term computes the DNF
— with the tree's depth bounded by the number of queries (`= path length`). -/
theorem canonicalDT_eval {cs : List (Clause n)} :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      SwitchingCounting.stars σ ≤ fuel → Rung4Restriction.Extends σ x →
      (canonicalDT cs fuel σ).eval x = dnfEval cs x := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ x h0 hext
    have hst : SwitchingCounting.stars σ = 0 := Nat.le_zero.mp h0
    rw [canonicalDT]
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => simp [hany, BoolDecisionTree.eval, (dnfEval_true_of_anyTermSat hany hext)]
    | false =>
      simp only [hany, Bool.false_eq_true, if_false, BoolDecisionTree.eval]
      exact (dnfEval_false_of_all_falsified
        (all_falsified_general hany (fun T _ => Or.inr (freeLits_nil_of_stars_zero hst T))) hext).symm
  | succ fuel ih =>
    intro σ x hfuel hext
    rw [canonicalDT]
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => simp [hany, BoolDecisionTree.eval, (dnfEval_true_of_anyTermSat hany hext)]
    | false =>
      simp only [hany, Bool.false_eq_true, if_false]
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        simp only [BoolDecisionTree.eval]
        refine (dnfEval_false_of_all_falsified (all_falsified_general hany (fun T hT => ?_)) hext).symm
        have hfind : cs.find? (fun T => !SwitchingCounting.termFalsified σ T &&
            decide (0 < (SwitchingCounting.freeLits σ T).length)) = none :=
          SwitchingCounting.activeTerm_eq_find hany ▸ hact
        have hp := (List.find?_eq_none.mp hfind) T hT
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Bool.not_eq_true'] at hp
        by_cases htf : SwitchingCounting.termFalsified σ T = true
        · exact Or.inl htf
        · exact Or.inr (List.length_eq_zero_iff.mp (by have := hp (by simpa using htf); omega))
      | some T =>
        obtain ⟨ℓ, hhead, hfree⟩ := activeTerm_first_free hact
        simp only [hhead, BoolDecisionTree.eval]
        have hstar : SwitchingCounting.stars (fixVar σ (litVar ℓ) (x (litVar ℓ))) ≤ fuel := by
          have := stars_fixVar_lt (b := x (litVar ℓ)) hfree; omega
        have hext' : Rung4Restriction.Extends (fixVar σ (litVar ℓ) (x (litVar ℓ))) x :=
          extends_fixVar hext rfl
        have key : (if x (litVar ℓ) then (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).eval x
              else (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).eval x)
            = (canonicalDT cs fuel (fixVar σ (litVar ℓ) (x (litVar ℓ)))).eval x := by
          cases x (litVar ℓ) <;> simp
        rw [key, ih (fixVar σ (litVar ℓ) (x (litVar ℓ))) x hstar hext']

/-- **De Morgan at the clause level.**  Negating an OR-clause's literals and reading them as an
AND-monomial computes the negation of the clause: `evalLits (map litNeg C.lits) = !(OR C.lits)`. -/
theorem evalLits_map_litNeg (lits : List (Rung4Literal n)) (x : Fin n → Bool) :
    evalLits (lits.map litNeg) x = !(lits.any (fun ℓ => ℓ.eval x)) := by
  induction lits with
  | nil => simp [evalLits]
  | cons ℓ rest ih =>
    simp only [List.map_cons, evalLits, litNeg_eval, ih, List.any_cons, Bool.not_or]

/-- The clause-level adapter in `Clause.eval` terms: `!(C.eval x) = evalLits (map litNeg C.lits) x`. -/
theorem clauseEval_neg (C : Clause n) (x : Fin n → Bool) :
    evalLits (C.lits.map litNeg) x = !(C.eval x) := by
  rw [Clause.eval, evalLits_map_litNeg]

/-- De Morgan over a list: `!(all p) = any (negation)`, transported through a map. -/
theorem not_all_eq_any_map {α β : Type*} (l : List α) (p : α → Bool) (f : α → β) (g : β → Bool)
    (h : ∀ a, (!p a) = g (f a)) : (!l.all p) = (l.map f).any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.all_cons, Bool.not_and, h a, ih, List.map_cons, List.any_cons]

/-- **The OR/AND adapter.**  A ΣΠΣ middle `Term` (AND of OR-clauses, a CNF) negates to a DNF
whose terms are the negated clauses (each an AND-monomial) — the exact object the switching
count consumes.  Variables are preserved (`litVar_litNeg`), so the bottom width is unchanged. -/
theorem termEval_neg (T : Term n) (x : Fin n → Bool) :
    (!T.eval x) = (T.clauses.map (fun C => C.lits.map litNeg)).any (fun t => evalLits t x) := by
  rw [Term.eval]
  exact not_all_eq_any_map T.clauses (fun C => C.eval x) (fun C => C.lits.map litNeg)
    (fun t => evalLits t x) (fun C => (clauseEval_neg C x).symm)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.litTrue_eval_extend
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.termSat_eval_extend
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.termFalsified_eval_extend
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dnfEval_true_of_anyTermSat
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dnfEval_false_of_all_falsified
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDT_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.termEval_neg
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.clauseEval_neg
