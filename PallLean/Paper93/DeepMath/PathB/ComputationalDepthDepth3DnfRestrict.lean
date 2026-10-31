import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DnfTree

/-!
# Block-DT model, foundation 24: DNF → DTree, increment 2 — restriction pruning (branch only)

The descent assembly, step 2: under a restriction `ρ`, the DNF tree prunes.  A *dead* clause (some
literal forced false) drops out, and a *live* clause keeps only its **free** literals (the fixed ones
are automatically true on `ρ`-consistent inputs).  So on the subcube, the DNF is computed by `dnfTree`
of the pruned clause list, whose depth is `≤ #live · w` — strictly smaller whenever the restriction
kills clauses.

* `litKilled` / `freeLit` / `clauseLive` — restriction status of literals/clauses (clean `Rung4Literal`
  world, no block-arc dependency).
* `restrictClause` / `restrictDnf` — drop dead clauses, keep free literals.
* `restrictDnf_dnfValue` — on `ρ`-consistent inputs the pruned DNF computes the same value.
* `restrictDnfTree_eval` — the pruned tree computes the DNF on the subcube.
* `restrictDnfTree_depth_le` — depth `≤ #live · w`.

## Honest scope

Increment 2 is the **restriction pruning** (non-adaptive): depth drops from `#clauses · w` to
`#live · w`, with `#live` the clauses surviving `ρ`.  The *adaptive* switching small-depth bound
(`≤ #blocks · width`, with `#blocks = blockStream length` small — the canonical decision tree with
per-leaf restriction threading) is the remaining hard core, increment 3.  Built incrementally and
honestly; no `sorry`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

namespace DTree

variable {n : ℕ}

/-- Bool equality from the `= true` iff. -/
theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- A literal is killed by `ρ` if `ρ` fixes its variable to the value making it false. -/
def litKilled (ρ : Fin n → Option Bool) : Rung4Literal n → Bool
  | Rung4Literal.pos v => match ρ v with | some b => !b | none => false
  | Rung4Literal.neg v => match ρ v with | some b => b | none => false

/-- A literal is free under `ρ` if its variable is unset. -/
def freeLit (ρ : Fin n → Option Bool) : Rung4Literal n → Bool
  | Rung4Literal.pos v => decide (ρ v = none)
  | Rung4Literal.neg v => decide (ρ v = none)

/-- A clause is live under `ρ` if no literal is killed. -/
def clauseLive (ρ : Fin n → Option Bool) (T : Clause n) : Bool := !T.lits.any (litKilled ρ)

/-- Restrict a clause to its free literals. -/
def restrictClause (ρ : Fin n → Option Bool) (T : Clause n) : Clause n :=
  ⟨T.lits.filter (freeLit ρ)⟩

/-- Restrict a DNF: drop dead clauses, keep free literals. -/
def restrictDnf (ρ : Fin n → Option Bool) (cs : List (Clause n)) : List (Clause n) :=
  (cs.filter (clauseLive ρ)).map (restrictClause ρ)

/-- **A fixed, unkilled literal is true on consistent inputs.** -/
theorem fixed_lit_true (ρ : Fin n → Option Bool) (x : Fin n → Bool) (ℓ : Rung4Literal n)
    (hx : agreeRestriction ρ x) (hfree : freeLit ρ ℓ = false) (hkill : litKilled ρ ℓ = false) :
    Rung4Literal.eval ℓ x = true := by
  cases ℓ with
  | pos v =>
    cases hv : ρ v with
    | none => simp [freeLit, hv] at hfree
    | some b =>
      have hxv : x v = b := hx v b hv
      simp only [litKilled, hv] at hkill
      simp only [Rung4Literal.eval, hxv]
      cases b <;> simp_all
  | neg v =>
    cases hv : ρ v with
    | none => simp [freeLit, hv] at hfree
    | some b =>
      have hxv : x v = b := hx v b hv
      simp only [litKilled, hv] at hkill
      simp only [Rung4Literal.eval, hxv]
      cases b <;> simp_all

/-- **A dead clause is false on consistent inputs.** -/
theorem dead_clause_false (ρ : Fin n → Option Bool) (x : Fin n → Bool) (T : Clause n)
    (hx : agreeRestriction ρ x) (hdead : clauseLive ρ T = false) :
    T.lits.all (fun ℓ => Rung4Literal.eval ℓ x) = false := by
  have hany : T.lits.any (litKilled ρ) = true := by
    simp only [clauseLive] at hdead
    by_contra hc
    rw [Bool.not_eq_true] at hc
    rw [hc] at hdead
    simp at hdead
  rw [List.any_eq_true] at hany
  obtain ⟨ℓ, hℓ, hkill⟩ := hany
  have hℓfalse : Rung4Literal.eval ℓ x = false := by
    cases ℓ with
    | pos v =>
      cases hv : ρ v with
      | none => simp [litKilled, hv] at hkill
      | some b =>
        have hxv : x v = b := hx v b hv
        simp only [litKilled, hv] at hkill
        simp only [Rung4Literal.eval, hxv]
        cases b <;> simp_all
    | neg v =>
      cases hv : ρ v with
      | none => simp [litKilled, hv] at hkill
      | some b =>
        have hxv : x v = b := hx v b hv
        simp only [litKilled, hv] at hkill
        simp only [Rung4Literal.eval, hxv]
        cases b <;> simp_all
  cases hres : T.lits.all (fun ℓ => Rung4Literal.eval ℓ x) with
  | false => rfl
  | true =>
    rw [List.all_eq_true] at hres
    have := hres ℓ hℓ
    rw [hℓfalse] at this
    exact absurd this (by simp)

/-- A list `all` over a predicate equals the `all` over its `q`-filter, when every non-`q` element
already satisfies the predicate. -/
theorem all_eq_filter_all {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, q a = false → p a = true) :
    l.all p = (l.filter q).all p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    by_cases hq : q a = true
    · rw [List.filter_cons_of_pos hq, List.all_cons, List.all_cons, ih']
    · simp only [Bool.not_eq_true] at hq
      rw [List.filter_cons_of_neg (by simp [hq]), List.all_cons, ih',
        h a (List.mem_cons_self ..) hq, Bool.true_and]

/-- **A live clause computes the same on consistent inputs as its free restriction.** -/
theorem live_clause_eval (ρ : Fin n → Option Bool) (x : Fin n → Bool) (T : Clause n)
    (hx : agreeRestriction ρ x) (hlive : clauseLive ρ T = true) :
    T.lits.all (fun ℓ => Rung4Literal.eval ℓ x)
      = (restrictClause ρ T).lits.all (fun ℓ => Rung4Literal.eval ℓ x) := by
  have hany : T.lits.any (litKilled ρ) = false := by
    simp only [clauseLive] at hlive
    by_contra hc
    rw [Bool.not_eq_false] at hc
    rw [hc] at hlive
    simp at hlive
  rw [restrictClause]
  apply all_eq_filter_all
  intro ℓ hℓ hfree
  refine fixed_lit_true ρ x ℓ hx hfree ?_
  by_contra hc
  rw [Bool.not_eq_false] at hc
  have : T.lits.any (litKilled ρ) = true := List.any_eq_true.mpr ⟨ℓ, hℓ, hc⟩
  rw [this] at hany
  exact absurd hany (by simp)

/-- **The pruned DNF computes the same value on consistent inputs.** -/
theorem restrictDnf_dnfValue (ρ : Fin n → Option Bool) (x : Fin n → Bool) (cs : List (Clause n))
    (hx : agreeRestriction ρ x) :
    dnfValue (restrictDnf ρ cs) x = dnfValue cs x := by
  apply bool_eq_of_iff
  simp only [dnfValue, restrictDnf, List.any_eq_true, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨S, ⟨T, ⟨hT, hlive⟩, rfl⟩, hsat⟩
    exact ⟨T, hT, by rw [live_clause_eval ρ x T hx hlive]; exact hsat⟩
  · rintro ⟨T, hT, hsat⟩
    by_cases hlive : clauseLive ρ T = true
    · exact ⟨restrictClause ρ T, ⟨T, ⟨hT, hlive⟩, rfl⟩,
        by rw [← live_clause_eval ρ x T hx hlive]; exact hsat⟩
    · simp only [Bool.not_eq_true] at hlive
      exact absurd hsat (by rw [dead_clause_false ρ x T hx hlive]; simp)

/-- **The pruned tree computes the DNF on the subcube.** -/
theorem restrictDnfTree_eval (ρ : Fin n → Option Bool) (x : Fin n → Bool) (cs : List (Clause n))
    (hx : agreeRestriction ρ x) :
    (dnfTree (restrictDnf ρ cs)).eval x = dnfValue cs x := by
  rw [dnfTree_eval, restrictDnf_dnfValue ρ x cs hx]

/-- **The pruned tree has depth `≤ #live · w`.** -/
theorem restrictDnfTree_depth_le (ρ : Fin n → Option Bool) (cs : List (Clause n)) (w : ℕ)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    (dnfTree (restrictDnf ρ cs)).depth ≤ (cs.filter (clauseLive ρ)).length * w := by
  have : (restrictDnf ρ cs).length = (cs.filter (clauseLive ρ)).length := by
    rw [restrictDnf, List.length_map]
  rw [← this]
  refine dnfTree_depth_le_mul (restrictDnf ρ cs) w ?_
  intro T hT
  rw [restrictDnf, List.mem_map] at hT
  obtain ⟨S, hS, rfl⟩ := hT
  rw [List.mem_filter] at hS
  refine le_trans ?_ (hw S hS.1)
  rw [restrictClause]
  exact (List.length_filter_le _ _)

end DTree

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.restrictDnfTree_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.restrictDnfTree_depth_le
