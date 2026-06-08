import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityRel

/-!
# Block-DT model, foundation 21: the restriction operation on circuits (branch only)

A formal **restriction-application** operation on the alternating circuit `Circ`: fixing some variables
(via `ρ : Fin n → Option Bool`) and simplifying.  This is the operation the multi-round switching
argument threads through its rounds; with it, a switching round on the *restricted* circuit feeds the
relativized parity bridge automatically.

* `Circ.restrict` — substitute the fixed coordinates of `ρ` (a fixed literal becomes a constant gate).
* `override` — the assignment that fills `ρ`'s holes with `x`.
* `eval_restrict` — substitution semantics: `eval x (restrict ρ c) = eval (override ρ x) c`.
* `eval_restrict_agree` — on `ρ`-consistent `x`, `restrict ρ c` agrees with `c`.
* `restricted_circuit_not_parity` — **the capstone**: if the *restricted* circuit equals a shallow tree
  (depth `< #survivors`), the original circuit disagrees with parity on the subcube — the relativized
  bridge fed by the restriction operation.

## Honest scope

This discharges the "restriction-application operation threaded through the rounds" piece: a switching
round's output on the restricted circuit (`restrict ρ c ≡ shallow tree`, hypothesis `hrt`) now feeds the
relativized parity bound directly.  The single remaining piece for unconditional `parity ∉ AC⁰` is the
`blockStream`↔`DTree` model bridge that *produces* that shallow tree from the switching count.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

namespace Circ

variable {n : ℕ}

/-- The assignment that fills the holes of `ρ` with `x`. -/
def override (ρ : Fin n → Option Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => (ρ i).getD (x i)

mutual
/-- Apply a restriction to a circuit: a fixed literal becomes a constant gate (`and []` = true,
`or []` = false), free literals and gates are kept (gates recursing into children). -/
def restrict (ρ : Fin n → Option Bool) : Circ n → Circ n
  | lit v b => match ρ v with
      | some bv => if bv = b then and [] else or []
      | none => lit v b
  | and cs => and (restrictList ρ cs)
  | or cs => or (restrictList ρ cs)
/-- `restrict` mapped over a child list. -/
def restrictList (ρ : Fin n → Option Bool) : List (Circ n) → List (Circ n)
  | [] => []
  | c :: cs => restrict ρ c :: restrictList ρ cs
end

/-- `restrictList` is `restrict` mapped over the list. -/
theorem restrictList_eq_map (ρ : Fin n → Option Bool) (cs : List (Circ n)) :
    restrictList ρ cs = cs.map (restrict ρ) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [restrictList, List.map_cons, ih]

/-- On `ρ`-consistent inputs, `override` is the identity. -/
theorem override_eq_of_agree (ρ : Fin n → Option Bool) (x : Fin n → Bool)
    (h : DTree.agreeRestriction ρ x) : override ρ x = x := by
  funext i
  simp only [override]
  cases hi : ρ i with
  | none => simp
  | some b => simp [h i b hi]

mutual
/-- **Substitution semantics.**  Evaluating a restricted circuit at `x` is evaluating the original at
the overridden assignment. -/
theorem eval_restrict (ρ : Fin n → Option Bool) :
    ∀ (c : Circ n) (x : Fin n → Bool), eval x (restrict ρ c) = eval (override ρ x) c
  | lit v b, x => by
    rw [restrict]
    cases hv : ρ v with
    | none =>
      show decide (x v = b) = decide (override ρ x v = b)
      simp only [override, hv, Option.getD_none]
    | some bv =>
      show eval x (if bv = b then and [] else or []) = decide (override ρ x v = b)
      simp only [override, hv, Option.getD_some]
      by_cases hbv : bv = b
      · rw [if_pos hbv, decide_eq_true hbv]; rfl
      · rw [if_neg hbv, decide_eq_false hbv]; rfl
  | and cs, x => by
      show evalAll x (restrictList ρ cs) = evalAll (override ρ x) cs
      exact eval_restrictAll ρ cs x
  | or cs, x => by
      show evalAny x (restrictList ρ cs) = evalAny (override ρ x) cs
      exact eval_restrictAny ρ cs x
/-- `restrict` commutes with `evalAll` (under `override`). -/
theorem eval_restrictAll (ρ : Fin n → Option Bool) :
    ∀ (cs : List (Circ n)) (x : Fin n → Bool),
      evalAll x (restrictList ρ cs) = evalAll (override ρ x) cs
  | [], _ => rfl
  | c :: cs, x => by
      show (eval x (restrict ρ c) && evalAll x (restrictList ρ cs))
            = (eval (override ρ x) c && evalAll (override ρ x) cs)
      rw [eval_restrict ρ c x, eval_restrictAll ρ cs x]
/-- `restrict` commutes with `evalAny` (under `override`). -/
theorem eval_restrictAny (ρ : Fin n → Option Bool) :
    ∀ (cs : List (Circ n)) (x : Fin n → Bool),
      evalAny x (restrictList ρ cs) = evalAny (override ρ x) cs
  | [], _ => rfl
  | c :: cs, x => by
      show (eval x (restrict ρ c) || evalAny x (restrictList ρ cs))
            = (eval (override ρ x) c || evalAny (override ρ x) cs)
      rw [eval_restrict ρ c x, eval_restrictAny ρ cs x]
end

/-- On `ρ`-consistent inputs, the restricted circuit agrees with the original. -/
theorem eval_restrict_agree (ρ : Fin n → Option Bool) (c : Circ n) (x : Fin n → Bool)
    (h : DTree.agreeRestriction ρ x) : eval x (restrict ρ c) = eval x c := by
  rw [eval_restrict, override_eq_of_agree ρ x h]

end Circ

/-- **Capstone.**  If the *restricted* circuit equals a shallow decision tree (depth `< #survivors`),
the original circuit disagrees with parity on some `ρ`-consistent input.  The restriction operation feeds
the relativized parity bridge. -/
theorem restricted_circuit_not_parity {n : ℕ} (c : Circ n) (ρ : Fin n → Option Bool) (t : DTree n)
    (hrt : ∀ x, Circ.eval x (Circ.restrict ρ c) = t.eval x)
    (hd : t.depth < (Finset.univ.filter (fun i => ρ i = none)).card) :
    ∃ x, DTree.agreeRestriction ρ x ∧ Circ.eval x c ≠ DTree.parity x := by
  refine DTree.circuit_not_parity_rel c t ρ (fun x hx => ?_) hd
  rw [← Circ.eval_restrict_agree ρ c x hx]
  exact hrt x

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Circ.eval_restrict
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.restricted_circuit_not_parity
