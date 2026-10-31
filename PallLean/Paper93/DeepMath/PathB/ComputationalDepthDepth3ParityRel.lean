import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ACZeroParity

/-!
# Block-DT model, foundation 20: the relativized parity lower bound (cross-round core) (branch only)

The fact that **survives each restriction round** in the multi-round argument: after fixing some
variables (a restriction `ρ`), parity *restricted to the surviving variables* still requires a decision
tree of depth `≥ #survivors`.  This is the relativized version of `parity_needs_full_depth`, and it is
exactly the invariant the cross-round composition carries forward — each round shrinks the survivor set,
but the relativized bound re-applies on whatever survives.

* `agreeRestriction` — `x` agrees with the fixed coordinates of `ρ`.
* `parity_needs_full_depth_rel` — a tree agreeing with parity on all `ρ`-consistent inputs has depth
  `≥ #survivors` (`= |{i : ρ i = none}|`).
* `circuit_not_parity_rel` — relativized bridge: a circuit equal on `ρ`-consistent inputs to a tree of
  depth `< #survivors` disagrees with parity on some `ρ`-consistent input.
* `reduce_chain` — a `k`-round reduction chain collapses by eval-transitivity (generalises
  `iterate_collapse` to any number of rounds).

## Honest scope

This supplies the parity-side invariant for the cross-round composition.  A fully unconditional
`parity ∉ AC⁰` additionally needs (a) a formal restriction-application operation on the circuit model
threaded through rounds, and (b) the bridge between the `blockStream` switching count and the abstract
`DTree` used here — both substantial.  The relativized lower bound itself is complete and machine-checked.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

namespace DTree

variable {n : ℕ}

/-- `x` agrees with the fixed coordinates of the restriction `ρ`. -/
def agreeRestriction (ρ : Fin n → Option Bool) (x : Fin n → Bool) : Prop :=
  ∀ i b, ρ i = some b → x i = b

/-- **Relativized parity lower bound.**  A decision tree that agrees with parity on every
`ρ`-consistent input has depth `≥` the number of surviving (free) variables. -/
theorem parity_needs_full_depth_rel (t : DTree n) (ρ : Fin n → Option Bool)
    (h : ∀ x, agreeRestriction ρ x → t.eval x = parity x)
    (hd : t.depth < (Finset.univ.filter (fun i => ρ i = none)).card) : False := by
  classical
  set x₀ : Fin n → Bool := fun i => (ρ i).getD false with hx0
  have hcons0 : agreeRestriction ρ x₀ := by
    intro i b hb; simp [hx0, hb]
  have hpv : (pathVars t x₀).card ≤ t.depth := pathVars_card_le_depth t x₀
  set F := Finset.univ.filter (fun i => ρ i = none) with hF
  have hlt : (pathVars t x₀).card < F.card := by omega
  have hns : ¬ F ⊆ pathVars t x₀ := fun hsub => by
    have := Finset.card_le_card hsub; omega
  obtain ⟨j, hjF, hjP⟩ := Finset.not_subset.mp hns
  have hρj : ρ j = none := (Finset.mem_filter.mp hjF).2
  have hcons1 : agreeRestriction ρ (Function.update x₀ j (!x₀ j)) := by
    intro i b hb
    by_cases hij : i = j
    · subst hij; exact absurd hb (by rw [hρj]; simp)
    · rw [Function.update_of_ne hij]; exact hcons0 i b hb
  have hinv : t.eval (Function.update x₀ j (!x₀ j)) = t.eval x₀ :=
    eval_invariant_off_path t x₀ j _ hjP
  have e0 := h x₀ hcons0
  have e1 := h _ hcons1
  rw [parity_flip, hinv, e0] at e1
  simp at e1

/-- **Relativized bridge.**  A circuit equal (on `ρ`-consistent inputs) to a tree of depth
`< #survivors` disagrees with parity on some `ρ`-consistent input. -/
theorem circuit_not_parity_rel (c : Circ n) (t : DTree n) (ρ : Fin n → Option Bool)
    (hct : ∀ x, agreeRestriction ρ x → Circ.eval x c = t.eval x)
    (hd : t.depth < (Finset.univ.filter (fun i => ρ i = none)).card) :
    ∃ x, agreeRestriction ρ x ∧ Circ.eval x c ≠ parity x := by
  classical
  by_contra hall
  push_neg at hall
  refine parity_needs_full_depth_rel t ρ (fun x hx => ?_) hd
  rw [← hct x hx]
  exact hall x hx

end DTree

/-- Eval-equality of circuits: the relation each switching round establishes. -/
def EvalEq (a b : Circ n) : Prop := ∀ x, Circ.eval x a = Circ.eval x b

theorem EvalEq.refl (a : Circ n) : EvalEq a a := fun _ => rfl

theorem EvalEq.trans {a b c : Circ n} (hab : EvalEq a b) (hbc : EvalEq b c) : EvalEq a c :=
  fun x => (hab x).trans (hbc x)

/-- The last circuit reached after a list of rounds starting from `a`. -/
def lastOf : Circ n → List (Circ n) → Circ n
  | a, [] => a
  | _, b :: rest => lastOf b rest

/-- A reduction chain: consecutive circuits are eval-equal. -/
def EvalChain : Circ n → List (Circ n) → Prop
  | _, [] => True
  | a, b :: rest => EvalEq a b ∧ EvalChain b rest

/-- **A chain composes by transitivity.**  Any number of eval-equal rounds compose to a single
eval-equality from the head to the last circuit. -/
theorem evalChain_eval : ∀ (rounds : List (Circ n)) (a : Circ n),
    EvalChain a rounds → EvalEq a (lastOf a rounds)
  | [], a, _ => EvalEq.refl a
  | b :: rest, _a, h => (h.1).trans (evalChain_eval rest b h.2)

/-- **A multi-round reduction chain collapses (any number of rounds).**  If a list of rounds connects
`c₀` to its last circuit by eval-equalities and that last circuit equals a shallow tree, then `c₀` is
not parity.  Each round contributes one `EvalEq`; they compose by transitivity over the whole list. -/
theorem reduce_chain (c₀ : Circ n) (rounds : List (Circ n)) (t : DTree n)
    (hchain : EvalChain c₀ rounds)
    (hlast : ∀ x, Circ.eval x (lastOf c₀ rounds) = t.eval x)
    (hd : t.depth < n) :
    ∃ x, Circ.eval x c₀ ≠ DTree.parity x :=
  circuit_not_parity_of_shallow c₀ t
    (fun x => ((evalChain_eval rounds c₀ hchain) x).trans (hlast x)) hd

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.parity_needs_full_depth_rel
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.circuit_not_parity_rel
