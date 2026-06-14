import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCRestrictionTree

/-!
# One real switching step on a depth-3 `MOD` fragment

The restriction tree (`…ACCRestrictionTree`) reduced depth `d → 2` *granted* a one-step switch
(`RestrictionTreeSwitch`).  This file discharges one genuine instance of that switch **deterministically**, with no
probabilistic hypothesis, on a concrete depth-3 fragment: a **CNF of `MOD` gates** — an AND of clauses, each clause
an OR of `MOD` gates (depth 3: AND / OR / MOD).

The real switching mechanism, proved here: **fixing one bounded-fan-in `MOD` gate's support so the gate is forced
true causes its whole clause to drop from the CNF** (an OR with a true disjunct is satisfied; an AND drops a
satisfied conjunct).  Each clause drop reduces the CNF; once a single clause remains the circuit is depth `≤ 2`.
So this is the atom the Håstad switching iterates — and it is *proved*, using only locality of `MOD` gates under
support fixing and the bounded fan-in (a clause is forced by fixing `≤ s` coordinates).

## What is proved (clean axioms, no `sorry`)

* `modGate_eval_eq_of_agreeOn` — **locality of a `MOD` gate**: it depends only on its support.
* `agree_on_fixed` — inputs respecting a restriction that fixes `S` agree on `S`.
* `evalClause_true_of_mem`, `evalCNF_cons_of_clause_true` — a satisfied disjunct satisfies its clause; a satisfied
  clause drops from the AND.
* `switch_step` — **the real switching step**: if a restriction fixes a gate `G ∈ c`'s support and forces `G`
  true, then on the restricted cube `evalCNF (c :: cnf) = evalCNF cnf` — the clause `c` drops.

## Honest scope

This is a *single, deterministic* switching step on the depth-3 CNF-of-`MOD` fragment, driven by support fixing
(`≤ s` coordinates per forced gate for fan-in `s`).  Iterating it over all clauses reduces the CNF to depth `≤ 2`,
feeding the depth-2 `MOD`-bottom bridge.  What remains probabilistic (the `RestrictionTreeSwitch` wall in general)
is that a *single* random restriction forces a gate in *every* clause at once while keeping enough coordinates live
— here each individual clause drop is mechanized.  So the restriction tree's atom is no longer assumed: it is
proved for this fragment, leaving only the simultaneous/whp control as the named difficulty.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCDepth3Switch

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACCRestrictionTree

variable {n : ℕ}

/-! ## Locality of a `MOD` gate under support fixing -/

/-- **A `MOD` gate depends only on its support (proved).** -/
theorem modGate_eval_eq_of_agreeOn (G : ModGate n) (x y : Fin n → Bool)
    (h : ∀ i ∈ G.support, x i = y i) : G.eval x = G.eval y := by
  have hw : weightOn G.support x = weightOn G.support y :=
    Finset.sum_congr rfl (fun i hi => by rw [h i hi])
  unfold ModGate.eval modQStatOn
  rw [hw]

/-- **Inputs respecting a restriction that fixes `S` agree on `S` (proved).** -/
theorem agree_on_fixed (ρ : Restriction n) (S : Finset (Fin n)) (hfix : ∀ i ∈ S, ∃ b, ρ i = some b)
    (x y : Fin n → Bool) (hx : Agrees ρ x) (hy : Agrees ρ y) : ∀ i ∈ S, x i = y i := by
  intro i hi
  obtain ⟨b, hb⟩ := hfix i hi
  rw [hx i b hb, hy i b hb]

/-! ## The depth-3 CNF-of-`MOD` fragment -/

/-- A clause: an OR of `MOD` gates. -/
abbrev Clause (n : ℕ) := List (ModGate n)

/-- A CNF of `MOD` gates: an AND of clauses (depth 3: AND / OR / `MOD`). -/
abbrev CNFMod (n : ℕ) := List (Clause n)

/-- A clause is satisfied if some `MOD` gate in it is true. -/
def evalClause (c : Clause n) (x : Fin n → Bool) : Bool := c.any (fun G => G.eval x)

/-- The CNF is satisfied if every clause is. -/
def evalCNF (cnf : CNFMod n) (x : Fin n → Bool) : Bool := cnf.all (fun c => evalClause c x)

/-- **A true disjunct satisfies its clause (proved).** -/
theorem evalClause_true_of_mem (c : Clause n) (G : ModGate n) (x : Fin n → Bool)
    (hG : G ∈ c) (htrue : G.eval x = true) : evalClause c x = true := by
  unfold evalClause
  rw [List.any_eq_true]
  exact ⟨G, hG, htrue⟩

/-- **A satisfied clause drops from the AND (proved).** -/
theorem evalCNF_cons_of_clause_true (c : Clause n) (cnf : CNFMod n) (x : Fin n → Bool)
    (hc : evalClause c x = true) : evalCNF (c :: cnf) x = evalCNF cnf x := by
  unfold evalCNF
  rw [List.all_cons, hc, Bool.true_and]

/-! ## The real switching step -/

/-- **One real switching step (proved): a forced clause drops.**  If a restriction `ρ` fixes the support of a gate
`G ∈ c` (bounded fan-in: `≤ s` coordinates) and forces `G` true (it is true at some `ρ`-agreeing witness, hence —
by locality — on the whole `ρ`-cube), then on every `ρ`-agreeing input the clause `c` is satisfied and drops:
`evalCNF (c :: cnf) = evalCNF cnf`.  No probabilistic hypothesis — this is the deterministic atom of the
restriction tree. -/
theorem switch_step (cnf : CNFMod n) (c : Clause n) (G : ModGate n) (ρ : Restriction n)
    (hGc : G ∈ c) (hfix : ∀ i ∈ G.support, ∃ b, ρ i = some b)
    (x₀ : Fin n → Bool) (hx₀ : Agrees ρ x₀) (hG0 : G.eval x₀ = true)
    (x : Fin n → Bool) (hx : Agrees ρ x) :
    evalCNF (c :: cnf) x = evalCNF cnf x := by
  have hGx : G.eval x = true := by
    rw [modGate_eval_eq_of_agreeOn G x x₀ (agree_on_fixed ρ G.support hfix x x₀ hx hx₀)]
    exact hG0
  exact evalCNF_cons_of_clause_true c cnf x (evalClause_true_of_mem c G x hGc hGx)

end PallLean.Paper93.DeepMath.PathB.ACCDepth3Switch

#print axioms PallLean.Paper93.DeepMath.PathB.ACCDepth3Switch.modGate_eval_eq_of_agreeOn
#print axioms PallLean.Paper93.DeepMath.PathB.ACCDepth3Switch.evalCNF_cons_of_clause_true
#print axioms PallLean.Paper93.DeepMath.PathB.ACCDepth3Switch.switch_step
