import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinSpace
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompleteGraphExpansion
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinUnsat

/-!
# Tseitin proof-space observer lower bound — a POSITIVE observer-boundary result

This is the payoff of Option C of `SCOPE_OBSERVER_BOUNDARY_ENTROPY.md` §5: turning the *proof-complexity
space* row from a suggestion into a theorem.

The observer-boundary programme (`ComputationalDepthObserverBoundary.lean`,
`ComputationalDepthObserverLowerBound.lean`) proved the laws of the invariant and the fooling-set lower-bound
*principle*, but the only **positive** boundary lower bounds it could exhibit were fixed-cut ones (EQUALITY),
which are *provably insufficient* for hardness.  Here we exhibit a genuine, unconditional, **super-constant**
observer-boundary lower bound — in the *resolution proof-space observer* model, where the observer's boundary
is the memory of the refutation (its **total space**, `configSize` = literal occurrences held at once).

## The interpretation

A *proof-space observer* of an unsatisfiable formula watches a blackboard refutation: at each step it holds a
configuration of clauses, and its **boundary** is the largest configuration it must hold,
`Blackboard.totalSpace`.  This is the faithful proof-space instance of "observer boundary entropy": the
interface information a deterministic refuter carries through the proof.

## What is proved

* `tseitin_proofSpace_observer_lower_bound` — every blackboard resolution refutation of the expander-Tseitin
  axioms has proof-space observer boundary `≥ c·t` (`t` up to `|V|/4`).  Directly from
  `TseitinSpace.tseitin_totalSpace_lower_bound`.
* `completeGraph_tseitin_space_lower_bound` — the concrete `Kₙ` family (odd charge, expansion `1`): every
  refutation has boundary `≥ t` for every `t` with `1 < t` and `4t ≤ n`.  So the boundary is `≥ ⌊n/4⌋ =
  Θ(|V|)`: **super-logarithmic** in the instance size — unlike a low-boundary (`O(log n)`) observer.
* `tseitin_proofSpace_observer_unbounded` — rigorously: for every bound `K` there is an instance forcing
  observer boundary `≥ K` (with `4K ≤ |V|`).  So this observer boundary is **not** `O(1)` — it genuinely
  separates from a constant/low-boundary observer, which is exactly what the fixed-cut EQUALITY bound failed
  to do.

## Honest scope (the contrast that matters)

This is a positive boundary lower bound for the **resolution proof-space observer** — a *restricted* observer
class.  It does **not** bound the general machine-decomposition observer of an arbitrary SAT-decider (the
central conjecture, `= CookLevinFrontierHyp`, still open and `P`-vs-`NP`-strength).  Its value is precisely
the one §5 predicted: in the regime where super-logarithmic boundary lower bounds are *actually provable*
(proof complexity), the observer-boundary invariant carries a true, non-vacuous, super-constant bound — a
real instance of the principle, in the model where it can be honestly established.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinSpaceObserver

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **Proof-space observer boundary** of a blackboard refutation: the largest configuration it must hold,
in literal occurrences.  (An alias for `Blackboard.totalSpace`, read as the observer's interface memory.) -/
def observerBoundary {compl : TLit Edge → TLit Edge} {Axiom : ResolutionClause (TLit Edge) → Prop}
    {M : Configuration (TLit Edge)} (Ref : Blackboard compl Axiom M) : ℕ :=
  Blackboard.totalSpace Ref

/-- **Tseitin proof-space observer lower bound (general expander).**  Every blackboard resolution refutation
of the expander-Tseitin axioms has proof-space observer boundary `≥ c·t`. -/
theorem tseitin_proofSpace_observer_lower_bound (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Axiom : ResolutionClause (TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht : 1 < t) (hcard : 4 * t ≤ Fintype.card V)
    {M : Configuration (TLit Edge)} (Ref : Blackboard tcompl Axiom M)
    (hbot : (∅ : ResolutionClause (TLit Edge)) ∈ M) :
    c * t ≤ observerBoundary Ref :=
  TseitinSpace.tseitin_totalSpace_lower_bound G charge hunsat Axiom haxiom hc hexp ht hcard Ref hbot

/-- **Concrete `Kₙ` family (proved).**  For the complete graph `Kₙ` with an odd charge (`∑ charge = 1`,
hence globally unsatisfiable) and any Tseitin axiom set, every blackboard resolution refutation has
proof-space observer boundary `≥ t`, for every `t` with `1 < t` and `4t ≤ n`.

Choosing `t = ⌊n/4⌋` gives boundary `≥ ⌊n/4⌋ = Θ(n) = Θ(|V|)` — super-logarithmic in the instance size. -/
theorem completeGraph_tseitin_space_lower_bound (n : ℕ)
    (charge : Fin n → ZMod 2) (hodd : ∑ v, charge v = 1)
    (Axiom : ResolutionClause (TLit {s : Finset (Fin n) // s.card = 2}) → Prop)
    (haxiom : ∀ C, Axiom C →
      ∃ v : Fin n, SemanticMeasure.Implies TSat (TConstr (completeGraph n) charge) {v} C)
    {t : ℕ} (ht : 1 < t) (hcard : 4 * t ≤ n)
    {M : Configuration (TLit {s : Finset (Fin n) // s.card = 2})}
    (Ref : Blackboard tcompl Axiom M)
    (hbot : (∅ : ResolutionClause (TLit {s : Finset (Fin n) // s.card = 2})) ∈ M) :
    t ≤ observerBoundary Ref := by
  have hunsat := tseitin_unsat (completeGraph n) charge hodd
  have := tseitin_proofSpace_observer_lower_bound (completeGraph n) charge hunsat Axiom haxiom
    (c := 1) (t := t) le_rfl (completeGraph_hasExpansion n) ht (by rwa [Fintype.card_fin]) Ref hbot
  simpa using this

/-- **The proof-space observer boundary is not `O(1)`.**  For every target `K ≥ 2`, the `K_{4K}` Tseitin
family (with any odd charge and axiom set) forces proof-space observer boundary `≥ K`.  So the boundary is
unbounded — genuinely super-constant — distinguishing this observer from a constant/low-boundary one (which
is exactly what the fixed-cut EQUALITY bound could not achieve). -/
theorem tseitin_proofSpace_observer_unbounded (K : ℕ) (hK : 2 ≤ K)
    (charge : Fin (4 * K) → ZMod 2) (hodd : ∑ v, charge v = 1)
    (Axiom : ResolutionClause (TLit {s : Finset (Fin (4 * K)) // s.card = 2}) → Prop)
    (haxiom : ∀ C, Axiom C →
      ∃ v : Fin (4 * K), SemanticMeasure.Implies TSat (TConstr (completeGraph (4 * K)) charge) {v} C)
    {M : Configuration (TLit {s : Finset (Fin (4 * K)) // s.card = 2})}
    (Ref : Blackboard tcompl Axiom M)
    (hbot : (∅ : ResolutionClause (TLit {s : Finset (Fin (4 * K)) // s.card = 2})) ∈ M) :
    K ≤ observerBoundary Ref :=
  completeGraph_tseitin_space_lower_bound (4 * K) charge hodd Axiom haxiom
    (by omega) (by omega) Ref hbot

end PallLean.Paper93.DeepMath.PathB.TseitinSpaceObserver

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSpaceObserver.tseitin_proofSpace_observer_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSpaceObserver.completeGraph_tseitin_space_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSpaceObserver.tseitin_proofSpace_observer_unbounded
