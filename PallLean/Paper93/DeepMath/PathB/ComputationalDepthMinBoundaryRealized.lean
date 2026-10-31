import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinSpace

/-!
# The min-over-decompositions quantifier, realized in a restricted class

The decomposition gap (`ComputationalDepthDecompositionGap.lean`) showed that a *single* decomposition's
boundary lower bound need not survive the minimum over decompositions (EQUALITY: one cut needs `n`, the
streaming decomposition needs `1`).  The separation needs the opposite: the **minimum over every admissible
decomposition** large for a hard family — which is open in the general machine class
(`= CookLevinFrontierHyp`).

This file shows that exact `min`-quantifier is **already achieved** — *proved* — in one restricted observer
class: the **resolution proof-space observer**.  The Tseitin total-space bound holds for *every* blackboard
refutation, so the minimum over *all* of them (the proof-space class's "decompositions") is `≥ c·t`.

So the three regimes of the `min`-over-decompositions quantifier are now pinned:

| observer class | `min` over its decompositions | status |
|---|---|---|
| single-cut continuation | can collapse (EQUALITY: `n → 1`) | ✅ proved (the gap) |
| resolution proof-space | `≥ c·t` for expander-Tseitin | ✅ **proved (here)** |
| general machine-decomposition | `≥ ω(log n)` for SAT | open `= CookLevinFrontierHyp` |

The middle row is the honest realization of the hard quantifier: in a class where the minimum *is* provable,
it is genuinely super-logarithmic.  The contribution is to state and prove that the `min` (not just a fixed
member) is large — closing the formal description of the quantifier the separation turns on.

**Honest scope.**  This is the minimum over the *resolution proof-space* decompositions only — a restricted
class.  It is **not** the minimum over general machine decompositions of an arbitrary SAT-decider; that stays
open.  The bound is conditional on a refutation existing (it does — the formula is unsatisfiable — but
resolution completeness is cited, not formalized here).
-/

namespace PallLean.Paper93.DeepMath.PathB.MinBoundary

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- The set of total-space values achieved by blackboard refutations of `Axiom` (derivations whose final
memory holds the empty clause). -/
def refutationSpaces (Axiom : ResolutionClause (TLit Edge) → Prop) : Set ℕ :=
  { b | ∃ (M : Configuration (TLit Edge)) (Ref : Blackboard tcompl Axiom M),
      (∅ : ResolutionClause (TLit Edge)) ∈ M ∧ b = Blackboard.totalSpace Ref }

/-- **Minimum proof-space boundary over all refutations** — the `min`-over-decompositions quantifier,
instantiated for the resolution proof-space observer class. -/
noncomputable def minProofSpaceBoundary (Axiom : ResolutionClause (TLit Edge) → Prop) : ℕ :=
  sInf (refutationSpaces Axiom)

/-- **The min-over-decompositions boundary is `≥ c·t` for expander-Tseitin (proved).**  Every blackboard
refutation has total space `≥ c·t`, so the *minimum* over all of them does too.  This realizes the hard
`min`-quantifier — super-logarithmic for the resolution proof-space observer class.  Conditional only on a
refutation existing (the formula is unsatisfiable, so one does, by completeness). -/
theorem tseitin_minProofSpaceBoundary_ge (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Axiom : ResolutionClause (TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht : 1 < t) (hcard : 4 * t ≤ Fintype.card V)
    (hne : (refutationSpaces Axiom).Nonempty) :
    c * t ≤ minProofSpaceBoundary Axiom := by
  obtain ⟨M, Ref, hbot, heq⟩ := Nat.sInf_mem hne
  rw [minProofSpaceBoundary, heq]
  exact TseitinSpace.tseitin_totalSpace_lower_bound G charge hunsat Axiom haxiom hc hexp ht hcard Ref hbot

end PallLean.Paper93.DeepMath.PathB.MinBoundary

#print axioms PallLean.Paper93.DeepMath.PathB.MinBoundary.tseitin_minProofSpaceBoundary_ge
