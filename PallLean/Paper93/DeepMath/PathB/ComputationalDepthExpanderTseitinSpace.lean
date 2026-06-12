import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionSpace
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinRootBound

/-!
# Expander-Tseitin resolution TOTAL-SPACE lower bound (proof-space observer)

The proof-space companion of the expander-Tseitin width lower bound.  Running the abstract total-space band
theorem (`Blackboard.totalSpace_ge_of_medium_wide`) with the Tseitin semantic measure gives:

> **Every blackboard (configuration) resolution refutation of the expander-Tseitin axioms has total space
> `≥ c·t`.**

This is a genuine, unconditional (clean-axiom) super-logarithmic *proof-space* lower bound — the first
**positive** observer-boundary lower bound in this development.  It reuses the already-proved
`measure_resolvent_le` (subadditivity), `width_ge_of_medium` (expansion ⇒ width), and `root_bound`
(`μ(⊥) ≥ t`); the band argument is run directly on the configuration sequence, so **no** Atserias–Dalmau
space–width inequality and **no** locking lemma are assumed.

**Honest scope.**  This bounds *total space* (literal occurrences in memory) of a *resolution* refutation —
a restricted proof-space observer.  It is a real Ω(`|V|`)-scale lower bound for that observer (`t` up to
`|V|/4`), **not** the general machine-decomposition observer (still open, `= CookLevinFrontierHyp`).  See
`SCOPE_OBSERVER_BOUNDARY_ENTROPY.md` §5 (proof-complexity row) and the connection in
`ComputationalDepthTseitinSpaceObserver.lean`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinSpace

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open scoped BigOperators

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **Expander-Tseitin resolution total-space lower bound.**  On an expander (`c ≥ 1`), for an
odd/globally-unsatisfiable charge and `4t ≤ |V|` with `t ≥ 2`, *every* blackboard resolution refutation of
the Tseitin axioms (a derivation whose final memory holds the empty clause) has total space `≥ c·t`.

The argument: the first configuration whose maximal clause-measure reaches `t` carries a freshly inferred
medium-measure clause (its parents were both `< t` on the previous board), which is wide by expansion; being
in memory, it forces the configuration's total space — hence the whole refutation's — up to `c·t`. -/
theorem tseitin_totalSpace_lower_bound (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Axiom : ResolutionClause (TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht : 1 < t) (hcard : 4 * t ≤ Fintype.card V)
    {M : Configuration (TLit Edge)} (Ref : Blackboard tcompl Axiom M)
    (hbot : (∅ : ResolutionClause (TLit Edge)) ∈ M) :
    c * t ≤ Blackboard.totalSpace Ref := by
  refine Blackboard.totalSpace_ge_of_medium_wide
    (μ := SemanticMeasure.measure TSat (TConstr G charge)) (a := 1) (t := t) (W := c * t)
    (fun {C D} p => SemanticMeasure.measure_resolvent_le TSat (TConstr G charge) tcompl
      tsat_tcompl hunsat C D p)
    (fun {C} hC => ?_)
    ht
    (fun {C} hlo hhi =>
      width_ge_of_medium G charge hunsat hexp (by omega) hcard hlo hhi)
    Ref
    ⟨∅, hbot, TseitinRootBound.root_bound G charge hunsat hc hexp hcard⟩
  -- axiom measure ≤ 1
  obtain ⟨v, hv⟩ := haxiom C hC
  calc SemanticMeasure.measure TSat (TConstr G charge) C
      ≤ ({v} : Finset V).card :=
        SemanticMeasure.measure_le_of_implies TSat (TConstr G charge) hv
    _ = 1 := Finset.card_singleton v

end PallLean.Paper93.DeepMath.PathB.TseitinSpace

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinSpace.tseitin_totalSpace_lower_bound
