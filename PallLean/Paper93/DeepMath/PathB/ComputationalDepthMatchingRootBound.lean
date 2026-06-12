import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMatchingMeasure

/-!
# The matching-measure root bound `μ(⊥) ≥ t` (proved generically + discharged for complete bipartite)

The remaining input to the graph-PHP proof-space lower bound (besides the flip) is the **root bound**:
`t ≤ matchingMeasure ⊥`.  Since `Implies S ⊥` says *no matching places all of `S`* (i.e. `S` is
**unmatchable**), the root bound is exactly:

> every pigeon-set of size `< t` is **matchable**.

This file proves the root bound **generically from a matchability hypothesis** (the Hall / bipartite-expansion
content, reusable for any graph), and **discharges that hypothesis concretely for complete-bipartite PHP**
(every set of `≤ n` pigeons injects into the `n` holes), giving an *unconditional* `μ(⊥) ≥ n+1`.

## Proved (clean axioms, no `sorry`)

* `root_bound_of_matchable` — **generic**: if every `S` with `|S| < t` is matchable, then `t ≤ μ(⊥)`.  (If
  the minimal `⊥`-implying set were `< t`, it would be matchable, contradicting that it implies `⊥`.)
* `matchable_of_small` — **complete-bipartite matchability**: every `S` with `|S| ≤ n` is matchable — an
  injection `S ↪ Fin n` (which exists as `|S| ≤ n`) *is* a matching placing `S`.
* `complete_root_bound` — **unconditional for complete-bipartite PHP**: `n + 1 ≤ μ(⊥)`.

## Status of the graph-PHP arc

With this, the matching-measure has **subadditivity** (`matchingMeasure_resolvent_le`), **unsatisfiability**
(`m_hunsat`), and a **root bound** (`complete_root_bound`) all proved.  For the *complete-bipartite* graph the
root bound is unconditional; for a bounded-degree **expander** the same `root_bound_of_matchable` applies with
expansion-matchability (Hall via expansion) — the generic form is ready for it.  The one remaining piece for a
full *unconditional* lower bound is the **flip / width link assembled over this measure** (the three proved
cores in `ComputationalDepthGraphPHPExpansion.lean`), which needs the expander's unique-neighbour structure
(absent in complete-bipartite).  So: measure + subadditivity + unsatisfiability + root bound **proved**; the
flip-over-measure is the last expander-specific assembly.
-/

namespace PallLean.Paper93.DeepMath.PathB.PHPProofSpace

open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

/-- **Root bound, generic.**  If every pigeon-set of size `< t` is matchable, then `t ≤ μ(⊥)`. -/
theorem root_bound_of_matchable {m n : ℕ} (hmn : n < m) {t : ℕ}
    (matchable : ∀ S : Finset (Fin m), S.card < t → ∃ a : Matching m n, ∀ p ∈ S, mConstr p a) :
    t ≤ matchingMeasure (∅ : ResolutionClause (PHPLit m n)) := by
  obtain ⟨S, hSimp, hScard⟩ :=
    SemanticMeasure.exists_implies_measure mSat mConstr (m_hunsat hmn) ∅
  by_contra hlt
  push_neg at hlt
  have hScard_lt : S.card < t := by rw [hScard]; exact hlt
  obtain ⟨a, ha⟩ := matchable S hScard_lt
  obtain ⟨l, hl, _⟩ := hSimp a ha
  simp at hl

/-- **Complete-bipartite matchability (proved).**  Every set of `≤ n` pigeons is matchable: an injection
`S ↪ Fin n` (exists since `|S| ≤ n`) gives a matching placing each pigeon of `S` in its image hole. -/
theorem matchable_of_small {m n : ℕ} (S : Finset (Fin m)) (hcard : S.card ≤ n) :
    ∃ a : Matching m n, ∀ p ∈ S, mConstr p a := by
  classical
  obtain ⟨g⟩ : Nonempty ({x // x ∈ S} ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_coe, Fintype.card_fin]; exact hcard)
  refine ⟨⟨fun ph => if hp : ph.1 ∈ S then decide (g ⟨ph.1, hp⟩ = ph.2) else false, ?_⟩, ?_⟩
  · intro h p p' hp hp'
    dsimp only at hp hp'
    by_cases hpS : p ∈ S
    · by_cases hp'S : p' ∈ S
      · rw [dif_pos hpS] at hp
        rw [dif_pos hp'S] at hp'
        have heq : (⟨p, hpS⟩ : {x // x ∈ S}) = ⟨p', hp'S⟩ :=
          g.injective ((of_decide_eq_true hp).trans (of_decide_eq_true hp').symm)
        exact congrArg Subtype.val heq
      · rw [dif_neg hp'S] at hp'; simp at hp'
    · rw [dif_neg hpS] at hp; simp at hp
  · intro p hp
    refine ⟨g ⟨p, hp⟩, ?_⟩
    dsimp only
    rw [dif_pos hp]
    simp

/-- **Unconditional root bound for complete-bipartite PHP.**  `n + 1 ≤ μ(⊥)`. -/
theorem complete_root_bound {m n : ℕ} (hmn : n < m) :
    n + 1 ≤ matchingMeasure (∅ : ResolutionClause (PHPLit m n)) :=
  root_bound_of_matchable hmn (fun S hS => matchable_of_small S (by omega))

end PallLean.Paper93.DeepMath.PathB.PHPProofSpace

#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.root_bound_of_matchable
#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.matchable_of_small
#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.complete_root_bound
