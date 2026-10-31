import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMinBoundaryRealized
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompleteGraphExpansion
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinUnsat

/-!
# A FULLY-DISCHARGED proof-space forcing family: complete-graph Tseitin (no named input)

The Lagrangian (`SCOPE_NFRAME_OBSERVER_LAGRANGIAN.md`, route 3) ranks new structured forcing families as
least-action.  The PHP instance bottomed out at a *named* sparse bipartite expander
(`ComputationalDepthBipartiteHallMatching.lean`).  This file gives the contrasting instance: a proof-space
forcing family that is **fully discharged — no named input** — by using **Tseitin on the complete graph
`Kₙ`**, whose expansion the repo *proves* (`completeGraph_hasExpansion`), unlike the sparse bipartite
expander PHP requires.

## Proved (clean axioms, no `sorry`)

`tseitin_complete_min_space` — for `Kₙ`-Tseitin with an **odd charge** (`∑ charge = 1`, hence globally
unsatisfiable) and any Tseitin axiom set, the **minimum total space over all blackboard refutations is `≥ t`**
for every `t` with `1 < t` and `4t ≤ n`.  Taking `t = ⌊n/4⌋` gives `min ≥ ⌊n/4⌋ = Θ(n)`.

Every ingredient is proved in the repo:

* expansion — `completeGraph_hasExpansion n : (completeGraph n).HasExpansion 1` (proved, no hypothesis);
* unsatisfiability — `tseitin_unsat` from the odd charge (proved);
* the band engine + `min` packaging — `MinBoundary.tseitin_minProofSpaceBoundary_ge` (proved).

So this forcing family is **unconditional** (modulo a refutation existing — the formula is unsatisfiable, so
one does by completeness; and the standard Tseitin axiom encoding `haxiom`).

## Why this matters next to PHP

| forcing family | expansion input | status |
|---|---|---|
| PHP proof-space | sparse bipartite **unique-neighbour expander** | **named** (deep construction) |
| `Kₙ`-Tseitin proof-space | `completeGraph_hasExpansion` | **proved** — unconditional |

The complete graph is dense, so its expansion is provable by the elementary injection argument the repo
already has — no lossless-expander construction needed.  This is the honest *fully-closed* member of the
forcing-family lattice: the abstraction demonstrated end-to-end, with the `min`-over-decompositions
super-logarithmic and **nothing named or assumed** beyond the standard encoding and refutability.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinCompleteForcing

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open scoped BigOperators

/-- **Fully-discharged `Kₙ`-Tseitin proof-space forcing family.**  For the complete graph `Kₙ` with an odd
charge (globally unsatisfiable) and any Tseitin axiom set, the minimum total space over *all* blackboard
refutations is `≥ t` (for `1 < t`, `4t ≤ n`).  No named expander input: `Kₙ`'s expansion is proved. -/
theorem tseitin_complete_min_space (n : ℕ) (charge : Fin n → ZMod 2) (hodd : ∑ v, charge v = 1)
    (Axiom : ResolutionClause (TLit {s : Finset (Fin n) // s.card = 2}) → Prop)
    (haxiom : ∀ C, Axiom C →
      ∃ v : Fin n, SemanticMeasure.Implies TSat (TConstr (completeGraph n) charge) {v} C)
    {t : ℕ} (ht : 1 < t) (hcard : 4 * t ≤ n)
    (hne : (MinBoundary.refutationSpaces Axiom).Nonempty) :
    t ≤ MinBoundary.minProofSpaceBoundary Axiom := by
  have hunsat := tseitin_unsat (completeGraph n) charge hodd
  have h := MinBoundary.tseitin_minProofSpaceBoundary_ge (completeGraph n) charge hunsat Axiom haxiom
    (c := 1) (t := t) le_rfl (completeGraph_hasExpansion n) ht (by rw [Fintype.card_fin]; exact hcard) hne
  simpa using h

end PallLean.Paper93.DeepMath.PathB.TseitinCompleteForcing

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinCompleteForcing.tseitin_complete_min_space
