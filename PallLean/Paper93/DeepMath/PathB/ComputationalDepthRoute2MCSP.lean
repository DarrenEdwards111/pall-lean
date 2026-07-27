import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRoute2Frontier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTriggerAnatomy

/-!
# Route 2's dent, concretised to the corpus-native sparse target

`Route2Frontier` isolated Route 2 to one concrete `Prop`, `ConcreteDent sparse 5`, for an abstract
sparse target.  This file instantiates that at the repository's actual sparse magnifiable language —
`TriggerAnatomy.mcspLang`, corpus-native MCSP — whose sparsity is already a THEOREM
(`mcspYes_sparse`).  So Route 2's single open statement becomes a concrete, named lower bound on a
concrete, provably-sparse language.

## What is proved

* **`route2_mcsp_frontier`** — with the magnification trigger for `mcspLang s`, the entire remaining
  content of Route 2 is `ConcreteDent (mcspLang s) 5`, i.e. `¬ DTS 5 (mcspLang s)` — corpus-native
  MCSP has no small-space `n^5` algorithm.  Route 2 ⟹ `SAT ∉ P`, from one concrete statement.
* **`mcsp_dent_is_sparse_target`** — the dent is a bound on a target that is PROVABLY sparse (below
  the Shannon threshold), by `mcspYes_sparse` — the exact precondition magnification consumes.  So
  the dent is not a bound on an arbitrary language; it is a bound on the specific sparse object the
  lever was built for.

## Honest scope

The trigger (`¬ DTS 5 (mcspLang s) → SAT ∉ P`) is the published magnification theorem
(McKay–Murray–Williams / Oliveira–Pich–Santhanam) as a named socket, exactly as in
`MagnificationBraid`; it is not proved here.  What this file does is pin the dent to a concrete,
sparse, corpus-native language: Route 2's wall is now "MCSP on the truth-table encoding has no
`n^{1+ε}`, small-space uniform algorithm", the weakest superlinear statement that still magnifies to
`SAT ∉ P`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Route2MCSP

open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.Route2Frontier
open PallLean.Paper93.DeepMath.PathB.SharingModelShannon
open PallLean.Paper93.DeepMath.PathB.TriggerAnatomy

/-- **Route 2 at the concrete sparse target (proved).**  With the magnification trigger for
`mcspLang s`, Route 2 reduces to the single concrete statement `ConcreteDent (mcspLang s) 5` —
corpus-native MCSP has no small-space `n^5` algorithm — which yields `SAT ∉ P`. -/
theorem route2_mcsp_frontier (s : ℕ)
    (trigger : ¬ DTS 5 (mcspLang s) → SAT_not_in_P) :
    ConcreteDent (mcspLang s) 5 → SAT_not_in_P :=
  route2_open_frontier (mcspLang s) trigger

/-- **The dent targets a provably-sparse language (proved).**  Below the Shannon threshold the
`mcspLang s` YES-set is strictly smaller than the `2^{2^m}` tables of its length — the exact
sparsity precondition magnification feeds on.  So Route 2's wall is a bound on the specific sparse
object the lever was built for, not an arbitrary language. -/
theorem mcsp_dent_is_sparse_target (m s : ℕ) (hcard : Fintype.card (Code m s) < 2 ^ 2 ^ m) :
    (mcspYes m s).card < 2 ^ 2 ^ m :=
  mcspYes_sparse m s hcard

end PallLean.Paper93.DeepMath.PathB.Route2MCSP

#print axioms PallLean.Paper93.DeepMath.PathB.Route2MCSP.route2_mcsp_frontier
#print axioms PallLean.Paper93.DeepMath.PathB.Route2MCSP.mcsp_dent_is_sparse_target
