import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingBadCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSmallCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingWalk
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingWidthFeasible
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHastad

/-!
# Switching-lemma decoder arc — consolidated stopping state

**STATUS: REAL.  HONEST CONSOLIDATION.  THE TIGHT `(2w)^s` WALK REDUCES TO `hpre`,
WHICH IS FALSE FOR ARBITRARY BLOCKS AND REQUIRES THE CANONICAL HÅSTAD ENCODING.**

This file is the documented stopping point for the faithful switching-lemma canonical
decoder.  Everything below is proved (clean axioms, no `sorry`); the single remaining gate
is named precisely.

## What is proved

**Faithful σ\* decode core (multi-clause):**
* `freeOn_completionVars_eq` — the σ\* decoder recovers `ρ` (`decode_encode_id`): the
  forward decoder, holding only the satisfying completion and the per-clause labels,
  reconstructs `ρ` with no path history and no access to `ρ`.
* `bad_inj` / `bad_inj'` — injectivity: `ρ` is determined by `(complete ρ …, path-var set)`.

**Count loop (closed and sharpened):**
* `bad_card_le_completion` — `|Bad| ≤ |Short| · 2ⁿ` (loosest).
* `bad_card_le_smallsets` — `|Bad| ≤ |Short| · #{S ⊆ Fin n : |S| ≤ s}` (the "few stars"
  regime, polynomial in `n` for fixed `s`).

**Toward the tight `(2w)^s`:**
* `pathLits_idxOf_lt` — clause-relative indices fit in `Fin w` (type-level feasibility).
* `walkVars` / `walkVars_step` — the σ\*-guided walk and its one-step correctness *given*
  the invariant `hpre`.

## The isolated remaining gate: `hpre`

The tight `(2w)^s` count needs the σ\*-guided walk to reconstruct the path-variable set
from a `PathLabel w s = Fin s → (Fin w × Bool)`.  `walkVars_step` proves the walk's one
step is correct **given** the invariant

  `hpre : ∀ C' ∈ pre, confirm σ* (blockVars C' block) C' = false`

— that no clause skipped before the target intrinsic-confirms with the current block.

**`hpre` is false for arbitrary blocks.**  In the CNF "first-unsatisfied-clause" picture,
a `ρ`-satisfied clause can sit in the skipped prefix; if the current block's positions
index that clause's satisfying (`ρ`-fixed) literal, freeing them unsatisfies it and it
intrinsic-confirms — a *foreign-block flip*.  Pointer + incremental reconstruction do not
prevent this (the satisfying variable is `ρ`-fixed, not a future path variable).

So `hpre` is **not** a lemma about an arbitrary walk: it is a property of *the canonical
encoding*.  Discharging it requires the exact Håstad clause-sequence encoding, where the
processed-clause sequence is forced by structure rather than guessed by `confirm`.

## The fix direction (recorded, not built)

`ComputationalDepthSwitchingHastad` records the soundness insight: in the *DNF/term*
picture a satisfied term is a decision-tree leaf, so on a deep path every prefix term is
*falsified*, never satisfied; and `termSat_complete_eq_false_of_litFalse` shows a falsified
term stays unsatisfied under σ\*.  Hence the decoder's selector "first term satisfied under
σ\*" lands on the first processed term with no flip and no block-guessing — discharging the
analog of `hpre`.  Reconstructing the full exact-Håstad encoding on this footing is a
focused follow-on project, not incremental patching of the CNF walk.

This entire arc is AC⁰-level (the canonical decoding behind the switching lemma);
`Depth3CollapseModel.collapse` and P vs NP are untouched throughout.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- Manifest: the proved load-bearing results of the arc compose (machine-checked that
each statement exists with the claimed shape). -/
theorem switching_arc_manifest
    (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ)
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ' ∈ Bad, complete ρ' (pathLits cs ρ' s) ∈ Short) :
    -- decode core: σ* recovers ρ
    (freeOn (complete ρ (pathLits cs ρ s))
        (completionVars cs (complete ρ (pathLits cs ρ s)) (pathClauseVars cs ρ s)) = ρ) ∧
    -- closed count (loose) and sharpened count
    (Bad.card ≤ Short.card * 2 ^ (Fintype.card (Fin n))) ∧
    (Bad.card ≤ Short.card *
      ((Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ s)).card) :=
  ⟨freeOn_completionVars_eq cs ρ s, bad_card_le_completion hmem, bad_card_le_smallsets hmem⟩

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_arc_manifest
