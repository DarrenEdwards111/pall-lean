import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingBadCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSmallCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingWalk
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingWidthFeasible
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHastad
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReplayPath

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

## The DNF/term selector fix — and what it does *not* cover

`ComputationalDepthSwitchingHastad` records the soundness fix: in the *DNF/term* picture a
satisfied term is a decision-tree leaf, so on a deep path every prefix term is *falsified*
(`activeTerm_prefix_falsified`), and a falsified term stays unsatisfied under σ\*
(`termSat_complete_eq_false_of_litFalse`).  Hence the *block-step* selector "first term
satisfied (all-true) under σ\*" is sound — no flip, no block-guessing.

But this rescues the **block** selector only, **not** the flattened one — and that is the
sharpened gate (see below).

## SHARPENED GATE — the shared open core: a sound *flattened* per-step selector

The two label factors split by how many variables a path step fixes per term:

* **Block step** (Codex's structural route, `termPath`/`circuitPath`): a step fixes *all*
  of a term's free variables; under σ\* the term is **all-true → satisfied**, so the
  `termSat` selector finds it.  Label: a subset of `[w]` per term → `((2^w)^m)^numTerms`.
  *Count loose, selector sound.*
* **Flattened step** (`replayPath`, this route, for `(2w)^s`): a step fixes **one**
  variable — the first free literal of the active term (`replayStep`).  The path falsifies
  one literal to kill the term, then advances, so an `s`-step path has exactly `s` selected
  coordinates.  *Count shape right, selector not yet sound.*

**Why the `termSat` selector fails for flattened steps:** after a single-variable step the
processed term has only *one* literal completed; its other free literals remain free, so
under σ\* the term is **not all-true → not satisfied**.  Thus the (sound) `termSat`
selector cannot identify a flattened-processed term, and the DNF reframing — which fixes
the block selector — does **not** transfer to the one-step path.

**The remaining theorem (shared by both routes):**

> Construct a sound *flattened* per-step selector for `replayPath`: recover the active
> term from `σ*` together with the prefix/label, while only **one** literal of the term
> has been completed.  Equivalently, a `(2w)^s`-bounded compact label whose recovery is
> injective.

This is the genuine open core; it is *distinct* from the now-solved block selector, and a
conditional wrapper should name exactly this hypothesis or nothing.

## Honest map of the two routes

1. **`replayPath` contribution** (this file's route): `freeOn_replayPath`,
   `replayPath_inj` — the flattened path object, set-recovery, injectivity (proved clean).
2. **Why the `termSat` selector fails for flattened steps**: a flattened-processed term is
   not fully satisfied under σ\* (only one literal completed) — recorded above.
3. **Existing closed counts** (both unconditional, both loose):
   * Codex's block count `|Bad| ≤ |Short| · ((2^w)^m)^numTerms`
     (`SwitchingCount`/`Assembly`, via `card_bad_le_of_label_bound`);
   * this route's flattened-set count `|Bad| ≤ |Short| · #{|S| ≤ s}` ≈ `nˢ`
     (`bad_card_le_smallsets`).
4. **Remaining target**: a sound flattened selector ⟹ the tight `(2w)^s`.

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
      ((Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ s)).card) ∧
    -- flattened replay path: set-level recovery (the object the (2w)^s route needs)
    (freeOn (replayPath cs ρ s) (replaySel cs ρ s) = ρ) :=
  ⟨freeOn_completionVars_eq cs ρ s, bad_card_le_completion hmem, bad_card_le_smallsets hmem,
    freeOn_replayPath cs ρ s⟩

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_arc_manifest
