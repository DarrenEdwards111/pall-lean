import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingBadCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSmallCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingWalk
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingWidthFeasible
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHastad
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReplayPath
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEncLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCanonLabel

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

**UPDATE — the `(2w)^s` count is now PROVED (via the block route, not a flattened selector).**
The above anticipated resolving `(2w)^s` by building a sound *flattened* per-step selector.
That turned out unnecessary: the `(2w)^s` count is achieved with the *sound block selector*
plus a *per-block flat label* (each confirmed term's path-literal index positions, flattened
to a single `(index, isLast)` sequence by `ungroupBlocks`).  See
`encLits_switching_count`/`encLits_switching_count_width` (`EncLabel.lean`):

> `|Bad| ≤ |Short| · (2w)^s`,

with `hdecode` discharged by `encLits_decode` (the concrete canonical path), `hrec` by
`encLits_label_inj` (equal completions + equal flat labels ⟹ `ρ = σ`, through
`termWalkLab_flat_det`), `hidx` by `encFlatLabel_idx_lt` (clause width `≤ w`), and the `hmem`
content by `stars_complete_encLits` (the completion fixes exactly the `s` path stars).  The
only remaining *inputs* are the genuine defining conditions of the bad set (flat-label length
`= s`, nonempty confirmed blocks) and the clause family (width, distinct-variable literals) —
not open lemmas.

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

/-- **Tight manifest: the `(2w)^s` count via the concrete encoder.**  The encoder route's
load-bearing results compose into the tight count.  Machine-checks that: the completion
decodes back to `ρ`; the completion fixes exactly the path-length stars (`hmem` content); and
the full `(2w)^s` bound holds from clause width plus the bad-set defining conditions. -/
theorem switching_arc_manifest_tight {w s : ℕ} [NeZero w]
    (ρ : Restriction n) (cs : List (Clause n))
    {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hblk : ∀ ρ' ∈ Bad, ∀ b ∈ encBlocks ρ' cs, b ≠ [])
    (hlen : ∀ ρ' ∈ Bad, (encFlatLabel ρ' cs).length = s)
    (hmem : ∀ ρ' ∈ Bad, complete ρ' (encLits ρ' cs) ∈ Short) :
    -- decode core for the concrete encoder
    (freeOn (complete ρ (encLits ρ cs))
        (termWalkVars (complete ρ (encLits ρ cs)) (termBlock (encLits ρ cs)) cs cs.length) = ρ) ∧
    -- hmem content: exactly the path stars are fixed
    (stars (complete ρ (encLits ρ cs)) = stars ρ - (encLits ρ cs).length) ∧
    -- the tight (2w)^s count
    (Bad.card ≤ Short.card * (2 * w) ^ s) :=
  ⟨encLits_decode ρ cs hcs, stars_complete_encLits ρ cs hcs,
    encLits_switching_count_width hcs hwidth hblk hlen hmem⟩

/-!
## The two-route fork — and the two meanings of `s` (READ BEFORE COMBINING ROUTES)

The `(2w)^s` switching count is reached by **two distinct routes**, and the `s` in each means
a **different thing**.  Do not equate them or feed one route's `s` into the other.

**Route B (block / `encLits`)** — `encLits_switching_count_width` / `switching_arc_manifest_tight`.
The decoder and count are *complete* (no open lemma).  But here

> `s = (encFlatLabel ρ cs).length` = the number of `(term, position)` pairs (`encFlatLabel_length`),

which **over-counts** a variable shared across several confirmed terms (counted once per term).
So this `s ≥` the number of fixed stars, with equality only when the confirmed terms' literal
lists are variable-disjoint.  The bound is honest; the `s` is the label length, not the star
count.

**Route F (flattened / `replayPath`)** — `replaySel_card_le` + `replay_switching_count`.
Here the path fixes **one variable per step**, so

> `s = the number of steps`, and the selected set has `(replaySel cs σ s).card ≤ s`
> (`replaySel_card_le`) — the *tight* star count, no over-count.

But Route F's decoder is **not proved**: `replay_switching_count` is conditional on the named
hypothesis `hdec` (a per-step decoder `D` recovering `replaySel` from the falsify end-state and
a `(2w)^s` label).

**The open research target (Route F's `hdec`):** *active-term recovery under mid-completion.*
At the end-state the final term may be only partially falsified — neither `termSat` nor
falsified — so the sound block selector does not apply, and reverse clause/term recovery is
ambiguous (the same obstruction that motivated the satisfying-completion route).  This is the
theorem to target, stated as `hdec` in `replay_switching_count`; it is *not* "one more lemma."

**Summary:** Route B gives a complete count with a loose (over-counted) `s`; Route F gives a
tight `s` but an open decoder.  Closing Route F's `hdec` would give the textbook `(2w)^s` with
`s` = star count and a working decoder.
-/

/-- **Fork manifest.**  Machine-checks both routes' final shapes coexist: Route B's *complete*
`(2w)^s` count (with `s` = flat-label length) and Route F's *proved tight set bound*
(`≤ s` coordinates, `s` = step count).  Route F's count itself is the conditional
`replay_switching_count` (open `hdec`), referenced in the doc above, not bundled here. -/
theorem switching_two_route_fork {w s : ℕ} [NeZero w] (cs : List (Clause n)) (σ : Restriction n)
    {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hblk : ∀ ρ' ∈ Bad, ∀ b ∈ encBlocks ρ' cs, b ≠ [])
    (hlen : ∀ ρ' ∈ Bad, (encFlatLabel ρ' cs).length = s)
    (hmem : ∀ ρ' ∈ Bad, complete ρ' (encLits ρ' cs) ∈ Short) :
    -- Route B: complete (2w)^s count (s = (term,position) label length)
    (Bad.card ≤ Short.card * (2 * w) ^ s) ∧
    -- Route F: proved tight set (s = step count, one variable per step, no over-count)
    ((replaySel cs σ s).card ≤ s) :=
  ⟨encLits_switching_count_width hcs hwidth hblk hlen hmem, replaySel_card_le cs σ s⟩

/-!
## The canonical `(2w)^s` route (resolves the over-count, generally)

Route B's `s` over-counts variables shared across confirmed clauses (it counts `(term,
position)` pairs).  The **canonical single-assignment** label fixes this *generally*: assign
each path variable to its **first** confirmed clause.  The per-clause blocks are then disjoint
by construction (`canonBlocks_pairwise_disjoint`), so the label length equals the **star
count** for arbitrary (shared-variable) clause families (`canonBlocks_sum_card_eq_length`) — no
read-once hypothesis.

The empty-block boundary problem (a confirmed clause whose path variables are all claimed
earlier) is handled by the delimiter-free `(index, isLast)`-per-position packing into
`PathLabel w s` (`canonMarkLabel`): the `isLast` bit is the per-position boundary, absorbed
into the `2` of `2w`, so the label lives in exactly `(2w)^s` (no per-block delimiter cost; the
tokenized `tokFlatten` alternative would cost `(w+1)^(s+#blocks)` by `tokFlatten_length`).
`canonMarkLabel_det` determines the path-variable set from `σ*` + the label;
`canonMarkLabel_switching_count` gives `|Bad| ≤ |Short| · (2w)^s` with `s` = star count.
-/

/-- **Canonical-route manifest.**  The canonical `(2w)^s` route composes: the first-claim label
length equals the star count (tight, general), the canonical blocks partition the path
variables, the label space is exactly `(2w)^s`, and the switching count holds with that tight,
delimiter-free `s`. -/
theorem switching_canonical_manifest {w s : ℕ} [NeZero w]
    (ρ : Restriction n) (cs : List (Clause n))
    {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hne : ∀ ρ' ∈ Bad, ∀ b ∈ canonPosBlocks (encLits ρ' cs) ∅
        (cs.filter (termSat (complete ρ' (encLits ρ' cs)))), b ≠ [])
    (hlen : ∀ ρ' ∈ Bad, (ungroupBlocks (canonPosBlocks (encLits ρ' cs) ∅
        (cs.filter (termSat (complete ρ' (encLits ρ' cs)))))).length = s)
    (hmem : ∀ ρ' ∈ Bad, complete ρ' (encLits ρ' cs) ∈ Short) :
    -- tight: canonical first-claim label length = star count (general, no disjointness)
    (((canonBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs))))).map Finset.card).sum
        = (encLits ρ cs).length) ∧
    -- canonical blocks partition the path-variable set
    ((canonBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs))))).Pairwise (fun A B => Disjoint A B)) ∧
    -- label space cardinality (2w)^s
    ((Finset.univ : Finset (PathLabel w s)).card = (2 * w) ^ s) ∧
    -- the (2w)^s switching count with tight canonical s, delimiter-free
    (Bad.card ≤ Short.card * (2 * w) ^ s) :=
  ⟨canonBlocks_sum_card_eq_length ρ cs hcs,
    canonBlocks_pairwise_disjoint (encLits ρ cs)
      (cs.filter (termSat (complete ρ (encLits ρ cs)))) ∅,
    card_canonMarkLabel_space w s,
    canonMarkLabel_switching_count hcs hwidth hne hlen hmem⟩

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_arc_manifest
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_arc_manifest_tight
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_two_route_fork
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_canonical_manifest
