# Star-encoding scope — Håstad/Razborov switching-lemma decoder

Scoping note for the canonical switching-lemma decoder (the "star-encoding"), the genuine path
toward closing **Obligation 1 / the confound** of the depth-3 AC⁰ arc (`DEPTH3_STATUS.md`).

## Goal

Discharge `replay_switching_count`'s `hdec` (or its set-route form
`replay_count_modulo_freeIndicator`) for the **general** bad set — where `ρ` may itself falsify
terms — giving the tight `(2w)^s` switching count unconditionally, hence the depth-3 lower bound
modulo only the (separate) collapse.

## What already exists (verified this session)

Decoder machinery, three parallel routes, **all proved only for the `ρ`-falsifies-nothing regime**:

| route | selector | end-state decoder | correctness lemma | regime |
|---|---|---|---|---|
| falsify | `activeTermLit` (¬falsified∧free) | `decodedSel` | `decodedSel_eq_replaySel` | `hnf` |
| satisfy / star | `satStepLit` via `firstUnsat` | `recoverStream` | `recoverStream_correct` | `hnf` + `hleaf` |
| deepest | `falSel ∪ satSel` | `decodedSel ∪ satSel` | `decodedSel_union_satSel_eq_deepestSel` | `hnf` |

Supporting infrastructure already present:
- satisfy process: `satStep`/`satPath`/`satSel`, `satStep_backward` (per-step inverse),
  `clauseSatisfied_satFix`, `firstUnsat`, and the new `satStep_satisfies_active`
  (`SwitchingStarAnchor`) — the satisfy step satisfies its active clause (recomputability anchor).
- star-pattern label: `BlockPathLabel w s := Fin s → Finset (Fin w)`, count `(2^w)^s`
  (`card_blockPathLabel`) — the subset-per-step ("stars") label.
- position label: `PathLabel w s := Fin s → Fin w × Bool`, count `(2w)^s` (`card_pathLabels`).
- set-route (this session): `replaySel_subset_decodedSel` (completeness, unconditional),
  `replaySel_eq_decodedSel_filter` (exact decomposition `replaySel = decodedSel ∩ {ρ-free}`),
  `replay_count_modulo_freeIndicator` (count modulo a ρ-free Boolean indicator),
  `replay_count_nothing_falsified_setroute` (trivial indicator closes `hnf`).

## Key scoping finding

**The star/satisfy route does *not* break the confound.**  `recoverStream_correct` is `hnf`-restricted
exactly like the falsify and set routes.  All three deterministic decoders bottom out at
ρ-falsifies-nothing.  Both the per-step `recT` route and the set-route `isFree` were driven (this
session) to the *same* irreducible point — recover the per-step active term / ρ-free indicator from
the end-state — and that is the confound (`confound_uncovered`).

So the confound is a genuine mathematical core, not an artifact of one selector: when `ρ` falsifies a
term, that term is *dead*, and its variables contribute spurious entries to the end-state decoder that
no deterministic, end-state-only decoder can distinguish from path-fixed variables.

## What breaking it actually requires

The classical proof does **not** decode arbitrary bad `ρ` deterministically in this form.  It either
(a) restricts to live DNFs (dead terms removed up front — the `hnf`-style normalization, already what
the codebase proves), then runs the probabilistic argument (random `ρ`, the bad event over the *live*
tree, union bound over star patterns); or (b) uses a decoder that explicitly carries the dead-term
structure.  Concretely, the remaining work is:

1. **Live-DNF normalization**: reduce a general `ρ` to the live sub-DNF (drop ρ-falsified terms),
   show the canonical tree / selected set is unchanged on live terms.  This converts the general case
   to the already-proved `hnf` case on the live sub-DNF.  *This is the genuine reachable next target*
   — it is combinatorial (term filtering + invariance), not the probabilistic core.
2. **Probabilistic switching lemma**: random `ρ`, `Pr[depth ≥ s] ≤ (5pw)^s` via the encoding
   injection into star patterns × short restrictions (the count is the `(2w)^s`/`(2^w)^s` label
   bound, already present; the measure step is new).

Step 1 is the honest next brick; step 2 is the larger probabilistic build.

## Honest ceiling

AC⁰/depth-3.  `Depth3CollapseModel.collapse` (general circuit ↔ collapse) and P vs NP are untouched.
Nothing here is faked or socketed; the confound and the probabilistic step remain genuine open cores.
