# Satisfy/deepest decoder scope — discharging `hinj` (the confound)

Scoping note for the last primitive of the switching lemma: `hinj`, the injectivity of
`ρ ↦ (replayPath cs ρ s, lab ρ)` on the bad set (equivalently, the decoder recovering `ρ` from the
leaf + code).  Everything else in the switching bound is now proved (see
`PROBABILISTIC_MEASURE_SCOPE.md` and the measure-step files); `hinj` is the irreducible core, reached
identically by all four routes.

## The existing decoder and its `hnf`

`Depth3RecoverStreamCorrect.recoverStream` is the codebase's satisfy/deepest decoder.
`recoverStream_eq` proves it reproduces the descent's active stream, carrying the invariant

  `∀ U ∈ cs, termFalsified τ U = termFalsified σ U`   (falsification-agreement),

consumed at each step by `activeTerm_eq_of_falsified_agree` (agreement ⟹ the decoder's recomputed
active term matches the descent's).  `recoverStream_correct` starts the decoder at `τ = (fun _ => none)`
(all-free).  All-free falsifies nothing (`termFalsified_allFree`), so the **base** agreement forces
`termFalsified ρ U = false` for all `U` — i.e. `hnf`.  *That* is the sole origin of the `hnf`
restriction.

## Live-DNF connection (proved)

The base agreement holds on the **live sub-DNF** (`liveCs_base_agree`): on `liveCs ρ cs`, both
`termFalsified (all-free) U` and `termFalsified ρ U` are `false` (`termFalsified_allFree`,
`liveCs_hnf`).  So `recoverStream` applied to `liveCs ρ cs` is correct *unconditionally*.  Combined
with the live-DNF path/selected-set invariance (`replayPath_liveCs`, `replaySel_liveCs`), the descent
on `cs` and on `liveCs ρ cs` coincide.  The remaining gap: the decoder must *know* to run on
`liveCs ρ cs` — identify the `ρ`-falsified terms from the leaf — the confound.

## Two routes to discharge `hinj`

1. **Live-DNF reindexing (cleaner target).**  Reformulate the bad event / measure on the live DNF
   from the start: the canonical tree of `F|ρ` only involves live terms, and dead (`ρ`-falsified)
   terms are removed up front.  Then `hnf` holds by construction, `recoverStream` gives `hinj` on the
   live DNF, and the measure bound (`switching_measure_bound_modulo_inj` + `sum_restrWeight_eq_one`)
   applies.  Remaining work: the bad-event/measure reindexing onto live sub-DNFs (combinatorial,
   building on `liveCs`/`liveCs_base_agree`/the path invariance).

2. **Razborov forward decoder.**  A decoder that, from the leaf + star code, un-sets path variables
   and recomputes active terms on partial states — no all-free base, hence no `hnf`.  This is the
   classical proof's actual decoder; a from-scratch construction (the satisfy-encoding with
   first-satisfied-term identification, anchored by `satStep_satisfies_active`).

Route 1 reuses the live-DNF machinery already built; route 2 is a larger independent build.

## Status / honesty

- Proved: `termFalsified_allFree`, `liveCs_base_agree` (the decoder's base holds on the live sub-DNF),
  plus all measure-step and live-DNF bricks.
- The `hnf`-origin is now pinpointed (the all-free base), and `hinj` is reduced to "identify the live
  sub-DNF from the leaf" (route 1) or "forward decoder without all-free base" (route 2).
- `hinj` itself is **not** discharged or faked.  It is the genuine irreducible core.

Honest ceiling: AC⁰/depth-3.  `Depth3CollapseModel.collapse` and P vs NP untouched.
