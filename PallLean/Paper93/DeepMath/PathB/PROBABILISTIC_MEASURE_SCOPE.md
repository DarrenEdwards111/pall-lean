# Probabilistic measure step — scope

Scoping note for the **probabilistic** half of the Håstad switching lemma — the step the deterministic
decoder work (3 routes, all `hnf`-restricted; see `STAR_ENCODING_SCOPE.md`) does **not** reach.  The
deterministic decoder gives an *injection*; the measure step *weights* it.

## Goal

Under the `p`-biased random restriction (each variable independently free w.p. `p`, fixed to `0`/`1`
each w.p. `(1-p)/2`):

  `Pr[ canonical tree of F|ρ has depth ≥ s ] ≤ (2w · 2p/(1-p))^s`   (≈ `(5pw)^s` for small `p`).

This is what the deterministic `replay_switching_count` (`Bad.card ≤ Short.card · (2w)^s`, a *cardinality*
bound) becomes under the measure — and it does **not** need a from-end-state decoder valid for all `ρ`
(the confound): the injection alone suffices once weighted.

## Pieces

1. **Weight ratio** — `SwitchingPMeasure` (done).
   - `pweight p n k = p^k · ((1-p)/2)^{n-k}`; `restrWeight p ρ = pweight p n (stars ρ)`.
   - `pweight_ratio : pweight p n (j+s) · ((1-p)/2)^s = pweight p n j · p^s` (cross-multiplied) ⇒
     `weight ρ = weight ρ' · (2p/(1-p))^s` when `ρ'` fixes `s` more variables than `ρ`.

2. **Injection** — already present in spirit.
   - `replayPath_inj` + the decoder give: `ρ ↦ (replayPath cs ρ s, lab ρ)` is injective on `Bad`.
   - Each bad `ρ` (with all `s` steps active) has `stars ρ = stars (replayPath cs ρ s) + s`
     (`replaySel_card = s` and `replaySel = freeVars ρ \ freeVars (end-state)`); this supplies the
     `j+s`/`j` star relation for `pweight_ratio`.
   - *Remaining*: `stars_replayPath`: `stars (replayPath cs ρ s) + (replaySel cs ρ s).card = stars ρ`
     (the path fixes exactly the selected coordinates), and `replaySel_card = s` when all steps active.

3. **Measure assembly** — the new probabilistic step.
   - `Pr[Bad] = ∑_{ρ∈Bad} restrWeight p ρ`.
   - Push through the injection: group by code `c`; for each `c`, the map `ρ ↦ ρ' = end-state` is
     injective (decoder), and `restrWeight p ρ = restrWeight p ρ' · (2p/(1-p))^s` (pweight_ratio).
   - `∑_{ρ : code=c} restrWeight p ρ = (2p/(1-p))^s ∑_{ρ'} restrWeight p ρ' ≤ (2p/(1-p))^s · 1`
     (the `ρ'` are distinct restrictions; total weight `≤ 1`).
   - Sum over the `(2w)^s` codes: `Pr[Bad] ≤ (2w)^s · (2p/(1-p))^s`.

## Status / honesty

- Piece 1 (weight ratio) is proved (`pweight_ratio`).
- Piece 2 (the star bookkeeping `stars (end-state) + s = stars ρ`) is the next reachable brick —
  combinatorial (the path fixes exactly the selected coordinates).
- Piece 3 (the measure assembly) is the genuine probabilistic core: a `Finset.sum` bound over `Bad`
  via the injection and the per-code weight transfer.  It uses the injection as an *injection*, not a
  decoder — so it is **not** blocked by the confound.  It is the real new mathematics and is **not**
  faked.

Honest ceiling: AC⁰/depth-3.  `Depth3CollapseModel.collapse` and P vs NP untouched.
