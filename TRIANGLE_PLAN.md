# The amoPair triangle under the grand loop — design (E4's last families)

## The row-bound obstruction

The at-most-one pair families are triangular: at time `t`, clauses `[(hV t i, F), (hV t j, F)]`
for all `0 ≤ i < j ≤ P`.  The lp3 row decomposition (row `i`, inner `d = 0..R-1`, `R = P - i`,
pair `(i, i+1+d)` via the fused splice) has **row-dependent inner bounds `R = P - i` that
DECREASE** as `i` increments.  Under the grand loop the rows must be a runtime loop (a `repP`
level), so the per-row body must be uniform — but an exact counter region (`unaryD R`) cannot
shrink in place (region lengths are fixed addresses), and `jT`-padding only supports `jT_incr`.

## The resolution: reindex by the larger coordinate

Enumerate the triangle by rows `j = 1..P` (row loop count = `P`, FIXED — `repP`-drivable), inner
`i = 0..j-1` emitting `(i, j)` directly (no fused splice needed).  The row's inner bound is `j`
— INCREASING by one per row, maintainable by the proved in-place `jT_incr` on a capacity-padded
bound mirror.  `j` also appears as the clause's second coordinate, and splice-marking would
conflict with the bound's find-marking, so the row state keeps **two copies** of `j`:

* the **bound mirror** `jT P j` — the engine's own loop bound (find-marked during the run,
  healed by the finale: the find/mark/done and heal pair-steps are content-blind on padded
  counters, exactly as brick 30 established);
* the **source mirror** `jT P j` — spliced (jsT/jhT machinery) for the second coordinate.

## The engine (`pairTMachine` = loopProg3T with everything padded)

Layout (as assembled under the two loop levels):

```
cntT B t ++ (cntT P r ++ (jT P j ++ (jT B t ++ (jT P j ++ (jT P i ++ encodeD out)))))
  grand      row loop     bound      t-mirror   j-source    live
```

The engine itself is proven with two generic prefixes `(G1, g1) (G2, g2)` (the `addTPP` pattern).
Per row it loops `i = 0..j-1`, body = `bits ++ spT(t) ++ bits ++ spJ(i) ++ bits ++ bits ++
spT(t) ++ bits ++ spB2(j) ++ bits` shaped to `encodeClause' [(headVar t i, F), (headVar t j, F)]`
(the aloHead-style factorization; `spB2` = the splice of the `j`-source mirror).

**Machine census** (from lp3p's `Fin 117`): the boundary-event scans absorb padding as equal
pairs (the brick-30 observation) — the bit track and every splice seek are UNCHANGED.  What
changes: (i) ten second-level prefix-skip pairs (the `addTPP` chaining of lp3p's pairs
`97–116`); (ii) fifteen pad-crossing pairs, one per low-lo hand-off that crosses a padded region
into a find/heal/walk: spliceT1 find+heal (1+1), spliceT2 find+heal (2+2), spliceJ find+heal
(3+3), increment (3).  Total `Fin 167`.  The loop-find and the finale heal are content-blind on
the padded bound (find marks filled pairs, done at the value marker; heal restores `jhT`).

**Lift levels**: six prefixes before the output (`liftJ5/liftJ6`, `preD6/preD7`,
`writes_snoc6/7` — one-line compositions over the proved level-4/5 layer).

## The row interstitial (`interRowMachine`)

One left-to-right pass after each row: `jT_incr` the bound mirror, `jT_incr` the source mirror,
zero the live (`zeroT` walk) — the `interT` pattern with two increments.  Fixed clock
(pad-crossing is value-independent).

## The triangle composite

`rep(grand) ∘ repP(row) ∘ (pairT ⨟ interRow)` — both loop combinators exist and compose
(`rep_run` / `repP_run`, brick 35); the per-grand-round body also chains the two-source families
(brick 33's fold) before the row loop, and `interT` advances the grand mirror.

## E6 (after the triangle)

`seq`-chain: `majorant_k` (E2, brick 35 — computes `B := p(|x|)` into the grand counter region)
⨟ init families (`initLoopP`, brick 27) ⨟ the grand loop over the full per-`t` family fold ⨟ the
finale; then `decodeFormula'` faithfulness + freeze/monotonicity close `EmitsTableau' M p`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
