# Nečiporuk combinatorial-counting formula-size lower bound — status

**Entrypoint:** `ComputationalDepthDepth3FullPipelineManifest.lean` (the second
route section indexes the whole Nečiporuk chain).

**State:** **complete, with no fenced core.** The combinatorial-counting lower-bound
route is assembled end-to-end on an *explicit* hard function and proven super-linear.
All files clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no
`native_decide`.

Unlike the depth-3 route (which reduces to two fenced switching/BSW cores), this
route carries **no** research wall — every step is discharged.

## The five stages (all proved)

1. **Method + tool.**
   - `neciporuk_formula_lower_bound` — `∑ᵢ log₂ #blockResiduals(Sᵢ,F) ≤
     2·clog₂(|Tok|+1)·litCount F + 2·#blocks` for any block partition
     (`ComputationalDepthNeciporukCountingLemma.lean`).
   - `card_blockResiduals_ge` — injective parameter family ⇒ many subfunctions
     (`ComputationalDepthNeciporukSubfunctionLB.lean`).

2. **Explicit hard function + per-block count.**
   `ComputationalDepthNeciporukHardFunction.lean` — `hardF`, a XOR of `m` table-lookups
   into a shared `2^b`-cell data region (`nn = m·b + 2^b` variables).
   `hardF_merge` (subfunction reads the addressed cell) ⇒ `card_blockResiduals_hardF_ge`
   (each address block has ≥ `#{t : t c₀ = false}` distinct subfunctions).

3. **Partition + plugged-in bound.**
   `ComputationalDepthNeciporukHardFunctionLB.lean` — `filter_c0_false_card`
   (`= 2^{2^b−1}`), `blkS`/`blkS_disj`/`blkS_cover` (the `m` address blocks + data
   block partition), `hardF_litCount_lower`:
   `m·(2^b − 1) ≤ 2·clog₂(|Tok|+1)·litCount F + 2·(m+1)`.

4. **Explicit alphabet + headline + a witnessed instance.**
   `...Explicit.lean` — `NF.card_Tok_eq` (`|Tok n| = 16 + 2n`),
   `hardF_litCount_lower_div` (`litCount F ≥ (m·(2^b−1) − 2(m+1)) / (2·clog₂(2·nn+17))`).
   `...Concrete.lean` — `hardF_litCount_lower_concrete`: at `b=10`, `m=1024`
   (`N=11264`), `litCount F ≥ 34850 > 3·N`.

5. **Genuine asymptotic super-linearity.**
   `...Asymptotic.lean` — `expBeatsQuad` (`∀ a, ∃ b ≥ 5, a·b² < 2^b`),
   `hardF_superlinear`: for every `C`, some `b` makes any formula computing the
   balanced-family `hardF` (`m = 2^b`) have `litCount F > C · nn b (2^b)`. **No linear
   bound survives.**

6. **Explicit rate + `N²/log²N`.**
   `...Rate.lean` — `hardF_rate`: balanced family ⇒ `litCount F ≥ 2^{2b}/(8b) ≈ Ω(N²/log³N)`.
   `...Square.lean` — `hardF_rate_sq` / `hardF_rate_sq_family`: balancing the address region
   against the data region (`m·b ≈ 2^b`, via `exists_balanced_m`) tightens this to
   `litCount F ≥ (nn b m)² / (64·b²) = Ω(N²/log²N)`.

7. **Optimal `N²/log N` (the method ceiling).**
   `...SubfunctionMultiplicative` / `SkeletonNoGo` / `LeafFactor` / `SpineContraction` / `Branching` /
   `QsetBound` build the **constant-per-leaf** subfunction bound `card_blockResiduals_le_pow`:
   `s_i ≤ 2·16^{leavesIn}` (no `log n`), via the post-composition closure `Qset` — pass-through-
   invariant (spine contraction) + the branching bound `|Qset(bin)| ≤ 4·|Qa|·|Qb|`.
   `...OptimalBound.lean` rewires the formula bound (`neciporuk_formula_lower_bound_opt`:
   `∑ log₂ s_i ≤ 4·litCount + #blocks`) and re-derives `hardF_rate_opt_family`:
   `litCount F ≥ (nn b m)² / (64·b) = Ω(N²/log N)` — denominator *linear* in `b ≈ log N`.

## Ceiling (honest)

`n²/log n` formula size — the **method ceiling** of Nečiporuk's bound, now reached
(`hardF_rate_opt_family`). This is a genuine **restricted** lower bound on an explicit
function, fully proved with no carried hypothesis, but it is **not** P vs NP. The
Nečiporuk method provably cannot exceed `n²/log n`, so this arc is closed at its
optimum: there is no further strengthening to chase here.
