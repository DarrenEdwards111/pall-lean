# KRW Information-Complexity Attack Sheet

*The one live frontier from the amortization map: on the communication side, the "god's eye" is
**information complexity** (IC). This sheet extracts, from the literature, the exact missing inequality,
where strong composition uses independence, what breaks in standard composition, and the toy cases.*
*This is a literature-extraction + attack plan, **not** a theorem. No Lean until a real lemma appears.*

---

## 0. The setup (KW → IC)

- **Formula depth = KW communication.** `D(f) = CC(KW_f)`, where in `KW_f` Alice holds `x∈f^{-1}(1)`,
  Bob holds `y∈f^{-1}(0)`, and they output a coordinate `i` with `x_i ≠ y_i`.
- **Composition.** `f ⋄ g` : `f` on `m` bits, each bit fed by an independent copy of `g` on `n` bits.
  KRW conjecture: `CC(KW_{f⋄g}) ≈ CC(KW_f) + CC(KW_g)` ⟹ `P ⊄ NC¹`.
- **Information complexity `IC`.** `IC(π) = I(X;Π|Y) + I(Y;Π|X)` (internal IC of protocol `π`);
  `IC(problem) = min_π IC(π)`. `IC ≤ CC`, and — the reason IC is the right tool — **IC satisfies a
  near-optimal direct-sum theorem** (`IC` of `m` independent copies `= m·IC − o`), which `CC` does not
  (deterministic/randomized `CC` can fail direct sum, e.g. `EQ_n`).

The IC approach (Gavinsky–Meir–Weinstein–Wigderson, STOC 2014): prove the composition bound in `IC`, where
direct-sum tools exist, then transfer to `CC`/depth.

---

## 1. THE EXACT MISSING INEQUALITY

> **Target (standard composition, IC form):**
> `IC(KW_{f ⋄ g}) ≥ IC(KW_f) + IC(KW_g) − o(log n)`
> for explicit `f, g` — or any lower bound strong enough to transfer the strong-composition result to
> standard composition.

Equivalently in the amortization language of the arc:
`CC(KW_{f⋄g}) = CC(KW_f) + CC(KW_g) − amort`, and the target is `amort = o(log n)`.
This is the communication-world twin of the circuit Freshness Lemma; here it is *attackable* because IC has
direct-sum structure.

---

## 2. WHERE STRONG COMPOSITION USES INDEPENDENCE (and why it's provable)

Strong composition (Meir, FOCS 2023 / arXiv 2306.00615) is `f ⋄ g` **forced to behave like a direct-sum
problem**: the `m` inner KW games (one per block) are made **INDEPENDENT** by construction. Then:

- the `m` inner games are `m` genuinely independent copies of `KW_g`;
- the IC **direct-sum theorem applies verbatim** → the inner information is `≥ m·IC(KW_g) − o`;
- combined with the outer game, `IC(strong f⋄g) ≥ IC(KW_f) + IC(KW_g) − o`. **Proved.**
- Meir (2024, arXiv 2410.10189) instantiates outer `= XOR`, inner `= random function`, giving `~3.04 log n`
  in the strong game.
- In the **monotone** setting strong = standard (2306.00615) — so there the reduction is free.

**The independence is the whole point:** it is exactly the "amort = 0 by construction" from the arc.

---

## 3. WHAT BREAKS IN STANDARD COMPOSITION (the gap)

In standard `f ⋄ g` the inner games are **NOT independent** — they share the outer structure:

- After (or while) solving the outer `KW_f` (locating a block `i` where the `g`-values differ), the players
  have already learned information about the inner instances (which block, partial values, the fact that
  block `i` is `g`-critical).
- This **correlation between the outer and inner games** is exactly what lets a single transcript
  potentially "pay for two games" — the non-monotone transcript amortization.
- Direct-sum for correlated instances is not covered by the IC direct-sum theorem; and direct sum is known
  to *fail* in some communication settings (`EQ_n`, randomized private-coin), so it is **not automatic**.

> **The crux (Dinur–Meir): "the naive way of computing `f ⋄ g` is the only optimal way" is the crucial
> barrier.** Standard composition needs this *without* the independence crutch — i.e. prove the players
> cannot exploit outer/inner correlation to reduce total information.

**Negation is the enabler** (consistent with the arc): monotone ⟹ no correlation-exploitation ⟹ strong =
standard; general (with negation) ⟹ correlation can be exploited ⟹ the gap.

---

## 4. THE PRECISE MISSING LEMMA (what would close strong → standard)

Any of the following (in decreasing strength) would do:

1. `standard_from_strong` : `IC(KW_{f⋄g}) ≥ IC(strong-KW_{f⋄g}) − o(log n)` — the reduction itself.
2. `no_correlation_amortization` : a transcript for standard `f⋄g` reveals `≥ IC(KW_f) + IC(KW_g) − o`
   information, even though the inner instances are correlated through `f`.
3. `IC_direct_sum_correlated` : extend the IC direct-sum theorem to the specific correlation structure
   induced by an outer function `f` (not fully independent, not arbitrary).

The heart of all three: **control the mutual information between the outer game's transcript and the inner
instances** — bound how much solving `KW_f` "leaks" about the `KW_g` instances.

---

## 5. TOY CASES (ranked by tractability, with the reason)

| # | Case | Why tractable / status |
|---|---|---|
| 1 | **XOR ∘ random inner, standard** | Outer parity's KW game is trivial (find any differing bit → minimal outer leakage); strong version = 3.04 (arXiv 2410.10189). Attack: bound outer→inner leakage for parity. **Closest to done.** |
| 2 | **XOR ∘ universal relation, standard** | Both sides structureless/parity — the universal relation has nothing to exploit; likely the cleanest first *standard* no-amortization proof. |
| 3 | **Fixed outer, random inner** | Randomness of inner may destroy any correlation the players could exploit → forces `amort → 0`. Probabilistic argument, no explicitness needed for the toy. |
| 4 | **Deterministic-transcript variant** | Deterministic `CC` amortization may be easier to rule out than randomized IC (no distributional subtleties); a stepping stone before the IC version. |
| 5 | **Small inner `g` (constant `n`)** | `IC(KW_g)` is `O(1)`; the composition is `f` on `m` bits with `O(1)`-bit gadgets — reduces to lifting-style analysis with an explicit small gadget. |

**Recommended first target: #2 (XOR ∘ universal relation, standard)** — parity outer + structureless inner
minimizes the correlation the players can exploit, so it is where "no outer→inner leakage" is most likely
provable, and it directly tests whether the independence assumption can be *removed* rather than *assumed*.

---

## 6. Connection to the arc, and honest scope

This sheet realizes the "global godmove" in its only surviving form: **information complexity as global
transcript debt-accounting** — the god's eye that tracks the whole protocol at once and asks whether one
transcript can pay for two games. On the circuit side the global charge provably becomes a function property
(`MeasureBarrier`) or erasure-work (`Bennett`) or occurrence-obstruction (`GCT`) and dies; on the
communication side IC is genuinely alive and gives the universal-relation, monotone, and strong-composition
results — stalling exactly at **non-monotone correlation amortization**, the strong→standard gap.

**Status:** OPEN. The general inequality is the KRW conjecture (`P ⊄ NC¹`); the improvement it would yield
(`3.04 log n`) beats Håstad after 25+ years but is contingent on the reduction. Nothing here is proved.
The next honest work is a **toy no-amortization lemma** (target #2), and Lean should wait until such a lemma
exists — a statement like `IC_no_amortization_for_XOR_lift` or `standard_from_strong_under_independence`.

*Sources:*
[GMWW, information complexity approach (users.math.cas.cz/~gavinsky/papers/FLow.pdf)](https://users.math.cas.cz/~gavinsky/papers/FLow.pdf) ·
[Dinur–Meir, cubic bounds via communication (arXiv/CCC 2016)](https://drops.dagstuhl.de/opus/volltexte/2016/5841/) ·
[Meir, strong composition, FOCS 2023 (arXiv:2306.00615)](https://arxiv.org/html/2306.00615) ·
[Strong composition of XOR and a random function (arXiv:2410.10189)](https://arxiv.org/abs/2410.10189) ·
[near-optimal IC direct-sum theorem (arXiv:2008.07188)](https://arxiv.org/pdf/2008.07188) ·
[KRW via lifting (arXiv:2007.02740)](https://arxiv.org/abs/2007.02740).

*Nothing in this document is `P ⊄ NC¹`, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.*
