# `p vs np1.pdf` → Lean status map (kernel-verified 2026-07-24)

Paper: *Toward P vs NP: An Observer-Theoretic Separation via SPDP Rank* (280 pp).
Verification key: **[K]** = `#print axioms` kernel-checked this session; **[G]** = source/grep.

The paper's spine is four parts: **(1) P-side upper bound** (compiled P-time ⇒ low SPDP rank),
**(2) NP-side lower bound** (explicit family ⇒ high SPDP rank), **(3) God-Move extraction**
(rank-monotone gauge pulls the hard object out of the P-solver), **(4) contradiction** under P=NP.

---

## Part 2 — NP-side lower bound  ✅ GENUINELY PROVED, axiom-clean

| Paper claim | Lean symbol | Status |
|---|---|---|
| Thm 5 (SPDP separation, compiled model); the explicit minor witness | `IdentityMinorReal.identity_minor_beats_poly` | **PROVED, `[propext, Classical.choice, Quot.sound]`** **[K]** |
| Tseitin/expander family has the high-rank minor | `IdentityMinorReal.tseitin_identity_minor_rank` | **PROVED, clean** **[K]** |
| Compiled NP lower bound, any DTM | `PaperFaithfulSeparation.compiled_np_lower_bound_any_dtm` | PROVED (clean per prior audit) **[G]** |

**This is the solid core.** An explicit family whose SPDP-rank minor `C(n/3, log n)` beats every
polynomial — real, kernel-clean mathematics. No custom axioms.

## Part 4 — the arithmetic contradiction  ✅ PROVED (but conditional inputs)

| Paper claim | Lean symbol | Status |
|---|---|---|
| Thm 12 rank sandwich `k ≤ … ≤ B < k` at `n=2⁸⁰⁴` | `PaperFaithfulSeparation.no_rank_sandwich_at_2pow804` | **PROVED, clean** **[K]** |
| Cor 9 / closeout: `CookLevinFrontierHyp ⇒ ¬PeqNP` | `Step4Compiler.peqnp_false_of_frontier` | **PROVED, clean — but takes `CookLevinFrontierHyp` as hypothesis** **[K]** |
| Thm 12 headline `P ≠ NP` | `Step4Compiler.P_ne_NP_finally_closed (hfront : CookLevinFrontierHyp)` | **CONDITIONAL on the socket** **[G]** |

The pure arithmetic is real. Everything hinges on the *input* `CookLevinFrontierHyp`.

## Part 1 — P-side upper bound  ⚠️ CONDITIONAL on an unproved socket

| Paper claim | Lean symbol | Status |
|---|---|---|
| Thm 10 Holographic Upper-Bound; Thm 23 Width⇒Rank; Cor 21 poly-many profiles; Lem 22 within-profile span | `ProfileCompression.p_side_rank_bound_for_cook_levin_of_exactWithinProfileLemma`, `totalProfileBound_le_pow` | **CONDITIONAL** on `CookLevinExactWithinProfileFinrankLemma`; the arithmetic is clean, the load-bearing lemma is the socket **[G]** |
| the packaged P-side frontier | `CookLevinFrontierRefutation.CookLevinFrontierHyp` | **UNPROVED `Prop` socket** — must contain the *full* super-polynomial P-side bound, not just an `N log N` recurrence **[G]** |

**This socket is the whole game.** It is not a small gap — discharging it *is* the super-polynomial
circuit lower bound.

## Part 3 — the God-Move  ❌ PROVEN CIRCULAR (re-encodes, does not reduce)

| Paper claim | Lean symbol | Status |
|---|---|---|
| Def 6/7, Lem 7, Thm 8/11/170 — rank-monotone gauge `T_Φ` | `GlobalGodMoveGauge.piStar_rank_monotone` | rank-monotonicity **PROVED clean** (its 4 gauge axioms were demoted to explicit hypotheses) **[K]** |
| "the gauge exists for a hard instance" | `GodMoveObligation.not_godMoveGaugeExists_of_gap (hgap : B < k)` | **PROVES ¬∃ such gauge** — `⟨T,_,hpside,hminor⟩; omega` (`k ≤ R(Tp) ≤ B < k`), clean **[K]** |
| Global God-Move hypothesis | `GodMoveObligation.globalGodMoveHyp_iff_no_hard` | **PROVES GodMove ↔ ¬∃ hard instance** — i.e. GodMove **IS** the separation, clean **[K]** |

**Verdict (your own kernel-checked theorems):** the God-Move / amplituhedron / holographic gauge cannot
exist for a hard instance, and asserting it exists is *logically equivalent* to the separation. It is a
faithful re-encoding, **not** a route. (Confirmed independently by Layer-10D `not_ppoly_of_observerHyp`:
the observer/holographic hypothesis is *at least as hard* as the lower bound — "relocation, not shortcut.")

## Live custom axioms (non-archived) — the disguised-assumption risk

| Axiom | File | Powers |
|---|---|---|
| `gadget_spdp_subspace_factoring`, `gadget_spdp_subspace_factoring_paperFaithful` | `PAC.lean` | P-side SPDP algebra |
| `gadget_factoring_linearmap_form` | `MatrixSPDP.lean` | SPDP matrix factoring |

These are **asserted `axiom` declarations**, not Props to discharge. The clean routes above
(`identity_minor_*`, `peqnp_false_of_frontier`, `piStar_rank_monotone`) do **not** depend on them (kernel
axiom sets show only `[propext, Classical.choice, Quot.sound]`). But any claim that *uses* them inherits
an unproved assumption — check `#print axioms` on the specific consumer, never trust a leaf lemma.

---

## Bottom line

- **Real, done, axiom-clean:** the NP-side explicit high-rank minor, and the arithmetic sandwich.
- **The one true gap:** `CookLevinFrontierHyp` / `CookLevinExactWithinProfileFinrankLemma` — the
  super-polynomial P-side upper bound. Discharging it = proving the separation. Nothing downstream is faked
  (kernel-clean), but nothing proves *it*.
- **The God-Move does not help:** it is kernel-proven equivalent to the separation, and contradictory for
  hard instances. Holographic / dynamic / "potential-infinity" reframings don't change the per-`n` finite
  `B(n) < k(n)` sandwich.
- **No "unconditional" theorem in the repo is unconditional:** each takes `CookLevinFrontierHyp` or a
  gauge/agent hypothesis; the `…_hypothesis_is_hypothesis_free : True := trivial` marker is a status stub,
  not a proof.
