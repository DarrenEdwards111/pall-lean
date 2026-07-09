# Håstad Switching-Lemma Capstone & Scope

*One-page ledger for the Håstad switching-lemma / `AC⁰` decoder arc. Unlike the prime `AC⁰[p]` and
Nečiporuk capstones (complete restricted-class theorems), this arc is **partial**: proved on the `hnf`
regime, reduced to one open decoder primitive in general. Capstone:
`PallLean/Paper93/DeepMath/PathB/ComputationalDepthSwitchingCapstone.lean`. Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.*

---

## What is PROVED (clean-axiom, no `sorry`)

Each name verified by `#print axioms` to depend on only `propext, Classical.choice, Quot.sound`.

| Capstone name | Statement | Backed by |
|---|---|---|
| `switching_hnf` | **unconditional** on the `hnf` regime: `∑_{ρ∈Bad} restrWeight p ρ ≤ (2w·2p/(1−p))^s` — the literal Håstad switching probability bound (decoder confound absent) | `SwitchingCounting.switching_bound_hnf` |
| `switching_general_weak` | general regime, **weak**: `≤ (#live-sub-DNFs)·(2w·2p/(1−p))^s`, `#live-sub-DNFs ≤ 2^{\|cs\|}` = the confound's cost | `SwitchingCounting.switching_bound_general` |
| `switching_measure_modulo_decoder` | tight general bound **modulo `hinj`** — assuming decoder injectivity, the tight bound follows (open step named as a hypothesis) | `SwitchingCounting.switching_measure_bound_modulo_inj` |

Supporting bricks (all `sorry`-free, indexed in `ComputationalDepthSwitchingArcManifest.lean`): the
deterministic decoder/counting (`replay_switching_count`, the `(2w)^s` count and its per-step inverse),
the live-DNF normalization (`replayPath_liveCs`, `liveCs_base_agree`), and the probabilistic measure
assembly (`sum_restrWeight_eq_one`, `pweight_ratio`).

---

## What is OPEN (the decoder confound `hinj`)

The **tight general** switching lemma needs one primitive: `hinj` — a decoder recovering the restriction
`ρ` from `(end-state, label)`. It is:

- **absent** on the `hnf` / live-sub-DNF regime (so `switching_hnf` is unconditional), and
- the **whole cost** of the general regime — exactly the `#live-sub-DNFs ≤ 2^{|cs|}` factor in
  `switching_general_weak`.

All four discharge routes reach it identically. Discharging it unconditionally is **Razborov's
satisfy-encoding forward decoder** — a from-scratch construction, **not done, not faked**. Until then the
tight general switching lemma is not closed here.

---

## Honest scope

- **Proved:** the Håstad switching probability bound on the `hnf` regime (unconditional), the weak general
  bound, and the tight bound modulo the named decoder primitive — machine-checked, clean-axiom.
- **Open:** the tight *general* switching lemma (the `hinj` decoder). This is an **`AC⁰`/depth-3-level,
  partial** result — real, but **not** a complete `AC⁰` lower bound, **not** `NEXP ⊄ ACC⁰`, **not**
  `P ≠ NP`.

This arc is a *partial* asset: unlike prime `AC⁰[p]` and Nečiporuk (both complete with an honest ceiling),
the switching arc is complete only on the restricted `hnf` regime and reduced-but-open in general.

*Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. Companions: `PRIME_ACC0_CAPSTONE.md`, `NECIPORUK_CAPSTONE.md`,
`ComputationalDepthSwitchingArcManifest.lean`, `SATISFY_DECODER_SCOPE.md`.*
