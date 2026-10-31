import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHnfHeadline
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingGeneralReindex
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFinalWiring

/-!
# Håstad switching-lemma capstone — the proved bounds, and the open decoder primitive

This file collects, under clean citable names, what the Håstad switching-lemma arc **proves**
unconditionally, and states honestly what it does **not**. Unlike the prime `AC⁰[p]` and Nečiporuk
capstones (which are complete restricted-class theorems), this arc is **partial**: the switching
probability bound is proved on the `hnf` / live-sub-DNF regime, but the **tight general** switching lemma
reduces to one open primitive — `hinj`, the decoder that recovers a restriction `ρ` from
`(end-state, label)` (Razborov's satisfy-encoding forward decoder). That primitive is **not** proved and
**not** faked; it is the whole cost of the general regime.

Each capstone name is verified by `#print axioms` to depend on **only** `propext`, `Classical.choice`,
`Quot.sound`. The proved bounds are complete proofs; the gap is carried as an explicit hypothesis
(`…_modulo_inj`), never a `sorry`.

## The capstone (PROVED, clean-axiom, no `sorry`)

* **`switching_hnf`** (`= SwitchingCounting.switching_bound_hnf`) — **unconditional** on the `hnf` regime:
  for any bad set of restrictions falsifying no clause, `∑_{ρ∈Bad} restrWeight p ρ ≤ (2w · 2p/(1−p))^s` —
  the literal Håstad switching probability bound, fully assembled. The decoder confound is *absent* here.
* **`switching_general_weak`** (`= SwitchingCounting.switching_bound_general`) — the general regime, proved
  but **weak**: `∑_{ρ∈Bad} restrWeight p ρ ≤ (#live-sub-DNFs) · (2w · 2p/(1−p))^s`, where the
  `#live-sub-DNFs ≤ 2^{|cs|}` factor is *exactly the confound's cost* made explicit.
* **`switching_measure_modulo_decoder`** (`= SwitchingCounting.switching_measure_bound_modulo_inj`) — the
  full measure bound **modulo `hinj`**: assuming the decoder injectivity, the tight general bound follows.
  This names the single open primitive as a hypothesis.

## The wall (open, honest)

The **tight general** switching lemma needs `hinj` — recover `ρ` from `(end-state, label)`. All four
discharge routes reach it identically; it is absent on the `hnf`/live-sub-DNF regime (so `switching_hnf`
is unconditional) and is the entire `2^{|cs|}` factor of `switching_general_weak`. Discharging it
unconditionally is Razborov's satisfy-encoding forward decoder — a from-scratch construction, not done.

## Honest scope

This is an **`AC⁰` / depth-3-level, partial** result: the switching probability bound is proved on the
restricted regime and reduced (modulo one named decoder primitive) in general. It is real machine-checked
mathematics, but it is **not** a complete `AC⁰` lower bound, **not** `NEXP ⊄ ACC⁰`, and **not** `P ≠ NP`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. See `SWITCHING_CAPSTONE.md` and the master ledger
`PRIME_ACC0_CAPSTONE.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SwitchingCapstone

/-- Unconditional Håstad switching probability bound on the `hnf` regime:
`∑_{ρ∈Bad} restrWeight p ρ ≤ (2w·2p/(1−p))^s`. -/
alias switching_hnf := PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_bound_hnf

/-- General-regime switching bound, weak form: bounded by `#live-sub-DNFs · (2w·2p/(1−p))^s`; the
`#live-sub-DNFs ≤ 2^{|cs|}` factor is the decoder confound's cost. -/
alias switching_general_weak := PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_bound_general

/-- The tight general switching measure bound **modulo the decoder primitive `hinj`** — the single open
step of the arc, carried as a hypothesis (not a `sorry`). -/
alias switching_measure_modulo_decoder :=
  PallLean.Paper93.DeepMath.PathB.SwitchingCounting.switching_measure_bound_modulo_inj

end PallLean.Paper93.DeepMath.PathB.SwitchingCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCapstone.switching_hnf
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCapstone.switching_general_weak
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCapstone.switching_measure_modulo_decoder
