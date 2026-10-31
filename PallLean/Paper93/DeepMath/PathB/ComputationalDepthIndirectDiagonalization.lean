import Mathlib.Data.Nat.Basic

/-!
# Indirect diagonalization: the Lipton–Viglas alternation-trading engine

The uniform axis of the separation program has a weapon the non-uniform axis lacks:
against uniform classes, hierarchy theorems bite.  The only unconditional SAT-specific
lower bounds in existence — the time-space tradeoffs (Lipton–Viglas `n^{√2}`,
Fortnow–van Melkebeek, Williams `n^{2cos(π/7)}`) — all follow one scheme, *indirect
diagonalization*: assume nondeterministic linear time has a fast small-space
deterministic simulation, TRADE alternations for time under that assumption, and
contradict the nondeterministic time hierarchy.

This file machine-checks the ENGINE of the base scheme (Lipton–Viglas): the inclusion
chain and every piece of exponent arithmetic.  Exponents are handled in scaled form —
the simulation exponent `c = p/q` appears only through the homogeneous statement
`NTIME(n^q) ⊆ DTS(n^p)`, so the whole engine lives in `ℕ` (`c² < 2  ⟺  p·p < 2·(q·q)`)
and every arithmetic step is `omega`/`Nat.mul_*`, no real numbers.

## The four ingredients (named sockets w.r.t. the concrete machine model)

`TradingWorld` packages the four standard theorems the chain consumes, as explicit
fields over abstract classes `NTIME`, `DTS` (time `n^a`, space `n^{o(1)}`), `Σ₂TIME`:

* `padding`   — translation: `NTIME(n^q) ⊆ DTS(n^p)` scales to `NTIME(n^{mq}) ⊆ DTS(n^{mp})`;
* `speedup`   — Nepomnjaščiĭ-style midpoint alternation: `DTS(n^{2b}) ⊆ Σ₂TIME(n^b)`;
* `slowdown`  — eliminate the alternation by the assumed simulation:
                 under `NTIME(n^q) ⊆ DTS(n^p)`, `Σ₂TIME(n^{aq}) ⊆ NTIME(n^{ap})`;
* `hierarchy` — the nondeterministic time hierarchy (Cook / Seiferas–Fischer–Meyer / Žák).

## What is proved and what is not

* **`lipton_viglas_engine` (proved)** — the trade: from the four ingredients, the
  simulation `NTIME(n^q) ⊆ DTS(n^p)` is REFUTED whenever `p·p < 2·(q·q)`, i.e. for
  every simulation exponent `c < √2`.  The chain is
  `NTIME(n^{2q²}) ⊆ DTS(n^{2qp}) ⊆ Σ₂TIME(n^{qp}) ⊆ NTIME(n^{p²})` against the
  hierarchy.
* **`sat_time_space_reading` (proved)** — the SAT-shaped cash-out: given additionally
  the quasilinear-completeness packaging (`SAT` easy ⟹ the simulation premise), SAT
  itself is not in `DTS(n^p)` for `p·p < 2·(q·q)`.
* **`toyWorld` (proved)** — the ingredient axioms are mutually consistent: an explicit
  instance (probe languages, empty `DTS`/`Σ₂`) satisfies all four fields.  It witnesses
  CONSISTENCY of the interface, not its truth for `ComposableMachine`.
* **NOT proved here** — the four ingredients for the repository's concrete machine
  model.  Each is a literature-standard theorem (formalization labor), and — unlike the
  KRW-type sockets — NONE is of `P ≠ NP` strength.  Discharging them against
  `ComposableMachine` is the announced uniform-ladder arc: it would make the time-space
  lower bound for SAT the first unconditional statement about SAT on the real machine
  model in this repository.

Honest ceiling, stated once: the alternation-trading method is provably capped
(Buss–Williams) at polynomial exponents (`n^{2cos(π/7)}`-ish); this arc reaches real
uniform SAT bounds, not `P ≠ NP`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization

/-- Languages over binary strings, as everywhere in the corpus. -/
abbrev Lang := List Bool → Bool

/-- The abstract world of an alternation-trading argument.  Classes are indexed by the
SCALED exponent: `NTIME a` reads "`NTIME(n^a)`", `DTS a` reads "deterministic time
`n^a`, space `n^{o(1)}`", `Sig2 a` reads "`Σ₂TIME(n^a)`".  The four fields are the four
standard theorems the trade consumes (see the file header for attribution). -/
structure TradingWorld where
  /-- Nondeterministic time `n^a`. -/
  NTIME : ℕ → Lang → Prop
  /-- Deterministic time `n^a`, space `n^{o(1)}`. -/
  DTS : ℕ → Lang → Prop
  /-- `Σ₂`-time `n^a`. -/
  Sig2 : ℕ → Lang → Prop
  /-- Translation/padding: a simulation of nondeterministic time by small-space
  deterministic time scales homogeneously. -/
  padding : ∀ p q : ℕ, (∀ L, NTIME q L → DTS p L) →
      ∀ m : ℕ, 1 ≤ m → ∀ L, NTIME (m * q) L → DTS (m * p) L
  /-- Nepomnjaščiĭ-style speedup: small-space deterministic time `n^{2b}` is `Σ₂`-time
  `n^b` (guess the midpoint configuration, check both halves universally). -/
  speedup : ∀ b : ℕ, 1 ≤ b → ∀ L, DTS (2 * b) L → Sig2 b L
  /-- Slowdown: under the assumed simulation, one alternation is eliminated at cost
  exponent `p/q`. -/
  slowdown : ∀ p q : ℕ, 1 ≤ q → (∀ L, NTIME q L → DTS p L) →
      ∀ a : ℕ, 1 ≤ a → ∀ L, Sig2 (a * q) L → NTIME (a * p) L
  /-- The nondeterministic time hierarchy: no collapse of `NTIME(n^a)` into
  `NTIME(n^b)` for `1 ≤ b < a`. -/
  hierarchy : ∀ a b : ℕ, 1 ≤ b → b < a → ¬ (∀ L, NTIME a L → NTIME b L)

/-- **The Lipton–Viglas engine (proved).**  From the four ingredients: nondeterministic
linear time has NO deterministic small-space simulation with exponent `c = p/q` below
`√2`.  The chain, fully explicit in scaled exponents:

`NTIME((2q)·q)  ⊆[padding, m=2q]  DTS((2q)·p)  ⊆[speedup, b=qp]  Σ₂TIME(q·p)
⊆[slowdown, a=p]  NTIME(p·p)` — contradicting the hierarchy since `p² < 2q²`. -/
theorem lipton_viglas_engine (W : TradingWorld) (p q : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hlt : p * p < 2 * (q * q)) :
    ¬ (∀ L, W.NTIME q L → W.DTS p L) := by
  intro hSim
  have hp : 1 ≤ p := le_trans hq hqp
  have hqp1 : 1 ≤ q * p := Nat.mul_le_mul hq hp
  -- Rung 1 (padding, `m = 2q`): `NTIME((2q)q) ⊆ DTS((2q)p)`.
  have h1 : ∀ L, W.NTIME (2 * q * q) L → W.DTS (2 * q * p) L := by
    intro L hL
    exact W.padding p q hSim (2 * q) (by omega) L hL
  -- Rung 2 (speedup, `b = qp`, using `2qp = 2(qp)`): `DTS(2qp) ⊆ Σ₂TIME(qp)`.
  have h2 : ∀ L, W.DTS (2 * q * p) L → W.Sig2 (q * p) L := by
    intro L hL
    apply W.speedup (q * p) hqp1 L
    rw [← Nat.mul_assoc]
    exact hL
  -- Rung 3 (slowdown, `a = p`, using `qp = pq`): `Σ₂TIME(pq) ⊆ NTIME(p·p)`.
  have h3 : ∀ L, W.Sig2 (q * p) L → W.NTIME (p * p) L := by
    intro L hL
    have hs := W.slowdown p q hq hSim p hp L
    rw [Nat.mul_comm q p] at hL
    exact hs hL
  -- The collapse `NTIME(2q²) ⊆ NTIME(p²)` against the hierarchy.
  have hcollapse : ∀ L, W.NTIME (2 * q * q) L → W.NTIME (p * p) L :=
    fun L hL => h3 L (h2 L (h1 L hL))
  have hpp1 : 1 ≤ p * p := Nat.mul_le_mul hp hp
  have hlt' : p * p < 2 * q * q := by
    have hassoc : 2 * q * q = 2 * (q * q) := Nat.mul_assoc 2 q q
    omega
  exact W.hierarchy (2 * q * q) (p * p) hpp1 hlt' hcollapse

/-- **The SAT-shaped reading (proved).**  Add the completeness packaging — "if SAT has
a `DTS(n^p)` algorithm then all of `NTIME(n^q)` does" (quasilinear Cook–Levin; a named
ingredient here, standard in the literature) — and the engine bounds SAT itself:
`SAT ∉ TISP(n^c, n^{o(1)})` for every `c = p/q < √2`. -/
theorem sat_time_space_reading (W : TradingWorld) (sat : Lang) (p q : ℕ)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hlt : p * p < 2 * (q * q))
    (completeness : W.DTS p sat → ∀ L, W.NTIME q L → W.DTS p L) :
    ¬ W.DTS p sat :=
  fun hsat => lipton_viglas_engine W p q hq hqp hlt (completeness hsat)

/-! ### Consistency of the interface: an explicit instance -/

/-- Probe languages: `probe j` accepts exactly the strings of length `j`. -/
def probe (j : ℕ) : Lang := fun w => decide (w.length = j)

/-- Distinct probes are distinct languages (evaluate at `List.replicate`). -/
theorem probe_ne {i j : ℕ} (hij : i ≠ j) : probe i ≠ probe j := by
  intro h
  have ht : probe i (List.replicate i false) = true := by
    simp [probe]
  rw [h] at ht
  have hlen : (List.replicate i false).length = j := of_decide_eq_true ht
  rw [List.length_replicate] at hlen
  exact hij hlen

/-- The toy `NTIME`: the probes of index between `1` and `a`.  Strictly growing in `a`,
so the hierarchy field is genuine. -/
def toyNTIME (a : ℕ) (L : Lang) : Prop := ∃ j, 1 ≤ j ∧ j ≤ a ∧ L = probe j

/-- **The interface is consistent (proved)**: an explicit `TradingWorld` — probe
languages for `NTIME`, empty `DTS` and `Σ₂` — satisfies all four ingredient fields.
(It witnesses consistency of the axioms, NOT their truth for the concrete machine
model; there the fields are the four literature theorems to be discharged.) -/
def toyWorld : TradingWorld where
  NTIME := toyNTIME
  DTS := fun _ _ => False
  Sig2 := fun _ _ => False
  padding := by
    intro p q hSim m _hm L hL
    obtain ⟨j, hj1, hjle, rfl⟩ := hL
    have hq : 1 ≤ q := by
      cases q with
      | zero => rw [Nat.mul_zero] at hjle; omega
      | succ q' => omega
    exact hSim (probe 1) ⟨1, Nat.le_refl 1, hq, rfl⟩
  speedup := fun _b _hb _L hL => hL.elim
  slowdown := fun _p _q _hq _hSim _a _ha _L hL => hL.elim
  hierarchy := by
    intro a b hb hab hsub
    obtain ⟨j, _hj1, hjb, hEq⟩ := hsub (probe a) ⟨a, by omega, Nat.le_refl a, rfl⟩
    exact probe_ne (by omega : a ≠ j) hEq

/-- The engine fires on the toy world at the `√2`-approximating ratio `4/3`
(`16 < 18`): the hypotheses are simultaneously satisfiable and the conclusion is
non-vacuous. -/
theorem engine_toy_instance : ¬ (∀ L, toyWorld.NTIME 3 L → toyWorld.DTS 4 L) :=
  lipton_viglas_engine toyWorld 4 3 (by omega) (by omega) (by omega)

end PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization

#print axioms PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization.lipton_viglas_engine
#print axioms PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization.sat_time_space_reading
#print axioms PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization.engine_toy_instance
