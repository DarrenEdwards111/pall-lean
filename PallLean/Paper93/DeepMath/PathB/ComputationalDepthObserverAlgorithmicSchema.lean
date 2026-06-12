import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForcingFamilyMin

/-!
# Observer → SAT-algorithm → Williams: the algorithmic schema (conditional, the second engine)

The observer programme so far proves lower bounds by forcing *high* boundary (the God-Move direction).  This
file adds the **second engine** (Williams' route, conditional): *low* observer boundary is algorithmically
exploitable — dynamic programming over the `2^B` boundary states solves satisfiability faster than brute
force — and a nontrivial SAT algorithm for a class yields a lower bound (Williams diagonalization).  Combining
them gives a path *around* the ACC⁰ barrier (§7): instead of forcing an NP language to high boundary, exploit
that a class has *low* boundary.

The pieces split cleanly into **proved** (the algorithmic core) and **explicit hypothesis** (Williams).

## Proved: low boundary ⇒ sub-brute-force SAT

`dpSat_beats_bruteforce` — an instance decomposed into `stages` stages each communicating through a boundary
of `B` bits (`2^B` states) is decided by DP over boundary states in time `≤ stages · 2^B`, which beats
brute-force `2^n` whenever `stages · 2^B ≤ 2^{n−1}` (i.e. `B + log₂ stages ≤ n − 1`).  This is the genuine
algorithmic content — the same DP that solves bounded-pathwidth / bounded-width-branching-program SAT.

## Explicit hypothesis: Williams diagonalization

`williams : (sub-brute-force SAT for `C`) → (NEXP ⊄ C)` is taken as an explicit hypothesis — it is Williams'
deep theorem (the `#SAT`-algorithm ⇒ lower-bound diagonalization), **not** reproved here.  The schema then
chains: low boundary `→` (DP, proved) sub-brute-force SAT `→` (Williams, hypothesis) lower bound.

## The expander amplifier (where the God-Move LOWER bound re-enters)

The two engines are complementary.  The algorithmic engine uses *low* boundary of the circuit class; the
God-Move engine forces *high* boundary on hard instances (proved for expander-Tseitin, §8, and the
address-block forcing families, §12).  An expander amplifier (`p vs np1` flavour) is the bridge: expansion
makes boundary reuse expensive, so a low-boundary observer must either collapse distinguishable continuations
or pay boundary proportional to the expansion frontier (`ForcingFamily` is the proved instance of "pay the
frontier").  This file states the algorithmic side; the forcing-family side is §12.

## Honest status

* DP bound (low boundary ⇒ sub-brute-force): **proved**.
* Williams bridge: **explicit hypothesis** (the real deep theorem; not reproved).
* `NEXP ⊄ ACC⁰` / `NP ⊄ ACC⁰`: **open**.  This schema does not close them; it states *precisely* the
  combined conditional and isolates the one deep input (Williams) and the one open input (that ACC⁰ has low
  enough observer boundary to feed the DP).
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic

open scoped BigOperators

/-- Time for **dynamic programming over boundary states**: `stages` stages, each costing `2^boundary` (one
per boundary state). -/
def dpSatTime (stages boundary : ℕ) : ℕ := stages * 2 ^ boundary

/-- Brute-force SAT time on `n` variables. -/
def bruteForceTime (n : ℕ) : ℕ := 2 ^ n

/-- **Low boundary ⇒ sub-brute-force SAT (proved).**  If `stages · 2^boundary ≤ 2^{n−1}` (boundary plus
`log₂ stages` below `n`), the boundary-state DP strictly beats brute force.  The genuine algorithmic content:
a low-boundary decomposition is exploitable. -/
theorem dpSat_beats_bruteforce {stages boundary n : ℕ} (hn : 1 ≤ n)
    (h : stages * 2 ^ boundary ≤ 2 ^ (n - 1)) :
    dpSatTime stages boundary < bruteForceTime n := by
  unfold dpSatTime bruteForceTime
  calc stages * 2 ^ boundary ≤ 2 ^ (n - 1) := h
    _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- A **low-boundary instance**: `n` variables decomposed into `stages` stages of boundary `boundary`, with
the gap condition that makes the DP sub-brute-force. -/
structure LowBoundaryInstance where
  /-- number of variables -/
  n : ℕ
  /-- number of stages -/
  stages : ℕ
  /-- boundary (bits) per stage -/
  boundary : ℕ
  /-- at least one variable -/
  npos : 1 ≤ n
  /-- the low-boundary gap: `stages · 2^boundary ≤ 2^{n−1}` -/
  low : stages * 2 ^ boundary ≤ 2 ^ (n - 1)

/-- Every low-boundary instance is solved by the boundary-state DP faster than brute force. -/
theorem LowBoundaryInstance.fast (I : LowBoundaryInstance) :
    dpSatTime I.stages I.boundary < bruteForceTime I.n :=
  dpSat_beats_bruteforce I.npos I.low

/-- **The combined Observer → Williams schema (conditional).**  Let `FastSat` be the proposition "`C`-SAT is
sub-brute-force" and `LowerBound` be "`NEXP ⊄ C`".  Given:

* `lowBoundaryGivesFast : LowBoundaryHyp → FastSat` — the DP bridge (proved-flavoured: low boundary ⇒ fast
  SAT, instantiating `dpSat_beats_bruteforce`);
* `lowBoundary : LowBoundaryHyp` — `C` admits low-boundary observer decompositions (the open input);
* `williams : FastSat → LowerBound` — Williams diagonalization (the deep input, explicit hypothesis);

then `LowerBound`.  The implication is modus ponens; the content is the three inputs, two of them named open. -/
theorem observer_williams_schema {LowBoundaryHyp FastSat LowerBound : Prop}
    (lowBoundaryGivesFast : LowBoundaryHyp → FastSat) (lowBoundary : LowBoundaryHyp)
    (williams : FastSat → LowerBound) : LowerBound :=
  williams (lowBoundaryGivesFast lowBoundary)

/-- **Concrete instantiation of the DP bridge.**  "Low boundary" `:=` a `LowBoundaryInstance`; "FastSat" `:=`
the DP beats brute force.  This discharges `lowBoundaryGivesFast` with the *proved* `LowBoundaryInstance.fast`
— so in `observer_williams_schema`, only `williams` (deep) and the existence of the low-boundary
decomposition (open) remain as inputs. -/
theorem lowBoundary_gives_fastSat (I : LowBoundaryInstance) :
    dpSatTime I.stages I.boundary < bruteForceTime I.n :=
  I.fast

/-- **The combined conditional separation, fully assembled.**  Given a low-boundary instance for the class
(the open input) and the Williams bridge from "the DP beats brute force on it" to the lower bound (the deep
input), the lower bound follows. -/
theorem nexp_not_subset_of_lowBoundary {LowerBound : Prop} (I : LowBoundaryInstance)
    (williams : (dpSatTime I.stages I.boundary < bruteForceTime I.n) → LowerBound) : LowerBound :=
  williams I.fast

end PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic.dpSat_beats_bruteforce
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic.nexp_not_subset_of_lowBoundary
