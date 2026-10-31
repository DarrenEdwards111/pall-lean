# ATTACK on step (6), round 2 — the poly-scale padding gap

Round-1 halt point: the unique gate-passing mechanism (completeness-powered diagonalization with an algorithmic
ingredient) lacks polynomial-scale diagonalization room. Round 2 attacks that gap directly. **Result: the gap is
INHABITED — there is a live poly-scale instance of the mechanism, and it produces the first NON-VACUOUS passage
of the QF A gate in this entire arc: a proven hardness property of SAT that is provably false of `QF A`. The
round then halts at two sharper, theorem-guarded sub-gaps: the space wall and the proof-system ceiling.**

## 1. The gap re-examined

Poly-scale hierarchy pairs exist and are proven: `DTIME(n^k) ⊊ DTIME(n^{k+1})`, `NTIME(n^k) ⊊ NTIME(n^{k+1})`,
and the alternation hierarchies. The question is whether completeness + padding can couple "SAT is easy" to one
of them at polynomial scale. Round 1 checked the direct couplings (Karp–Lipton: circular at `PH ≠ Σ₂`; plain
padding: no purchase). Round 2 finds the indirect one.

## 2. The find: indirect diagonalization / alternation trading

The coupling exists — **alternation-trading proofs** (Fortnow–van Melkebeek; Williams): assume SAT is easy in a
time-and-space-restricted regime, `SAT ∈ TISP(n^c, n^{o(1)})`; use completeness + padding to convert this into
faster-and-faster simulations of alternating computations (trading alternations against time inside the small
space budget); iterate; contradict a *proven* alternation/time hierarchy. Yield, unconditional:

> `SAT ∉ TISP(n^{2cos(π/7)}, n^{o(1)})` — time `n^{1.8019...}` is impossible for SAT with subpolynomial space.

This is the strongest unconditional lower bound known for SAT in a general machine model, it lives at polynomial
scale, and it is *exactly* the round-1 mechanism: completeness (of SAT), padding (upward translation of the
assumed easiness), diagonalization (the hierarchy at the end). The poly-scale padding gap is inhabited.

## 3. The QF A gate — passed non-vacuously, for the first time

Every prior passage was vacuous (the mechanism "isn't a measure"). Here the gate is passed by a **theorem pair**:

* `QF A ∈ TISP(n², O(log n))` — the corpus's own `qfProg A` is the certificate: **3 wires**, `4n²` gates, one
  streaming pass over the pairs (machine-checked: `qfProg : Prog n 3`, `qfProg_cost`, `qfProg_correct`);
* `SAT ∉ TISP(n^{1.8}, n^{o(1)})` — proven (alternation trading).

The mechanism asserts a hardness property of SAT that is **provably false** of `QF A`. This is the first object
in the entire arc — after entanglement, rank, information, cut-flow, space, and schedule measures all failed —
that formally distinguishes SAT from `QF A` on the hard side. The distinguishing fuel is, as predicted,
completeness: the trading argument runs *because* every small-space poly-time computation reduces to SAT.

## 4. Where round 2 halts: two theorem-guarded sub-gaps

1. **The space wall.** The trading simulations trade alternations against time *inside a small space budget*
   (speedups of space-bounded computation are what the alternations buy). Remove the `n^{o(1)}` space restriction
   and the mechanism's engine stalls — general poly-space `P` gives the simulation nothing to compress. Removing
   the space wall at strength IS `P` vs `NP`. (Consistency check that the map is right: alternation-trading
   arguments relativize — machine simulations — which is *permitted* at sub-separation yield; the scope's
   relativization gate binds at separation strength. Yield strength and barrier-evasion correlate exactly as the
   gate structure predicts: relativizing rules → capped at `n^{1.8}`; superpolynomial would demand a
   non-relativizing ingredient — a structure-inspecting general-Circuit-SAT algorithm, whose known cash-out is
   Williams' route back to NEXP, not `P` vs `NP`.)
2. **The proof-system ceiling.** Buss–Williams proved that alternation-trading proofs, as a formal proof system
   over the standard speedup/slowdown rules, **cannot establish any exponent beyond `2cos(π/7)`** — the current
   yield is exactly the system's optimum. Going further requires a genuinely new inference rule. None is
   proposed this round — stated plainly rather than manufactured.

## 5. Round verdict

* The poly-scale padding gap is inhabited: alternation trading is the live instance, its yield (`n^{1.8019}`
  time–space for SAT) is real, unconditional, and SAT-specific, and it passes the QF A gate non-vacuously — the
  arc's first formal SAT/`QF A` hardness distinction, with the easy side already machine-checked in this corpus.
* The gap refines into two named, theorem-guarded sub-gaps: the space wall (removal = the separation) and the
  Buss–Williams ceiling (breach = a new inference rule, open research). The attack cannot proceed past them this
  round without manufacturing something — per protocol, it halts.
* No formalization of the uniform machinery this round: alternating machines + hierarchy theorems + completeness
  is a major infrastructure build (the corpus's `ClockedMachine`/RAM bricks are the natural substrate if ever
  directed). Genuine formalizable offshoots: (i) the easy-side certificate is already in-corpus (`qfProg`,
  3 wires, `4n²`); (ii) a Borodin–Cook-style time×space tradeoff in the charged model for a multi-output
  function — a genuinely new restricted target for this corpus, buildable, and the honest poly-scale analogue of
  what the mechanism does for SAT.
* **Round-3 target, if directed**: the Buss–Williams ceiling — specifically, whether any of the corpus's
  machinery (the derived horizon laws are new simulation primitives; the charged model is a new host) yields a
  trading rule outside the standard speedup/slowdown set. No candidate is claimed to exist; that is the honest
  frontier, and it is a research problem, not a build.

No closure is claimed. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
