# ATTACK on step (6), round 1 — executed per protocol

Protocol: name the SAT-specific, non-natural, non-relativizing mechanism; pass the QF A gate on paper; then
formalize. This memo is the execution record. **Result: stages 1 and 2 PASS — there is exactly one mechanism
class that clears every gate. The attack halts at stage 3 (strength), at a precisely named gap: the mechanism's
engine has no diagonalization room at polynomial scale. No formalization is attempted, per protocol. The gap
itself is now the sharpest available target.**

## Stage 1 — the mechanism, named

Candidates enumerated against the gate list:

* **Static/structural measures** (entanglement, rank profiles, correlation complexity, residual counts): fail the
  QF A gate before starting — `QF A` maximizes them and is quadratic-time. Dead on arrival, machine-checked.
* **Self-reducibility as the distinguishing feature**: FAILS the QF A gate — quadratic forms are also downward
  self-reducible (fixing a variable of a quadratic form yields an affine quadratic form). Self-reducibility alone
  does not distinguish SAT from `QF A`.
* **Universality (NP-completeness) as a truth-table property**: non-large ✓ (random functions are not complete),
  hard-to-compute from the table ✓ — evades Razborov–Rudich *formally*. But completeness relativizes, so as a
  stand-alone property it fails the relativization gate: it needs a non-relativizing partner.
* **Karp–Lipton dynamics** (poly-size SAT programs ⟹ witness-finding family ⟹ PH = Σ₂): SAT-specific ✓,
  non-natural ✓ — but circular at one remove: the contradiction requires `PH ≠ Σ₂`, itself an open separation.
* **The survivor — completeness-powered algorithms-to-lower-bounds** (the Williams paradigm, and its
  diagonalization ancestors Kannan/Santhanam): a nontrivial algorithm for the model's satisfiability problem +
  a time hierarchy + succinct-completeness padding ⟹ a lower bound. It is *not a truth-table measure at all*
  (non-natural by construction — this is why it evades Razborov–Rudich), its algorithmic ingredient inspects
  program/circuit structure (non-relativizing), and its fuel is completeness (SAT-specific).

**The named mechanism: completeness-powered diagonalization with an algorithmic (structure-inspecting)
ingredient.** It is the only class that clears gates (i)–(v) of the scope simultaneously.

## Stage 2 — the QF A gate, on paper

PASSED, and instructively: the mechanism cannot misfire on `QF A` **because `QF A` is not NP-complete** — it is
in P (`qfProg A`, cost `4n²`, machine-checked), and if it were NP-complete then `P = NP`. A completeness-powered
argument has no purchase on non-complete functions; there is no measure to erroneously assign `QF A` a high
value. The gate that kills every measure-shaped attack is passed by the mechanism *because it is not a measure* —
which is the same fact that lets it evade natural proofs. Stages 1 and 2 are therefore genuinely satisfiable;
the protocol's first two hurdles are not where step (6) dies.

## Stage 3 — strength: where the round halts

The engine's cash-out inventory, checked at scale:

* **Williams**: needs succinct-SAT completeness for NEXP — the padding that turns a barely-nontrivial SAT
  algorithm into a hierarchy contradiction lives at exponential scale. At polynomial scale (P vs NP) the
  succinctness collapses: there is no analogous "poly-scale padding" that converts a SAT algorithm into a
  contradiction with a hierarchy theorem below NP. The paradigm's own authors have made the scaling problem
  explicit; nothing in this corpus's machinery supplies the missing room.
* **Kannan/Santhanam-style completeness diagonalization**: proves fixed-polynomial lower bounds — but for Σ₂ᵖ
  and MA/promise levels, not for SAT. Even `SAT ∉ SIZE(n²)` — a fixed-polynomial statement infinitely weaker
  than step (6) — is **open**. The strongest known circuit lower bound for SAT is *linear* (~3n, gate
  elimination — itself a capped, natural-shaped technique).
* **Magnification**: would accept a near-linear bound for the right sparse problem in the right model — but the
  needed bounds sit at the locality barrier, and this corpus's genuine restricted bounds (`hardF`, the Nečiporuk
  family) are local techniques on the wrong problems: exactly what the locality barrier says cannot feed
  magnification.

**The named gap: polynomial-scale diagonalization room.** The unique gate-passing mechanism converts algorithms
into lower bounds only where padding/succinctness creates a hierarchy gap to diagonalize against; between P and
NP no such room is known to exist. This is not a restatement of "the problem is hard" — it is the specific,
localized missing component of the one mechanism that survives every other filter.

## Round verdict

* Stages 1–2 pass: the mechanism class exists and clears the QF A gate — the protocol is not vacuous.
* Stage 3 halts the round: the mechanism is currently an engine without poly-scale fuel. Per protocol,
  **no formalization is attempted** — formalizing the engine without the fuel would be the socket pattern
  (assumed-hypothesis cash-outs), which this corpus already charts (the Williams socket map).
* Genuine formalizable offshoots identified (real theorems, honestly restricted, available on request):
  (a) linear gate-elimination-style bounds in the charged model (the actual species of the current SAT frontier;
  `cost_ge_deps` is its Shannon base case); (b) the Karp–Lipton implication chain as formal conditional
  infrastructure (poly SAT programs ⟹ witness-finding family), which is true, non-trivial, and useful for any
  future round even though its contradiction endpoint is open.
* **Round-2 target, if directed**: the poly-scale padding gap itself — any construction placing a hierarchy-
  separated pair within polynomial scale of SAT would re-fuel the mechanism. That is where an attack on step (6)
  now lives, stated as sharply as this corpus can state it.

No closure is claimed. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
