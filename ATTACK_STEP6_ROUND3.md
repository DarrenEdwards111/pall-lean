# ATTACK on step (6), round 3 — the Buss–Williams ceiling

Round-2 halt point: alternation trading yields `SAT ∉ TISP(n^{2cos(π/7)}, n^{o(1)})` and is provably optimal for
the standard speedup/slowdown rule set (Buss–Williams). Round-3 question: does anything corpus-unique — the
derived horizon laws as simulation primitives, the charged model as host, the entanglement/N-Frame machinery —
yield a trading rule **outside** the standard set? **Result: no. The central finding, now machine-checked, is an
identification: the derived horizon laws ARE the standard speedup rule's semantic core in the charged host — the
corpus's primitives instantiate the rule set that Buss–Williams caps, rather than extending it. The escape routes
each reduce to other named separation-adjacent open problems. No new rule is claimed; the round halts honestly.**

## 1. The identification (machine-checked): horizon laws = the standard speedup

`ChargedSpeedupPrimitive.lean`: `midpoint_sound_complete` — verification of a charged run decomposes exactly as
*guess-a-midpoint-state, verify both segments independently* (`∃ m, prefix → m ∧ suffix from m → b`), soundly,
completely, with a unique witness (`midpoint_unique`, axiom-free) and a genuine time split (`segment_costs`).
This is precisely the Nepomnjaščiĭ-style speedup that powers alternation trading: split a space-bounded
computation at guessed configuration boundaries, verify blocks universally. `forward_determinism` and
`residual_decodes_from_state` were its two halves all along — the "horizon laws" are not a new primitive; they
are the standard one, derived in a new host. Consequence: **the charged model natively hosts alternation trading
with the standard rule set, and therefore inherits the `2cos(π/7)` ceiling — it does not escape it.** A new host
is not a new rule.

## 2. The other corpus assets, probed

* **The slowdown side**: slowdown = "SAT easy ⟹ remove an alternation at polynomial cost" — pure completeness +
  padding; the charged compiler reproduces it, adds nothing beyond constants.
* **Entanglement/rank machinery**: a "rank speedup" would need cut-rank to interface with uniform time-space
  hierarchy endpoints; no sound inclusion of that shape exists in the corpus or emerged on paper. The rank
  quantities cap at `n` (log) or misfire on `QF A` (raw) — both machine-checked earlier; neither yields a class
  inclusion.
* **The non-uniform variant** (charged model's native quantifier): in non-uniform land the hierarchy endpoint is
  FREE (the size hierarchy is a counting theorem), and trading against it with Karp–Lipton-style slowdowns is a
  known argument — it is exactly Kannan's theorem (`Σ₂ ⊄ SIZE(n^k)`) and Santhanam's (`MA/1 ⊄ SIZE(n^k)`). Its
  known stall: moving the hard-by-counting function from `Σ₂`/promise-`MA` down into `NP` — the missing-witness
  problem, a named open frontier. The corpus reproduces the argument's shape; it does not move the stall.
* **N-Frame cone-excess line**: direct-sum structure over circuit cones; no interface with time-space class
  inclusions was found. No candidate rule.

## 3. The escape routes, each reduced to a named wall

A rule that moves the ceiling must be a new **sound inclusion** among the class expressions. The known shapes:

1. **A better speedup** (beating Nepomnjaščiĭ/Savitch-style simulation of `DTISP`): would itself be a
   breakthrough on `NL`-vs-`P` / `SC`-adjacent questions — separation-adjacent, open.
2. **A non-black-box slowdown** (inspecting the assumed SAT algorithm's structure): the Williams move — its only
   known cash-out is the route back to `NEXP ⊄ ACC⁰`, not poly-scale.
3. **Randomized/algebraic rules**: explored in the literature (Diehl–van Melkebeek et al.); the ceilings in
   those regimes are of the same magnitude; no superpolynomial opening is known.
4. **The non-uniform endpoint**: stalls at the `MA`-vs-`NP` missing-witness frontier (above).

Every exit from the ceiling is another named wall. That is the round-3 map, and it is consistent: the ceiling is
not an artifact of the proof system's presentation — its escape routes are guarded by the same family of open
separations it would help prove.

## 4. Round verdict

* **Finding (positive, machine-checked)**: the horizon laws are the standard speedup primitive in the charged
  host (`midpoint_sound_complete`, `midpoint_unique` — the latter axiom-free). The corpus's simulation machinery
  is *correct* — and *standard*. It hosts trading; it does not extend it.
* **Finding (negative, honest)**: no trading rule outside the standard set was found in any corpus asset, and
  each literature escape route reduces to a named separation-adjacent open problem. No candidate is manufactured.
* The attack, three rounds in, has converged to a stable frontier: the mechanism is unique (round 1), its
  poly-scale instance is real and optimal-for-its-rules (round 2), and its extension points are each guarded by
  named walls (round 3). The protocol held at every stage — three honest halts, zero sockets.
* **What remains directable**: (a) the Borodin–Cook time×space tradeoff in the charged model (a real restricted
  build, the model's own analogue of the trading yield); (b) formalizing the trading proof system itself
  (speedup/slowdown as formal rules over class expressions + the Buss–Williams cap as a formal meta-theorem) —
  a substantial but genuine formalization target that would make the ceiling itself machine-checked. Neither is
  a separation; both are honest.

No closure is claimed. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
