# Crossing-energy separation audit — 2026-09-08

Repository inspected: `DarrenEdwards111/pall-lean`, local checkout
`the inspected pall-lean checkout`, commit
`03cd5d1ecfe72c00ed40db86749a24f70c6b524e` (commit existence verified on GitHub).

## Result

No unconditional P ≠ NP proof was obtained. The supplied progress report stops
two commits before the inspected checkout. Memory-robust cost is already proved
in `f88e15bb`; numerical amplification calibration is addressed in `03cd5d1e`.

## What the statements establish

- `DirectSumObserver` is an indexed family of independent reconstruction
  observers. Total energy is defined as the sum of component energies. Its
  additive lower bound does not itself encode an arbitrary joint algorithm
  sharing work between blocks, or prove a reduction from one to this family.
- The shared `bits` parameter is a ceiling, not a modeled shared physical
  memory store. `totalReuseCost` charges `bits²` once per component by definition.
  This is not a derived theorem that physical memory must be refreshed or
  reallocated for each block.
- The memory-robust lower bound is `blocks * (2 * m)`, linear in the number
  of explicitly supplied block bits. It is compatible with polynomial time.
- `equalityCNF_satisfiable_iff` reduces this SAT family to equality;
  `scanEquality_correct_for_SAT` supplies a correct executable scan. Restricted
  model lower bounds on this family do not make it hard for unrestricted P.
- Generic calibrated numerical amplification preserves polynomially bounded
  profiles, including the proved linear floor. Repetition must also be charged
  to total input size; exponentially many explicit blocks are not a
  polynomial-size reduction.

## Exact unresolved theorem

`InvHard SATV crossingEnergyInv` requires that every machine deciding the chosen
boundary language has crossing energy that is not polynomially bounded in input
length. The P-side `InvSound` theorem is proved. `crossingEnergy_route` still
takes `InvHard` as an explicit hypothesis. The final `PneqNP_from_invariant`
also takes `CookLevin SATV` as a hypothesis; an unconditional application must
instantiate a concrete appropriate boundary and discharge that hypothesis too.

Neither the direct-sum inequality nor adding a memory-charge definition proves
this universal hardness claim. Closing it needs new algorithm-sensitive
lower-bound mathematics, not a missing Lean tactic or the removal of a `sorry`.
Standard-axiom-only checking validates these conditional/restricted statements;
it does not discharge their explicit hypotheses.
