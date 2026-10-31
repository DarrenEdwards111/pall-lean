# Observer-Visible Dynamic Hypercube SPDP — the Attempt, and the Tetralemma It Hits

*Honest record of pressure-testing HAL 9000 / D's candidate: "observer-visible **dynamic hypercube**
SPDP under a thermodynamic constraint" — measure not the raw compiled rank, but what a resource-bounded
(thermodynamically constrained) observer can persistently see of the hypercube/SPDP structure after
quotienting easy dynamics. The instinct is correct (raw SPDP "sees everything, including Cook–Levin junk").
But the observer has one dial — how much resource it has — and **every setting of that dial lands in a wall
we have already identified, three of them machine-checked.** Nothing here is `P ≠ NP`.*

---

## The candidate (HAL 9000 / D)

```
μ_obs(C, S) = visible SPDP-rank / boundary complexity of the hypercube dynamics induced by C on S,
              under observer constraints: memory ≤ M, energy/work ≤ W, time ≤ T, resolution ≤ R.
Goal:  μ_obs(P-time trivial/easy compilation) ≤ poly(n),   μ_obs(NP/Tseitin search) ≥ superpoly(n).
```

Refinements over raw SPDP: **dynamic** (track the computation's collapse of hypercube regions over time,
not static rank); **observer/thermodynamic** (only count structure that is dynamically accessible,
persistent, not erased by cheap reversible bookkeeping, not mere representation blow-up); **quotient**
(SPDP only on the residual surviving easy dynamics).

---

## HAL's four sanity tests, run

The exact poly-computable incarnation of "edge-boundary / expansion of the level set on the hypercube"
is the **total influence** (average sensitivity) `I[f] = 2·(#bichromatic edges)/2ⁿ`, `0 ≤ I[f] ≤ n`
(`observer_hypercube_test.py`):

| test | hypercube/SPDP witness | in P? |
|---|---|---|
| do-nothing DTM | raw compiled SPDP rank `≈2^638536` at `n=2^804` (`spdp_blowup.py`) — **HIGH** (grid junk) | yes |
| **parity** | `I[f] = n` = **MAXIMAL** (every edge is a boundary edge) | **yes (trivially)** |
| Tseitin gadget | resolution/expansion **HIGH** | yes (Gaussian elimination, `tseitin_in_P.py`) |
| expander-Tseitin | **HIGHER** | yes (still a GF(2) linear system) |

Parity is decisive for the hypercube costume: the witness is **maximal on the single easiest non-trivial
function**. `I[f]` measured for n = 6…12: parity `= n`; majority `≈ √n`; dictator `= 1`; AND/OR `→ 0`;
const `= 0` — all in P. The witness does not track P-hardness; it tracks sensitivity, a query-complexity
measure that is poly-related to decision-tree depth and thus **≤ P**.

---

## The tetralemma — the observer's one dial, four walls

**1. Observer = a general poly-resource process** ("dynamic" = it runs the computation). "Observer sees no
persistent residual on `S`" *means* "some P process collapses `S`'s dynamics" `= S ∈ P`. So `μ_obs(S)`
superpoly `⟺ S ∉ P`; certifying `μ_obs(SAT)` superpoly **is** `P ≠ NP`. Circular — the measure faithfully
restates the question. *(= the ω(1)-Lipschitz-is-circular half of `…MeasureBarrier`.)*

**2. Observer = a fixed efficiently-computable measurement.** Then `μ_obs` is *constructive + large* — a
**natural property** (`I[f]` is poly(2ⁿ)-time from the truth table and `≤ n`). Razborov–Rudich: such a
property breaks strong PRGs. **Natural-proofs barrier.**

**3. Observer = a weak restricted model** (bounded memory/resolution, cannot do linear algebra). Then it is
high on exactly the objects the weak model can't handle: parity (`I=n`), Tseitin (resolution-hard) — both
**in P**. Restricted-model lower bound on P-easy objects — the same Layer-2 collapse as the composite `μ`.

**4. The thermodynamic specialization** — count only *irreversible* boundary debt. **Bennett:** any
computation → reversible with erasure cost `= |output|`, decoupled from gate count/difficulty. So the
irreversible debt of deciding `f` is `~1` bit for *any* decision problem, hard or easy — the observer sees
nothing distinguishing. The constraint does not sharpen the witness; it **erases** it. *(= machine-checked
`…InfoBoundaryTest · thermo_work_blind_reversible_computing`.)*

`"dynamic"` is branch 1; `"hypercube boundary"` is branch 2/3; `"thermodynamic"` is branch 4.

---

## Why no non-circular certification exists (structural, not a gap in this construction)

*Certifying that a witness is superpoly for **all** poly-resource observers* **is** a super-polynomial lower
bound against `P`. Any measure genuinely high on SAT and genuinely low on all of `P` has a certification
step equal to the theorem. That is what "separating measure" means; it is not a fixable weakness of this
particular candidate.

---

## Verdict

The observer-visible dynamic-hypercube SPDP is the correct *instinct* (quotient the junk) but the same
`MeasureBarrier` + info-vs-size gap + Bennett cluster in thermodynamic-observer vocabulary. It relocates the
barrier; it does not cross it. New concrete dead-end frozen this round: **for the hypercube costume the
natural hard-witness (total influence / edge-boundary) is maximized by parity — the easiest object** —
joining do-nothing (SPDP grid) and Gaussian-elimination (Tseitin) as demonstrated "high on a P-easy object"
collapses. No live route opens.

*Demos: `observer_hypercube_test.py` (parity maximizes hypercube boundary yet ∈ P), `spdp_blowup.py`,
`tseitin_in_P.py`. Companions: `COMPOSITE_MEASURE_ATTEMPT.md`, `PVSNP1_SCALE_AUDIT.md`,
`NFRAME_RESTRICTED_NOTE.md`. Nothing here is `P ≠ NP`, `P ⊄ NC¹`, or `NEXP ⊄ ACC⁰`.*
