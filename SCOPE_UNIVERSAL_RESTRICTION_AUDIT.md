# Audit — the fixed-exponent universal-restriction SPDP scheme (paper-only)

Directed target: audit the p-vs-np1 "universal-restriction" idea HAL resurfaced, against its three checks, and
decide whether it discharges or restates the separation.  Grounded in the existing `SCOPE_PVSNP1_AUDIT.md`
(the repo's prior kernel-checked status of exactly this route).  **No Lean this round (per instruction).**

## 0. What is genuinely new — credit where due

The scheme *does* solve the "all polynomial exponents" problem that kills a single NP diagonal:

> For each constant `k`: one universal simulator `U_k` for `DTIME(n^k)`; one machine-independent restriction
> `ρ_{n,k}`; prove `∀ M ∈ DTIME(n^k), R(compile(M,n) ↾ ρ_{n,k}) ≤ n^{O(1)}`; prove `R(SAT_n ↾ ρ_{n,k}) ≥ n^{ω(1)}`.
> Under `SAT ∈ P` the decider has *some* fixed `k`, so that one `k`-slice contradicts — no need for one language to
> beat every exponent at once.

This is real and it is the right move for the quantifier problem (the exact obstacle that stopped the round-3
alternation-trading uniform diagonal).  It is not the wall.

## 1. Check 1 — universal-simulator commutation

Claim needed: fixing `U_k`'s machine-code bits to `⌜M⌝` and applying `ρ_{n,k}` recovers `compile(M,n) ↾ ρ_{n,k}`
with the rank bound intact.  **Assessment: plausible as a technical lemma, not load-bearing.**  It is a
compilation-hygiene statement (the universal simulator's restricted compiled object specializes to each machine's
restricted compiled object).  If the compilation is monotone/local under `ρ`, this holds.  It is a real proof
obligation but it is *not* where the route dies.

## 2. Check 2 — semantic invariance / extraction: THE WALL, and it equals the separation

This is the load-bearing bridge, and the audit is decisive.

* Step 3 bounds `R(compile(M,n) ↾ ρ)` — the rank of a **specific representation** (the tableau/verifier compiled
  object of `M`).
* Step 4 lower-bounds `R(SAT_n ↾ ρ)` — the rank of a **different representation** (the natural 3SAT/Tseitin
  object).
* SPDP rank is a property of the **representation (matrix/tableau), not the function.**  Two objects computing the
  same function `SAT` can have different ranks.  So low `R(compile(M))` and high `R(SAT_n)` **do not contradict** —
  both compute `SAT`, at different ranks.  No contradiction without a **representation-invariance bridge**.

That bridge is exactly the God-Move `T_Φ` (Item 3 of the spine), and it is a **live unproved hypothesis**
(`AmplituhedronGaugeHyp`, `Theorem207WitnessHyp` — the audit confirms these are hypotheses/axioms, not theorems).
Unfold what it must say:

> `T_Φ` maps *any correct decider's* `compile(M) ↾ ρ` to the high-rank SAT object with `R(T_Φ p) ≤ R(p)`.

Then `R(compile(M) ↾ ρ) ≥ R(T_Φ(compile(M) ↾ ρ)) = R(SAT object) = high`, **for every correct decider `M`**.  So
the bridge asserts precisely:

> **every correct SAT decider's compiled object has high SPDP rank.**

Combined with the P-side (every `n^k` computation has low rank after `ρ`), that is `SAT ∉ P`.  Conversely, if
`SAT ∈ P` a poly decider has low rank, so the bridge is false.  **The semantic-extraction bridge is equivalent to
the separation itself** (given the P-side).  It is not a lemma the scheme can supply — it is the conclusion.  This
is exactly HAL's own stop-condition: *"if check 2 reduces to 'every SAT decider has high rank,' the route has
merely restated the separation."*  It does.

## 3. Check 3 — easy-function / witness-slack calibration: a concrete falsification risk

Two ways the NP-side high rank can be an **artifact** that does not bound decision hardness:

* **Witness slack.**  A *verifier* tableau for an NP object carries the witness/assignment variables; those can
  inflate SPDP rank without the *decision* problem being hard.  The proved asset (Item 2,
  `compiled_np_lower_bound_any_dtm`, the identity-minor `C(n/3, log n)` bound) lower-bounds the rank of a
  **compiled verifier/tableau representation**.  A **decider** carries no witness variables.  So Item 2 — genuine
  and axiom-free as it is — bounds the **wrong object** for the separation: verifier rank, not decider rank.
  Bridging verifier-rank to decider-rank is again the representation-invariance of check 2.
* **QF calibration (corrected — see `SCOPE_QF_CALIBRATION_AUDIT.md`).**  `QF A` is in P (`qfProg A`, `4n²` gates,
  `ChargedCompiler.qfProg_correct`) yet has maximal *tensor/entanglement* (Schmidt) rank across every cut
  (`exists_global_best_partition_bond`).  **This makes `QF A` a clean falsifier for any COMMUNICATION/tensor-rank
  measure — but NOT for SPDP** (shifted-partial-derivative) rank, a *different* measure: the natural quadratic
  `q_A` has total degree 2, so at matched params `κ = log n ≥ 3` all `∂_S q_A` vanish and `spdpRank q_A = 0`.  So
  the SPDP easy-function check is *passed* by the natural quadratic; QF A does not over-count *here*.  (My earlier
  wording "ready falsifier for any SPDP measure" was an error, conflating tensor rank with SPDP rank.)  The
  residual risk is only sub-case (a) above — verifier vs decider representation — which is check 2 again.

## 4. Cross-check against the prior audit and the memory refutation

Consistent on every point:

* Item 1 (P-side) = **`CookLevinFrontierHyp`**, and the prior audit already sharpened that it must contain a
  *No-Fixed-Structure-Amortization* theorem **and** a *Scale Bridge*, where the Scale Bridge (H4) *is* the
  P-vs-NP-scale barrier (`PVSNP1_NO_AMORTIZATION_PATCH.md`, `PVSNP1_SCALE_AUDIT.md`).  The universal-restriction
  reframing does not supply either; `ρ_{n,k}` is orthogonal to the amortization/scale content.
* Item 3 (extraction) = the God-Move, **live hypothesis**, = check 2 above.
* The memory note "SPDP route refuted — measure uniform-across-machines can't separate; within-profile FALSE at
  `n = 2^804`" is the *same* representation-dependence wall: a measure that is uniform across machines cannot both
  be low on every P-decider's representation and high on the fixed SAT representation unless it is
  representation-invariant — which is check 2.  `no_rank_sandwich_at_2pow804` is the arithmetic showing the
  polynomial-threshold version has no consistent value; the universal-restriction scheme does not change that
  arithmetic, only the exponent quantification.

## 5. Verdict

* **Genuinely new:** the fixed-exponent restriction resolves the "one language beats every exponent" quantifier
  problem.  Credit it; it is not the wall.
* **The wall is check 2**, and it is *equivalent to the separation*: the semantic-extraction/representation-
  invariance bridge asserts "every correct SAT decider has high SPDP rank," which with the P-side is `SAT ∉ P`.
  The scheme relocates the diagonal but leaves this bridge exactly where the prior audit left it — an unproved
  hypothesis that cannot be discharged by rank bookkeeping.
* **Concrete falsification pressure (check 3):** the proved NP-side bound is about a *verifier/tableau* (witness
  variables inflate rank), not a *decider*; and `QF A` — poly-time, maximal-rank — is a ready falsifier for any
  SPDP measure not proven to ignore poly-time structure.  Until the measure is shown to give `QF A` low rank and
  to bound *decider* (not verifier) rank, the NP-side is not a decision lower bound.
* **Recommendation:** do not start Lean.  The scheme does not discharge `CookLevinFrontierHyp` + the semantic
  bridge; it re-expresses them.  Per HAL's criterion the route restates the separation at check 2.  The two
  genuine, surviving assets remain what the prior audit found: (i) the axiom-free identity-minor NP-side rank bound
  (real mathematics, but for the verifier representation), and (ii) the `QF A` calibration (a machine-checked
  falsifier keeping any rank measure honest).  The missing content is a *proved, witness-free, decider-level,
  representation-invariant* rank map — i.e. the separation.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
