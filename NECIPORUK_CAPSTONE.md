# Nečiporuk `n²/log n` Capstone & Scope

*One-page ledger for the Nečiporuk formula-size lower bound: the genuinely-proved restricted result and its
honest ceiling. Capstone: `PallLean/Paper93/DeepMath/PathB/ComputationalDepthNeciporukCapstone.lean`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.*

---

## The capstone (PROVED, `sorry`-free, custom-axiom-free)

Each name is verified by `#print axioms` to depend on **only** `propext, Classical.choice, Quot.sound`
(the no-go: `propext, Quot.sound`). Complete proofs, not shells.

| Capstone name | Statement | Backed by |
|---|---|---|
| `neciporuk_method` | Nečiporuk method: `∑ᵢ log₂(#blockResiduals Sᵢ F) ≤ 2·⌈log₂(16+2n+1)⌉·litCount F + 2·#blocks` — no carried hypotheses | `neciporuk_formula_lower_bound` |
| `neciporuk_method_opt` | rewired optimal form, constant `4` per leaf: `∑ᵢ log₂(#blockResiduals Sᵢ F) ≤ 4·litCount F + #blocks` | `neciporuk_formula_lower_bound_opt` |
| `neciporuk_n2_over_logn` | explicit `hardF` on `N = nn b m` vars: any `B₂` formula has `litCount F ≥ N²/(64·b)`, `b ≈ log₂N` — **`Ω(N²/log N)`** | `NecHard.hardF_rate_sq_opt` |
| `neciporuk_n2_over_logn_family` | headline family form: `∀ b ≥ 5, ∃ m`, the `Ω(N²/log N)` bound on `hardF` | `NecHard.hardF_rate_opt_family` |
| `neciporuk_skeleton_nogo` | no-go: `freeCount` is unbounded by `leavesIn`, so the naive skeleton bound gives no constant-per-leaf subfunction bound | `freeCount_unbounded_by_leavesIn` |

**What it is:** the classical Nečiporuk `Ω(N²/log N)` De Morgan (`B₂`) formula-size lower bound for an
explicit function, formalized from scratch — the method (`∑ log₂` of per-block distinct-subfunction counts
bounds the leaf count) and an explicit hard function attaining the rate.

---

## The ceiling (why this is a wall, not a bridge)

Nečiporuk's method **provably tops out at `Θ(N²/log N)`**:

- Per block the subfunction count is `≤ 2^{block size}`, so `log₂` of it is `≤ block size`; summed over
  `≈ N/log N` blocks of size `≈ log N`, the method yields at most `Θ(N²/log N)` — this is intrinsic to the
  additive-over-blocks structure (`neciporuk_sum` analysis), not a looseness in the proof.
- The **crossing-capacity bridge** from Nečiporuk-style bounds to `TC⁰` / `NC¹` / width-5 branching
  programs is **false** (recorded in the corpus). So the method does not extend to those classes.
- The `neciporuk_skeleton_nogo` result shows the naive route to a better constant fails, consistent with
  the `N²/log N` ceiling being genuine.

So this is the **best possible** bound from this method — real, restricted, and terminal at `N²/log N`.

---

## Honest scope

- **Proved unconditional:** the Nečiporuk method and an explicit `Ω(N²/log N)` De Morgan formula-size lower
  bound; machine-checked; axioms ⊆ `{propext, Classical.choice, Quot.sound}`; no `sorry`.
- **Not proved / not reachable by this method:** any super-`N²/log N` formula bound, any `TC⁰`/`NC¹`
  bound (bridge false), any super-polynomial bound, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.

Nečiporuk sits at the same tier as the prime `AC⁰[p]` capstone: a genuine, complete, restricted-class
circuit/formula lower bound — real mathematics that is honestly *not* a path to `P ≠ NP`.

*Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. Companion: `PRIME_ACC0_CAPSTONE.md`.*
