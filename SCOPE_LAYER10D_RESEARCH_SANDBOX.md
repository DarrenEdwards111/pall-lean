# Scope — Layer 10D: the research sandbox

**Status: a disciplined sandbox for *candidate* frontier hypotheses.  Nothing here is a separation claim.
Every candidate is a named `Prop`, never a theorem; every consequence is conditional.**

This is where genuinely *new* (speculative) content is allowed to live — under strict rules, so it can
never masquerade as a result.

---

## The rules (non-negotiable)

1. **A candidate is a `def … : Prop`, never a `theorem`.**  Naming it does not assert it.
   (`Hyp_explicit_circuit_lower_bound`, `Hyp_monotone_complete` in
   `ComputationalDepthLayer10ResearchSandbox.lean`.)
2. **Use only as an explicit hypothesis.**  Every downstream statement *takes the candidate as an
   argument* — exactly the `CookLevinFrontierHyp` pattern (`sep_of_hyp`, `p_ne_np_of_hyp`).
3. **Keep it falsifiable.**  Where the surrounding objects are finite, add small-`n` `native_decide` tests
   that would *catch* a wrong definition or a naive false conjecture.
4. **Be explicit about trust.**  The conditional bridges are axiom-clean (`[propext, Quot.sound]`).  The
   small-`n` tests use `native_decide`, which adds the standard compiler-trust axioms
   (`Lean.ofReduceBool`, `Lean.trustCompiler`) — *not* `sorry`, *not* custom axioms, but worth stating.

## What is in the sandbox

### Computational tests (validate the framework against known values)

* `dedekind_one/two/three` — the number of monotone functions on `n` bits is `3, 6, 20` for `n = 1,2,3`
  (the **Dedekind numbers** `M(n)`).  These match the literature, so `MonotoneFn` (10C) is faithfully
  formalized.  (Dedekind numbers have no known closed form — `M(9)` was first computed in 2023 — a genuine
  open combinatorial frontier, here a *sanity oracle*.)
* `parity_two_not_monotone`, `not_all_monotone` — falsification: PARITY is non-monotone and not all
  functions are monotone, so a careless "everything is monotone" conjecture dies at `n = 2`.

### Candidate hypotheses (OPEN, named, never asserted)

* `Hyp_explicit_circuit_lower_bound` — *some `NP/poly` language is `∉ P/poly`* (a super-polynomial
  general-circuit lower bound for an explicit language).  This **is** the open frontier
  (`SCOPE_LAYER8_EXPLICIT_LOWER_BOUND_FRONTIER.md`), barrier-blocked
  (`SCOPE_LAYER10A_BARRIER_LANDSCAPE.md`).
* `Hyp_monotone_complete n` — *every monotone function has a monotone circuit* (a known theorem; its
  converse is proved in 10C; stated here as a named hypothesis, consistent with the Dedekind tests).

### Conditional chain (the honest payoff)

`p_ne_np_of_hyp : (P ⊆ P/poly) → Hyp_explicit_circuit_lower_bound → P ≠ NP/poly`.  Both inputs explicit:
the standard inclusion `P ⊆ P/poly`, and the open lower-bound hypothesis.  This is the entire circuit route
to `P ≠ NP`, with its two load-bearing assumptions named and isolated — and *neither asserted*.

## How a future conjecture enters the sandbox

1. Write it as `def Hyp_… : Prop` with a precise statement.
2. If finite-at-small-`n`, add `native_decide` tests of instances / consequences; if a test fails, the
   conjecture (or a definition) is wrong — stop.
3. State its consequences as conditional theorems taking `Hyp_…` as an argument.
4. Never discharge `Hyp_…` unless a *real proof* exists; a plausible-looking small-`n` pattern is evidence,
   **not** a proof, and must not be promoted to a `theorem`.

This closes Layer 10: the frontier is mapped (10A), the route to `P ≠ NP` is precise (10B), a real
restricted-model separation is proved (10C), and the sandbox (10D) gives speculative work a home that
cannot be mistaken for a result.
