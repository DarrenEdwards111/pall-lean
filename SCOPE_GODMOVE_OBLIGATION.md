# Scope — the God-Move / Cook–Levin proof obligation, made precise

**Goal (per the plan): state the two load-bearing frontier hypotheses exactly, decompose them into local
lemmas, and prove the logical skeleton — so the proof obligation is fully visible.  The skeleton is
formalized in `ComputationalDepthGodMoveObligation.lean` (sorry-free, axiom-clean).**

---

## The two routes, and the honest status of each

A `P ≠ NP` proof becomes unconditional iff one of these becomes a theorem:

* **Route F — `CookLevinFrontierHyp`** (P-side rank frontier): every bounded Cook–Levin compilation has the
  within-profile / SPDP rank upper bound.  Already isolated as a `Prop`; `peqnp_false_of_frontier` is
  kernel-clean conditional on it.
* **Route G — `GlobalGodMoveHyp`** (God-Move extraction): a rank-monotone, witness-free, instance-uniform
  gauge `T_Φ` with `T_Φ(P_solver Φ) = Q_Φ` and `rank(T_Φ p) ≤ rank p`.  Now demoted from a custom axiom to
  explicit `Prop` hypotheses (`SCOPE_PVSNP1_AUDIT.md`, "RESOLVED").

## What the skeleton theorem settles about Route G

`ComputationalDepthGodMoveObligation.lean` formalizes the God-Move gauge precisely
(`GodMoveGaugeExists R p₀ B k` = `∃ T, RankMonotone R T ∧ R(T p₀) ≤ B ∧ k ≤ R(T p₀)`) and proves:

* **`not_godMoveGaugeExists_of_gap`** — *the central danger, as a theorem*: when `B < k` (`B = n²⁰⁰`,
  `k = C(n/3, log n)`, gap holds at `n = 2⁸⁰⁴`), **no such gauge exists**.  It is the rank sandwich
  `k ≤ R(T p₀) ≤ B < k` — `godMove_rank_monotone` + the projected P-side bound, confronted with the
  axiom-free NP-side minor.
* **`globalGodMoveHyp_iff_no_hard`** — **`GlobalGodMoveHyp ↔ ¬∃ hard instance`**, given the per-instance gap.

**Verdict.**  Route G is **not** an independent path.  `GlobalGodMoveHyp` is *logically equivalent* to the
restricted separation.  Proving it cannot mean *constructing* a gauge — for a hard instance the gauge is
internally contradictory (the sandwich) — it can only mean proving no hard instance exists, i.e. proving the
separation directly.  The amplituhedron / God-Move language faithfully re-encodes the problem; it does not
reduce it.  (Same shape as `ObserverFrontierHyp` and the Layer-10 bridges.)

## Decomposition of the two load-bearing lemmas (the local targets)

These remain genuinely open; each is a named obligation, never asserted.

### Route G local lemmas (the gauge)
1. `godMove_gauge_exists` — the amplituhedron/global gauge exists for the instance.
2. `godMove_projection_multilinear` — the projection preserves multilinearity.
3. `godMove_admin_collapse` — administrative (tableau-bookkeeping) variables collapse correctly.
4. `godMove_clause_sheet_survives` — the clause-sheet `Q_Φ` survives the projection.
5. `godMove_correct` — the extracted object equals `Q_Φ`: `T_Φ(P_solver Φ) = Q_Φ`.
6. `godMove_rows_into_subspace` — SPDP rows map into subrows/subspaces.
7. `godMove_rank_monotone` — `rank(T_Φ p) ≤ rank p` (profile rank cannot increase).
8. `godMove_witness_free` — `T_Φ` depends only on `Φ`, not on a satisfying assignment.

**But (1)+(5)+(7) jointly, for a *hard* instance, are impossible** (`not_godMoveGaugeExists_of_gap`): the
gauge that is correct *and* rank-monotone *and* P-side-bounded *and* minor-preserving cannot exist when
`B < k`.  So this list is not a to-do list whose completion yields a proof — completing 1–8 for a hard
instance is contradictory.  The only consistent way they all hold is if the instance is not hard — the
separation.

### Route F local lemmas (the P-side frontier — `CookLevinFrontierHyp`)
1. profile classification (finitely many local profiles);
2. within-profile finrank bound;
3. bounded number of profiles;
4. Cook–Levin locality;
5. profile-span compression;
6. final SPDP rank bound `≤ n²⁰⁰`.

This is the cleaner route (no gauge to construct): it is a genuine upper-bound program on the SPDP rank of
the *unprojected* Cook–Levin compilation.  It does not collapse to "the separation" the way Route G does —
it is a concrete (open) rank bound.  Recommended target if the work continues.

## Tiny-instance test (item 3)

`tiny_no_gauge` (in the Lean file) is the minimal computational sanity: with `R = id`, `B = 3 < k = 5`, no
gauge keeps `R(T p₀) ≤ 3` while `5 ≤ R(T p₀)`.  This is the rank sandwich at the smallest scale — it shows
the obstruction is not an artifact of `n = 2⁸⁰⁴` but holds whenever `B < k`.

A fuller tiny test (next concrete step, honest sandbox): build a tiny SAT instance → tiny Cook–Levin
tableau → compiled polynomial → a candidate projection `T` → compute the SPDP/partial-derivative rank
before and after via `native_decide`.  Two things to look for: (a) does the candidate `T` actually satisfy
`rank(T p) ≤ rank p` (most projections do *not* — rank monotonicity is special); (b) can any `T` both
collapse the P-side rank and keep the minor — which the skeleton theorem says is impossible once `B < k`.

## Bottom line

The God-Move architecture is now fully precise and its skeleton proven.  The honest finding is that **Route
G ≡ the separation** (proving the gauge = proving `P ≠ NP`), so the productive frontier is **Route F**
(`CookLevinFrontierHyp`): a concrete SPDP rank upper bound, decomposed above, that does not secretly contain
the whole problem.  Neither is asserted; both stay explicit hypotheses until genuinely proved.
