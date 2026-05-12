# P≠NP Lean Hard-Closeout Status (No Shortcuts)

Date: 2026-05-12
Branch: `godmove-paper-faithful`

## Goal
A **custom-axiom-free canonical theorem** of the form:

```lean
theorem P_ne_NP_canonical_zero_custom_axioms : ∀ (_ : PeqNP_Paper), False
```

with `#print axioms` showing only classical Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Current audited state (machine-checked via `#print axioms`)

### Core stack
1. `PaperFaithfulSeparation.p_side_rank_bound_for_cook_levin`
   - Axioms: `propext`, `Classical.choice`, `Quot.sound`, `SymmetricPower.spdp_profile_generators`
   - **Blocker:** custom axiom `spdp_profile_generators`

2. `Step4Compiler.perm_spdp_rank_exponential`
   - Axioms: `propext`, `Classical.choice`, `Quot.sound`
   - **Good:** no custom axiom

3. `PallLean.Paper93.DeepMath.CookLevin.paper_theorem_207`
   - Axioms: `propext`, `Classical.choice`, `Quot.sound`
   - **Good:** no custom axiom

### P≠NP closure variants
4. `PaperFaithfulSeparation.P_ne_NP_via_theorem207`
   - Axioms: `...`, `GlobalGodMoveGauge.exists_theorem207_witness`
   - **Blocker:** custom existence axiom

5. `PaperFaithfulSeparation.P_ne_NP_unconditional`
   - Axioms: `...`, `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider`
   - **Blocker:** custom existence axiom

6. `PaperFaithfulSeparation.P_ne_NP_unconditional_step4_constructive`
   - Axioms: `...`, `SymmetricPower.spdp_profile_generators`
   - **Blocker:** custom profile-compression axiom remains

### Route B (newly closed seam)
7. `...noBoundedSATDeciderAtPaperScale_of_step247Uniform...ProfileTemplateSpanData`
8. `...noBoundedSATDeciderAtPaperScale_of_step247Uniform...ProfileTemplateLocalMonoidNormalForms`
9. SAT Path B extraction moves for both seams
   - Axioms: classical only (`propext`, `Classical.choice`, `Quot.sound`)
   - **Good:** no custom axiom on these theorems
   - **But:** these are conditional on Step247 uniform seam hypotheses.

---

## Exact blockers to eliminate for a zero-custom-axiom canonical close

## Blocker A: `SymmetricPower.spdp_profile_generators`
Used by `p_side_rank_bound_for_cook_levin` and thus by constructive global closure variants.

### Required replacement theorem
Need a theorem (same shape) with no custom axiom dependency:

```lean
theorem p_side_rank_bound_for_cook_levin_zero_custom
  (M : DTM) (n : ℕ) (hn : n ≥ 2)
  (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
  mlBlockedSpdpRank ... (compiledPoly ...) ≤ n ^ 200
```

with `#print axioms` classical-only.

This is the main hard mathematical closeout item.

## Blocker B: Gauge/Theorem207 existence axioms
- `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider`
- `GlobalGodMoveGauge.exists_theorem207_witness`

These remain in top-level theorem variants that route through existential gauge witnesses.

### Required action
Either:
1. avoid these variants in canonical claim, and route through an axiom-free contradiction chain, or
2. discharge those existence axioms constructively.

Given current codebase, option (1) is likely faster: canonicalize on a chain that does not consume `GlobalGodMoveGauge.exists_*`.

---

## No-shortcut canonicalization strategy

1. Keep Route B seam as already proved (classical-only) and treat it as the paper-faithful closure route.
2. Build/identify one theorem that turns a proved Route B no-decider statement into `∀ (_ : PeqNP_Paper), False`.
3. Ensure that theorem itself uses only arithmetic + `PeqNP_Paper` fields (decider/time/state bounds), no custom axiom.
4. Replace paper “canonical theorem” references with that chain.
5. Re-run `#print axioms` on final named theorem.

---

## Immediate next executable tasks

- [x] Add theorem: `noBoundedSATDeciderAtPaperScale_implies_not_PeqNP` (bridge from no-decider proposition to `PeqNP_Paper → False`).
- [x] Add canonical conditional Route-B theorem at `PeqNP_Paper` level:
  - `P_ne_NP_canonical_routeB_profileTemplateSpan_conditional`
  - Axiom footprint: `propext`, `Classical.choice`, `Quot.sound`.
- [ ] Find/import an **unconditional** no-decider theorem already present in `Paper93` (if any), else formalize one minimal route with explicit assumptions and mark as conditional.
- [ ] If unconditional route still depends on `spdp_profile_generators`, isolate that as the sole remaining custom-axiom frontier.
- [ ] Add `#print axioms` anchors for the final unconditional canonical theorem candidate.

---

## Bottom line right now

- Route B proof engineering is strong and paper-faithful.
- Global claim is **not yet** zero-custom-axiom complete.
- Remaining hard frontier is explicit and narrowed: primarily replacing `spdp_profile_generators`, and avoiding/discharging gauge existence axioms in canonical top-level closure.
