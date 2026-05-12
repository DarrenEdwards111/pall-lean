# Global Assumption Inventory v1 (Paper ↔ Lean)

Date: 2026-05-12  
Repo: `pall-lean`  
Branch: `godmove-paper-faithful`  
Route B closure commit: `b3f9fbac`

This file is a **paper-facing audit table** mapping load-bearing claims to Lean artifacts and their current axiom footprint.

Axiom footprints below were checked via Lean (`#print axioms`) on:
- `PaperFaithfulSeparation.p_side_rank_bound_for_cook_levin`
- `Step4Compiler.perm_spdp_rank_exponential`
- `PallLean.Paper93.DeepMath.CookLevin.paper_theorem_207`
- `PaperFaithfulSeparation.P_ne_NP_via_theorem207`
- `PaperFaithfulSeparation.P_ne_NP_unconditional`
- `PaperFaithfulSeparation.P_ne_NP_unconditional_step4_constructive`
- Route B new Step247/profile-template closure theorems

---

## A) Core paper spine (Theorem 92 / 94 / 207)

| Paper claim | Lean artifact | Status | Axiom footprint (audited) | Notes |
|---|---|---|---|---|
| Theorem 92-style P-side bound (`Γ(P_{M,n}) ≤ n^200`) | `PallLean/PaperFaithfulSeparation.lean` — `p_side_rank_bound_for_cook_levin` | **present, load-bearing theorem** | `propext`, `Classical.choice`, `Quot.sound`, `SymmetricPower.spdp_profile_generators` | Includes custom axiom `spdp_profile_generators` (known problematic/legacy in repo commentary). |
| Theorem 94 NP-side exponential lower bound | `PallLean/Step4Compiler.lean` — `perm_spdp_rank_exponential` | **proved theorem** | `propext`, `Classical.choice`, `Quot.sound` | No custom nonstandard axiom in this theorem. |
| Theorem 207 rank-chain statement (paper-named) | `PallLean/Paper93/DeepMath/CookLevin/Theorem207Statement.lean` — `paper_theorem_207` | **proved theorem** | `propext`, `Classical.choice`, `Quot.sound` | Kernel-side rank-chain statement present and audited. |

---

## B) P≠NP closure variants (important for paper wording)

| Closure theorem | Lean artifact | Status | Axiom footprint (audited) | Interpretation |
|---|---|---|---|---|
| Theorem-207-style closure | `PallLean/PaperFaithfulSeparation.lean` — `P_ne_NP_via_theorem207` | **present** | `propext`, `Classical.choice`, `Quot.sound`, `GlobalGodMoveGauge.exists_theorem207_witness` | Uses one custom existence axiom (`exists_theorem207_witness`). |
| “Unconditional” chain (narrow gauge form) | `.../PaperFaithfulSeparation.lean` — `P_ne_NP_unconditional` | **present** | `propext`, `Classical.choice`, `Quot.sound`, `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` | Depends on custom SAT-decider gauge existence axiom. |
| Step4 constructive variant | `.../PaperFaithfulSeparation.lean` — `P_ne_NP_unconditional_step4_constructive` | **present** | `propext`, `Classical.choice`, `Quot.sound`, `SymmetricPower.spdp_profile_generators` | Uses `spdp_profile_generators` custom axiom. |

---

## C) Route B paper-faithful closure (newly wired, no singleton EventAtom dependency)

| Route B claim | Lean artifact | Status | Axiom footprint (audited) | Notes |
|---|---|---|---|---|
| Step247 profile-template span-data seam closes | `PallLean/Paper93/DeepMath/PathB/RouteBPlacedQuotientDescentKR.lean` — `noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData` | **proved theorem** | `propext`, `Classical.choice`, `Quot.sound` | No custom nonstandard axiom here. |
| Step247 exact-budget profile-template local-monoid seam closes | `...RouteBPlacedQuotientDescentKR.lean` — `noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms` | **proved theorem** | `propext`, `Classical.choice`, `Quot.sound` | No custom nonstandard axiom here. |
| SAT Path B extraction move (span seam) | `PallLean/Paper93/DeepMath/PathB/SATPathBChain.lean` — `SAT_path_B_paperFaithfulSourceWitnessedLeibnizProfileTemplateSpanData_TPhi_extraction_move` | **proved theorem** | `propext`, `Classical.choice`, `Quot.sound` | New paper-facing seam theorem. |
| SAT Path B extraction move (exact-budget local-monoid seam) | `.../SATPathBChain.lean` — `SAT_path_B_paperFaithfulSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms_TPhi_extraction_move` | **proved theorem** | `propext`, `Classical.choice`, `Quot.sound` | New paper-facing seam theorem. |
| Singleton EventAtom-QDim universal target-span route required for final closure | (no theorem required on final route) | **not used** | n/a | Final Route B closeout explicitly bypasses this frontier. |

---

## D) Paper text updates required (to stay faithful)

1. Replace blanket claims like “Lean completion is future work” with precise status:
   - Route B profile-template/local-monoid Step247 closure is now Lean-wired + build-checked.
2. Keep open only what is truly open:
   - custom existence axioms in selected P≠NP closure variants;
   - `spdp_profile_generators` dependency where still present.
3. Add one concise paragraph:
   - Final Route B closeout does **not** rely on universal singleton EventAtom-QDim target-span membership.

---

## E) Build evidence for Route B close

Verified target builds:

```bash
lake build PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction
lake build PallLean.Paper93.DeepMath.PathB.RouteBPlacedQuotientDescentKR
lake build PallLean.Paper93.DeepMath.PathB.SATPathBChain
```

---

## F) Suggested paper snippet (drop-in)

> **Lean audit status (current).** The Route-B Step247 closeout is machine-checked along the selected-profile template span / exact-budget local-monoid normal-form route, with checked adapters into the existing local-monoid closure surface. This route does not require a universal singleton EventAtom-QDim target-row-in-target-span claim. In the global separation stack, NP-side Theorem-94-style rank growth and the paper-named Theorem-207 rank-chain statement are Lean-checked; some top-level P≠NP closure variants still depend on explicitly named custom existence/profile axioms, itemized in the assumption inventory table.
