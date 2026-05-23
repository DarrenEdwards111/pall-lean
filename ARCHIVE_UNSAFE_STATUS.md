# `archive-unsafe-chain` — false-axiom cleanup status

**Branch:** `archive-unsafe-chain`  (forked from `godmove-paper-faithful`)
**Goal:** remove the false `spdp_profile_generators` axiom and everything built on it
from the *live* build, preserving (archiving) the removed code under
`PallLean/Archive/Paper93Unsafe/`.

---

## TL;DR

- ✅ The core false axiom and its inconsistency machinery are **archived and
  build-verified** at the source layer.
- ❌ The **full repo build is NOT green**: `Step4Compiler.lean` is a
  ~54,780-line / 1,727-declaration file containing ~**169 false-axiom-based
  "P ≠ NP" wrapper theorems** that dangle on the symbols moved in increments
  1–4. They cannot be excised cleanly by script (two attempts corrupted the
  file) and rewriting 50k lines of the author's formalization is out of scope
  for automated tooling. **This file requires a human, author-led rewrite.**

The mathematical bottom line (established earlier and unchanged): the false
axiom is *refuted by the repo's own proven NP-side identity-minor lower bound*;
there is no honest unconditional `P ≠ NP` here. The honest, axiom-clean results
(obstruction theorems + the NP lower bound) are preserved.

---

## Done & VERIFIED (committed on this branch)

Increments 1–4 moved the following from live files into
`PallLean/Archive/Paper93Unsafe/` (text preserved):

| inc | moved out of | what | archive module |
|----|----|----|----|
| 1 | `SymmetricPower.lean` | `axiom spdp_profile_generators` (+ `product_leibniz_profile_cover`, `leibniz_symmetric_power_descent_bound`) | `SpdpProfileGeneratorsAxiom.lean` |
| 2 | `SymmetricPowerBound.lean` | the axiom-using Step-D assembly (`profile_compression_rank_bound` chain) — **kept** the conditional `_honest_`/arithmetic siblings | `ProfileCompressionRankBound.lean` |
| 3 | `ProfileCompression.lean` | unconditional `profile_compression_rank_bound` + `p_side_rank_bound_for_cook_levin` — **kept** all 10 `_of_*` conditionals | `ProfileCompressionPSide.lean` |
| 4 | `PaperFaithfulSeparation.lean` | unconditional `p_side`, the `: False` witness `spdp_profile_generators_inconsistent_with_np_side`, and all `P_ne_NP_unconditional*` / `P_ne_NP_via_*` separation claims — **kept** the obstruction + `no_rank_sandwich_*` arithmetic + conditional `_of_*` + PAC bridge | `PaperFaithfulSeparationUnsafe.lean` |

**Build-verified green** (via `lake build`, mathlib v4.28.0):
- `lake build PallLean.ProfileCompression`  → `Build completed successfully (8048 jobs)`
- `lake build PallLean.PaperFaithfulSeparation` → `Build completed successfully (8060 jobs)`

`WithinProfileBound` theorems verified `#print axioms = [propext, Classical.choice, Quot.sound]`
(the honest conditional path survived the cuts).

**Honest results preserved live (axiom-clean):**
- `PaperFaithfulSeparation.no_rank_sandwich_at_large_n` — pure arithmetic, no `r` with `C(n/3,log n) ≤ r ≤ n^200` at `n ≥ 2^804`.
- `PaperFaithfulSeparation.isAmplituhedronGauge_uninhabited_for_sat_decider`.
- `Step4Compiler.Step252.cookLevinStrictFOBTarget_same_target_lower` — the proven NP-side identity-minor lower bound.
- PathB obstruction theorems: `godMove_transport_upper_bound_impossible_at_paperScale`, `theorem207_strict_target_incompatibility`.
- The NP-side / Tseitin-OBDD lower bound machinery.

---

## BLOCKER: `Step4Compiler.lean`

- Imported (transitively) by the root `PallLean.lean`, so it gates the full build.
- Contains ~169 unsafe declarations (separation claims + `*_from_p_side` bridges)
  that reference the now-archived `PaperFaithfulSeparation.p_side_rank_bound_for_cook_levin`
  and `P_ne_NP_unconditional` → they now produce `Unknown identifier`.
- Examples: `P_ne_NP_absolute`, `P_ne_NP_truly_final`, `P_ne_NP_finally_closed`,
  `P_ne_NP_ultimate`, `P_ne_NP_truly_unconditional_final`, the `P_ne_NP_Lean*`
  family, `P_ne_NP_unconditional_constructive*`, `bounded_params_at_2pow804_absurd`,
  `amplituhedron_gauge_for_sat_decider_constructive`, `PeqNP_Paper_False_unconditional`,
  `cookLevinQ_rank_le_from_p_side` (+ `_at_B_total`, `DirectRankPackage_…_from_p_side`).
- Why automated removal fails: doc-comment + attribute + nested-namespace
  (`Step199`/`Step213`/…) structure defeats line-based segmentation (leaves
  syntax fragments), and a transitive-closure pass over-deletes safe
  infrastructure (e.g. `TMSimBlock`).

### What a rewrite must KEEP (safe symbols downstream depends on)
The honest theorems and other live files need at minimum:
- the Cook–Levin compiler construction: `cook_levin_compilation`, `Step247.partitioned_output_cookLevin`, `TMSimBlock`, the partition/compiledPoly machinery;
- `Step252.cookLevinStrictFOBTarget` + `cookLevinStrictFOBTarget_same_target_lower` (NP-side lower bound) + the strict-`TΦ` extraction-transfer machinery;
- the conditional `cookLevinQ_rank_le_from_templateCollapse(_at_B_total)` and `DirectRankPackage_…_from_templateCollapse` chain, and `P_ne_NP_from_cookLevin_templateCollapse_hypothesis` (these are *conditional*, axiom-clean — KEEP).

### What a rewrite must DROP
- Every theorem concluding `P ≠ NP` / `PeqNP_Paper → False` / unconditional `False`
  (no honest proof exists — all route through the false axiom/gauge), and the
  `*_from_p_side` (non-`templateCollapse`) bridges, plus their scattered
  `#print axioms` lines.

---

## Also still pending (separate, lower severity)
- `GlobalGodMoveGauge.lean` still **declares** `exists_amplituhedron_gauge` and
  `exists_amplituhedron_gauge_for_sat_decider` (their *users* were archived in
  inc 4). These are guarded by `DecidesSAT`, so they do **not** produce an
  unconditional `False`, but they remain declared custom axioms and should be
  archived for full cleanliness.

---

## How to verify / resume
```bash
git checkout archive-unsafe-chain
lake build PallLean.ProfileCompression       # green
lake build PallLean.PaperFaithfulSeparation  # green
lake build PallLean.Step4Compiler            # FAILS: ~169 dangling separation wrappers
```
Full green build requires the author-led `Step4Compiler.lean` rewrite described above.
