import Mathlib

/-!
# Staged fast-SAT without flattening — the outer stages for free; the obstruction relocates into the per-cell count

The candidate crossing route (entries 246 + 249): a *staged* fast-SAT for the depth-2 mixed circuit (outer `MOD_3` of
inner `MOD_2` outputs) that counts in stages — **without flattening** to a single `SYM∘AND` over one field.  Entry 249
proved the staged *representation* is low-degree per layer; entry 246 proved the *cell budget* composes.  This file does
the fast-SAT step honestly, and the finding is decisive but sober:

* **The outer staging is free (PROVED).**  SAT through the outer `MOD_3` is a *bounded disjunction* over the accepting
  residue-classes: `(∃ x, innerCount x ∈ S) ↔ ∃ v ∈ S, ∃ x, innerCount x = v` (`stagedSAT_outer_decomp`).  The outer
  gate is handled by a `|S| ≤ 3`-way case split (`staged_work_le`), **not** by composing it into a single polynomial —
  this is exactly "without flattening."  So the outer layer costs only a constant factor.
* **The obstruction relocates into the per-cell count (socket).**  Each branch `∃ x, innerCount x = v` requires counting
  inputs `x` by the value `innerCount x = #(inner MOD_2 gates firing on x)` **mod 3**.  Counting `F_2`-gate fires
  *mod 3* is the **cross-field mixing in counting form** — the very obstruction (entry 244/249) reappears here, now
  inside the per-cell count rather than in a flattened polynomial.

**Conclusion (honest):** staging the outer is free and the budget composes, but **staging does not bypass the wall** —
the cross-field mixing is intrinsic to the per-cell inner count (count `F_2`-fires mod 3), so it reappears whether or not
you flatten.  The "staged fast-SAT without flattening" route relocates the obstruction; it does not remove it.

⚠️ **No crossing, no faked no-go.**  The outer-staging and work-bound facts are proved.  The per-cell inner count
(`count F_2-fires mod 3` efficiently) is *named* as the relocated obstruction; whether it is tractable is the open
`ACC⁰[composite]` core (entry-238 `CarryRefinementCrossing`).  I do not prove it tractable (a crossing) and I do not
prove it hard (a no-go) — proving the latter is itself the deep Smolensky-strength statement.

## What is proved (clean axioms, no `sorry`)

* **`stagedSAT_outer_decomp`** (PROVED, **no axioms**) — `(∃ x, P x ∈ S) ↔ ∃ v ∈ S, ∃ x, P x = v`: SAT through the outer
  gate is a bounded disjunction over accepting residue-classes (the outer staging, no flattening).
* **`staged_work_le`** (PROVED) — `(∀ v ∈ S, W v ≤ M) → ∑ v ∈ S, W v ≤ S.card * M`: the outer staging contributes only a
  `|S|`-fold (`≤` modulus, constant) factor to the total work.

## The relocated obstruction (named, not proved)

Each per-cell branch counts inputs by `#(inner MOD_2 gates firing) mod 3` — counting `F_2`-gate fires mod 3, the
cross-field mixing in counting form (entry 244/249).  Whether this per-cell count is efficient is the open
`ACC⁰[composite]` core (entry-238 `CarryRefinementCrossing`); staging relocates the obstruction here, not away.

## Honest scope

This proves the outer staging is a free bounded disjunction (`stagedSAT_outer_decomp`) costing a constant factor
(`staged_work_le`) — confirming the outer `MOD_3` needs *no* flattening.  But the per-cell inner count (count `F_2`-fires
mod 3) *is* the cross-field mixing, so staging without flattening **does not bypass** the wall; it relocates the
obstruction into the count.  This file builds the staging and locates the residual obstruction; it does not resolve it
(neither crossing nor no-go).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0StagedFastSAT

/-- **The outer staging (PROVED, no axioms).**  SAT through the outer gate is a bounded disjunction over accepting
residue-classes: `(∃ x, P x ∈ S) ↔ ∃ v ∈ S, ∃ x, P x = v`, where `P x` is the inner count read by the outer gate.  The
outer `MOD_3` is handled by a `|S|`-way case split — **not** by flattening into a single polynomial. -/
theorem stagedSAT_outer_decomp {X : Type} (P : X → ℕ) (S : Set ℕ) :
    (∃ x, P x ∈ S) ↔ ∃ v ∈ S, ∃ x, P x = v := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨P x, hx, x, rfl⟩
  · rintro ⟨v, hv, x, hx⟩; exact ⟨x, hx ▸ hv⟩

/-- **The outer staging is a constant factor (PROVED).**  If each per-residue branch costs `≤ M`, the total staged work
is `≤ |S| * M` — the outer gate contributes only a `|S| ≤ modulus` factor (here `≤ 3`).  So the outer layer is cheap;
the work is dominated by the per-cell inner count. -/
theorem staged_work_le (S : Finset ℕ) (W : ℕ → ℕ) (M : ℕ) (h : ∀ v ∈ S, W v ≤ M) :
    ∑ v ∈ S, W v ≤ S.card * M := by
  calc ∑ v ∈ S, W v ≤ ∑ _v ∈ S, M := Finset.sum_le_sum h
    _ = S.card * M := by rw [Finset.sum_const, smul_eq_mul]

/-!
**The relocated obstruction (named, not proved).**  The outer staging above reduces SAT to `|S| ≤ 3` branches, each
counting inputs by `innerCount x = #(inner MOD_2 gates firing) mod 3`.  Counting `F_2`-gate fires *mod 3* is the
cross-field mixing in counting form (entries 244/249): the obstruction is intrinsic to the per-cell inner count, not to
the outer staging.  So staging without flattening does **not** bypass the wall — it relocates the cross-field mixing
into the count.  Whether this per-cell count is efficient is the open `ACC⁰[composite]` core (entry-238
`CarryRefinementCrossing`); not resolved here.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0StagedFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0StagedFastSAT.stagedSAT_outer_decomp
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0StagedFastSAT.staged_work_le
