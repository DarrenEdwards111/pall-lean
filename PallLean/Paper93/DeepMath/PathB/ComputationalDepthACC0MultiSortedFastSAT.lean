import Mathlib

/-!
# Multi-sorted fast-SAT — the cell budget composes (proved); per-field gate representation is the blocked core

Entry 245 built the multi-sorted product-field observer (faithful reader of `MOD_m` with per-prime low-degree
components) and left feeding fast-SAT as the open socket.  This file analyses that fast-SAT step honestly.  The finding
again splits cleanly into a *proved* good-news budget fact and the *blocked* core:

* **The multi-sorted fast-SAT cell budget composes and stays quasipoly (PROVED).**  A `k`-prime multi-sorted observer
  counts over the *product* of per-prime count-ranges; the joint cell-count is `∏ᵢ (mᵢ+1) ≤ (M+1)^k` — quasipolynomial
  when each `mᵢ ≤ M` is quasipoly and `k` (the number of prime factors) is constant.  And the speedup condition is the
  usual one: joint cells `≤ 2^{n-j}` gives savings `2^j` (`2^j · work ≤ 2^n`).  So the *counting* side of a
  multi-sorted fast-SAT is fine — no blow-up (analogue of entry 239 for the product structure).
* **Per-field `SYM∘AND` representation of composite gates is the blocked core (socket).**  To run the per-prime
  counting, each prime layer needs the *whole circuit* (with its `MOD_m` gates) as a `SYM∘AND` over `F_{pᵢ}`.  But a
  `MOD_m` gate `= ⋀ⱼ MOD_{pⱼ}` cannot be represented over a single `F_{pᵢ}` (the other factor `MOD_{pⱼ}`, `j ≠ i`, is
  not low-degree over `F_{pᵢ}` — Smolensky, entry 244), and downstream gates *mix* the per-field computations.  This
  cross-field mixing inside the circuit — not the final readout — is the actual `ACC⁰[composite]` barrier.

⚠️ **No crossing.**  The proved part is the budget composition (cells stay quasipoly).  Constructing the per-field
`SYM∘AND` representations of composite gates — the thing that would actually feed the counting — is the open,
separation-strength core, **not** built here.

## What is proved (clean axioms, no `sorry`)

* **`jointCells mcount := ∏ᵢ (mcountᵢ + 1)`** — the joint count-tuple space of a `k`-prime multi-sorted observer.
* **`jointCells_le_pow`** (PROVED) — `jointCells mcount ≤ (M+1)^k` when each `mcountᵢ ≤ M`: the cell budget composes
  multiplicatively and stays quasipoly for constant `k` (`Finset.prod_le_prod` + `prod_const`).
* **`multiSorted_savings`** (PROVED) — `j ≤ n → jointCells ≤ 2^{n-j} → 2^j · jointCells ≤ 2^n`: the joint cells meeting
  the budget give a `2^j` speedup (same savings form as the single-field fast-SAT, `…ACC0WilliamsFastSat`).

## The blocked core (named, not proved)

The per-prime counting needs each `MOD_m` gate realised as a low-degree `SYM∘AND` over a single `F_{pᵢ}`, which is
impossible (Smolensky, entry 244), and the circuit's downstream gates mix the per-field computations.  Constructing a
genuinely product-sorted `SYM∘AND` for an `ACC⁰[m]` circuit — where the cross-field mixing is handled — is the open
`ACC⁰[composite]` barrier (entry-238 `CarryRefinementCrossing`).  Not built here.

## Honest scope

This proves that the multi-sorted fast-SAT *cell budget* composes multiplicatively and stays quasipoly (the counting
side is fine), and that the joint cells meeting the budget give the usual savings.  It does **not** construct the
per-field `SYM∘AND` representation of composite gates — the cross-field mixing inside the circuit is the actual blocked
core, Smolensky-strength (entry 244).  So: the multi-sorted fast-SAT *would* work *if* the per-field representations
existed; building them is the open wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0MultiSortedFastSAT

/-- **The joint count-tuple space of a `k`-prime multi-sorted observer.**  Each prime layer has count-range `mcountᵢ +
1` (counts `0,…,mcountᵢ`); the joint observer's cells are the product. -/
def jointCells {k : ℕ} (mcount : Fin k → ℕ) : ℕ := ∏ i, (mcount i + 1)

/-- **The cell budget composes multiplicatively and stays quasipoly (PROVED).**  `jointCells mcount ≤ (M+1)^k` when
each per-prime count `mcountᵢ ≤ M`.  For `M` quasipoly and `k` (the number of prime factors) constant, `(M+1)^k` is
quasipoly — the counting side of a multi-sorted fast-SAT does not blow up. -/
theorem jointCells_le_pow {k : ℕ} (mcount : Fin k → ℕ) (M : ℕ) (h : ∀ i, mcount i ≤ M) :
    jointCells mcount ≤ (M + 1) ^ k := by
  unfold jointCells
  calc ∏ i, (mcount i + 1) ≤ ∏ _i : Fin k, (M + 1) := by
        apply Finset.prod_le_prod
        · intro i _; exact Nat.zero_le _
        · intro i _; exact Nat.add_le_add_right (h i) 1
    _ = (M + 1) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The multi-sorted savings condition (PROVED).**  If the joint cell-count `W` meets the budget `W ≤ 2^{n-j}` (with
`j ≤ n`), then `2^j · W ≤ 2^n` — a `2^j` speedup, the same savings form as the single-field fast-SAT
(`…ACC0WilliamsFastSat`).  So the multi-sorted counting, meeting the budget, gives the speedup. -/
theorem multiSorted_savings (W n j : ℕ) (hj : j ≤ n) (hW : W ≤ 2 ^ (n - j)) :
    2 ^ j * W ≤ 2 ^ n := by
  calc 2 ^ j * W ≤ 2 ^ j * 2 ^ (n - j) := Nat.mul_le_mul_left _ hW
    _ = 2 ^ n := by rw [← pow_add]; congr 1; omega

/-!
**The blocked core (named, not proved).**  The proved budget facts show the multi-sorted fast-SAT *counting* is fine:
the joint cells `∏ᵢ (mᵢ+1) ≤ (M+1)^k` stay quasipoly (`jointCells_le_pow`) and meeting the budget gives the savings
(`multiSorted_savings`).  What is *not* built: the per-prime `SYM∘AND` representations of the circuit's `MOD_m` gates
over each `F_{pᵢ}`.  A `MOD_m` gate cannot live over a single `F_{pᵢ}` (Smolensky, entry 244), and downstream gates
mix the per-field computations — the cross-field mixing inside the circuit is the open `ACC⁰[composite]` barrier
(entry-238 `CarryRefinementCrossing`).  So a multi-sorted fast-SAT *would* run if those representations existed; building
them is the unresolved wall, not constructed here.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0MultiSortedFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultiSortedFastSAT.jointCells_le_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultiSortedFastSAT.multiSorted_savings
