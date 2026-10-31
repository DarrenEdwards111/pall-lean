import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BlockOverlapCount

/-!
# Treewidth count — separator conditioning: the bounded-treewidth DP core, generalizing block factorization

Entry 252 made the tractable boundary of `CrossFieldCount` the gate–variable incidence graph's *block decomposition*
(bounded local overlap).  This file pushes the boundary outward to **bounded treewidth** via its DP core: **separator
conditioning**.  When a separator set of variables `S` splits the gates into two parts `A`, `B` that share only `S`, the
count factors as a sum over separator-assignments of the product of the two conditional counts:

> `#{x : Pₐ ∧ P_b} = ∑_{s : S} #{a : Pₐ(s, a)} · #{b : P_b(s, b)}`.

This is the variable-elimination / junction-tree recurrence.  Iterated over a tree decomposition of width `≤ w`, each
step is a `|S| ≤ 2^w`-fold sum of products of recursively-computed sub-counts — the FPT-in-treewidth dynamic program.
Block-diagonal (entry 252) is the **empty-separator** special case (`separator_factor_indep`: no shared variables ⇒
product).

⚠️ **No crossing.**  The separator-conditioning recurrence and the no-separator product are proved.  The full iterated
tree-decomposition DP (recursion over a junction tree) and, crucially, the **unbounded-treewidth / expander-incidence**
case — where no bounded separator exists and the `mod-q` fire-count is the genuine cross-field mixing (Smolensky) — are
*not* resolved here.  The latter is the open `ACC⁰[composite]` core.

## What is proved (clean axioms, no `sorry`)

* **`separator_factor`** (PROVED) — the bounded-treewidth DP core: for a separator `S` splitting the gates into parts
  `A`, `B` (predicates `Pₐ : S → A → Bool`, `P_b : S → B → Bool`, sharing only `S`),
  `#{x : S×A×B | Pₐ x.1 x.2.1 ∧ P_b x.1 x.2.2} = ∑ s, #{a : Pₐ s a} · #{b : P_b s b}`.  Conditioning on the separator
  makes the two sides independent.
* **`separator_factor_indep`** (PROVED) — the empty-separator special case: with no shared variables,
  `#{x : A×B | Pₐ x.1 ∧ P_b x.2} = #{a : Pₐ a} · #{b : P_b b}` — the block/disjoint product (entries 251/252) recovered.

## The treewidth recursion and the open case (named, not proved)

Iterating `separator_factor` over a tree decomposition of width `≤ w`: each elimination conditions on a separator of
size `≤ 2^w` (a `≤ 2^w`-fold sum) and recurses on the two sides — the FPT-in-treewidth DP, poly-time for bounded `w`.
The disjoint case (251) is treewidth 0; block-diagonal (252) is bounded treewidth with disconnected bags.  The open
case is **unbounded treewidth** — a connected / expander-like incidence graph with no small separators — where the
count does not factor and the `mod-q` fire-count is the cross-field mixing (Smolensky, entries 244/249/250); the open
`ACC⁰[composite]` core (entry-238 `CarryRefinementCrossing`).  Not resolved here.

## Honest scope

This proves the separator-conditioning recurrence (the bounded-treewidth DP core) and its empty-separator product
specialisation, extending the proved tractable fragment from block-diagonal toward bounded treewidth.  It does **not**
formalize the full iterated junction-tree DP, and it does **not** resolve the unbounded-treewidth / expander case, which
is the exposed ACC wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0TreewidthCount

/-- **Separator conditioning — the bounded-treewidth DP core (PROVED).**  A separator `S` splits the gates into parts
`A`, `B` sharing only `S` (predicates `PA : S → A → Bool` for the `A`-side, `PB : S → B → Bool` for the `B`-side).
Conditioning on the separator value makes the two sides independent, so the count factors:
`#{x : S×A×B | PA x.1 x.2.1 ∧ PB x.1 x.2.2} = ∑ s, #{a : PA s a} · #{b : PB s b}`.  This is the
variable-elimination / junction-tree recurrence. -/
theorem separator_factor (S A B : Type) [Fintype S] [Fintype A] [Fintype B]
    (PA : S → A → Bool) (PB : S → B → Bool) :
    (Finset.univ.filter (fun x : S × A × B => PA x.1 x.2.1 ∧ PB x.1 x.2.2)).card
      = ∑ s : S, (Finset.univ.filter (fun a => PA s a)).card
                  * (Finset.univ.filter (fun b => PB s b)).card := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : PA s a <;> by_cases hb : PB s b <;> simp [ha, hb]

/-- **Empty separator → product (PROVED).**  With no shared variables (no separator), the count is the product of the
two side counts: `#{x : A×B | PA x.1 ∧ PB x.2} = #{a : PA a} · #{b : PB b}` — the block/disjoint product of entries
251/252, recovered as the treewidth-0 special case of `separator_factor`. -/
theorem separator_factor_indep (A B : Type) [Fintype A] [Fintype B]
    (PA : A → Bool) (PB : B → Bool) :
    (Finset.univ.filter (fun x : A × B => PA x.1 ∧ PB x.2)).card
      = (Finset.univ.filter (fun a => PA a)).card * (Finset.univ.filter (fun b => PB b)).card := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : PA a <;> by_cases hb : PB b <;> simp [ha, hb]

/-!
**The treewidth recursion (named, not proved).**  Iterating `separator_factor` over a tree decomposition of width `≤ w`
gives the FPT-in-treewidth DP: each elimination conditions on a separator of size `≤ 2^w` and recurses on the two
sides, poly-time for bounded `w`.  Disjoint (251) = treewidth 0; block-diagonal (252) = bounded treewidth, disconnected
bags.  The open case is **unbounded treewidth** (connected / expander incidence, no small separators), where the count
does not factor and the `mod-q` fire-count is the cross-field mixing (Smolensky, entries 244/249/250) — the open
`ACC⁰[composite]` core (entry-238 `CarryRefinementCrossing`).
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TreewidthCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TreewidthCount.separator_factor
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TreewidthCount.separator_factor_indep
