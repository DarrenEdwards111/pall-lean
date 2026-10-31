import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ExactDegreeNoGo

/-!
# Why the integer route exists: the symmetric count escapes the exact-degree no-go (PROVED)

`ACC0ExactDegreeNoGo` proves the **polynomial-method** route is impossible at the bottom clause: an
exact unbounded-fan-in `OR`/`AND` over `F₂` has degree **= fan-in `n`** (`or_exact_degree_full`,
`and_exact_degree_full`) — so its exact monomial count is exponential.  This file proves the precise
*escape* the integer/Beigel–Tarui route uses: the **same** `OR`/`AND` is **exactly symmetric** — a
function of the single integer count (Hamming weight) — and that count takes only `≤ n+1` values.

  `or_eq_symmetric` / `and_eq_symmetric` — `OR`/`AND` are exactly the count predicates `0 < hw` / `hw =
  n` (exact, no approximation).
  `or_cells_le` — the count takes `≤ n+1` values: the symmetric representation has `≤ n+1` cells.

So the contrast is sharp and proved on both sides: **polynomial** exact form ⇒ degree `n`
(exponential monomials, `or_exact_degree_full`); **integer/symmetric** exact form ⇒ `≤ n+1` cells
(`or_cells_le`).  This is exactly why the integer route sidesteps the no-go — it represents the gate by
its *count*, not by a polynomial.

## What is proved (clean axioms, no `sorry`)

* `or_eq_symmetric`, `and_eq_symmetric` — exact symmetric (count) form of unbounded `OR`/`AND`.
* `hw_le`, `or_cells_le` — the count is in `[0,n]`, so `≤ n+1` cells.

## Honest scope

This is the **bottom-gate** crux: the integer/symmetric route represents an unbounded `OR`/`AND`
*exactly* with `≤ n+1` cells, where the polynomial method provably needs degree `n`.  It explains why
the integer route exists; it does **not** discharge the **across-depth** front-half wall (ACC⁰ → exact
low-degree integer polynomial across unbounded depth, `MixedACCDepthReductionSocket`), which is the deep
Beigel–Tarui/Toda content.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SymmetricEscapesNoGo

variable {n : ℕ}

/-- The integer **count** (Hamming weight): the number of `true` bits. -/
def hw (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

/-- **Unbounded `OR` is exactly the count predicate `0 < hw` (proved).**  No approximation: `OR` accepts
iff the count of `true` bits is positive. -/
theorem or_eq_symmetric (x : Fin n → Bool) :
    decide (∃ i, x i = true) = decide (0 < hw x) := by
  rw [hw]; congr 1; simp [Finset.card_pos, Finset.filter_nonempty_iff]

/-- **Unbounded `AND` is exactly the count predicate `hw = n` (proved).** -/
theorem and_eq_symmetric (x : Fin n → Bool) :
    decide (∀ i, x i = true) = decide (hw x = n) := by
  rw [hw, decide_eq_decide]
  constructor
  · intro h
    have hf : Finset.univ.filter (fun i => x i = true) = Finset.univ :=
      Finset.filter_true_of_mem (fun i _ => h i)
    rw [hf, Finset.card_univ, Fintype.card_fin]
  · intro h i
    have huniv : Finset.univ.filter (fun i => x i = true) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [h]; exact (Fintype.card_fin n).symm)
    have hi : i ∈ Finset.univ.filter (fun i => x i = true) := by rw [huniv]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2

/-- **The count is in `[0, n]` (proved).** -/
theorem hw_le (x : Fin n → Bool) : hw x ≤ n := by
  rw [hw]
  calc (Finset.univ.filter (fun i => x i = true)).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- **The symmetric representation has `≤ n+1` cells (proved).**  The count `hw` takes at most `n+1`
distinct values, so the count-based (integer) representation of any unbounded gate over `n` bits has
`≤ n+1` cells — versus degree `n` (exponential monomials) for the exact polynomial form
(`ACC0ExactDegreeNoGo.or_exact_degree_full`). -/
theorem or_cells_le : (Finset.univ.image (hw (n := n))).card ≤ n + 1 := by
  calc (Finset.univ.image (hw (n := n))).card
      ≤ (Finset.range (n + 1)).card := by
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_image] at hs
        obtain ⟨x, _, rfl⟩ := hs
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (hw_le x)
    _ = n + 1 := Finset.card_range _

/-!
**Symmetric escape proved.**  The unbounded `OR`/`AND` that the polynomial method needs degree `n` for
is *exactly* a function of the integer count, with `≤ n+1` cells — the precise reason the
integer/Beigel–Tarui route sidesteps the exact-degree no-go.  The across-depth front-half wall is
untouched.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SymmetricEscapesNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymmetricEscapesNoGo.or_eq_symmetric
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymmetricEscapesNoGo.or_cells_le
-- contrast: the polynomial-method no-go (degree = fan-in) this escapes
#check @PallLean.Paper93.DeepMath.PathB.ACC0ExactDegreeNoGo.or_exact_degree_full
