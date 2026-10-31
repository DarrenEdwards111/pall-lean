import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyPoly

/-!
# Beigel–Tarui, rung 3: the Razborov–Smolensky subset-sum probability

Rung 2 (`…RazborovSmolenskyPoly`) built the RS approximator and proved it correct **whenever a subset "fires"** (has
nonzero sum).  This file proves the counting fact that makes firing likely: **for any nonzero input, at least half the
subsets fire.**  With subsets drawn uniformly (measure `1/2ⁿ`), this is exactly `Pr[a subset fires] ≥ 1/2` — the
probability estimate at the heart of Razborov–Smolensky, and the reason `t` independent trials fail with probability
`≤ 2^{-t}`.

The argument is a **pairing involution**: fix a coordinate `i₀` with `x_{i₀} ≠ 0`, and pair each subset `S` with
`S △ {i₀}` (toggle `i₀`).  The two subset-sums differ by `x_{i₀} ≠ 0`, so at most one of the pair has sum `0`; hence the
zero-sum subsets are at most half.

  `toggle` / `toggle_toggle` — **PROVED**: toggling `i₀` in/out of a subset is an involution.
  `ssum_toggle_ne` — **PROVED**: toggling `i₀` (with `x_{i₀} ≠ 0`) changes the subset sum — the two paired sums differ.
  `subset_sum_zero_card_le` — **PROVED, the counting core**: given a coordinate with `x_{i₀} ≠ 0`, at most half the
        subsets have zero sum: `2 · #{S : ∑_S x = 0} ≤ 2ⁿ`.
  `subset_sum_nonzero_card_ge` — **PROVED, the probability**: for any nonzero Boolean input, at least half the subsets
        fire: `2ⁿ ≤ 2 · #{S : ∑_S x ≠ 0}` — i.e. `Pr[fire] ≥ 1/2`.

## Honest scope

This is the exact `Pr[fire] ≥ 1/2` counting.  Combined with rung 2's `orApprox_fires`, it gives the RS approximator's
correctness probability on any *fixed* nonzero input.  What remains for Beigel–Tarui: (i) **amplification** — `t`
independent subset-families reduce the failure probability to `≤ 2^{-t}` (a union/product over trials), and (ii) the
**union bound + composition** — a single polynomial correct on all `2ⁿ` inputs simultaneously (degree `t·(p-1)` with
`t = O(n)`), then composing the low-degree `OR`/`AND` approximators through a depth-`d` circuit to degree `polylog` and
folding into one `SYM∘AND` with `m` quasipolynomial.  Those are the remaining Beigel–Tarui content.  This file supplies
the `1/2` bound the amplification runs on.  Nothing here is the Beigel–Tarui reduction, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

variable {p n : ℕ} [Fact p.Prime]

open scoped Classical

/-- Toggle coordinate `i₀` in or out of a subset. -/
def toggle (i₀ : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  if i₀ ∈ S then S.erase i₀ else insert i₀ S

/-- **Toggling is an involution (proved)**. -/
theorem toggle_toggle (i₀ : Fin n) (S : Finset (Fin n)) : toggle i₀ (toggle i₀ S) = S := by
  unfold toggle
  by_cases h : i₀ ∈ S
  · rw [if_pos h, if_neg (Finset.notMem_erase i₀ S), Finset.insert_erase h]
  · rw [if_neg h, if_pos (Finset.mem_insert_self i₀ S), Finset.erase_insert h]

/-- **Toggling changes the subset sum (proved)**: if `x_{i₀} ≠ 0`, then `S` and its toggle have different sums (they
differ by `x_{i₀}`). -/
theorem ssum_toggle_ne (i₀ : Fin n) (S : Finset (Fin n)) (x : Fin n → Bool)
    (hne : xf (p := p) x i₀ ≠ 0) :
    ssum (p := p) (toggle i₀ S) x ≠ ssum (p := p) S x := by
  unfold toggle ssum
  by_cases h : i₀ ∈ S
  · rw [if_pos h]
    intro heq
    have key := Finset.add_sum_erase S (xf (p := p) x) h
    rw [heq] at key
    exact hne (add_right_cancel (key.trans (zero_add _).symm))
  · rw [if_neg h, Finset.sum_insert h]
    intro heq
    exact hne (add_right_cancel (heq.trans (zero_add _).symm))

/-- **The counting core (proved)**: given a coordinate `i₀` with `x_{i₀} ≠ 0`, at most half the subsets have zero sum —
`2 · #{S : ∑_S x = 0} ≤ 2ⁿ`.  Proof: `toggle i₀` injects the zero-sum subsets into the nonzero-sum ones (their sums
differ by `x_{i₀}`), so the zero-sum set is no larger than its complement. -/
theorem subset_sum_zero_card_le (x : Fin n → Bool) (i₀ : Fin n) (hne : xf (p := p) x i₀ ≠ 0) :
    2 * (Finset.univ.filter (fun S : Finset (Fin n) => ssum (p := p) S x = 0)).card ≤ 2 ^ n := by
  set A := Finset.univ.filter (fun S : Finset (Fin n) => ssum (p := p) S x = 0) with hA
  have hmap : ∀ S ∈ A, toggle i₀ S ∈ Aᶜ := by
    intro S hS
    rw [hA, Finset.mem_filter] at hS
    rw [Finset.mem_compl, hA, Finset.mem_filter, not_and]
    intro _
    rw [← hS.2]
    exact ssum_toggle_ne i₀ S x hne
  have hinj : Set.InjOn (toggle i₀) A := by
    intro S _ T _ hST
    have := congrArg (toggle i₀) hST
    rwa [toggle_toggle, toggle_toggle] at this
  have hcard : A.card ≤ Aᶜ.card := Finset.card_le_card_of_injOn (toggle i₀) hmap hinj
  have hsum : A.card + Aᶜ.card = 2 ^ n := by
    rw [Finset.card_add_card_compl, Fintype.card_finset, Fintype.card_fin]
  omega

/-- A `true` Boolean coordinate embeds to a nonzero `F_p` value. -/
theorem xf_ne_zero {x : Fin n → Bool} {i : Fin n} (h : x i = true) : xf (p := p) x i ≠ 0 := by
  simp [xf, h]

/-- **The probability (proved): at least half the subsets fire.**  For any nonzero Boolean input `x` (some `x_i = true`),
`2ⁿ ≤ 2 · #{S : ∑_S x ≠ 0}` — with uniform subsets this is `Pr[a subset fires] ≥ 1/2`, the RS probability estimate. -/
theorem subset_sum_nonzero_card_ge (x : Fin n → Bool) (hx : ∃ i, x i = true) :
    2 ^ n ≤ 2 * (Finset.univ.filter (fun S : Finset (Fin n) => ssum (p := p) S x ≠ 0)).card := by
  obtain ⟨i₀, hi⟩ := hx
  have hzero := subset_sum_zero_card_le (p := p) x i₀ (xf_ne_zero (p := p) hi)
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Finset (Fin n)))) (fun S => ssum (p := p) S x = 0)
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at hpart
  simp only [ne_eq] at *
  omega

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.subset_sum_zero_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.subset_sum_nonzero_card_ge
