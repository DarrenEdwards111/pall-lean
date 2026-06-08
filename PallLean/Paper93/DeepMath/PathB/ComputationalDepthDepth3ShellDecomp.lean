import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarTail

/-!
# Tight switching, step 7: the shell decomposition (branch `razborov-recoverRho-wip`)

The combinatorial partition behind the shell sum: a weighted sum over `{a : s ≤ g a}` (the "deep" set,
`g = canonical-tree depth`) splits as a sum over depth-shells `{a : g a = K}` for `K ∈ [s, N]`, when `g`
is bounded by `N`.  This is the partition the tight switching count is summed across: each shell `{depth =
K}` is bounded by `descent_switching_le_tight` (brick 44), and `geom_shell_tail_le` (brick 45) sums them.

* `sum_filter_ge_eq_sum_shells` — `∑_{g a ≥ s} f a = ∑_{K ∈ Icc s N} ∑_{g a = K} f a` (for `g ≤ N`).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

/-- **Shell decomposition.**  A sum over the "deep" set `{g a ≥ s}` is the sum, over depth-shells
`K ∈ [s, N]`, of the sums over `{g a = K}` — when `g` is bounded by `N`. -/
theorem sum_filter_ge_eq_sum_shells {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → ℕ) (f : α → ℚ) (s N : ℕ) (hN : ∀ a, g a ≤ N) :
    ∑ a ∈ Finset.univ.filter (fun a => s ≤ g a), f a
      = ∑ K ∈ Finset.Icc s N, ∑ a ∈ Finset.univ.filter (fun a => g a = K), f a := by
  have hbiU : Finset.univ.filter (fun a => s ≤ g a)
      = (Finset.Icc s N).biUnion (fun K => Finset.univ.filter (fun a => g a = K)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_Icc]
    constructor
    · intro h; exact ⟨g a, ⟨h, hN a⟩, rfl⟩
    · rintro ⟨K, ⟨hsK, _⟩, hgK⟩; omega
  rw [hbiU, Finset.sum_biUnion]
  intro K1 _ K2 _ hne
  refine Finset.disjoint_left.mpr (fun a hK1a hK2a => hne ?_)
  exact (Finset.mem_filter.mp hK1a).2.symm.trans (Finset.mem_filter.mp hK2a).2

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.sum_filter_ge_eq_sum_shells
