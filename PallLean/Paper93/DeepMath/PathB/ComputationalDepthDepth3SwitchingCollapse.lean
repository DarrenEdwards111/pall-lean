import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseBothRoutes
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullPathDepth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingBinomialRegime

/-!
# From the full-path switching count to the collapse seed — branch only

`fullpath_switching_count` bounds the deep-tree (bad) restrictions: `|Bad| ≤ |Short|·(2w)^s`.  Feeding
it into the generic counting-collapse `SwitchingCounting.exists_good_of_count` gives the **collapse
seed**: in the Håstad regime (`|Short|·(2w)^s < 2^n`, the count below the total), some restriction is
**not** bad — i.e. its canonical tree is shallow.  This is the existence step the depth-3 collapse
consumes.

* `exists_good_fullpath` — a good (non-deep) restriction exists once the full-path count is sub-total.

Clean, no `sorry`.  `Depth3CollapseModel.collapse` (the structural collapse interface) and P≠NP remain
untouched — this is the count→existence bridge, one ingredient.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The collapse seed from the full-path switching count.**  If the bad (deep-path) restrictions have
their leaves in `Short`, with full paths of length `s` and positions `< w`, and the count
`|Short|·(2w)^s` is below the total number of restrictions, then some restriction is **not** bad. -/
theorem exists_good_fullpath (cs : List (Clause n)) (w s F : ℕ) [NeZero w]
    {Bad Short : Finset (SwitchingCounting.Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hlen : ∀ ρ ∈ Bad, (deepestFullSeq cs F ρ).length = s)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ deepestFullSeq cs F ρ, p.1 < w)
    (hlt : Short.card * (2 * w) ^ s
      < (Finset.univ : Finset (SwitchingCounting.Restriction n)).card) :
    ∃ ρ : SwitchingCounting.Restriction n, ρ ∉ Bad :=
  SwitchingCounting.exists_good_of_count
    (fullpath_switching_count cs w s F hmem hnf hleaf hlen hpos) hlt

/-- **The switching count as a genuine max-depth count.**  At most `|Short|·(2w)^s` restrictions have
canonical-tree depth *exactly* `s` — using `deepestFullSeq_length_eq_depth` to discharge the path-length
hypothesis from the depth.  This is the form the depth-3 collapse consumes (the Side-A label could not
bound the true depth; the full path does). -/
theorem fullpath_depth_count (cs : List (Clause n)) (w s F : ℕ) [NeZero w]
    {Short : Finset (SwitchingCounting.Restriction n)}
    (hmem : ∀ ρ, (canonicalDT cs F ρ).depth = s → deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ, (canonicalDT cs F ρ).depth = s → ∀ U ∈ cs,
      SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ ρ, (canonicalDT cs F ρ).depth = s →
      SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ, (canonicalDT cs F ρ).depth = s → ∀ p ∈ deepestFullSeq cs F ρ, p.1 < w) :
    (Finset.univ.filter (fun ρ => (canonicalDT cs F ρ).depth = s)).card
      ≤ Short.card * (2 * w) ^ s := by
  refine fullpath_switching_count cs w s F ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ; exact hmem ρ (Finset.mem_filter.mp hρ).2
  · intro ρ hρ; exact hnf ρ (Finset.mem_filter.mp hρ).2
  · intro ρ hρ; exact hleaf ρ (Finset.mem_filter.mp hρ).2
  · intro ρ hρ; rw [deepestFullSeq_length_eq_depth]; exact (Finset.mem_filter.mp hρ).2
  · intro ρ hρ; exact hpos ρ (Finset.mem_filter.mp hρ).2

/-- **The deep-fraction bound (regime arithmetic).**  In the binomial regime `4wK + K ≤ n+1` with
`s ≤ K`, if the depth-`s` leaves land in the `(K-s)`-star shell (`|Short| ≤ 2^(n-K+s)·C(n,K-s)`), then
the depth-`s` restrictions number at most the `K`-star layer `2^(n-K)·C(n,K)` — the full-path max-depth
count combined with `short_family_ratio`.  So the deep set does not exceed the layer it is restricted
within: the switching savings beat the `(2w)^s` blow-up. -/
theorem fullpath_deep_fraction (cs : List (Clause n)) (w s F K : ℕ) [NeZero w]
    (hsK : s ≤ K) (hreg : 4 * w * K + K ≤ n + 1)
    {Short : Finset (SwitchingCounting.Restriction n)}
    (hShort : Short.card ≤ 2 ^ (n - K + s) * n.choose (K - s))
    (hmem : ∀ ρ, (canonicalDT cs F ρ).depth = s → deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ, (canonicalDT cs F ρ).depth = s → ∀ U ∈ cs,
      SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ ρ, (canonicalDT cs F ρ).depth = s →
      SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ, (canonicalDT cs F ρ).depth = s → ∀ p ∈ deepestFullSeq cs F ρ, p.1 < w) :
    (Finset.univ.filter (fun ρ => (canonicalDT cs F ρ).depth = s)).card
      ≤ 2 ^ (n - K) * n.choose K :=
  calc (Finset.univ.filter (fun ρ => (canonicalDT cs F ρ).depth = s)).card
      ≤ Short.card * (2 * w) ^ s := fullpath_depth_count cs w s F hmem hnf hleaf hpos
    _ ≤ 2 ^ (n - K + s) * n.choose (K - s) * (2 * w) ^ s := by gcongr
    _ ≤ 2 ^ (n - K) * n.choose K := SwitchingCounting.short_family_ratio hsK hreg

/-- **A restriction avoiding depth `s` exists, in the binomial regime.**  Combining the deep-fraction
bound with the counting-collapse: once the `K`-star layer is strictly below the total number of
restrictions, not every restriction has canonical-tree depth `s` — some `ρ` has `depth ≠ s`.  (The
strict `2^(n-K)·C(n,K) < 3^n` is the regime's analytic input; the shell bound `hShort` and the
`(K-s)`-star structure are the descent-side inputs.) -/
theorem exists_shallow_fullpath (cs : List (Clause n)) (w s F K : ℕ) [NeZero w]
    (hsK : s ≤ K) (hreg : 4 * w * K + K ≤ n + 1)
    {Short : Finset (SwitchingCounting.Restriction n)}
    (hShort : Short.card ≤ 2 ^ (n - K + s) * n.choose (K - s))
    (hmem : ∀ ρ, (canonicalDT cs F ρ).depth = s → deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ, (canonicalDT cs F ρ).depth = s → ∀ U ∈ cs,
      SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ ρ, (canonicalDT cs F ρ).depth = s →
      SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ, (canonicalDT cs F ρ).depth = s → ∀ p ∈ deepestFullSeq cs F ρ, p.1 < w)
    (hlt : 2 ^ (n - K) * n.choose K
      < (Finset.univ : Finset (SwitchingCounting.Restriction n)).card) :
    ∃ ρ : SwitchingCounting.Restriction n, (canonicalDT cs F ρ).depth ≠ s := by
  obtain ⟨ρ, hρ⟩ := SwitchingCounting.exists_good_of_count
    (fullpath_deep_fraction cs w s F K hsK hreg hShort hmem hnf hleaf hpos) hlt
  exact ⟨ρ, fun h => hρ (Finset.mem_filter.mpr ⟨Finset.mem_univ ρ, h⟩)⟩

/-- **The `s`-sum: a shallow restriction exists.**  If the canonical tree depth is bounded by `D`, each
depth-`s` count is bounded by `M s`, and the total `∑_{s=T}^{D} M s` is below the number of
restrictions, then some restriction has depth `< T`.  (`{depth ≥ T}` is the disjoint union of the
depth-`s` fibers for `s ∈ [T,D]`, so its card is `∑` of the fiber cards; below total ⟹ the complement,
the shallow restrictions, is nonempty.) -/
theorem exists_depth_lt_of_sum_bound {cs : List (Clause n)} {F T D : ℕ} {M : ℕ → ℕ}
    (hdepth : ∀ ρ, (canonicalDT cs F ρ).depth ≤ D)
    (hbound : ∀ s, T ≤ s →
      (Finset.univ.filter (fun ρ => (canonicalDT cs F ρ).depth = s)).card ≤ M s)
    (hsum : ∑ s ∈ Finset.Icc T D, M s
      < (Finset.univ : Finset (SwitchingCounting.Restriction n)).card) :
    ∃ ρ : SwitchingCounting.Restriction n, (canonicalDT cs F ρ).depth < T := by
  classical
  set deep := Finset.univ.filter (fun ρ => T ≤ (canonicalDT cs F ρ).depth) with hdeep
  have hfib : deep.card
      = ∑ s ∈ Finset.Icc T D,
          (deep.filter (fun ρ => (canonicalDT cs F ρ).depth = s)).card :=
    Finset.card_eq_sum_card_fiberwise (fun ρ hρ =>
      Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hρ).2, hdepth ρ⟩))
  have hcard_le : deep.card ≤ ∑ s ∈ Finset.Icc T D, M s := by
    rw [hfib]
    refine Finset.sum_le_sum (fun s hs => ?_)
    have hTs : T ≤ s := (Finset.mem_Icc.mp hs).1
    have heq : deep.filter (fun ρ => (canonicalDT cs F ρ).depth = s)
        = Finset.univ.filter (fun ρ => (canonicalDT cs F ρ).depth = s) := by
      rw [hdeep, Finset.filter_filter]
      refine Finset.filter_congr (fun ρ _ => ?_)
      simp only [eq_iff_iff, and_iff_right_iff_imp]
      exact fun h => h ▸ hTs
    rw [heq]; exact hbound s hTs
  have hsc : deepᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl]
    have hlt2 : deep.card < Fintype.card (SwitchingCounting.Restriction n) := by
      rw [← Finset.card_univ]; exact lt_of_le_of_lt hcard_le hsum
    exact Nat.sub_pos_of_lt hlt2
  obtain ⟨ρ, hρ⟩ := hsc
  refine ⟨ρ, ?_⟩
  rw [Finset.mem_compl, hdeep, Finset.mem_filter, not_and] at hρ
  exact Nat.not_le.mp (hρ (Finset.mem_univ ρ))

/-- **The `s`-sum with the depth bound discharged.**  Since `(canonicalDT cs F ρ).depth ≤ F`
(`canonicalDT_depth_le`), the depth bound `D` is just the fuel `F`: a per-depth count bound whose sum
over `[T,F]` is below the number of restrictions yields a restriction of depth `< T`. -/
theorem exists_depth_lt_of_sum_fuel {cs : List (Clause n)} {F T : ℕ} {M : ℕ → ℕ}
    (hbound : ∀ s, T ≤ s →
      (Finset.univ.filter (fun ρ => (canonicalDT cs F ρ).depth = s)).card ≤ M s)
    (hsum : ∑ s ∈ Finset.Icc T F, M s
      < (Finset.univ : Finset (SwitchingCounting.Restriction n)).card) :
    ∃ ρ : SwitchingCounting.Restriction n, (canonicalDT cs F ρ).depth < T :=
  exists_depth_lt_of_sum_bound (fun ρ => canonicalDT_depth_le cs F ρ) hbound hsum

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_good_fullpath
