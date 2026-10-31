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

/-! ## The geometric tail-sum estimate -/

/-- **Geometric range sum.**  If `M` at least halves each step (`2·M(s+1) ≤ M s`), the sum of any run
`M T, M(T+1), …` is at most twice the first term. -/
theorem geom_range_sum {M : ℕ → ℕ} (hdec : ∀ s, 2 * M (s + 1) ≤ M s) :
    ∀ (m T : ℕ), ∑ i ∈ Finset.range m, M (T + i) ≤ 2 * M T := by
  intro m
  induction m with
  | zero => intro T; simp
  | succ m ih =>
    intro T
    rw [Finset.sum_range_succ']
    have h1 : ∑ i ∈ Finset.range m, M (T + (i + 1)) ≤ 2 * M (T + 1) := by
      have hih := ih (T + 1)
      have hcongr : ∀ i ∈ Finset.range m, M (T + (i + 1)) = M (T + 1 + i) := by
        intro i _; congr 1; omega
      rw [Finset.sum_congr rfl hcongr]; exact hih
    have hd := hdec T
    simp only [Nat.add_zero]
    omega

/-- **The geometric tail-sum bound (`Icc` form).**  Under halving decay, `∑_{s=T}^{D} M s ≤ 2·M T`. -/
theorem geom_tail_sum_Icc {M : ℕ → ℕ} (hdec : ∀ s, 2 * M (s + 1) ≤ M s) (T D : ℕ) :
    ∑ s ∈ Finset.Icc T D, M s ≤ 2 * M T := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  exact geom_range_sum hdec _ T

/-- **A shallow restriction exists from a decaying per-depth bound.**  If the depth-`s` counts are
bounded by a sequence `M` that halves each step, and twice the threshold term `2·M T` is below the
number of restrictions, then some restriction has depth `< T`.  This is the binomial/geometric
tail-sum closing of the collapse: the deep set is geometrically dominated, so it does not fill the
space. -/
theorem exists_depth_lt_of_decay {cs : List (Clause n)} {F T : ℕ} {M : ℕ → ℕ}
    (hdec : ∀ s, 2 * M (s + 1) ≤ M s)
    (hbound : ∀ s, T ≤ s →
      (Finset.univ.filter (fun ρ => (canonicalDT cs F ρ).depth = s)).card ≤ M s)
    (hbase : 2 * M T < (Finset.univ : Finset (SwitchingCounting.Restriction n)).card) :
    ∃ ρ : SwitchingCounting.Restriction n, (canonicalDT cs F ρ).depth < T :=
  exists_depth_lt_of_sum_fuel hbound (lt_of_le_of_lt (geom_tail_sum_Icc hdec T F) hbase)

/-! ### Range-local geometric tail sum

The actual switching count `M_s` only halves while `s < K` (its form grows again for `s ≥ K`).  We
therefore need the decay hypothesis only on the pairs *inside* the summed range, never beyond it.  The
minimal hypothesis is `2·M(s+1) ≤ M s` for `s + 1 < T + m` (equivalently `s < D` in the `Icc` form):
the bound `∑ M ≤ 2·M T` only ever compares consecutive summands. -/

/-- **Range-local geometric range sum.**  Decay is required only on the consecutive pairs that occur
in the sum (`s + 1 < T + m`), not beyond it. -/
theorem geom_range_sum_local {M : ℕ → ℕ} :
    ∀ (m T : ℕ), (∀ s, T ≤ s → s + 1 < T + m → 2 * M (s + 1) ≤ M s) →
      ∑ i ∈ Finset.range m, M (T + i) ≤ 2 * M T := by
  intro m
  induction m with
  | zero => intro T _; simp
  | succ m ih =>
    intro T hdec
    rw [Finset.sum_range_succ']
    have h1 : ∑ i ∈ Finset.range m, M (T + (i + 1)) ≤ 2 * M (T + 1) := by
      have hih := ih (T + 1) (fun s hs1 hs2 => hdec s (by omega) (by omega))
      have hcongr : ∀ i ∈ Finset.range m, M (T + (i + 1)) = M (T + 1 + i) := by
        intro i _; congr 1; omega
      rw [Finset.sum_congr rfl hcongr]; exact hih
    simp only [Nat.add_zero]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp only [Finset.range_zero, Finset.sum_empty, Nat.zero_add] at h1 ⊢; omega
    · have hd := hdec T (le_refl T) (by omega)
      omega

/-- **Range-local geometric tail-sum bound (`Icc` form).**  Decay is required only for `s < D`. -/
theorem geom_tail_sum_Icc_local {M : ℕ → ℕ} (T D : ℕ)
    (hdec : ∀ s, T ≤ s → s < D → 2 * M (s + 1) ≤ M s) :
    ∑ s ∈ Finset.Icc T D, M s ≤ 2 * M T := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  apply geom_range_sum_local
  intro s hs1 hs2
  exact hdec s hs1 (by omega)

/-- **Shallow restriction from a range-local decay.**  Like `exists_depth_lt_of_decay`, but the decay
of the per-depth bound `M` is required only on the meaningful range `s < D` (`D` the depth bound). -/
theorem exists_depth_lt_of_decay_local {cs : List (Clause n)} {D T : ℕ} {M : ℕ → ℕ}
    (hdepth : ∀ ρ, (canonicalDT cs D ρ).depth ≤ D)
    (hdec : ∀ s, T ≤ s → s < D → 2 * M (s + 1) ≤ M s)
    (hbound : ∀ s, T ≤ s →
      (Finset.univ.filter (fun ρ => (canonicalDT cs D ρ).depth = s)).card ≤ M s)
    (hbase : 2 * M T < (Finset.univ : Finset (SwitchingCounting.Restriction n)).card) :
    ∃ ρ : SwitchingCounting.Restriction n, (canonicalDT cs D ρ).depth < T :=
  exists_depth_lt_of_sum_bound hdepth hbound
    (lt_of_le_of_lt (geom_tail_sum_Icc_local T D hdec) hbase)

/-- **The collapse closed modulo the two structural facts.**  Under the doubled-slack regime
`(8w)·K + K ≤ n+1`, if (i) every canonical tree (with fuel `K`) has depth `≤ K`, (ii) the depth-`s`
count is bounded by the switching count `2^(n-K+s)·C(n,K-s)·(2w)^s`, and (iii) twice the threshold
term is below the number of restrictions, then **a restriction with canonical depth `< T` exists**.

The decay is supplied automatically by `count_decay_step` (the strict binomial inequality), and the
depth bound `depth ≤ K` is automatic from `canonicalDT_depth_le` (fuel `= K`).  So the *entire analytic
spine* — geometric tail sum + binomial decay — is discharged here.  What remains is exactly the single
structural input: the `(K-s)`-shell count bound `hbound`. -/
theorem exists_shallow_of_count {cs : List (Clause n)} {w K T : ℕ}
    (hreg : (8 * w) * K + K ≤ n + 1)
    (hbound : ∀ s, T ≤ s →
      (Finset.univ.filter (fun ρ => (canonicalDT cs K ρ).depth = s)).card
        ≤ 2 ^ (n - K + s) * n.choose (K - s) * (2 * w) ^ s)
    (hbase : 2 * (2 ^ (n - K + T) * n.choose (K - T) * (2 * w) ^ T)
      < (Finset.univ : Finset (SwitchingCounting.Restriction n)).card) :
    ∃ ρ : SwitchingCounting.Restriction n, (canonicalDT cs K ρ).depth < T :=
  exists_depth_lt_of_decay_local (M := fun s => 2 ^ (n - K + s) * n.choose (K - s) * (2 * w) ^ s)
    (fun ρ => canonicalDT_depth_le cs K ρ)
    (fun s _ hsK => SwitchingCounting.count_decay_step hsK hreg)
    hbound hbase

/-! ### Family-relative existence — over the `K`-star family, not all of `univ`

The switching argument lives in a fixed `K`-star *family*, not over all `3^n` restrictions: the leaf
of a `K`-star depth-`s` branch has `K-s` stars, so the count compares the `(K-s)`-shell to the `K`-shell
(`short_family_ratio`).  We re-base the existence chain over an arbitrary `Fam : Finset (Restriction n)`
and compare against `Fam.card`. -/

/-- **`s`-sum over a family.**  Like `exists_depth_lt_of_sum_bound`, but quantified over an arbitrary
`Fam`: `{ρ ∈ Fam : depth ≥ T}` is the disjoint union of its depth-`s` fibers, so its card is `∑` of
the fiber cards; below `Fam.card` ⟹ the shallow part `Fam \ deep` is nonempty. -/
theorem exists_depth_lt_in_of_sum_bound {cs : List (Clause n)} {F T D : ℕ} {M : ℕ → ℕ}
    (Fam : Finset (SwitchingCounting.Restriction n))
    (hdepth : ∀ ρ ∈ Fam, (canonicalDT cs F ρ).depth ≤ D)
    (hbound : ∀ s, T ≤ s →
      (Fam.filter (fun ρ => (canonicalDT cs F ρ).depth = s)).card ≤ M s)
    (hsum : ∑ s ∈ Finset.Icc T D, M s < Fam.card) :
    ∃ ρ ∈ Fam, (canonicalDT cs F ρ).depth < T := by
  classical
  set deep := Fam.filter (fun ρ => T ≤ (canonicalDT cs F ρ).depth) with hdeep
  have hfib : deep.card
      = ∑ s ∈ Finset.Icc T D,
          (deep.filter (fun ρ => (canonicalDT cs F ρ).depth = s)).card :=
    Finset.card_eq_sum_card_fiberwise (fun ρ hρ =>
      Finset.mem_coe.mpr (Finset.mem_Icc.mpr
        ⟨(Finset.mem_filter.mp hρ).2, hdepth ρ (Finset.mem_filter.mp hρ).1⟩))
  have hcard_le : deep.card ≤ ∑ s ∈ Finset.Icc T D, M s := by
    rw [hfib]
    refine Finset.sum_le_sum (fun s hs => ?_)
    have hTs : T ≤ s := (Finset.mem_Icc.mp hs).1
    have heq : deep.filter (fun ρ => (canonicalDT cs F ρ).depth = s)
        = Fam.filter (fun ρ => (canonicalDT cs F ρ).depth = s) := by
      rw [hdeep, Finset.filter_filter]
      refine Finset.filter_congr (fun ρ _ => ?_)
      simp only [eq_iff_iff, and_iff_right_iff_imp]
      exact fun h => h ▸ hTs
    rw [heq]; exact hbound s hTs
  have hdeepsub : deep ⊆ Fam := Finset.filter_subset _ _
  have hlt2 : deep.card < Fam.card := lt_of_le_of_lt hcard_le hsum
  have hsdiff : (Fam \ deep).Nonempty := by
    rw [← Finset.card_pos]
    have hadd := Finset.card_sdiff_add_card_eq_card hdeepsub
    omega
  obtain ⟨ρ, hρ⟩ := hsdiff
  rw [Finset.mem_sdiff, hdeep, Finset.mem_filter, not_and] at hρ
  exact ⟨ρ, hρ.1, Nat.not_le.mp (hρ.2 hρ.1)⟩

/-- **Shallow restriction in a family, from a range-local decay.**  With fuel `= K`, the depth bound
`depth ≤ K` is free, so a per-depth bound `M` that halves on `[T,K)` and stays below `Fam.card` yields
a depth-`< T` restriction *inside* `Fam`. -/
theorem exists_depth_lt_in_of_decay {cs : List (Clause n)} {T : ℕ} {M : ℕ → ℕ} (K : ℕ)
    {Fam : Finset (SwitchingCounting.Restriction n)}
    (hdec : ∀ s, T ≤ s → s < K → 2 * M (s + 1) ≤ M s)
    (hbound : ∀ s, T ≤ s →
      (Fam.filter (fun ρ => (canonicalDT cs K ρ).depth = s)).card ≤ M s)
    (hbase : 2 * M T < Fam.card) :
    ∃ ρ ∈ Fam, (canonicalDT cs K ρ).depth < T :=
  exists_depth_lt_in_of_sum_bound Fam (fun ρ _ => canonicalDT_depth_le cs K ρ) hbound
    (lt_of_le_of_lt (geom_tail_sum_Icc_local T K hdec) hbase)

/-- **The collapse closed over the `K`-star family, modulo the shell count.**  Under the doubled-slack
regime `(8w)·K + K ≤ n+1`, if the depth-`s` count *within the `K`-star family* is bounded by the
switching count `2^(n-K+s)·C(n,K-s)·(2w)^s`, and twice the threshold term is below the family size
`|{stars = K}|`, then a `K`-star restriction with canonical depth `< T` exists.  Decay is supplied by
`count_decay_step`; the universe is now the correct `K`-star family. -/
theorem exists_shallow_in_of_count {cs : List (Clause n)} {w K T : ℕ}
    (hreg : (8 * w) * K + K ≤ n + 1)
    (hbound : ∀ s, T ≤ s →
      ((Finset.univ.filter (fun ρ : SwitchingCounting.Restriction n =>
          SwitchingCounting.stars ρ = K)).filter
        (fun ρ => (canonicalDT cs K ρ).depth = s)).card
        ≤ 2 ^ (n - K + s) * n.choose (K - s) * (2 * w) ^ s)
    (hbase : 2 * (2 ^ (n - K + T) * n.choose (K - T) * (2 * w) ^ T)
      < (Finset.univ.filter (fun ρ : SwitchingCounting.Restriction n =>
          SwitchingCounting.stars ρ = K)).card) :
    ∃ ρ ∈ Finset.univ.filter (fun ρ : SwitchingCounting.Restriction n =>
        SwitchingCounting.stars ρ = K),
      (canonicalDT cs K ρ).depth < T :=
  exists_depth_lt_in_of_decay (M := fun s => 2 ^ (n - K + s) * n.choose (K - s) * (2 * w) ^ s) K
    (fun s _ hsK => SwitchingCounting.count_decay_step hsK hreg)
    hbound hbase

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_good_fullpath
