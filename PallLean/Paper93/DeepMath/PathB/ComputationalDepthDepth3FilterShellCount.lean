import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarShell
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FilterFalsified

/-!
# The grouped shell count — assembling the falsifying case (branch only)

Combining the `(K-s)`-shell count (`shell_count`, for `ρ` that falsify nothing) with the filter
reduction (`canonicalDT_depth_eq_filter`, `deepestEnd_eq_filter`, `deepestFullSeq_eq_filter`,
`hnf_filter`), we bound the depth-`s` part of a family **without** the `hnf` hypothesis, by grouping
`ρ` by its **killed-clause set** `cs' = cs.filter (!termFalsified ρ ·)`:

  `|Bad| ≤ (#distinct live-sublists) · C(n,K-s)·2^(n-(K-s))·(2w)^s`.

Each fiber `{ρ ∈ Bad : cs.filter(!termFalsified ρ ·) = cs''}` consists of `ρ` falsifying nothing on
`cs''` (`hnf_filter`), with the *same* depth, leaf, and path as on `cs''` (the filter reduction), so
`shell_count cs''` bounds it by the single `(K-s)`-shell bound — independent of `cs''`.  Summing over
the image gives the count.

**Honest scope.**  This is a *true, complete* bound, but it is **lossy**: the factor
`(Bad.image (cs.filter (!termFalsified · ·))).card` (the number of distinct live-sublists arising) can
be as large as `2^|cs|`.  Removing it is the tight-encoding content of Håstad's lemma (recovering the
active clause for falsifying `ρ` from the *public* `cs` alone, which the filter reduction cannot do
since `cs'` depends on the private `ρ`) — genuine open research, **not** done here.  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The grouped shell count.**  Without the `hnf` hypothesis: grouping the depth-`s` bad set by
killed-clause set and applying `shell_count` per fiber bounds it by `(#distinct live-sublists)` times
the single `(K-s)`-shell bound. -/
theorem family_depth_count_grouped [DecidableEq (Clause n)]
    (cs : List (Clause n)) (w K s F : ℕ) [NeZero w]
    {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, SwitchingCounting.stars ρ = K)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ deepestFullSeq cs F ρ, p.1 < w) :
    Bad.card
      ≤ (Bad.image (fun ρ => cs.filter (fun T => !SwitchingCounting.termFalsified ρ T))).card
        * (n.choose (K - s) * 2 ^ (n - (K - s)) * (2 * w) ^ s) := by
  classical
  have hfib : Bad.card
      = ∑ b ∈ Bad.image (fun ρ => cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)),
          (Bad.filter (fun ρ => cs.filter (fun T => !SwitchingCounting.termFalsified ρ T) = b)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun ρ hρ => Finset.mem_image_of_mem
        (fun ρ => cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) hρ)
  rw [hfib]
  calc ∑ b ∈ Bad.image (fun ρ => cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)),
          (Bad.filter (fun ρ => cs.filter (fun T => !SwitchingCounting.termFalsified ρ T) = b)).card
      ≤ ∑ _b ∈ Bad.image (fun ρ => cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)),
          (n.choose (K - s) * 2 ^ (n - (K - s)) * (2 * w) ^ s) := by
        refine Finset.sum_le_sum (fun b _hb => ?_)
        apply shell_count b w K s F
        · intro ρ hρ; exact hstars ρ (Finset.mem_filter.mp hρ).1
        · intro ρ hρ
          obtain ⟨hρBad, hgb⟩ := Finset.mem_filter.mp hρ
          have h1 := canonicalDT_depth_eq_filter cs F ρ
          rw [hgb] at h1
          rw [← h1]; exact hdepth ρ hρBad
        · intro ρ hρ U hU
          obtain ⟨_hρBad, hgb⟩ := Finset.mem_filter.mp hρ
          rw [← hgb] at hU
          exact hnf_filter cs ρ U hU
        · intro ρ hρ
          obtain ⟨hρBad, hgb⟩ := Finset.mem_filter.mp hρ
          have hstable : ∀ T, SwitchingCounting.termFalsified ρ T = true →
              SwitchingCounting.termFalsified (deepestEnd cs F ρ) T = true :=
            fun T h => termFalsified_deepestEnd_stable cs T F ρ h
          have he := deepestEnd_eq_filter cs ρ F ρ (fun _ h => h)
          rw [hgb] at he
          rw [← he, ← hgb, anyTermSat_filter_eq hstable]
          exact hleaf ρ hρBad
        · intro ρ hρ p hp
          obtain ⟨hρBad, hgb⟩ := Finset.mem_filter.mp hρ
          have hf := deepestFullSeq_eq_filter cs ρ F ρ (fun _ h => h)
          rw [hgb] at hf
          rw [← hf] at hp
          exact hpos ρ hρBad p hp
    _ = (Bad.image (fun ρ => cs.filter (fun T => !SwitchingCounting.termFalsified ρ T))).card
          * (n.choose (K - s) * 2 ^ (n - (K - s)) * (2 * w) ^ s) := by
        rw [Finset.sum_const, smul_eq_mul]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.family_depth_count_grouped
