import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecoverStreamSat
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingInjective
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FilterShellCount

/-!
# Dropping the unsatisfied-leaf hypothesis from the count (branch only)

`recoverStream` works for *satisfied* leaves (`recoverStream_eq_sat`/`recoverStream_correct_sat`):
`hleaf` is plumbing — the active-clause stream is read only at intermediate descent states, which are
unsatisfied inherently.  This file propagates that through the whole count chain, producing `hleaf`-free
versions:

* `deepestSatSeq_reconstructed_sat`, `deepestSel_recovered_sat` — the reconstruction, no `hleaf`.
* `reconstructionCorrect_fullpath_sat`, `fullpath_switching_count_sat` — the injection/count, no `hleaf`.
* `shell_count_sat` — the `(K-s)`-shell count, no `hleaf` (the leaf may be a satisfied `true` leaf).
* `family_depth_count_grouped_sat` — the assembled grouped count over a family, with **neither** the
  falsified-clause (`hnf`) nor the satisfied-leaf (`hleaf`) restriction:

    `|{ρ ∈ Bad : stars=K, depth=s, positions<w}| ≤ (#live-sublists) · C(n,K-s)·2^(n-(K-s))·(2w)^s`.

So both leaf types and all falsification patterns are now handled.  Star conservation
(`deepestEnd_mem_shell`) is unconditional, so the leaf lands in the `(K-s)`-shell regardless.

All clean, no `sorry`.  Still **lossy** (the `#live-sublists ≤ 2^|cs|` factor from the falsified
grouping); the satisfied-leaf restriction, however, is gone entirely.  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Reconstruction of `deepestSatSeq`, without the unsatisfied-leaf hypothesis. -/
theorem deepestSatSeq_reconstructed_sat (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool)
    (hnf : ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false) :
    fullReplaySatPar
        (recoverStream cs (deepestEnd cs F ρ) ((deepestFullSeq cs F ρ).map Prod.fst)
          (fun _ => none))
        (deepestFullSeq cs F ρ)
      = deepestSatSeq cs F ρ := by
  rw [recoverStream_correct_sat cs F ρ hnf, fullReplaySatPar_correct]

/-- The selected set recovered from the leaf and full path, without the unsatisfied-leaf hypothesis. -/
theorem deepestSel_recovered_sat (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool)
    (hnf : ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false) :
    SwitchingCounting.decodedSel cs (deepestEnd cs F ρ)
        ∪ decodeSatSeq (fullReplaySatPar
            (recoverStream cs (deepestEnd cs F ρ) ((deepestFullSeq cs F ρ).map Prod.fst)
              (fun _ => none))
            (deepestFullSeq cs F ρ))
      = deepestSel cs F ρ := by
  rw [deepestSatSeq_reconstructed_sat cs F ρ hnf,
      ← deepestSatSel_eq_decodeSatSeq cs F ρ,
      decodedSel_union_satSel_eq_deepestSel hnf]

/-- `ReconstructionCorrect` via the full path, without the unsatisfied-leaf hypothesis. -/
theorem reconstructionCorrect_fullpath_sat (cs : List (Clause n)) (w s F : ℕ) [NeZero w]
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hlen : ∀ ρ ∈ Bad, (deepestFullSeq cs F ρ).length = s)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ deepestFullSeq cs F ρ, p.1 < w) :
    ReconstructionCorrect cs w s F Bad := by
  refine ⟨fun ρ => SwitchingCounting.flatToLabel (toFinW w (deepestFullSeq cs F ρ)),
    fun π lbl => SwitchingCounting.decodedSel cs π
      ∪ decodeSatSeq (fullReplaySatPar
          (recoverStream cs π (((List.ofFn lbl).map finToNat).map Prod.fst) (fun _ => none))
          ((List.ofFn lbl).map finToNat)),
    fun ρ hρ => ?_⟩
  have hround : (List.ofFn (SwitchingCounting.flatToLabel
        (toFinW w (deepestFullSeq cs F ρ)) : SwitchingCounting.PathLabel w s)).map finToNat
      = deepestFullSeq cs F ρ := by
    rw [ofFn_flatToLabel (by rw [toFinW, List.length_map]; exact hlen ρ hρ)]
    exact finToNat_toFinW (hpos ρ hρ)
  show SwitchingCounting.decodedSel cs (deepestEnd cs F ρ)
      ∪ decodeSatSeq (fullReplaySatPar
          (recoverStream cs (deepestEnd cs F ρ)
            (((List.ofFn (SwitchingCounting.flatToLabel
              (toFinW w (deepestFullSeq cs F ρ)) : SwitchingCounting.PathLabel w s)).map finToNat).map
              Prod.fst) (fun _ => none))
          ((List.ofFn (SwitchingCounting.flatToLabel
            (toFinW w (deepestFullSeq cs F ρ)) : SwitchingCounting.PathLabel w s)).map finToNat))
      = deepestSel cs F ρ
  rw [hround]
  exact deepestSel_recovered_sat cs F ρ (hnf ρ hρ)

/-- The full-path switching count, without the unsatisfied-leaf hypothesis. -/
theorem fullpath_switching_count_sat (cs : List (Clause n)) (w s F : ℕ) [NeZero w]
    {Bad Short : Finset (SwitchingCounting.Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hlen : ∀ ρ ∈ Bad, (deepestFullSeq cs F ρ).length = s)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ deepestFullSeq cs F ρ, p.1 < w) :
    Bad.card ≤ Short.card * (2 * w) ^ s :=
  deepest_switching_count_of_reconstruction hmem
    (reconstructionCorrect_fullpath_sat cs w s F hnf hlen hpos)

/-- **The `(K-s)`-shell count, without the unsatisfied-leaf hypothesis.**  The leaf may be a satisfied
`true` leaf; star conservation still lands it in the `(K-s)`-shell. -/
theorem shell_count_sat (cs : List (Clause n)) (w K s F : ℕ) [NeZero w]
    {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, SwitchingCounting.stars ρ = K)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s)
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ deepestFullSeq cs F ρ, p.1 < w) :
    Bad.card ≤ n.choose (K - s) * 2 ^ (n - (K - s)) * (2 * w) ^ s := by
  have hmem : ∀ ρ ∈ Bad,
      deepestEnd cs F ρ ∈
        Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ = K - s) :=
    fun ρ hρ => deepestEnd_mem_shell cs F ρ (hstars ρ hρ) (hdepth ρ hρ)
  have hlen : ∀ ρ ∈ Bad, (deepestFullSeq cs F ρ).length = s :=
    fun ρ hρ => (deepestFullSeq_length_eq_depth cs F ρ).trans (hdepth ρ hρ)
  have hcount := fullpath_switching_count_sat cs w s F hmem hnf hlen hpos
  rwa [SwitchingCounting.card_stars_eq (K - s)] at hcount

/-- **The grouped shell count, with neither `hnf` nor `hleaf`.**  Combining the falsified-clause
grouping with the satisfied-leaf removal: the depth-`s` part of a family — over **all** falsification
patterns and **both** leaf types — is bounded by the number of distinct live-sublists times the single
`(K-s)`-shell bound. -/
theorem family_depth_count_grouped_sat [DecidableEq (Clause n)]
    (cs : List (Clause n)) (w K s F : ℕ) [NeZero w]
    {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, SwitchingCounting.stars ρ = K)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s)
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
        apply shell_count_sat b w K s F
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

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.shell_count_sat
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.family_depth_count_grouped_sat
