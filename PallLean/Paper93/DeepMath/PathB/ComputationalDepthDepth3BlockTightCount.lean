import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockCompactRecovery
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockInject
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockSwitchingCount

/-!
# Block-DT model, foundation 10d: the tight holographic switching count (branch only)

The final concrete switching count, with the **compact** in-clause label: `|Bad| ≤ |Short| · (2^w)^s`,
no `|cs|` factor.

* `block_injective_compact` — `ρ ↦ (blockEncode ρ, compactMasks ρ)` is injective (the global masks are
  reconstructed from the compact labels via `blockMasks_eq_zipWith` + `block_recovery_compact`).
* `compactMasks_length` — `|compactMasks| = |blockStream|` (number of blocks).
* `block_switching_count_tight` — `|Bad| ≤ |{σ : stars σ ≤ K-s}| · (2^w)^s`.

Clean, no `sorry`.  AC⁰/depth-3 holographic switching count, complete.  Not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Compact injection.**  `ρ ↦ (blockEncode ρ, compactMasks ρ)` is injective. -/
theorem block_injective_compact (cs : List (Clause n)) (w F : ℕ)
    (hcons : ∀ T ∈ cs, Consistent T) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    {ρ₁ ρ₂ : Restriction n}
    (he : blockEncode cs F ρ₁ = blockEncode cs F ρ₂)
    (hc : compactMasks cs w F ρ₁ = compactMasks cs w F ρ₂) : ρ₁ = ρ₂ := by
  apply block_injective cs F he
  rw [blockMasks_eq_zipWith cs w hw F ρ₁, blockMasks_eq_zipWith cs w hw F ρ₂,
      ← block_recovery_compact cs w hcons hw F ρ₁, ← block_recovery_compact cs w hcons hw F ρ₂,
      he, hc]

/-- The number of compact masks equals the number of blocks. -/
theorem compactMasks_length (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      (compactMasks cs w F σ).length = (blockStream cs F σ).length := by
  intro F
  induction F with
  | zero => intro σ; simp [compactMasks, blockStream]
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [compactMasks, blockStream]; simp [hany]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none => rw [compactMasks, blockStream]; simp [hany, hact]
      | some T =>
        rw [show compactMasks cs w (F + 1) σ = freePosOf w σ T :: compactMasks cs w F (killTerm σ T) by
              rw [compactMasks]; simp only [hany, Bool.false_eq_true, if_false, hact],
            show blockStream cs (F + 1) σ = T :: blockStream cs F (killTerm σ T) by
              rw [blockStream]; simp only [hany, Bool.false_eq_true, if_false, hact],
            List.length_cons, List.length_cons, ih (killTerm σ T)]

/-- **The tight holographic switching count.**  `|Bad| ≤ |{σ : stars σ ≤ K-s}| · (2^w)^s`. -/
theorem block_switching_count_tight (cs : List (Clause n)) (w F K s : ℕ)
    (hcons : ∀ T ∈ cs, Consistent T) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, SwitchingCounting.stars ρ = K)
    (hdepth : ∀ ρ ∈ Bad, (blockStream cs F ρ).length = s) :
    Bad.card
      ≤ (Finset.univ.filter (fun σ : Restriction n => SwitchingCounting.stars σ ≤ K - s)).card
        * (2 ^ w) ^ s := by
  classical
  have hcard : Bad.card ≤
      ((Finset.univ.filter (fun σ : Restriction n => SwitchingCounting.stars σ ≤ K - s)) ×ˢ
        (Finset.univ : Finset (BlockPathLabel w s))).card := by
    refine Finset.card_le_card_of_injOn
      (fun ρ => (blockEncode cs F ρ,
        (fun i : Fin s => (compactMasks cs w F ρ).getD i.val ∅ : BlockPathLabel w s)))
      (fun ρ hρ => ?_) (fun ρ₁ h₁ ρ₂ h₂ heq => ?_)
    · refine Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h := stars_blockEncode_le cs F ρ
      rw [hstars ρ (Finset.mem_coe.mp hρ), hdepth ρ (Finset.mem_coe.mp hρ)] at h
      exact h
    · have hfst : blockEncode cs F ρ₁ = blockEncode cs F ρ₂ := congrArg Prod.fst heq
      have hsnd := congrArg Prod.snd heq
      have hlen1 : (compactMasks cs w F ρ₁).length = s := by
        rw [compactMasks_length]; exact hdepth ρ₁ (Finset.mem_coe.mp h₁)
      have hlen2 : (compactMasks cs w F ρ₂).length = s := by
        rw [compactMasks_length]; exact hdepth ρ₂ (Finset.mem_coe.mp h₂)
      refine block_injective_compact cs w F hcons hw hfst ?_
      apply List.ext_getElem (by rw [hlen1, hlen2])
      intro i hi1 hi2
      have hi_s : i < s := hlen1 ▸ hi1
      have hgi := congrFun hsnd ⟨i, hi_s⟩
      dsimp only at hgi
      rw [List.getD_eq_getElem (l := compactMasks cs w F ρ₁) (d := ∅) hi1,
          List.getD_eq_getElem (l := compactMasks cs w F ρ₂) (d := ∅) hi2] at hgi
      exact hgi
  rwa [Finset.card_product, Finset.card_univ, card_blockPathLabel] at hcard

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.block_injective_compact
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.block_switching_count_tight
