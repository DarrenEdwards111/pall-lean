import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingReconstructed
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Threading

/-!
# The switching injection — the count-enabling result (branch only)

The reconstruction recovers `deepestSatSeq` from the leaf and the full path.  Threading it through the
proved selected-set recovery closes the loop: **ρ itself is recovered** from `(leaf, full-path)`, so the
map `ρ ↦ (deepestEnd cs F ρ, deepestFullSeq cs F ρ)` is **injective** on the bad set.  This is exactly
what the `(2w)^s` switching count needs (an injection of `Bad` into leaves × labels).

* `rho_recovered` — `ρ = freeOn σ_end (decodedSel σ_end ∪ decodeSatSeq (reconstructed deepestSatSeq))`,
  a left inverse using only the leaf and the full path (`freeOn_deepestEnd` +
  `decodedSel_union_satSel_eq_deepestSel` + `deepestSatSel_eq_decodeSatSeq` + the reconstruction).
* `leaf_fullpath_injective` — hence `ρ ↦ (leaf, full-path)` is injective on bad restrictions.

Clean axioms, no `sorry`.  The only thing between this and the full `|Bad| ≤ |leaves|·(2w)^s` bound is
encoding `deepestFullSeq` into `PathLabel` (clause-width gives positions `< w`) and the cardinality
arithmetic — the codebase's counting machinery (`card_pathLabels`, `card_bad_le`) consumes an injection
of exactly this shape.  `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **ρ recovered from the leaf and the full path.**  A left inverse to `ρ ↦ (leaf, full-path)`,
built entirely from legal data. -/
theorem rho_recovered (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool)
    (hnf : ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false) :
    SwitchingCounting.freeOn (deepestEnd cs F ρ)
        (SwitchingCounting.decodedSel cs (deepestEnd cs F ρ)
          ∪ decodeSatSeq (fullReplaySatPar
              (recoverStream cs (deepestEnd cs F ρ) ((deepestFullSeq cs F ρ).map Prod.fst)
                (fun _ => none))
              (deepestFullSeq cs F ρ)))
      = ρ := by
  rw [deepestSatSeq_reconstructed cs F ρ hnf hleaf,
      ← deepestSatSel_eq_decodeSatSeq cs F ρ,
      decodedSel_union_satSel_eq_deepestSel hnf]
  exact freeOn_deepestEnd cs F ρ

/-- **The switching injection.**  On the bad set, `ρ ↦ (deepestEnd cs F ρ, deepestFullSeq cs F ρ)` is
injective. -/
theorem leaf_fullpath_injective (cs : List (Clause n)) (F : ℕ) {ρ₁ ρ₂ : Fin n → Option Bool}
    (h1nf : ∀ U ∈ cs, SwitchingCounting.termFalsified ρ₁ U = false)
    (h1leaf : SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ₁) = false)
    (h2nf : ∀ U ∈ cs, SwitchingCounting.termFalsified ρ₂ U = false)
    (h2leaf : SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ₂) = false)
    (he : deepestEnd cs F ρ₁ = deepestEnd cs F ρ₂)
    (hf : deepestFullSeq cs F ρ₁ = deepestFullSeq cs F ρ₂) :
    ρ₁ = ρ₂ := by
  rw [← rho_recovered cs F ρ₁ h1nf h1leaf, ← rho_recovered cs F ρ₂ h2nf h2leaf, he, hf]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.rho_recovered
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.leaf_fullpath_injective
