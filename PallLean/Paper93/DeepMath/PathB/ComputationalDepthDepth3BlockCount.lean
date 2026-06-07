import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockInject

/-!
# Block-DT model, foundation 7: the holographic count (branch only)

The injection `ρ ↦ (blockEncode cs F ρ, blockMasks cs F ρ)` (`block_injective`) yields the count

  `|Bad| ≤ |Short| · |Labels|`

for any `Short` containing the boundary leaves and any `Labels` containing the stars-patterns of the
bad set.  This is the holographic switching count — **no `2^|cs|` live-sublist factor**: the active-clause
path is recovered from the boundary, so each bad `ρ` is pinned by its leaf and tiny label alone.

* `block_count` — `|Bad| ≤ |Short| · |Labels|` from the injection.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.

**Honest scope.**  This is the count *shape* from the injection.  Quantifying `|Short|` (the leaf shell:
`blockEncode` fixes the block variables, so leaves have fewer stars) and `|Labels|` (the stars-pattern
space, `≤ (2^w)^s`-type per the per-block `≤ w` block variables) and feeding the regime is the final
arithmetic step — and the block model sets a *variable* number of variables per block, so that shell
accounting differs from the binary-model `(K-s)` shell.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The holographic count.**  From the injection `ρ ↦ (blockEncode, blockMasks)`: the bad set injects
into `Short × Labels`, so `|Bad| ≤ |Short| · |Labels|`. -/
theorem block_count (cs : List (Clause n)) (F : ℕ)
    {Bad Short : Finset (Restriction n)} {Labels : Finset (List (Fin n → Bool))}
    (hS : ∀ ρ ∈ Bad, blockEncode cs F ρ ∈ Short)
    (hL : ∀ ρ ∈ Bad, blockMasks cs F ρ ∈ Labels) :
    Bad.card ≤ Short.card * Labels.card := by
  classical
  have hcard : Bad.card ≤ (Short ×ˢ Labels).card := by
    refine Finset.card_le_card_of_injOn
      (fun ρ => (blockEncode cs F ρ, blockMasks cs F ρ)) (fun ρ hρ => ?_) (fun ρ₁ _ ρ₂ _ heq => ?_)
    · exact Finset.mem_product.mpr ⟨hS ρ hρ, hL ρ hρ⟩
    · exact block_injective cs F (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  rwa [Finset.card_product] at hcard

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.block_count
