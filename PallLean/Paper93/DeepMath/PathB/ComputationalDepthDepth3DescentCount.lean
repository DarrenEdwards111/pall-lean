import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DescentInject

/-!
# Block-DT model, foundation 51: branching holography, step 4i — the count (branch only)

The branching holographic count, from the injection `σ ↦ (descentSat, descentSatMasks)` (brick 50): the bad
restrictions inject into `Short × Labels`, so `|Bad| ≤ |Short| · |Labels|`.  This is the branching analog
of the single-path `block_count`, now standing on the *satisfying-boundary + peel + injectivity* chain
(bricks 48–50) rather than the single `killTerm` path.

* `descent_count` — `Bad.card ≤ Short.card * Labels.card`, given the boundary lands in `Short` and the
  masks land in `Labels` (the descent input may vary per `σ`).

## What this reduces the switching bound to — and what is NOT proven

`descent_count` is the count *framework*: it turns `Pr[depth ≥ s]` into `|Short| · |Labels| / |all|`.  Two
quantitative inputs remain, and neither is proven here (they are the genuine remaining content, the same
ones the single-path `block_count` leaves to its caller):

  1. `|Labels| ≤ (3^w)^s` — bound the label space.  Each mask is supported on the freed variables of its
     block (`⊆ w` of the *peel-recovered* term's variables), with a value each, so per block it is one of
     `≤ 3^w` (position-free / free-with-0 / free-with-1).  Turning this into a concrete `Labels` Finset
     requires the **position-encoding injection** (encode each mask by positions-in-its-recovered-term +
     signs, landing in a `(3^w)^s`-size type) — a further construction, not done here.
  2. the **p-biased measure** converting the counting ratio into a probability.

So `descent_count` is honestly a reduction, not the switching estimate; the `(3^w)^s` label bound and the
measure are still open.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The branching holographic count.**  From the injection `σ ↦ (descentSat, descentSatMasks)`: the bad
set injects into `Short × Labels`, so `|Bad| ≤ |Short| · |Labels|`.  The descent input may vary per `σ`
(the recovery, hence the injectivity, uses only the boundary and masks). -/
theorem descent_count (cs : List (Clause n)) (w F : ℕ)
    {Bad Short : Finset (Fin n → Option Bool)} {Labels : Finset (List (Fin n → Option Bool))}
    (xσ : (Fin n → Option Bool) → (Fin n → Bool))
    (hS : ∀ σ ∈ Bad, descentSat cs w F σ (xσ σ) ∈ Short)
    (hL : ∀ σ ∈ Bad, descentSatMasks cs w F σ (xσ σ) ∈ Labels) :
    Bad.card ≤ Short.card * Labels.card := by
  classical
  have hcard : Bad.card ≤ (Short ×ˢ Labels).card := by
    refine Finset.card_le_card_of_injOn
      (fun σ => (descentSat cs w F σ (xσ σ), descentSatMasks cs w F σ (xσ σ)))
      (fun σ hσ => ?_) (fun σ₁ _ σ₂ _ heq => ?_)
    · exact Finset.mem_product.mpr ⟨hS σ hσ, hL σ hσ⟩
    · exact descentSat_injective cs w F (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  rwa [Finset.card_product] at hcard

/-- **Per-block label count.**  A mask supported on a set `S` (one of `none`/`some true`/`some false` on
`S`, `none` elsewhere) is one of at most `3 ^ |S|`.  This is the per-block ingredient of the
`|Labels| ≤ (3^w)^s` bound: each descent mask is supported on its block's freed variables (`⊆ w` of the
recovered term's variables). -/
theorem card_masks_supported_le (S : Finset (Fin n)) :
    (Finset.univ.filter (fun m : Fin n → Option Bool => ∀ v, v ∉ S → m v = none)).card
      ≤ 3 ^ S.card := by
  classical
  have hinj : (Finset.univ.filter (fun m : Fin n → Option Bool => ∀ v, v ∉ S → m v = none)).card
      ≤ (Finset.univ : Finset (S → Option Bool)).card := by
    refine Finset.card_le_card_of_injOn (fun m => fun v : S => m v.val)
      (fun m _ => Finset.mem_univ _) (fun m₁ h₁ m₂ h₂ heq => ?_)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at h₁ h₂
    funext v
    by_cases hv : v ∈ S
    · exact congrFun heq ⟨v, hv⟩
    · rw [h₁ v hv, h₂ v hv]
  calc (Finset.univ.filter (fun m : Fin n → Option Bool => ∀ v, v ∉ S → m v = none)).card
      ≤ (Finset.univ : Finset (S → Option Bool)).card := hinj
    _ = Fintype.card (S → Option Bool) := (Finset.card_univ)
    _ = Fintype.card (Option Bool) ^ Fintype.card S := Fintype.card_fun
    _ = 3 ^ S.card := by rw [Fintype.card_option, Fintype.card_bool, Fintype.card_coe]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_count
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.card_masks_supported_le
