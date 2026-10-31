import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderAmplificationBoundary

/-!
# Does PAC help?  The PAC projection boundary

The `p vs np1` PAC layer is a set of geometry‑preserving operations: invertible / block‑local basis changes,
affine relabellings, restrictions / projections, tag constants, and local gadget multiplication followed by a
positivity‑preserving projection.  Their stated property is *rank‑preserving / rank‑non‑increasing / at most
polynomial‑factor blowup*.  The honest question: does PAC rescue the fixed‑order SPDP collapse?

This file proves it does **not** — for the same locality reason — and isolates exactly the PAC route that *could*
still work.

## What is proved (clean axioms, no `sorry`)

* `pac_postProjection_nonincrease` — a PAC **projection / restriction** (post‑composing any `g : R₂ → R₁`) only
  *decreases* projected rank: `pcrank (g ∘ proj) M ≤ pcrank proj M`.  PAC restrictions cannot create rank.
* `pacRelabel_spdp_collapse` — a PAC **local relabelling** `σ` with bounded weight blowup (`hw (σ v) ≤ c·hw v`)
  cannot rescue the collapse: a high‑distance residual (`MinSupportWeight M Δ`) relabelled by `σ` still has
  `pcrank (spdpProj a k d) ≤ 1` whenever `c·(k+d) < Δ`.  A local gadget only rescales the visibility radius by its
  locality factor `c` — for constant `c` and expander distance `Δ = Ω(n)`, the collapse survives.
* `pacPositiveMinorSurvival_needs_scaling` — the **live certificate** `PACPositiveMinorSurvival` (a positive /
  identity minor of size `≥ s` survives the projection on the hard family) provably *forces the order to reach the
  distance*: if `MinSupportWeight M Δ` and `s ≥ 2`, then survival implies `Δ ≤ k + d`.  No fixed sub‑distance
  order can carry a positive minor.

## Verdict — PAC is the right ingredient, but only at scaling order

PAC genuinely helps in two ways the framework confirms: (1) **P‑side control** — PAC restrictions are
rank‑non‑increasing (`pac_postProjection_nonincrease`), so they preserve low projected rank through compilation
(the A1 upper‑bound side); (2) **NP‑side positivity** — the positive‑minor geometry is exactly what a survival
certificate `PACPositiveMinorSurvival` would carry (the A3 side).  But PAC operations are local/projective, and
`pacRelabel_spdp_collapse` shows they only shift the visibility radius by `O(1)` — they **cannot** beat the
locality no‑go at fixed order.  `pacPositiveMinorSurvival_needs_scaling` makes the requirement precise: the live
PAC route is **scaling‑order PAC‑SPDP** (`k + d ≥ Δ = Θ(distance)`) with positive‑minor survival — the same
`ScalingSPDPBridge` the expander analysis reached, now seen to be PAC's only opening too.  Fixed‑order
PAC‑SPDP is closed.
-/

namespace PallLean.Paper93.DeepMath.PathB.PACProjectionBoundary

open PallLean.Paper93.DeepMath.PathB.RankContextualWidth
open PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank
open PallLean.Paper93.DeepMath.PathB.LowDegreeProjection
open PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection
open PallLean.Paper93.DeepMath.PathB.AffineIndicatorCollapse
open PallLean.Paper93.DeepMath.PathB.ExpanderAmplificationBoundary

variable {a : ℕ}

/-- **PAC restriction is rank‑non‑increasing (proved).**  Post‑composing any PAC projection `g : R₂ → R₁` onto a
feature map only merges features: `pcrank (g ∘ proj) M ≤ pcrank proj M`.  PAC restrictions/projections cannot
create projected rank — good for the P‑side A1 upper bound, useless for resurrecting collapsed A3 rank. -/
theorem pac_postProjection_nonincrease {A : Type*} [Fintype A] {R₁ R₂ : Type*}
    [DecidableEq R₁] [DecidableEq R₂]
    (proj : ((Fin a → Bool) → Bool) → R₂) (g : R₂ → R₁) (M : A → (Fin a → Bool) → Bool) :
    pcrank (fun r => g (proj r)) M ≤ pcrank proj M :=
  pcrank_le_of_factor (fun r => g (proj r)) proj g M (fun _ => rfl)

/-- A PAC **local relabelling** with bounded weight blowup: each output point has Hamming weight at most `c` times
the input's (a locality‑`c` / block‑local basis change). -/
def WeightBoundedMap (σ : (Fin a → Bool) → (Fin a → Bool)) (c : ℕ) : Prop :=
  ∀ v, hw (σ v) ≤ c * hw v

/-- **A PAC local relabelling cannot rescue the collapse (proved).**  Relabelling a high‑distance residual
(`MinSupportWeight M Δ`) by a weight‑blowup‑`c` map `σ` (matrix `fun x v => M x (σ v)`) still collapses under a
fixed‑order SPDP probe whenever `c·(k+d) < Δ`: the local map only rescales the visibility radius by `c`. -/
theorem pacRelabel_spdp_collapse {A : Type*} [Fintype A] (k d Δ c : ℕ)
    (σ : (Fin a → Bool) → (Fin a → Bool)) (M : A → (Fin a → Bool) → Bool)
    (hM : MinSupportWeight M Δ) (hσ : WeightBoundedMap σ c) (hlt : c * (k + d) < Δ) :
    pcrank (spdpProj a k d) (fun x v => M x (σ v)) ≤ 1 := by
  refine le_trans (spdp_pcrank_le_ballMeeting k d (fun x v => M x (σ v))) ?_
  have hempty : (Finset.univ.filter (fun x => ∃ z, hw z ≤ k + d ∧ M x (σ z) = true)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x _
    rintro ⟨z, hz, hMz⟩
    have h1 := hM x (σ z) hMz
    have h2 := hσ z
    have h3 : c * hw z ≤ c * (k + d) := Nat.mul_le_mul (le_refl c) hz
    omega
  rw [hempty]
  simp

/-- **The live PAC certificate.**  A positive / identity minor of size `≥ s` of the hard family survives the
projection: there is a subset `T` of `≥ s` rows on which the (PAC‑)SPDP feature map is injective. -/
def PACPositiveMinorSurvival {A : Type*} [Fintype A] (k d : ℕ) (M : A → (Fin a → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ T : Finset ((Fin a → Bool) → Bool), s ≤ T.card ∧ T ⊆ rowsOf M ∧ Set.InjOn (spdpProj a k d) ↑T

/-- **Positive‑minor survival forces scaling order (proved).**  If the residual has distance `Δ`
(`MinSupportWeight M Δ`) and the surviving minor is nontrivial (`s ≥ 2`), then any PAC‑SPDP feature map carrying
it must have order reaching the distance: `Δ ≤ k + d`.  No fixed sub‑distance order can carry a positive minor —
PAC's only opening is the scaling‑order regime. -/
theorem pacPositiveMinorSurvival_needs_scaling {A : Type*} [Fintype A] (k d Δ s : ℕ)
    (M : A → (Fin a → Bool) → Bool) (hM : MinSupportWeight M Δ) (hs : 2 ≤ s)
    (hsurv : PACPositiveMinorSurvival k d M s) :
    Δ ≤ k + d := by
  by_contra hlt
  push_neg at hlt
  have hcollapse := highDistance_spdp_collapse k d Δ M hM hlt
  obtain ⟨T, hTcard, hTsub, hTinj⟩ := hsurv
  have hge := pcrank_ge_of_injOn (spdpProj a k d) M T hTsub hTinj
  omega

end PallLean.Paper93.DeepMath.PathB.PACProjectionBoundary

#print axioms PallLean.Paper93.DeepMath.PathB.PACProjectionBoundary.pac_postProjection_nonincrease
#print axioms PallLean.Paper93.DeepMath.PathB.PACProjectionBoundary.pacRelabel_spdp_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.PACProjectionBoundary.pacPositiveMinorSurvival_needs_scaling
