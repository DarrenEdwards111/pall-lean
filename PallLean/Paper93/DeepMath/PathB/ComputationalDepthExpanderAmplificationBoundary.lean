import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAffineIndicatorCollapse

/-!
# Can a Ramanujan / expander layer amplify SPDP survival?  The amplification boundary

The honest answer (formalized here): **an expander amplifies *visibility*, not *invisibility*.**  A
high-distance (expander) residual has its accepting inputs concentrated at *high* Hamming weight — precisely where
a fixed-order SPDP/low-degree probe never looks.  So coupling many high-distance copies amplifies *zero* features
into more zero features: the collapse becomes **total**, not weaker.

This file proves the two sides of the amplification boundary.

## Negative side — distance amplifies invisibility (proved)

`MinSupportWeight M Δ` says every accepting input of every row has Hamming weight `≥ Δ` (the residual's distance /
expansion).  Then:

* `highDistance_spdp_collapse` — `MinSupportWeight M Δ → k + d < Δ → pcrank (spdpProj a k d) M ≤ 1`.  *Every* row
  vanishes on the weight-`≤(k+d)` ball, so all map to the single zero feature: the rank collapses to `≤ 1`,
  regardless of how many expander-coupled rows there are.  More distance ⇒ harder collapse, not amplification.
* `highDistance_lowDeg_collapse` — the same for low-degree (`d < Δ ⇒ pcrank ≤ 1`).

## The boundary — to see the residual the order must reach the distance (proved)

* `lowDeg_full_order_eq_crank` — at order `d = a` (probe radius = full dimension) the low-degree projection is
  injective and `pcrank = crank`: full visibility, no collapse.  So between order `< Δ` (total collapse) and order
  `= a` (full rank) the rank "turns on" only once the probe radius crosses the distance `Δ`.
* `spdpProj_feature_bound` (from `…SPDPFeatureProjection`) caps the feature space at `2^{N(a, k+d)}`, and `N(a,m)`
  grows past every polynomial once `m` is non-constant.  So crossing `k+d ≥ Δ` for an expander distance
  `Δ = Ω(n)` forces a `2^{super-poly}` feature space — breaking the A1 (polynomial feature count) side.

## Positive side — where an expander genuinely helps (existing levers)

Amplification works exactly when the gadgets are *visible*: `pcrank_eq_crank_of_injective` (a projection injective
on rows preserves the full rank), witnessed concretely by `spdp_ipMatrix_survives` (the linear core keeps full
rank `2^a`).  An expander product of *visible* gadgets multiplies their surviving distinctions — but a fixed-order
probe has **no** surviving distinction on a high-distance residual to multiply.

## Verdict

The expander is the right amplifier but not a fix: it multiplies visible rank and amplifies invisible collapse.
For the high-distance (Tseitin/expander) residuals A3 needs, a *fixed*-order probe sees nothing, so expansion only
deepens the collapse.  Survival still requires the probe order to scale with the expander distance — the
`ScalingSPDPBridge` (order `≥` distance while feature count stays polynomial), which is the SPDP-rank lower bound
itself.  Stop testing constant-order projections on expander residuals: this file proves they collapse.
-/

namespace PallLean.Paper93.DeepMath.PathB.ExpanderAmplificationBoundary

open PallLean.Paper93.DeepMath.PathB.RankContextualWidth
open PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank
open PallLean.Paper93.DeepMath.PathB.LowDegreeProjection
open PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection
open PallLean.Paper93.DeepMath.PathB.AffineIndicatorCollapse

variable {a : ℕ}

/-- **Distance / expansion property:** every accepting input of every row has Hamming weight `≥ Δ`.  (For an
expander Tseitin residual `Δ` is the expansion distance, `Ω(n)`.) -/
def MinSupportWeight {A : Type*} (M : A → (Fin a → Bool) → Bool) (Δ : ℕ) : Prop :=
  ∀ x z, M x z = true → Δ ≤ hw z

/-- **Low-degree collapse bound: `pcrank ≤ (#rows meeting the d-ball) + 1`.**  (Low-degree analogue of
`spdp_pcrank_le_ballMeeting`.) -/
theorem lowDeg_pcrank_le_ballMeeting {A : Type*} [Fintype A] (d : ℕ) (M : A → (Fin a → Bool) → Bool) :
    pcrank (lowDegProj a d) M
      ≤ (Finset.univ.filter (fun x => ∃ z, hw z ≤ d ∧ M x z = true)).card + 1 := by
  classical
  rw [pcrank_eq_image]
  have hsub : Finset.univ.image (fun x => lowDegProj a d (fun b => M x b))
      ⊆ insert (fun _ => false)
          ((Finset.univ.filter (fun x => ∃ z, hw z ≤ d ∧ M x z = true)).image
            (fun x => lowDegProj a d (fun b => M x b))) := by
    intro w hw'
    rw [Finset.mem_image] at hw'
    obtain ⟨x, _, rfl⟩ := hw'
    by_cases hx : ∃ z, hw z ≤ d ∧ M x z = true
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩, rfl⟩)
    · rw [Finset.mem_insert]
      left
      apply lowDegProj_zero_of_vanishing
      intro z hz
      cases hb : M x z
      · rfl
      · exact absurd ⟨z, hz, hb⟩ hx
  calc (Finset.univ.image (fun x => lowDegProj a d (fun b => M x b))).card
      ≤ (insert (fun _ => false)
          ((Finset.univ.filter (fun x => ∃ z, hw z ≤ d ∧ M x z = true)).image
            (fun x => lowDegProj a d (fun b => M x b)))).card := Finset.card_le_card hsub
    _ ≤ ((Finset.univ.filter (fun x => ∃ z, hw z ≤ d ∧ M x z = true)).image
            (fun x => lowDegProj a d (fun b => M x b))).card + 1 := Finset.card_insert_le _ _
    _ ≤ (Finset.univ.filter (fun x => ∃ z, hw z ≤ d ∧ M x z = true)).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1

/-- **Distance amplifies invisibility, SPDP (proved): `pcrank ≤ 1` when the probe order is below the distance.**
A high-distance residual is invisible to a fixed-order SPDP probe — coupling more copies just amplifies the zero
feature. -/
theorem highDistance_spdp_collapse {A : Type*} [Fintype A] (k d Δ : ℕ) (M : A → (Fin a → Bool) → Bool)
    (hM : MinSupportWeight M Δ) (hlt : k + d < Δ) :
    pcrank (spdpProj a k d) M ≤ 1 := by
  refine le_trans (spdp_pcrank_le_ballMeeting k d M) ?_
  have hempty : (Finset.univ.filter (fun x => ∃ z, hw z ≤ k + d ∧ M x z = true)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x _
    rintro ⟨z, hz, hMz⟩
    have hge := hM x z hMz
    omega
  rw [hempty]
  simp

/-- **Distance amplifies invisibility, low-degree (proved): `pcrank ≤ 1` when `d < Δ`.** -/
theorem highDistance_lowDeg_collapse {A : Type*} [Fintype A] (d Δ : ℕ) (M : A → (Fin a → Bool) → Bool)
    (hM : MinSupportWeight M Δ) (hlt : d < Δ) :
    pcrank (lowDegProj a d) M ≤ 1 := by
  refine le_trans (lowDeg_pcrank_le_ballMeeting d M) ?_
  have hempty : (Finset.univ.filter (fun x => ∃ z, hw z ≤ d ∧ M x z = true)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x _
    rintro ⟨z, hz, hMz⟩
    have hge := hM x z hMz
    omega
  rw [hempty]
  simp

/-- Every Boolean point has Hamming weight `≤ a`. -/
theorem hw_le (y : Fin a → Bool) : hw y ≤ a := by
  unfold hw
  calc (Finset.univ.filter (fun i => y i = true)).card
      ≤ (Finset.univ : Finset (Fin a)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = a := by rw [Finset.card_univ, Fintype.card_fin]

/-- At full order `d = a` the low-degree projection is injective (the probe ball is the whole cube). -/
theorem lowDegProj_full_injective : Function.Injective (lowDegProj a a) := by
  intro r r' h
  funext v
  have hco := congrFun h ⟨v, hw_le v⟩
  simpa [lowDegProj] using hco

/-- **The boundary, upper end (proved): at probe radius `= a` the rank is fully visible, `pcrank = crank`.**  So
between order `< Δ` (total collapse) and order `= a` (full rank) the rank turns on only once the probe radius
crosses the distance `Δ` — and the feature count `2^{N(a, k+d)}` explodes super-polynomially as the order rises
toward an expander distance `Δ = Ω(n)`. -/
theorem lowDeg_full_order_eq_crank {A : Type*} [Fintype A] (M : A → (Fin a → Bool) → Bool) :
    pcrank (lowDegProj a a) M = crank M :=
  pcrank_eq_crank_of_injective (lowDegProj a a) M lowDegProj_full_injective

end PallLean.Paper93.DeepMath.PathB.ExpanderAmplificationBoundary

#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderAmplificationBoundary.highDistance_spdp_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderAmplificationBoundary.highDistance_lowDeg_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderAmplificationBoundary.lowDeg_full_order_eq_crank
