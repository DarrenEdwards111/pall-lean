import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingCircuitLinearGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3IteratedReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundCount2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvRoundREL2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecursiveTowerSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictionCardinality

/-!
# Varying-parameter iteration of corrected switching rounds

The first corrected circuit theorem is now threaded through an actual sequence of layered collapse rounds.
Each round may use its own gate count, term bound, restriction density, and threshold; this is essential
because switching changes the next round's bottom width and clause count.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.Depth3.Layered
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCircuitLinearGap
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets

/-- Canonical coordinates for the live variables of a current restriction. -/
noncomputable def liveCoordEquiv {n : ℕ} (τ : Restriction n) :
    Fin (stars τ) ≃ ↑(freeVars τ) :=
  (Finset.equivFin (freeVars τ)).symm

/-- Lift a restriction on the canonically relabelled live coordinates back to the
ambient cube, retaining every fixing already made by `τ`. -/
noncomputable def liftLiveRestriction {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) :
    Restriction n :=
  fun v => if h : v ∈ freeVars τ
    then σ ((liveCoordEquiv τ).symm ⟨v, h⟩)
    else τ v

@[simp] theorem liftLiveRestriction_apply_live {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (i : Fin (stars τ)) :
    liftLiveRestriction τ σ (liveCoordEquiv τ i) = σ i := by
  rw [liftLiveRestriction, dif_pos (liveCoordEquiv τ i).property]
  simp

theorem liftLiveRestriction_apply_fixed {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) {v : Fin n} (hv : v ∉ freeVars τ) :
    liftLiveRestriction τ σ v = τ v := by
  rw [liftLiveRestriction, dif_neg hv]

/-- Every lifted local restriction is a genuine extension of the current subcube. -/
theorem liftLiveRestriction_extends {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) : Extends τ (liftLiveRestriction τ σ) := by
  intro v b hv
  have hfixed : v ∉ freeVars τ := by
    rw [mem_freeVars, hv]
    simp
  rw [liftLiveRestriction_apply_fixed τ σ hfixed, hv]

/-- Relabelling loses no local restriction: distinct restrictions give distinct
extensions of the current subcube. -/
theorem liftLiveRestriction_injective {n : ℕ} (τ : Restriction n) :
    Function.Injective (liftLiveRestriction τ) := by
  intro σ₁ σ₂ h
  funext i
  have hi := congrFun h (liveCoordEquiv τ i)
  simpa using hi

/-- A lifted coordinate is free exactly when its relabelled local coordinate is free. -/
theorem liftLiveRestriction_apply_eq_none_iff {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (i : Fin (stars τ)) :
    liftLiveRestriction τ σ (liveCoordEquiv τ i) = none ↔ σ i = none := by
  simp

theorem freeVars_liftLiveRestriction {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) :
    freeVars (liftLiveRestriction τ σ) =
      (freeVars σ).image (fun i => (liveCoordEquiv τ i).1) := by
  ext v
  rw [mem_freeVars, Finset.mem_image]
  constructor
  · intro hv
    have hvτ : v ∈ freeVars τ := by
      by_contra hnot
      have hfixed := liftLiveRestriction_apply_fixed τ σ hnot
      have hτne : τ v ≠ none := by
        simpa [mem_freeVars] using hnot
      exact hτne (hfixed ▸ hv)
    let i : Fin (stars τ) := (liveCoordEquiv τ).symm ⟨v, hvτ⟩
    refine ⟨i, ?_, ?_⟩
    · rw [mem_freeVars]
      rw [liftLiveRestriction, dif_pos hvτ] at hv
      simpa [i] using hv
    · simp [i]
  · rintro ⟨i, hi, rfl⟩
    rw [mem_freeVars] at hi
    simpa using hi

/-- The subcube lift preserves the number of live variables exactly. -/
@[simp] theorem stars_liftLiveRestriction {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) :
    stars (liftLiveRestriction τ σ) = stars σ := by
  unfold stars
  rw [freeVars_liftLiveRestriction, Finset.card_image_of_injective _]
  intro i j hij
  exact (liveCoordEquiv τ).injective (Subtype.ext hij)

/-- Project an ambient restriction onto the canonical coordinates of the current live set. -/
noncomputable def projectLiveRestriction {n : ℕ} (τ ρ : Restriction n) :
    Restriction (stars τ) :=
  fun i => ρ (liveCoordEquiv τ i)

@[simp] theorem projectLiveRestriction_lift {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) :
    projectLiveRestriction τ (liftLiveRestriction τ σ) = σ := by
  funext i
  simp [projectLiveRestriction]

theorem liftLiveRestriction_project_of_extends {n : ℕ} {τ ρ : Restriction n}
    (hρ : Extends τ ρ) :
    liftLiveRestriction τ (projectLiveRestriction τ ρ) = ρ := by
  funext v
  by_cases hv : v ∈ freeVars τ
  · rw [liftLiveRestriction, dif_pos hv, projectLiveRestriction]
    simp
  · rw [liftLiveRestriction_apply_fixed τ _ hv]
    have hne : τ v ≠ none := by simpa [mem_freeVars] using hv
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
    rw [hb, hρ v b hb]

/-- Restrictions on the relabelled live coordinates are in bijection with all
ambient restrictions extending the current restriction. -/
noncomputable def liveRestrictionEquiv {n : ℕ} (τ : Restriction n) :
    Restriction (stars τ) ≃ {ρ : Restriction n // Extends τ ρ} where
  toFun σ := ⟨liftLiveRestriction τ σ, liftLiveRestriction_extends τ σ⟩
  invFun ρ := projectLiveRestriction τ ρ.1
  left_inv := projectLiveRestriction_lift τ
  right_inv := by
    intro ρ
    apply Subtype.ext
    exact liftLiveRestriction_project_of_extends ρ.2

/-- The restriction-dependent circuit sequence produced by successive real `collapseRound`s. -/
def collapseSeq {n : ℕ} (K : ℕ → ℕ) (ρ : ℕ → Restriction n) (C₀ : Layered n) :
    ℕ → Layered n
  | 0 => C₀
  | i + 1 => collapseRound (K i) (ρ i) (collapseSeq K ρ C₀ i)

theorem collapseSeq_succ {n : ℕ} (K : ℕ → ℕ) (ρ : ℕ → Restriction n)
    (C₀ : Layered n) (i : ℕ) :
    collapseSeq K ρ C₀ (i + 1) =
      collapseRound (K i) (ρ i) (collapseSeq K ρ C₀ i) := rfl

/-- The exact per-round data needed to connect a genuine circuit bad set to the current layered tower. -/
structure GoodRound {n : ℕ} (K threshold : ℕ) (C : Layered n) (ρ : Restriction n) where
  G : ℕ
  gates : Fin G → List (Clause n)
  enumerates : ∀ cs, cs ∈ dualBottomGates C ↔ ∃ g, gates g = cs
  stars_eq : stars ρ = K
  good : ρ ∉ circuitBad gates K threshold

theorem GoodRound.shallows {n K threshold : ℕ} {C : Layered n} {ρ : Restriction n}
    (h : GoodRound K threshold C ρ) : Shallows K ρ threshold C :=
  good_implies_layered_shallows C h.gates K threshold h.enumerates ρ h.stars_eq h.good

theorem GoodRound.equivOn {n K threshold : ℕ} {C : Layered n} {ρ : Restriction n}
    (h : GoodRound K threshold C ρ) : EquivOn ρ C (collapseRound K ρ C) :=
  collapseRound_EquivOn K (by rw [h.stars_eq]) C

/-- A survivor-style round separates the collapse fuel from the number of surviving variables. -/
structure AnalyticRound {n : ℕ} (F threshold : ℕ) (C : Layered n) (ρ : Restriction n) where
  stars_le : stars ρ ≤ F
  shallow : Shallows F ρ threshold C

theorem AnalyticRound.equivOn {n F threshold : ℕ} {C : Layered n} {ρ : Restriction n}
    (h : AnalyticRound F threshold C ρ) : EquivOn ρ C (collapseRound F ρ C) :=
  collapseRound_EquivOn F h.stars_le C

/-- The relative two-threshold switching theorem produces an actual analytic round extending the
current subcube.  The survivor target `s` and the constant collapse depth `t` are independent. -/
theorem exists_analyticRound_REL2 {n : ℕ} {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp3 : 3 * p ≤ 1) {w F s t m : ℕ} [NeZero w] [NeZero m]
    (hs : 2 ≤ s) (hF : n ≤ F) (C : Layered n) (τ : Restriction n)
    (hbw : BottomWidth w C) (hmc : BottomCount m C)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hgap : 7 * (s : ℚ) < (stars τ : ℚ) * p)
    (hh2 : ((bottomGatesG C).card : ℚ)
      * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ t
        / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)))) < 1 / 2) :
    ∃ ρ : Restriction n, Extends τ ρ ∧ s ≤ stars ρ ∧ AnalyticRound F t C ρ := by
  obtain ⟨ρ, hext, hstars, hle, hsh⟩ :=
    hsurv_REL2_round hp0 hp1 hp3 hs hF C τ hbw hmc hr1 hgap hh2
  exact ⟨ρ, hext, hstars, ⟨hle, hsh⟩⟩

def concreteM : ℕ := 1000000
def concreteT : ℕ := 30
def concreteTerms : ℕ := concreteM * 2 ^ concreteT
def concreteQ : ℕ := 16 * concreteT * concreteTerms
def concreteB : ℕ := 8 * concreteQ
def concreteSched (d r i : ℕ) : ℕ := r * concreteB ^ (d - i)
def concreteG : ℕ := 2 * concreteM
def concreteScale : ℕ := 1000 * (concreteG * (concreteT * concreteTerms))

/-- A fully numerical later-round certificate.  These constants are closed under collapse:
width `30`, at most `10^6` bottom gates, and at most `10^6·2^30` clauses per gate. -/
theorem exists_concreteAnalyticRound {n F s : ℕ} (hs : 2 ≤ s) (hF : n ≤ F)
    (C : Layered n) (τ : Restriction n)
    (hbw : BottomWidth concreteT C) (hmc : BottomCount concreteTerms C)
    (hcnt : (bottomGates C).length ≤ concreteM)
    (hgap : 7 * (s : ℚ) < (stars τ : ℚ) * (1 / concreteQ)) :
    ∃ ρ : Restriction n, Extends τ ρ ∧ s ≤ stars ρ ∧
      AnalyticRound F concreteT C ρ := by
  haveI : NeZero concreteT := ⟨by norm_num [concreteT]⟩
  haveI : NeZero concreteTerms := ⟨by norm_num [concreteTerms, concreteM, concreteT]⟩
  apply exists_analyticRound_REL2 (p := 1 / concreteQ) (by positivity) (by norm_num [concreteQ,
    concreteT, concreteTerms, concreteM]) (by norm_num [concreteQ, concreteT, concreteTerms, concreteM])
    hs hF C τ hbw hmc
  · norm_num [concreteQ, concreteT, concreteTerms, concreteM]
  · exact hgap
  · have hcard : ((bottomGatesG C).card : ℚ) ≤ 2 * concreteM := by
      exact_mod_cast le_trans (bottomGatesG_card_le C) (by omega : 2 * (bottomGates C).length ≤ 2 * concreteM)
    have hcap0 : (0 : ℚ) ≤
        (((2 * (1 / concreteQ) / (1 - 1 / concreteQ)) *
          (2 * (concreteT : ℚ) * (concreteTerms : ℚ))) ^ concreteT /
          (1 - (2 * (1 / concreteQ) / (1 - 1 / concreteQ)) *
            (2 * (concreteT : ℚ) * (concreteTerms : ℚ)))) := by
      norm_num [concreteQ, concreteT, concreteTerms, concreteM]
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcard hcap0) ?_
    norm_num [concreteQ, concreteT, concreteTerms, concreteM]

/-- The concrete invariant is closed under the real collapse transformation. -/
theorem concreteAnalyticRound_closed {n F : ℕ} {C : Layered n} {ρ : Restriction n}
    (hround : AnalyticRound F concreteT C ρ) (hne : NonEmptyGates C)
    (hcnt : (bottomGates C).length ≤ concreteM) :
    BottomWidth concreteT (collapseRound F ρ C) ∧
      BottomCount concreteTerms (collapseRound F ρ C) ∧
      (bottomGates (collapseRound F ρ C)).length ≤ concreteM := by
  refine ⟨collapseRound_BottomWidth F ρ hround.shallow, ?_,
    le_trans (collapseRound_count_le F ρ hne) hcnt⟩
  simpa [concreteTerms] using
    collapseRound_BottomCount F ρ (by norm_num [concreteM]) hne hround.shallow hcnt

/-- Two genuinely nested concrete rounds, including the actual depth-four-to-DNF collapse and
semantic composition on the final subcube. -/
theorem concreteTwoRoundChain {n F s₁ s₂ : ℕ} (hs₁ : 2 ≤ s₁) (hs₂ : 2 ≤ s₂)
    (hF : n ≤ F) (C₀ : Layered n) (τ₀ : Restriction n) (hAlt : AltO 4 C₀)
    (hbw : BottomWidth concreteT C₀) (hmc : BottomCount concreteTerms C₀)
    (hcnt : (bottomGates C₀).length ≤ concreteM)
    (hgap₁ : 7 * (s₁ : ℚ) < (stars τ₀ : ℚ) * (1 / concreteQ))
    (hgap₂ : 7 * (s₂ : ℚ) < (s₁ : ℚ) * (1 / concreteQ)) :
    ∃ ρ₁ ρ₂ : Restriction n, ∃ C₁ C₂ : Layered n,
      Extends τ₀ ρ₁ ∧ Extends ρ₁ ρ₂ ∧ s₂ ≤ stars ρ₂ ∧
      AnalyticRound F concreteT C₀ ρ₁ ∧ AnalyticRound F concreteT C₁ ρ₂ ∧
      C₁ = collapseRound F ρ₁ C₀ ∧ C₂ = collapseRound F ρ₂ C₁ ∧
      (∃ D : List (Clause n), C₂ = Layered.dnf D) ∧
      ∀ x, DTree.agreeRestriction ρ₂ x → Reduces x C₀ C₂ := by
  obtain ⟨ρ₁, hext₁, hstars₁, hr₁⟩ :=
    exists_concreteAnalyticRound hs₁ hF C₀ τ₀ hbw hmc hcnt hgap₁
  let C₁ := collapseRound F ρ₁ C₀
  have hb₁ := concreteAnalyticRound_closed hr₁ (AltO_NonEmptyGates hAlt) hcnt
  have hgap₂' : 7 * (s₂ : ℚ) < (stars ρ₁ : ℚ) * (1 / concreteQ) := by
    have hp : (0 : ℚ) ≤ 1 / concreteQ := by positivity
    have hs : (s₁ : ℚ) ≤ stars ρ₁ := by exact_mod_cast hstars₁
    exact lt_of_lt_of_le hgap₂ (mul_le_mul_of_nonneg_right hs hp)
  obtain ⟨ρ₂, hext₂, hstars₂, hr₂⟩ :=
    exists_concreteAnalyticRound hs₂ hF C₁ ρ₁ hb₁.1 hb₁.2.1 hb₁.2.2 hgap₂'
  let C₂ := collapseRound F ρ₂ C₁
  have hAlt₁ : AltO 3 C₁ := by
    simpa [C₁] using collapseRound_AltO F ρ₁ hAlt
  have hAlt₂ : AltO 2 C₂ := by
    simpa [C₂] using collapseRound_AltO F ρ₂ hAlt₁
  obtain ⟨D, hD⟩ := AltO_two_dnf hAlt₂
  refine ⟨ρ₁, ρ₂, C₁, C₂, hext₁, hext₂, hstars₂, hr₁, hr₂, rfl, rfl,
    ⟨D, hD⟩, ?_⟩
  intro x hx
  have hx₁ := agreeRestriction_of_extends hext₂ hx
  exact (Reduces.head hr₁.equivOn hx₁).trans (Reduces.head hr₂.equivOn hx)

/-- Arbitrary-depth recursive nesting of the concrete closed switching round. -/
theorem concreteDepthChain {n F d : ℕ} (s : ℕ → ℕ)
    (hmono : ∀ i, s (i + 1) ≤ s i) (hpos : ∀ i < d, 2 ≤ s (i + 1))
    (hgap : ∀ i < d, 7 * (s (i + 1) : ℚ) < (s i : ℚ) * (1 / concreteQ))
    (hF : n ≤ F) (C₀ : Layered n) (τ₀ : Restriction n) (hAlt : AltO (d + 2) C₀)
    (hbw : BottomWidth concreteT C₀) (hmc : BottomCount concreteTerms C₀)
    (hcnt : (bottomGates C₀).length ≤ concreteM) (hstars : s 0 ≤ stars τ₀) :
    ∃ Cd : Layered n, ∃ σ : Restriction n,
      (∃ D : List (Clause n), Cd = Layered.dnf D) ∧ Extends τ₀ σ ∧ s d ≤ stars σ ∧
      BottomWidth concreteT Cd ∧ BottomCount concreteTerms Cd ∧
      (bottomGates Cd).length ≤ concreteM ∧
      ∀ x, DTree.agreeRestriction σ x → Reduces x C₀ Cd := by
  let Valid : ℕ → Layered n → Prop := fun i C =>
    (if i ≤ d then AltO (d + 2 - i) C else True) ∧ BottomWidth concreteT C ∧
      BottomCount concreteTerms C ∧ (bottomGates C).length ≤ concreteM
  have hV₀ : Valid 0 C₀ := by
    refine ⟨?_, hbw, hmc, hcnt⟩
    simp only [Nat.zero_le, if_true, Nat.sub_zero]
    exact hAlt
  have horacle : ∀ (i : ℕ) (C : Layered n) (τ : Restriction n), Valid i C →
      s i ≤ stars τ → ∃ (C' : Layered n) (ρ : Restriction n),
        Extends τ ρ ∧ s (i + 1) ≤ stars ρ ∧ EquivOn ρ C C' ∧ Valid (i + 1) C' := by
    intro i C τ hV hsτ
    obtain ⟨hshape, hbwC, hmcC, hcntC⟩ := hV
    by_cases hid : i < d
    · have hgap' : 7 * (s (i + 1) : ℚ) < (stars τ : ℚ) * (1 / concreteQ) := by
        have hp : (0 : ℚ) ≤ 1 / concreteQ := by positivity
        have hsQ : (s i : ℚ) ≤ stars τ := by exact_mod_cast hsτ
        exact lt_of_lt_of_le (hgap i hid) (mul_le_mul_of_nonneg_right hsQ hp)
      obtain ⟨ρ, hext, hsurv, hr⟩ :=
        exists_concreteAnalyticRound (hpos i hid) hF C τ hbwC hmcC hcntC hgap'
      have hshape₀ : AltO (d + 2 - i) C := by
        simpa [if_pos (le_of_lt hid)] using hshape
      have hshape' : AltO (d + 2 - (i + 1)) (collapseRound F ρ C) := by
        have hk : d + 2 - i = (d - 1 - i) + 3 := by omega
        rw [hk] at hshape₀
        have hred := collapseRound_AltO F ρ hshape₀
        have hk' : d + 2 - (i + 1) = (d - 1 - i) + 2 := by omega
        rwa [hk']
      have hb := concreteAnalyticRound_closed hr (AltO_NonEmptyGates hshape₀) hcntC
      refine ⟨collapseRound F ρ C, ρ, hext, hsurv, hr.equivOn, ?_, hb.1, hb.2.1, hb.2.2⟩
      rw [if_pos (by omega : i + 1 ≤ d)]
      exact hshape'
    · refine ⟨C, τ, fun _ _ h => h, le_trans (hmono i) hsτ, ?_, ?_, hbwC, hmcC, hcntC⟩
      · intro x _; rfl
      · rw [if_neg (by omega : ¬ i + 1 ≤ d)]
        trivial
  obtain ⟨Cd, σ, hVd, hext, hsd, hred⟩ :=
    recursive_tower_chain_surv_seq Valid s C₀ τ₀ hV₀ hstars horacle d
  obtain ⟨hshape, hbwD, hmcD, hcntD⟩ := hVd
  rw [if_pos (le_refl d), show d + 2 - d = 2 by omega] at hshape
  obtain ⟨D, hD⟩ := AltO_two_dnf hshape
  exact ⟨Cd, σ, ⟨D, hD⟩, hext, hsd, hbwD, hmcD, hcntD, hred⟩

/-- The explicit base-`8·Q` geometric schedule leaves `r` live variables after `d` rounds. -/
theorem concreteGeometricDepthChain {n F d r : ℕ} (hr : 2 ≤ r) (hF : n ≤ F)
    (C₀ : Layered n) (τ₀ : Restriction n) (hAlt : AltO (d + 2) C₀)
    (hbw : BottomWidth concreteT C₀) (hmc : BottomCount concreteTerms C₀)
    (hcnt : (bottomGates C₀).length ≤ concreteM)
    (hstars : concreteSched d r 0 ≤ stars τ₀) :
    ∃ Cd : Layered n, ∃ σ : Restriction n,
      (∃ D : List (Clause n), Cd = Layered.dnf D) ∧ Extends τ₀ σ ∧ r ≤ stars σ ∧
      BottomWidth concreteT Cd ∧ BottomCount concreteTerms Cd ∧
      (bottomGates Cd).length ≤ concreteM ∧
      ∀ x, DTree.agreeRestriction σ x → Reduces x C₀ Cd := by
  have hmono : ∀ i, concreteSched d r (i + 1) ≤ concreteSched d r i := by
    intro i
    unfold concreteSched
    gcongr
    all_goals first | omega | norm_num [concreteB, concreteQ, concreteT, concreteTerms, concreteM]
  have hpos : ∀ i < d, 2 ≤ concreteSched d r (i + 1) := by
    intro i hi
    unfold concreteSched
    exact le_trans hr (Nat.le_mul_of_pos_right r
      (pow_pos (by norm_num [concreteB, concreteQ, concreteT, concreteTerms, concreteM]) _))
  have hgap : ∀ i < d,
      7 * (concreteSched d r (i + 1) : ℚ) <
        (concreteSched d r i : ℚ) * (1 / concreteQ) := by
    intro i hi
    unfold concreteSched
    have he : d - i = (d - (i + 1)) + 1 := by omega
    rw [he, pow_succ]
    push_cast
    have hrQ : (0 : ℚ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr)
    have hBQ : (0 : ℚ) < concreteB := by
      norm_num [concreteB, concreteQ, concreteT, concreteTerms, concreteM]
    have hx : (0 : ℚ) < (r : ℚ) * (concreteB : ℚ) ^ (d - (i + 1)) :=
      mul_pos hrQ (pow_pos hBQ _)
    have hratio : (7 : ℚ) < (concreteB : ℚ) * (1 / concreteQ) := by
      norm_num [concreteB, concreteQ, concreteT, concreteTerms, concreteM]
    nlinarith
  have h := concreteDepthChain (concreteSched d r) hmono hpos hgap hF C₀ τ₀ hAlt
    hbw hmc hcnt hstars
  simpa [concreteSched] using h

/-- A fully deterministic, fully charged later-round bucket at the closed invariant constants. -/
theorem concreteDeterministicRoundGap (r : ℕ) [NeZero r]
    (gates : Fin concreteG → List (Clause (concreteScale * r)))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms) :
    ∃ i : Fin ((concreteScale * r).choose (20 * r)),
      goodBadWork (concreteScale * r) (concreteScale * r - 20 * r)
        (2 ^ (concreteScale * r - 20 * r))
        (concreteBadCount (K := 20 * r) (circuitBad gates (20 * r) (10 * r)) i)
        (10 * r - 1) ≤ 2 ^ (concreteScale * r - 9 * r) := by
  letI : NeZero concreteG := ⟨by norm_num [concreteG, concreteM]⟩
  letI : NeZero concreteT := ⟨by norm_num [concreteT]⟩
  letI : NeZero concreteTerms := ⟨by norm_num [concreteTerms, concreteM, concreteT]⟩
  simpa [concreteScale, concreteG] using
    wideCircuitLinearGap_selectedBucket_activeGap concreteG concreteT concreteTerms r gates hwidth hterms

/-- A chain of genuine good rounds drops an alternating tower by one level per round. -/
theorem collapseSeq_AltO {n d : ℕ} (K : ℕ → ℕ)
    (ρ : ℕ → Restriction n) (C₀ : Layered n) (hAlt : AltO (d + 2) C₀) :
    ∀ i j, i + j = d → AltO (j + 2) (collapseSeq K ρ C₀ i) := by
  intro i
  induction i with
  | zero =>
      intro j hj
      simpa [show j = d by omega] using hAlt
  | succ i ih =>
      intro j hj
      have hid : i < d := by omega
      have hshape := ih (j + 1) (by omega)
      rw [show j + 1 + 2 = j + 3 by omega] at hshape
      have hnext := collapseRound_AltO (K i) (ρ i) hshape
      simpa [collapseSeq_succ] using hnext

/-- After exactly `d` good rounds, the real tower is a bottom DNF. -/
theorem collapseSeq_terminal_dnf {n d : ℕ} (K : ℕ → ℕ)
    (ρ : ℕ → Restriction n) (C₀ : Layered n) (hAlt : AltO (d + 2) C₀) :
    ∃ D : List (Clause n), collapseSeq K ρ C₀ d = Layered.dnf D := by
  have h := collapseSeq_AltO K ρ C₀ hAlt d 0 (by omega)
  simpa using AltO_two_dnf h

/-- Every round is an actual subcube equivalence on its own restriction. -/
theorem collapseSeq_round_equiv {n d : ℕ} (K threshold : ℕ → ℕ)
    (ρ : ℕ → Restriction n) (C₀ : Layered n)
    (hround : ∀ i < d, GoodRound (K i) (threshold i) (collapseSeq K ρ C₀ i) (ρ i)) :
    ∀ i < d, EquivOn (ρ i) (collapseSeq K ρ C₀ i) (collapseSeq K ρ C₀ (i + 1)) := by
  intro i hi
  rw [collapseSeq_succ]
  exact (hround i hi).equivOn

/-- Analytic survivor rounds drive the same real collapse sequence without requiring an exact-star
bucket certificate. -/
theorem collapseSeq_round_equiv_analytic {n d : ℕ} (F threshold : ℕ → ℕ)
    (ρ : ℕ → Restriction n) (C₀ : Layered n)
    (hround : ∀ i < d, AnalyticRound (F i) (threshold i) (collapseSeq F ρ C₀ i) (ρ i)) :
    ∀ i < d, EquivOn (ρ i) (collapseSeq F ρ C₀ i) (collapseSeq F ρ C₀ (i + 1)) := by
  intro i hi
  rw [collapseSeq_succ]
  exact (hround i hi).equivOn

/-- Every consumed round has the width promised by its own varying threshold. -/
theorem collapseSeq_round_width {n d : ℕ} (K threshold : ℕ → ℕ)
    (ρ : ℕ → Restriction n) (C₀ : Layered n)
    (hround : ∀ i < d, GoodRound (K i) (threshold i) (collapseSeq K ρ C₀ i) (ρ i)) :
    ∀ i < d, BottomWidth (threshold i) (collapseSeq K ρ C₀ (i + 1)) := by
  intro i hi
  rw [collapseSeq_succ]
  exact collapseRound_BottomWidth (K i) (ρ i) (hround i hi).shallows

theorem collapseSeq_round_width_analytic {n d : ℕ} (F threshold : ℕ → ℕ)
    (ρ : ℕ → Restriction n) (C₀ : Layered n)
    (hround : ∀ i < d, AnalyticRound (F i) (threshold i) (collapseSeq F ρ C₀ i) (ρ i)) :
    ∀ i < d, BottomWidth (threshold i) (collapseSeq F ρ C₀ (i + 1)) := by
  intro i hi
  rw [collapseSeq_succ]
  exact collapseRound_BottomWidth (F i) (ρ i) (hround i hi).shallow

/-- The real collapse sequence never increases its number of bottom gates. -/
theorem collapseSeq_gateCount_le {n d : ℕ} (K : ℕ → ℕ)
    (ρ : ℕ → Restriction n) (C₀ : Layered n) (hAlt : AltO (d + 2) C₀) :
    ∀ i ≤ d, (bottomGates (collapseSeq K ρ C₀ i)).length ≤ (bottomGates C₀).length := by
  intro i hi
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
      have hid : i < d := by omega
      have hshape : AltO ((d - i) + 2) (collapseSeq K ρ C₀ i) :=
        collapseSeq_AltO K ρ C₀ hAlt i (d - i) (by omega)
      rw [collapseSeq_succ]
      exact le_trans (collapseRound_count_le (K i) (ρ i) (AltO_NonEmptyGates hshape))
        (ih (by omega))

/-- **The generated later-round parameters are structural invariants, not assumptions.**  If the
initial tower has at most `M` bottom gates, round `i` produces width at most `threshold i`, at most
`M·2^(threshold i)` clauses per bottom gate, and still at most `M` bottom gates. -/
theorem collapseSeq_round_structuralBounds {n d M : ℕ} (K threshold : ℕ → ℕ)
    (ρ : ℕ → Restriction n) (C₀ : Layered n) (hAlt : AltO (d + 2) C₀)
    (hround : ∀ i < d, GoodRound (K i) (threshold i) (collapseSeq K ρ C₀ i) (ρ i))
    (hM : (bottomGates C₀).length ≤ M) :
    ∀ i < d,
      BottomWidth (threshold i) (collapseSeq K ρ C₀ (i + 1)) ∧
      BottomCount (M * 2 ^ threshold i) (collapseSeq K ρ C₀ (i + 1)) ∧
      (bottomGates (collapseSeq K ρ C₀ (i + 1))).length ≤ M := by
  intro i hi
  have hshape : AltO ((d - i) + 2) (collapseSeq K ρ C₀ i) :=
    collapseSeq_AltO K ρ C₀ hAlt i (d - i) (by omega)
  have hcnt : (bottomGates (collapseSeq K ρ C₀ i)).length ≤ M :=
    le_trans (collapseSeq_gateCount_le K ρ C₀ hAlt i (by omega)) hM
  have hM1 : 1 ≤ M := le_trans (bottomGates_length_pos_AltO hshape) hcnt
  rw [collapseSeq_succ]
  refine ⟨collapseRound_BottomWidth (K i) (ρ i) (hround i hi).shallows,
    collapseRound_BottomCount (K i) (ρ i) hM1 (AltO_NonEmptyGates hshape)
      (hround i hi).shallows hcnt, ?_⟩
  exact le_trans (collapseRound_count_le (K i) (ρ i) (AltO_NonEmptyGates hshape)) hcnt

theorem collapseSeq_round_structuralBounds_analytic {n d M : ℕ} (F threshold : ℕ → ℕ)
    (ρ : ℕ → Restriction n) (C₀ : Layered n) (hAlt : AltO (d + 2) C₀)
    (hround : ∀ i < d, AnalyticRound (F i) (threshold i) (collapseSeq F ρ C₀ i) (ρ i))
    (hM : (bottomGates C₀).length ≤ M) :
    ∀ i < d,
      BottomWidth (threshold i) (collapseSeq F ρ C₀ (i + 1)) ∧
      BottomCount (M * 2 ^ threshold i) (collapseSeq F ρ C₀ (i + 1)) ∧
      (bottomGates (collapseSeq F ρ C₀ (i + 1))).length ≤ M := by
  intro i hi
  have hshape : AltO ((d - i) + 2) (collapseSeq F ρ C₀ i) :=
    collapseSeq_AltO F ρ C₀ hAlt i (d - i) (by omega)
  have hcnt : (bottomGates (collapseSeq F ρ C₀ i)).length ≤ M :=
    le_trans (collapseSeq_gateCount_le F ρ C₀ hAlt i (by omega)) hM
  have hM1 : 1 ≤ M := le_trans (bottomGates_length_pos_AltO hshape) hcnt
  rw [collapseSeq_succ]
  refine ⟨collapseRound_BottomWidth (F i) (ρ i) (hround i hi).shallow,
    collapseRound_BottomCount (F i) (ρ i) hM1 (AltO_NonEmptyGates hshape)
      (hround i hi).shallow hcnt, ?_⟩
  exact le_trans (collapseRound_count_le (F i) (ρ i) (AltO_NonEmptyGates hshape)) hcnt

/-- **Multi-round semantic composition.**  On the final nested subcube, the original circuit reduces
to the actual `d`-round collapsed circuit, hence their evaluations agree everywhere on that subcube. -/
theorem collapseSeq_reduces_final {n d : ℕ} (K threshold : ℕ → ℕ)
    (ρ : ℕ → Restriction n) (C₀ : Layered n)
    (hround : ∀ i < d, GoodRound (K i) (threshold i) (collapseSeq K ρ C₀ i) (ρ i))
    (hnest : ∀ i < d, Extends (ρ i) (ρ (i + 1))) :
    ∀ x, DTree.agreeRestriction (ρ d) x →
      Reduces x C₀ (collapseSeq K ρ C₀ d) := by
  intro x hx
  induction d with
  | zero => exact Reduces.refl _
  | succ d ih =>
      have hxprev : DTree.agreeRestriction (ρ d) x :=
        agreeRestriction_of_extends (hnest d (by omega)) hx
      have hprev : Reduces x C₀ (collapseSeq K ρ C₀ d) :=
        ih (fun i hi => hround i (by omega)) (fun i hi => hnest i (by omega)) hxprev
      have heq := collapseSeq_round_equiv K threshold ρ C₀ hround d (by omega)
      exact hprev.trans (Reduces.head heq hxprev)

/-- Nested analytic survivor rounds compose semantically through the full collapse sequence. -/
theorem collapseSeq_reduces_final_analytic {n d : ℕ} (F threshold : ℕ → ℕ)
    (ρ : ℕ → Restriction n) (C₀ : Layered n)
    (hround : ∀ i < d, AnalyticRound (F i) (threshold i) (collapseSeq F ρ C₀ i) (ρ i))
    (hnest : ∀ i < d, Extends (ρ i) (ρ (i + 1))) :
    ∀ x, DTree.agreeRestriction (ρ d) x → Reduces x C₀ (collapseSeq F ρ C₀ d) := by
  intro x hx
  induction d with
  | zero => exact Reduces.refl _
  | succ d ih =>
      have hxprev : DTree.agreeRestriction (ρ d) x :=
        agreeRestriction_of_extends (hnest d (by omega)) hx
      have hprev : Reduces x C₀ (collapseSeq F ρ C₀ d) :=
        ih (fun i hi => hround i (by omega)) (fun i hi => hnest i (by omega)) hxprev
      have heq := collapseSeq_round_equiv_analytic F threshold ρ C₀ hround d (by omega)
      exact hprev.trans (Reduces.head heq hxprev)

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.collapseSeq_terminal_dnf
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.collapseSeq_reduces_final
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.collapseSeq_gateCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.collapseSeq_round_structuralBounds
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_analyticRound_REL2
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.collapseSeq_reduces_final_analytic
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.collapseSeq_round_structuralBounds_analytic
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_concreteAnalyticRound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteAnalyticRound_closed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteTwoRoundChain
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteDepthChain
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteGeometricDepthChain
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteDeterministicRoundGap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.stars_liftLiveRestriction
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.liveRestrictionEquiv
