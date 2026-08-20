import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingCircuitLinearGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3IteratedReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundCount2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvRoundREL2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecursiveTowerSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictionCardinality
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSkipCollision
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GeomTail

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
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermFamily
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingTailIntegerBridge
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingFixedTermLinearGap

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

/-- Relabel a literal whose variable is live in `τ`; fixed-coordinate literals
are removed after the usual dead-term filtering. -/
noncomputable def localizeLiveLiteral {n : ℕ} (τ : Restriction n) :
    Rung4Literal n → Option (Rung4Literal (stars τ))
  | Rung4Literal.pos v =>
      if h : v ∈ freeVars τ then
        some (Rung4Literal.pos ((liveCoordEquiv τ).symm ⟨v, h⟩))
      else none
  | Rung4Literal.neg v =>
      if h : v ∈ freeVars τ then
        some (Rung4Literal.neg ((liveCoordEquiv τ).symm ⟨v, h⟩))
      else none

/-- Extend an assignment on the live-coordinate cube to an ambient assignment,
using the values fixed by `τ` off the live set. -/
noncomputable def liftLiveAssignment {n : ℕ} (τ : Restriction n)
    (x : Fin (stars τ) → Bool) : Fin n → Bool :=
  fun v => if h : v ∈ freeVars τ
    then x ((liveCoordEquiv τ).symm ⟨v, h⟩)
    else (τ v).getD false

theorem liftLiveAssignment_agrees {n : ℕ} (τ : Restriction n)
    (x : Fin (stars τ) → Bool) :
    DTree.agreeRestriction τ (liftLiveAssignment τ x) := by
  intro v b hv
  have hfixed : v ∉ freeVars τ := by
    rw [mem_freeVars, hv]
    simp
  rw [liftLiveAssignment, dif_neg hfixed, hv]
  simp

@[simp] theorem liftLiveAssignment_apply_live {n : ℕ} (τ : Restriction n)
    (x : Fin (stars τ) → Bool) (i : Fin (stars τ)) :
    liftLiveAssignment τ x (liveCoordEquiv τ i) = x i := by
  rw [liftLiveAssignment, dif_pos (liveCoordEquiv τ i).property]
  simp

theorem localizeLiveLiteral_eval {n : ℕ} (τ : Restriction n)
    (x : Fin (stars τ) → Bool) (l : Rung4Literal n)
    (l' : Rung4Literal (stars τ)) (h : localizeLiveLiteral τ l = some l') :
    Rung4Literal.eval l' x = Rung4Literal.eval l (liftLiveAssignment τ x) := by
  cases l with
  | pos v =>
      simp only [localizeLiveLiteral] at h
      split at h
      · next hv =>
        cases h
        simp [Rung4Literal.eval, liftLiveAssignment, hv]
      · simp at h
  | neg v =>
      simp only [localizeLiveLiteral] at h
      split at h
      · next hv =>
        cases h
        simp [Rung4Literal.eval, liftLiveAssignment, hv]
      · simp at h

theorem localizeLiveLiteral_fixedVal {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (l : Rung4Literal n)
    (l' : Rung4Literal (stars τ)) (h : localizeLiveLiteral τ l = some l') :
    litFixedVal σ l' = litFixedVal (liftLiveRestriction τ σ) l := by
  cases l with
  | pos v =>
      simp only [localizeLiveLiteral] at h
      split at h
      · next hv =>
        cases h
        simp [litFixedVal, liftLiveRestriction, hv]
      · simp at h
  | neg v =>
      simp only [localizeLiveLiteral] at h
      split at h
      · next hv =>
        cases h
        simp [litFixedVal, liftLiveRestriction, hv]
      · simp at h

theorem localizeLiveLiteral_litTrue {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (l : Rung4Literal n)
    (l' : Rung4Literal (stars τ)) (h : localizeLiveLiteral τ l = some l') :
    litTrue σ l' = litTrue (liftLiveRestriction τ σ) l := by
  unfold litTrue
  rw [localizeLiveLiteral_fixedVal τ σ l l' h]

theorem localizeLiveLiteral_litFree {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (l : Rung4Literal n)
    (l' : Rung4Literal (stars τ)) (h : localizeLiveLiteral τ l = some l') :
    litFree σ l' = litFree (liftLiveRestriction τ σ) l := by
  unfold litFree
  rw [localizeLiveLiteral_fixedVal τ σ l l' h]

theorem localizeLiveLiteral_litFalse {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (l : Rung4Literal n)
    (l' : Rung4Literal (stars τ)) (h : localizeLiveLiteral τ l = some l') :
    litFalse σ l' = litFalse (liftLiveRestriction τ σ) l := by
  unfold litFalse
  rw [localizeLiveLiteral_fixedVal τ σ l l' h]

theorem litKilled_eq_litFalse {n : ℕ} (τ : Restriction n) (l : Rung4Literal n) :
    DTree.litKilled τ l = litFalse τ l := by
  cases l with
  | pos v => cases h : τ v with
    | none => simp [DTree.litKilled, litFalse, litFixedVal, h]
    | some b => cases b <;> simp [DTree.litKilled, litFalse, litFixedVal, h]
  | neg v => cases h : τ v with
    | none => simp [DTree.litKilled, litFalse, litFixedVal, h]
    | some b => cases b <;> simp [DTree.litKilled, litFalse, litFixedVal, h]

theorem clauseLive_eq_not_termFalsified {n : ℕ} (τ : Restriction n) (T : Clause n) :
    DTree.clauseLive τ T = !termFalsified τ T := by
  unfold DTree.clauseLive termFalsified
  congr 2
  funext l
  exact litKilled_eq_litFalse τ l

theorem localizeLiveLits_all_eval {n : ℕ} (τ : Restriction n)
    (x : Fin (stars τ) → Bool) : ∀ (ls : List (Rung4Literal n)),
    (∀ l ∈ ls, DTree.litKilled τ l = false) →
    (ls.filterMap (localizeLiveLiteral τ)).all
        (fun l => Rung4Literal.eval l x) =
      ls.all (fun l => Rung4Literal.eval l (liftLiveAssignment τ x)) := by
  intro ls
  induction ls with
  | nil => simp
  | cons l ls ih =>
      intro hkill
      have hhead := hkill l (by simp)
      have htail : ∀ q ∈ ls, DTree.litKilled τ q = false :=
        fun q hq => hkill q (by simp [hq])
      cases l with
      | pos v =>
          by_cases hv : v ∈ freeVars τ
          · simp only [List.filterMap_cons, localizeLiveLiteral, dif_pos hv,
              List.all_cons]
            rw [ih htail]
            simp [Rung4Literal.eval, liftLiveAssignment, hv]
          · have hfree : DTree.freeLit τ (Rung4Literal.pos v) = false := by
              simp [DTree.freeLit, mem_freeVars] at hv ⊢
              exact hv
            have htrue := DTree.fixed_lit_true τ (liftLiveAssignment τ x)
              (Rung4Literal.pos v) (liftLiveAssignment_agrees τ x) hfree hhead
            simp only [List.filterMap_cons, localizeLiveLiteral, dif_neg hv]
            rw [ih htail]
            simp [htrue]
      | neg v =>
          by_cases hv : v ∈ freeVars τ
          · simp only [List.filterMap_cons, localizeLiveLiteral, dif_pos hv,
              List.all_cons]
            rw [ih htail]
            simp [Rung4Literal.eval, liftLiveAssignment, hv]
          · have hfree : DTree.freeLit τ (Rung4Literal.neg v) = false := by
              simp [DTree.freeLit, mem_freeVars] at hv ⊢
              exact hv
            have htrue := DTree.fixed_lit_true τ (liftLiveAssignment τ x)
              (Rung4Literal.neg v) (liftLiveAssignment_agrees τ x) hfree hhead
            simp only [List.filterMap_cons, localizeLiveLiteral, dif_neg hv]
            rw [ih htail]
            simp [htrue]
/-- A clause transported to the live-coordinate cube. -/
noncomputable def localizeLiveClause {n : ℕ} (τ : Restriction n) (T : Clause n) :
    Clause (stars τ) :=
  ⟨T.lits.filterMap (localizeLiveLiteral τ)⟩

theorem localizeLiveClause_eval {n : ℕ} (τ : Restriction n)
    (x : Fin (stars τ) → Bool) (T : Clause n)
    (hlive : DTree.clauseLive τ T = true) :
    (localizeLiveClause τ T).lits.all (fun l => Rung4Literal.eval l x) =
      T.lits.all (fun l => Rung4Literal.eval l (liftLiveAssignment τ x)) := by
  apply localizeLiveLits_all_eval
  intro l hl
  by_contra hk
  rw [Bool.not_eq_false] at hk
  have hany : T.lits.any (DTree.litKilled τ) = true :=
    List.any_eq_true.mpr ⟨l, hl, hk⟩
  simp [DTree.clauseLive, hany] at hlive

/-- Free-literal filtering commutes with localization, including list order.  This
is the selector-order invariant used by the canonical decision tree. -/
theorem localizeLiveClause_freeLits {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (T : Clause n) :
    freeLits σ (localizeLiveClause τ T) =
      (freeLits (liftLiveRestriction τ σ) T).filterMap
        (localizeLiveLiteral τ) := by
  unfold localizeLiveClause freeLits
  induction T.lits with
  | nil => simp
  | cons l ls ih =>
      cases hloc : localizeLiveLiteral τ l with
      | some l' =>
          have hs := localizeLiveLiteral_litFree τ σ l l' hloc
          cases hb : litFree σ l' <;> simp [hloc, hb, hb ▸ hs, ih]
      | none =>
          have hfixed : litFree (liftLiveRestriction τ σ) l = false := by
            cases l with
            | pos v =>
                simp only [localizeLiveLiteral] at hloc
                split at hloc
                · simp at hloc
                · next hv =>
                  have hne : τ v ≠ none := by simpa [mem_freeVars] using hv
                  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
                  simp [litFree, litFixedVal, liftLiveRestriction, hv, hb]
            | neg v =>
                simp only [localizeLiveLiteral] at hloc
                split at hloc
                · simp at hloc
                · next hv =>
                  have hne : τ v ≠ none := by simpa [mem_freeVars] using hv
                  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
                  simp [litFree, litFixedVal, liftLiveRestriction, hv, hb]
          simp [hloc, hfixed, ih]

theorem exists_localizeLiveLiteral_of_free {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (l : Rung4Literal n)
    (hfree : litFree (liftLiveRestriction τ σ) l = true) :
    ∃ l', localizeLiveLiteral τ l = some l' := by
  cases l with
  | pos v =>
      by_cases hv : v ∈ freeVars τ
      · exact ⟨Rung4Literal.pos ((liveCoordEquiv τ).symm ⟨v, hv⟩), by
          simp [localizeLiveLiteral, hv]⟩
      · have hne : τ v ≠ none := by simpa [mem_freeVars] using hv
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
        simp [litFree, litFixedVal, liftLiveRestriction, hv, hb] at hfree
  | neg v =>
      by_cases hv : v ∈ freeVars τ
      · exact ⟨Rung4Literal.neg ((liveCoordEquiv τ).symm ⟨v, hv⟩), by
          simp [localizeLiveLiteral, hv]⟩
      · have hne : τ v ≠ none := by simpa [mem_freeVars] using hv
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
        simp [litFree, litFixedVal, liftLiveRestriction, hv, hb] at hfree

theorem length_filterMap_eq_of_exists {A B : Type*} (f : A → Option B) :
    ∀ (xs : List A), (∀ x ∈ xs, ∃ y, f x = some y) →
      (xs.filterMap f).length = xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro h
      obtain ⟨y, hy⟩ := h x (by simp)
      simp [hy, ih (fun z hz => h z (by simp [hz]))]

theorem localizeLiveClause_freeLits_length {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (T : Clause n) :
    (freeLits σ (localizeLiveClause τ T)).length =
      (freeLits (liftLiveRestriction τ σ) T).length := by
  rw [localizeLiveClause_freeLits]
  apply length_filterMap_eq_of_exists
  intro l hl
  have hfree : litFree (liftLiveRestriction τ σ) l = true :=
    (List.mem_filter.mp hl).2
  exact exists_localizeLiveLiteral_of_free τ σ l hfree

theorem localizeLiveLits_any_litFalse {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) : ∀ (ls : List (Rung4Literal n)),
    (∀ l ∈ ls, DTree.litKilled τ l = false) →
    (ls.filterMap (localizeLiveLiteral τ)).any (litFalse σ) =
      ls.any (litFalse (liftLiveRestriction τ σ)) := by
  intro ls
  induction ls with
  | nil => simp
  | cons l ls ih =>
      intro hkill
      have hhead := hkill l (by simp)
      have htail : ∀ q ∈ ls, DTree.litKilled τ q = false :=
        fun q hq => hkill q (by simp [hq])
      cases hloc : localizeLiveLiteral τ l with
      | some l' =>
          have hs := localizeLiveLiteral_litFalse τ σ l l' hloc
          simp [hloc, hs, ih htail]
      | none =>
          have hfalse : litFalse (liftLiveRestriction τ σ) l = false := by
            cases l with
            | pos v =>
                simp only [localizeLiveLiteral] at hloc
                split at hloc
                · simp at hloc
                · next hv =>
                  have hne : τ v ≠ none := by simpa [mem_freeVars] using hv
                  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
                  cases b <;> simp [DTree.litKilled, litFalse, litFixedVal,
                    liftLiveRestriction, hv, hb] at hhead ⊢
            | neg v =>
                simp only [localizeLiveLiteral] at hloc
                split at hloc
                · simp at hloc
                · next hv =>
                  have hne : τ v ≠ none := by simpa [mem_freeVars] using hv
                  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
                  cases b <;> simp [DTree.litKilled, litFalse, litFixedVal,
                    liftLiveRestriction, hv, hb] at hhead ⊢
          simp [hloc, hfalse, ih htail]

theorem localizeLiveClause_termFalsified {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (T : Clause n)
    (hlive : DTree.clauseLive τ T = true) :
    termFalsified σ (localizeLiveClause τ T) =
      termFalsified (liftLiveRestriction τ σ) T := by
  unfold termFalsified localizeLiveClause
  apply localizeLiveLits_any_litFalse
  intro l hl
  by_contra hk
  rw [Bool.not_eq_false] at hk
  have hany : T.lits.any (DTree.litKilled τ) = true :=
    List.any_eq_true.mpr ⟨l, hl, hk⟩
  simp [DTree.clauseLive, hany] at hlive

theorem localizeLiveLits_all_litTrue {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) : ∀ (ls : List (Rung4Literal n)),
    (∀ l ∈ ls, DTree.litKilled τ l = false) →
    (ls.filterMap (localizeLiveLiteral τ)).all (litTrue σ) =
      ls.all (litTrue (liftLiveRestriction τ σ)) := by
  intro ls
  induction ls with
  | nil => simp
  | cons l ls ih =>
      intro hkill
      have hhead := hkill l (by simp)
      have htail : ∀ q ∈ ls, DTree.litKilled τ q = false :=
        fun q hq => hkill q (by simp [hq])
      cases hloc : localizeLiveLiteral τ l with
      | some l' =>
          have hs := localizeLiveLiteral_litTrue τ σ l l' hloc
          simp [hloc, hs, ih htail]
      | none =>
          have htrue : litTrue (liftLiveRestriction τ σ) l = true := by
            cases l with
            | pos v =>
                simp only [localizeLiveLiteral] at hloc
                split at hloc
                · simp at hloc
                · next hv =>
                  have hne : τ v ≠ none := by simpa [mem_freeVars] using hv
                  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
                  cases b <;> simp [DTree.litKilled, litTrue, litFixedVal,
                    liftLiveRestriction, hv, hb] at hhead ⊢
            | neg v =>
                simp only [localizeLiveLiteral] at hloc
                split at hloc
                · simp at hloc
                · next hv =>
                  have hne : τ v ≠ none := by simpa [mem_freeVars] using hv
                  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
                  cases b <;> simp [DTree.litKilled, litTrue, litFixedVal,
                    liftLiveRestriction, hv, hb] at hhead ⊢
          simp [hloc, htrue, ih htail]

theorem localizeLiveClause_termSat {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (T : Clause n)
    (hlive : DTree.clauseLive τ T = true) :
    termSat σ (localizeLiveClause τ T) =
      termSat (liftLiveRestriction τ σ) T := by
  unfold termSat localizeLiveClause
  apply localizeLiveLits_all_litTrue
  intro l hl
  by_contra hk
  rw [Bool.not_eq_false] at hk
  have hany : T.lits.any (DTree.litKilled τ) = true :=
    List.any_eq_true.mpr ⟨l, hl, hk⟩
  simp [DTree.clauseLive, hany] at hlive

/-- Restrict a DNF to the current subcube, discard killed terms, and relabel all
remaining free literals by the canonical live coordinates. -/
noncomputable def localizeLiveDnf {n : ℕ} (τ : Restriction n)
    (cs : List (Clause n)) : List (Clause (stars τ)) :=
  (cs.filter (DTree.clauseLive τ)).map (localizeLiveClause τ)

theorem localizeLiveDnf_anyTermSat {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (cs : List (Clause n)) :
    anyTermSat (localizeLiveDnf τ cs) σ =
      anyTermSat cs (liftLiveRestriction τ σ) := by
  apply DTree.bool_eq_of_iff
  simp only [anyTermSat, localizeLiveDnf, List.any_eq_true,
    List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨S, ⟨T, ⟨hT, hlive⟩, rfl⟩, hsat⟩
    exact ⟨T, hT, by rw [← localizeLiveClause_termSat τ σ T hlive]; exact hsat⟩
  · rintro ⟨T, hT, hsat⟩
    by_cases hlive : DTree.clauseLive τ T = true
    · exact ⟨localizeLiveClause τ T, ⟨T, ⟨hT, hlive⟩, rfl⟩,
        by rw [localizeLiveClause_termSat τ σ T hlive]; exact hsat⟩
    · simp only [Bool.not_eq_true] at hlive
      have hfτ : termFalsified τ T = true := by
        rw [clauseLive_eq_not_termFalsified] at hlive
        cases h : termFalsified τ T <;> simp [h] at hlive ⊢
      have hf := termFalsified_mono (liftLiveRestriction_extends τ σ) hfτ
      have hfalse : termSat (liftLiveRestriction τ σ) T = false := by
        rw [termFalsified, List.any_eq_true] at hf
        obtain ⟨l, hl, hlf⟩ := hf
        rw [termSat]
        by_contra hs
        rw [Bool.not_eq_false, List.all_eq_true] at hs
        have ht := hs l hl
        rw [litTrue_eq_false_of_litFalse hlf] at ht
        simp at ht
      rw [hfalse] at hsat
      simp at hsat

theorem localizeLiveClause_activePred {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (T : Clause n)
    (hlive : DTree.clauseLive τ T = true) :
    (!termFalsified σ (localizeLiveClause τ T) &&
        decide (0 < (freeLits σ (localizeLiveClause τ T)).length)) =
      (!termFalsified (liftLiveRestriction τ σ) T &&
        decide (0 < (freeLits (liftLiveRestriction τ σ) T).length)) := by
  rw [localizeLiveClause_termFalsified τ σ T hlive,
    localizeLiveClause_freeLits_length]

theorem localizeLiveDnf_cons {n : ℕ} (τ : Restriction n) (T : Clause n)
    (cs : List (Clause n)) :
    localizeLiveDnf τ (T :: cs) =
      if DTree.clauseLive τ T then
        localizeLiveClause τ T :: localizeLiveDnf τ cs
      else localizeLiveDnf τ cs := by
  unfold localizeLiveDnf
  cases h : DTree.clauseLive τ T <;> simp [h]

theorem localizeLiveDnf_findActive {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) : ∀ (cs : List (Clause n)),
    (localizeLiveDnf τ cs).find? (fun T =>
        !termFalsified σ T && decide (0 < (freeLits σ T).length)) =
      (cs.find? (fun T => !termFalsified (liftLiveRestriction τ σ) T &&
        decide (0 < (freeLits (liftLiveRestriction τ σ) T).length))).map
          (localizeLiveClause τ) := by
  intro cs
  induction cs with
  | nil => simp [localizeLiveDnf]
  | cons T cs ih =>
      by_cases hlive : DTree.clauseLive τ T = true
      · have hp := localizeLiveClause_activePred τ σ T hlive
        rw [localizeLiveDnf_cons, if_pos hlive]
        cases hlocal : (!termFalsified σ (localizeLiveClause τ T) &&
            decide (0 < (freeLits σ (localizeLiveClause τ T)).length))
        · have hamb : (!termFalsified (liftLiveRestriction τ σ) T &&
              decide (0 < (freeLits (liftLiveRestriction τ σ) T).length)) = false :=
            hp ▸ hlocal
          simp [hlocal, hamb, ih]
        · have hamb : (!termFalsified (liftLiveRestriction τ σ) T &&
              decide (0 < (freeLits (liftLiveRestriction τ σ) T).length)) = true :=
            hp ▸ hlocal
          simp [hlocal, hamb]
      · have hfτ : termFalsified τ T = true := by
          simp only [Bool.not_eq_true] at hlive
          rw [clauseLive_eq_not_termFalsified] at hlive
          cases h : termFalsified τ T <;> simp [h] at hlive ⊢
        have hf := termFalsified_mono (liftLiveRestriction_extends τ σ) hfτ
        rw [localizeLiveDnf_cons, if_neg hlive]
        simp [hf, ih]

theorem localizeLiveDnf_activeTerm {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (cs : List (Clause n)) :
    activeTerm (localizeLiveDnf τ cs) σ =
      (activeTerm cs (liftLiveRestriction τ σ)).map (localizeLiveClause τ) := by
  unfold activeTerm
  rw [localizeLiveDnf_anyTermSat]
  cases h : anyTermSat cs (liftLiveRestriction τ σ)
  · simp [h, localizeLiveDnf_findActive]
  · simp [h]

/-- Fixing a relabelled live coordinate and then lifting is exactly the same
restriction as lifting first and fixing the corresponding ambient coordinate. -/
theorem liftLiveRestriction_fixVar {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (i : Fin (stars τ)) (b : Bool) :
    liftLiveRestriction τ (fixVar σ i b) =
      fixVar (liftLiveRestriction τ σ) (liveCoordEquiv τ i) b := by
  funext v
  by_cases hvi : v = liveCoordEquiv τ i
  · subst v
    rw [liftLiveRestriction, dif_pos (liveCoordEquiv τ i).property]
    rw [(liveCoordEquiv τ).symm_apply_apply i]
    simp [fixVar]
  · by_cases hv : v ∈ freeVars τ
    · have hidx : (liveCoordEquiv τ).symm ⟨v, hv⟩ ≠ i := by
        intro heq
        apply hvi
        have := congrArg (liveCoordEquiv τ) heq
        simpa using congrArg Subtype.val this
      rw [liftLiveRestriction, dif_pos hv, fixVar, Function.update_of_ne hidx,
        fixVar, Function.update_of_ne hvi, liftLiveRestriction, dif_pos hv]
    · rw [liftLiveRestriction, dif_neg hv, fixVar,
        Function.update_of_ne hvi, liftLiveRestriction, dif_neg hv]

theorem localizeLiveLiteral_litVar {n : ℕ} (τ : Restriction n)
    (l : Rung4Literal n) (l' : Rung4Literal (stars τ))
    (h : localizeLiveLiteral τ l = some l') :
    (liveCoordEquiv τ (litVar l')).1 = litVar l := by
  cases l with
  | pos v =>
      simp only [localizeLiveLiteral] at h
      split at h
      · cases h; simp [litVar]
      · simp at h
  | neg v =>
      simp only [localizeLiveLiteral] at h
      split at h
      · cases h; simp [litVar]
      · simp at h

theorem localizeLiveClause_freeLits_head {n : ℕ} (τ : Restriction n)
    (σ : Restriction (stars τ)) (T : Clause n) (l : Rung4Literal n)
    (hhead : (freeLits (liftLiveRestriction τ σ) T).head? = some l) :
    ∃ l', localizeLiveLiteral τ l = some l' ∧
      (freeLits σ (localizeLiveClause τ T)).head? = some l' := by
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hhead
  have hl : l ∈ freeLits (liftLiveRestriction τ σ) T := by
    rw [hys]
    simp
  obtain ⟨l', hloc⟩ := exists_localizeLiveLiteral_of_free τ σ l
    (List.mem_filter.mp hl).2
  refine ⟨l', hloc, ?_⟩
  rw [localizeLiveClause_freeLits]
  cases hs : freeLits (liftLiveRestriction τ σ) T with
  | nil => simp [hs] at hhead
  | cons a as =>
      simp [hs] at hhead
      subst a
      simp [hs, hloc]

/-- The canonical switching tree has exactly the same depth after relabelling to
the current live-coordinate cube. -/
theorem canonicalDT_depth_localize {n : ℕ} (τ : Restriction n)
    (cs : List (Clause n)) : ∀ (fuel : ℕ) (σ : Restriction (stars τ)),
    (canonicalDT (localizeLiveDnf τ cs) fuel σ).depth =
      (canonicalDT cs fuel (liftLiveRestriction τ σ)).depth := by
  intro fuel
  induction fuel with
  | zero =>
      intro σ
      rw [canonicalDT, canonicalDT, localizeLiveDnf_anyTermSat]
      cases h : anyTermSat cs (liftLiveRestriction τ σ) <;> rfl
  | succ fuel ih =>
      intro σ
      rw [canonicalDT, canonicalDT, localizeLiveDnf_anyTermSat]
      cases hsat : anyTermSat cs (liftLiveRestriction τ σ)
      · simp only [Bool.false_eq_true, if_false]
        rw [localizeLiveDnf_activeTerm]
        cases hact : activeTerm cs (liftLiveRestriction τ σ) with
        | none => simp [hact, BoolDecisionTree.depth]
        | some T =>
            simp only [hact, Option.map_some]
            cases hfree : (freeLits (liftLiveRestriction τ σ) T).head? with
            | none =>
                have hempty : freeLits (liftLiveRestriction τ σ) T = [] := by
                  cases hls : freeLits (liftLiveRestriction τ σ) T with
                  | nil => rfl
                  | cons l ls => simp [hls] at hfree
                have hlocal : (freeLits σ (localizeLiveClause τ T)).head? = none := by
                  rw [localizeLiveClause_freeLits, hempty]
                  rfl
                simp [hfree, hlocal, BoolDecisionTree.depth]
            | some l =>
                obtain ⟨l', hloc, hlocal⟩ :=
                  localizeLiveClause_freeLits_head τ σ T l hfree
                have hvar := localizeLiveLiteral_litVar τ l l' hloc
                simp only [hfree, hlocal, BoolDecisionTree.depth]
                rw [ih (fixVar σ (litVar l') false),
                  ih (fixVar σ (litVar l') true),
                  liftLiveRestriction_fixVar, liftLiveRestriction_fixVar]
                rw [show (liveCoordEquiv τ (litVar l')).1 = litVar l from hvar]
      · rfl

theorem mem_boundedTermBad_localize_iff {n : ℕ} (τ : Restriction n)
    (cs : List (Clause n)) (K threshold : ℕ) (σ : Restriction (stars τ)) :
    liftLiveRestriction τ σ ∈ boundedTermBad cs K threshold ↔
      σ ∈ boundedTermBad (localizeLiveDnf τ cs) K threshold := by
  rw [mem_boundedTermBad_iff, mem_boundedTermBad_iff,
    stars_liftLiveRestriction, canonicalDT_depth_localize]

/-- The localized DNF computes exactly the original ambient DNF throughout the
current subcube. -/
theorem localizeLiveDnf_eval {n : ℕ} (τ : Restriction n)
    (x : Fin (stars τ) → Bool) (cs : List (Clause n)) :
    DTree.dnfValue (localizeLiveDnf τ cs) x =
      DTree.dnfValue cs (liftLiveAssignment τ x) := by
  apply DTree.bool_eq_of_iff
  simp only [DTree.dnfValue, localizeLiveDnf, List.any_eq_true,
    List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨S, ⟨T, ⟨hT, hlive⟩, rfl⟩, hsat⟩
    exact ⟨T, hT, by rw [← localizeLiveClause_eval τ x T hlive]; exact hsat⟩
  · rintro ⟨T, hT, hsat⟩
    by_cases hlive : DTree.clauseLive τ T = true
    · exact ⟨localizeLiveClause τ T, ⟨T, ⟨hT, hlive⟩, rfl⟩,
        by rw [localizeLiveClause_eval τ x T hlive]; exact hsat⟩
    · simp only [Bool.not_eq_true] at hlive
      exact absurd hsat (by
        rw [DTree.dead_clause_false τ (liftLiveAssignment τ x) T
          (liftLiveAssignment_agrees τ x) hlive]
        simp)

theorem localizeLiveClause_width_le {n : ℕ} (τ : Restriction n) (T : Clause n) :
    (localizeLiveClause τ T).lits.length ≤ T.lits.length := by
  exact List.length_filterMap_le _ _

theorem localizeLiveDnf_length_le {n : ℕ} (τ : Restriction n)
    (cs : List (Clause n)) :
    (localizeLiveDnf τ cs).length ≤ cs.length := by
  rw [localizeLiveDnf, List.length_map]
  exact List.length_filter_le _ _

theorem localizeLiveDnf_width_le {n w : ℕ} (τ : Restriction n)
    (cs : List (Clause n)) (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    ∀ T ∈ localizeLiveDnf τ cs, T.lits.length ≤ w := by
  intro T hT
  rw [localizeLiveDnf, List.mem_map] at hT
  obtain ⟨U, hU, rfl⟩ := hT
  exact le_trans (localizeLiveClause_width_le τ U)
    (hw U (List.mem_of_mem_filter hU))

/-- Transport a whole indexed bottom-gate family to the current live-coordinate cube. -/
noncomputable def localizeLiveGates {n G : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) :
    Fin G → List (Clause (stars τ)) :=
  fun g => localizeLiveDnf τ (gates g)

theorem localizeLiveGates_width_le {n G w : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n))
    (hw : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ w) :
    ∀ g, ∀ T ∈ localizeLiveGates τ gates g, T.lits.length ≤ w := by
  intro g
  exact localizeLiveDnf_width_le τ (gates g) (hw g)

theorem localizeLiveGates_count_le {n G m : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n))
    (hm : ∀ g, (gates g).length ≤ m) :
    ∀ g, (localizeLiveGates τ gates g).length ≤ m := by
  intro g
  exact le_trans (localizeLiveDnf_length_le τ (gates g)) (hm g)

theorem localizeLiveGates_eval {n G : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (x : Fin (stars τ) → Bool) :
    ∀ g, DTree.dnfValue (localizeLiveGates τ gates g) x =
      DTree.dnfValue (gates g) (liftLiveAssignment τ x) := by
  intro g
  exact localizeLiveDnf_eval τ x (gates g)

theorem mem_circuitBad_localize_iff {n G : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (K threshold : ℕ)
    (σ : Restriction (stars τ)) :
    liftLiveRestriction τ σ ∈ circuitBad gates K threshold ↔
      σ ∈ circuitBad (localizeLiveGates τ gates) K threshold := by
  rw [mem_circuitBad_iff, mem_circuitBad_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, (mem_boundedTermBad_localize_iff τ (gates g) K threshold σ).mp hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (mem_boundedTermBad_localize_iff τ (gates g) K threshold σ).mpr hg⟩

/-- The complete local restriction bucket selected by its canonical finite index. -/
noncomputable def selectedLocalBucket (N K : ℕ) (i : Fin (N.choose K)) :
    Finset (Restriction N) :=
  restrictionBucket ((freeSetBucketEquivFin N K).symm i)

/-- Lift every child of a selected local bucket into the current ambient subcube. -/
noncomputable def liftedSelectedBucket {n : ℕ} (τ : Restriction n) (K : ℕ)
    (i : Fin ((stars τ).choose K)) : Finset (Restriction n) :=
  (selectedLocalBucket (stars τ) K i).image (liftLiveRestriction τ)

theorem mem_selectedLocalBucket_stars {N K : ℕ} {i : Fin (N.choose K)}
    {σ : Restriction N} (hσ : σ ∈ selectedLocalBucket N K i) : stars σ = K := by
  exact stars_eq_of_mem_restrictionBucket hσ

theorem liftedSelectedBucket_extends {n K : ℕ} (τ : Restriction n)
    (i : Fin ((stars τ).choose K)) {ρ : Restriction n}
    (hρ : ρ ∈ liftedSelectedBucket τ K i) : Extends τ ρ := by
  classical
  rw [liftedSelectedBucket, Finset.mem_image] at hρ
  obtain ⟨σ, _, rfl⟩ := hρ
  exact liftLiveRestriction_extends τ σ

theorem liftedSelectedBucket_stars {n K : ℕ} (τ : Restriction n)
    (i : Fin ((stars τ).choose K)) {ρ : Restriction n}
    (hρ : ρ ∈ liftedSelectedBucket τ K i) : stars ρ = K := by
  classical
  rw [liftedSelectedBucket, Finset.mem_image] at hρ
  obtain ⟨σ, hσ, rfl⟩ := hρ
  rw [stars_liftLiveRestriction, mem_selectedLocalBucket_stars hσ]

/-- On every selected child, local badness is exactly genuine ambient badness. -/
theorem selectedLocalBucket_bad_iff {n G K threshold : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (i : Fin ((stars τ).choose K))
    {σ : Restriction (stars τ)} (_hσ : σ ∈ selectedLocalBucket (stars τ) K i) :
    liftLiveRestriction τ σ ∈ circuitBad gates K threshold ↔
      σ ∈ circuitBad (localizeLiveGates τ gates) K threshold :=
  mem_circuitBad_localize_iff τ gates K threshold σ

/-- A finite deterministic cover tree.  Bad children stop at their node and pay `badCost`; only
good children carry recursive subtrees.  Every stored child is certified to extend its parent. -/
inductive ChargedCover (n : ℕ) where
  | leaf (τ : Restriction n) (leafWork : ℕ)
  | node (τ : Restriction n) (bucket bad : Finset (Restriction n)) (badCost : ℕ)
      (bad_subset : bad ⊆ bucket)
      (extends_parent : ∀ ρ ∈ bucket, Extends τ ρ)
      (children : (ρ : {ρ : Restriction n // ρ ∈ bucket \ bad}) → ChargedCover n)

/-- Exact recursive work of a charged cover: stopped bad arms plus every recursively expanded good
arm.  No exceptional or good child is omitted. -/
def ChargedCover.work {n : ℕ} : ChargedCover n → ℕ
  | .leaf _ leafWork => leafWork
  | .node _ bucket bad badCost _ _ children =>
      bad.card * badCost +
        ∑ ρ : {ρ : Restriction n // ρ ∈ bucket \ bad}, (children ρ).work

def ChargedCover.root {n : ℕ} : ChargedCover n → Restriction n
  | .leaf τ _ => τ
  | .node τ _ _ _ _ _ _ => τ

/-- Genuine ambient bad children inside one complete lifted selected bucket. -/
noncomputable def selectedBadChildren {n G K threshold : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (i : Fin ((stars τ).choose K)) :
    Finset (Restriction n) :=
  liftedSelectedBucket τ K i ∩ circuitBad gates K threshold

theorem selectedBadChildren_subset {n G K threshold : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (i : Fin ((stars τ).choose K)) :
    selectedBadChildren (threshold := threshold) τ gates i ⊆ liftedSelectedBucket τ K i := by
  exact Finset.inter_subset_left

theorem selectedBadChildren_eq_image_badBucket {n G K threshold : ℕ}
    (τ : Restriction n) (gates : Fin G → List (Clause n))
    (i : Fin ((stars τ).choose K)) :
    selectedBadChildren (threshold := threshold) τ gates i =
      (badBucket (circuitBad (localizeLiveGates τ gates) K threshold)
        ((freeSetBucketEquivFin (stars τ) K).symm i)).image (liftLiveRestriction τ) := by
  classical
  ext ρ
  constructor
  · intro hρ
    obtain ⟨hlift, hamb⟩ := Finset.mem_inter.mp hρ
    rw [liftedSelectedBucket, Finset.mem_image] at hlift
    obtain ⟨σ, hσ, rfl⟩ := hlift
    apply Finset.mem_image.mpr
    refine ⟨σ, ?_, rfl⟩
    rw [badBucket, Finset.mem_filter]
    refine ⟨(mem_circuitBad_localize_iff τ gates K threshold σ).mp hamb, ?_⟩
    exact mem_restrictionBucket.mp hσ
  · intro hρ
    rw [Finset.mem_image] at hρ
    obtain ⟨σ, hσ, rfl⟩ := hρ
    rw [badBucket, Finset.mem_filter] at hσ
    apply Finset.mem_inter.mpr
    constructor
    · rw [liftedSelectedBucket, Finset.mem_image]
      exact ⟨σ, mem_restrictionBucket.mpr hσ.2, rfl⟩
    · exact (mem_circuitBad_localize_iff τ gates K threshold σ).mpr hσ.1

/-- The number stored in the selected-bucket certificate is exactly the number of genuine ambient
bad children stopped by the charged cover node. -/
theorem card_selectedBadChildren {n G K threshold : ℕ}
    (τ : Restriction n) (gates : Fin G → List (Clause n))
    (i : Fin ((stars τ).choose K)) :
    (selectedBadChildren (threshold := threshold) τ gates i).card =
      concreteBadCount (K := K)
        (circuitBad (localizeLiveGates τ gates) K threshold) i := by
  rw [selectedBadChildren_eq_image_badBucket]
  exact Finset.card_image_of_injective _ (liftLiveRestriction_injective τ)

/-- Assemble one real charged node from a selected bucket; recursive data are requested exactly for
the children outside the genuine ambient bad set. -/
noncomputable def selectedChargedNode {n G K threshold : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (i : Fin ((stars τ).choose K))
    (badCost : ℕ)
    (children : (ρ : {ρ : Restriction n //
      ρ ∈ liftedSelectedBucket τ K i \
        selectedBadChildren (threshold := threshold) τ gates i}) → ChargedCover n) :
    ChargedCover n :=
  .node τ (liftedSelectedBucket τ K i)
    (selectedBadChildren (threshold := threshold) τ gates i) badCost
    (selectedBadChildren_subset (threshold := threshold) τ gates i)
    (fun ρ hρ => liftedSelectedBucket_extends τ i hρ) children

theorem card_liftedSelectedBucket_le {n K : ℕ} (τ : Restriction n)
    (i : Fin ((stars τ).choose K)) :
    (liftedSelectedBucket τ K i).card ≤ 2 ^ (stars τ - K) := by
  classical
  rw [liftedSelectedBucket,
    Finset.card_image_of_injective _ (liftLiveRestriction_injective τ)]
  exact card_restrictionBucket_le ((freeSetBucketEquivFin (stars τ) K).symm i)

/-- Replacing every good child by a subtree of work at most `childWork` bounds the exact tree node
by the arithmetic splice expression. -/
theorem selectedChargedNode_work_le_splice {n G K threshold : ℕ}
    (τ : Restriction n) (gates : Fin G → List (Clause n))
    (i : Fin ((stars τ).choose K))
    (children : (ρ : {ρ : Restriction n //
      ρ ∈ liftedSelectedBucket τ K i \
        selectedBadChildren (threshold := threshold) τ gates i}) → ChargedCover n)
    (childWork : ℕ) (hchild : ∀ ρ, (children ρ).work ≤ childWork) :
    (selectedChargedNode τ gates i (2 ^ K) children).work ≤
      recursiveSpliceWork K
        (liftedSelectedBucket τ K i \
          selectedBadChildren (threshold := threshold) τ gates i).card
        (selectedBadChildren (threshold := threshold) τ gates i).card childWork := by
  classical
  simp only [selectedChargedNode, ChargedCover.work, recursiveSpliceWork]
  have hsum :
    ∑ ρ, (children ρ).work ≤ ∑ _ρ, childWork :=
      Finset.sum_le_sum fun ρ _ => hchild ρ
  have hconst : (∑ _ρ : {ρ : Restriction n //
      ρ ∈ liftedSelectedBucket τ K i \
        selectedBadChildren (threshold := threshold) τ gates i}, childWork) =
      (liftedSelectedBucket τ K i \
        selectedBadChildren (threshold := threshold) τ gates i).card * childWork := by
    simp [Nat.mul_comm]
  rw [hconst] at hsum
  omega

theorem card_selectedGoodChildren_le {n G K threshold : ℕ}
    (τ : Restriction n) (gates : Fin G → List (Clause n))
    (i : Fin ((stars τ).choose K)) :
    (liftedSelectedBucket τ K i \
      selectedBadChildren (threshold := threshold) τ gates i).card ≤
        2 ^ (stars τ - K) := by
  exact le_trans (Finset.card_le_card (Finset.sdiff_subset))
    (card_liftedSelectedBucket_le τ i)

/-- A retry cover has the opposite branching orientation from `ChargedCover`: good children stop
after paying the collapsed-layer cost, while genuine bad children receive another restriction round
for the same circuit.  This permits constant-threshold failure probabilities to be amplified
geometrically without increasing the circuit's width on retry branches. -/
inductive RetryCover (n : ℕ) where
  | leaf (τ : Restriction n) (leafWork : ℕ)
  | node (τ : Restriction n) (bucket bad : Finset (Restriction n)) (goodCost : ℕ)
      (bad_subset : bad ⊆ bucket)
      (extends_parent : ∀ ρ ∈ bucket, Extends τ ρ)
      (retries : (ρ : {ρ : Restriction n // ρ ∈ bad}) → RetryCover n)

/-- Exact retry work: solve every good child now and recurse on every bad child. -/
def RetryCover.work {n : ℕ} : RetryCover n → ℕ
  | .leaf _ leafWork => leafWork
  | .node _ bucket bad goodCost _ _ retries =>
      (bucket \ bad).card * goodCost +
        ∑ ρ : {ρ : Restriction n // ρ ∈ bad}, (retries ρ).work

def RetryCover.root {n : ℕ} : RetryCover n → Restriction n
  | .leaf τ _ => τ
  | .node τ _ _ _ _ _ _ => τ

def RetryCover.height {n : ℕ} : RetryCover n → ℕ
  | .leaf _ _ => 0
  | .node _ _ bad _ _ _ retries =>
      1 + (bad.attach.sup fun ρ => (retries ρ).height)

/-- Assemble a retry node from the same genuine selected bucket/bad set used by the deterministic
certificate. -/
noncomputable def selectedRetryNode {n G K threshold : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (i : Fin ((stars τ).choose K))
    (goodCost : ℕ)
    (retries : (ρ : {ρ : Restriction n //
      ρ ∈ selectedBadChildren (threshold := threshold) τ gates i}) → RetryCover n) :
    RetryCover n :=
  .node τ (liftedSelectedBucket τ K i)
    (selectedBadChildren (threshold := threshold) τ gates i) goodCost
    (selectedBadChildren_subset (threshold := threshold) τ gates i)
    (fun ρ hρ => liftedSelectedBucket_extends τ i hρ) retries

/-- Exact work of a real retry node is bounded by `retrySpliceWork`. -/
theorem selectedRetryNode_work_le_splice {n G K threshold : ℕ}
    (τ : Restriction n) (gates : Fin G → List (Clause n))
    (i : Fin ((stars τ).choose K))
    (goodCost retryWork : ℕ)
    (retries : (ρ : {ρ : Restriction n //
      ρ ∈ selectedBadChildren (threshold := threshold) τ gates i}) → RetryCover n)
    (hretry : ∀ ρ, (retries ρ).work ≤ retryWork) :
    (selectedRetryNode τ gates i goodCost retries).work ≤
      retrySpliceWork
        (liftedSelectedBucket τ K i \
          selectedBadChildren (threshold := threshold) τ gates i).card
        (selectedBadChildren (threshold := threshold) τ gates i).card
        goodCost retryWork := by
  classical
  simp only [selectedRetryNode, RetryCover.work, retrySpliceWork]
  have hsum : ∑ ρ, (retries ρ).work ≤ ∑ _ρ, retryWork :=
    Finset.sum_le_sum fun ρ _ => hretry ρ
  have hconst : (∑ _ρ : {ρ : Restriction n //
      ρ ∈ selectedBadChildren (threshold := threshold) τ gates i}, retryWork) =
      (selectedBadChildren (threshold := threshold) τ gates i).card * retryWork := by
    simp [Nat.mul_comm]
  rw [hconst] at hsum
  omega

/-- One actual selected retry node inherits the geometric half-bad recurrence. -/
theorem selectedRetryNode_work_le {n G K threshold saving : ℕ}
    (τ : Restriction n) (gates : Fin G → List (Clause n))
    (i : Fin ((stars τ).choose K)) (hK : K ≤ stars τ)
    (hq : 1 ≤ stars τ - K) (hsK : saving + 1 ≤ K)
    (goodCost : ℕ) (hgoodCost : goodCost ≤ 2 ^ (K - saving - 1))
    (retries : (ρ : {ρ : Restriction n //
      ρ ∈ selectedBadChildren (threshold := threshold) τ gates i}) → RetryCover n)
    (hretry : ∀ ρ, (retries ρ).work ≤ 2 ^ (K - saving))
    (hbad : concreteBadCount (K := K)
      (circuitBad (localizeLiveGates τ gates) K threshold) i ≤
        2 ^ ((stars τ - K) - 1)) :
    (selectedRetryNode τ gates i goodCost retries).work ≤ 2 ^ (stars τ - saving) := by
  apply le_trans (selectedRetryNode_work_le_splice τ gates i goodCost
    (2 ^ (K - saving)) retries hretry)
  apply retrySpliceWork_le (stars τ) (stars τ - K) K
  · omega
  · exact hq
  · exact hsK
  · exact card_selectedGoodChildren_le τ gates i
  · exact hgoodCost
  · rw [card_selectedBadChildren]
    exact hbad
  · exact le_rfl

/-- End-to-end work bound for one actual charged tree node.  The hypotheses are precisely the
selected bad-count certificate and a uniform recursive bound for every genuine good child. -/
theorem selectedChargedNode_work_le {n G K threshold saving : ℕ}
    (τ : Restriction n) (gates : Fin G → List (Clause n))
    (i : Fin ((stars τ).choose K)) (hK : K ≤ stars τ)
    (hsq : saving + 1 ≤ stars τ - K) (hsK : saving + 1 ≤ K)
    (children : (ρ : {ρ : Restriction n //
      ρ ∈ liftedSelectedBucket τ K i \
        selectedBadChildren (threshold := threshold) τ gates i}) → ChargedCover n)
    (hchild : ∀ ρ, (children ρ).work ≤ 2 ^ (K - saving - 1))
    (hbad : concreteBadCount (K := K)
      (circuitBad (localizeLiveGates τ gates) K threshold) i ≤
        2 ^ ((stars τ - K) - saving - 1)) :
    (selectedChargedNode τ gates i (2 ^ K) children).work ≤
      2 ^ (stars τ - saving) := by
  apply le_trans (selectedChargedNode_work_le_splice τ gates i children
    (2 ^ (K - saving - 1)) hchild)
  apply recursiveSpliceWork_le (stars τ) (stars τ - K) K
  · omega
  · exact hsq
  · exact hsK
  · exact card_selectedGoodChildren_le τ gates i
  · exact le_rfl
  · rw [card_selectedBadChildren]
    exact hbad

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
  good_implies_layered_shallows C h.gates K threshold
    (fun cs hcs => (h.enumerates cs).mp hcs) ρ h.stars_eq h.good

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

/-- Fixed-size enumeration of the real dual bottom gates, padded by empty DNFs. -/
def paddedDualBottomGates {n : ℕ} (C : Layered n) :
    Fin concreteG → List (Clause n) :=
  fun i => (dualBottomGates C).getD i.1 []

theorem dualBottomGates_length_le_concreteG {n : ℕ} (C : Layered n)
    (hcnt : (bottomGates C).length ≤ concreteM) :
    (dualBottomGates C).length ≤ concreteG := by
  simp [dualBottomGates, concreteG]
  omega

theorem paddedDualBottomGates_covers {n : ℕ} (C : Layered n)
    (hcnt : (bottomGates C).length ≤ concreteM) :
    ∀ cs, cs ∈ dualBottomGates C → ∃ g, paddedDualBottomGates C g = cs := by
  intro cs hcs
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hcs
  have hjG : j.1 < concreteG := lt_of_lt_of_le j.2
    (dualBottomGates_length_le_concreteG C hcnt)
  refine ⟨⟨j.1, hjG⟩, ?_⟩
  rw [paddedDualBottomGates, List.getD_eq_get]
  exact hj

theorem dualBottomGates_width {n : ℕ} (C : Layered n)
    (hbw : BottomWidth concreteT C) :
    ∀ cs ∈ dualBottomGates C, ∀ T ∈ cs, T.lits.length ≤ concreteT := by
  intro cs hcs T hT
  rw [dualBottomGates, List.mem_append] at hcs
  rcases hcs with hcs | hcs
  · exact hbw cs hcs T hT
  · rw [List.mem_map] at hcs
    obtain ⟨ds, hds, rfl⟩ := hcs
    rw [negDNF, List.mem_map] at hT
    obtain ⟨U, hU, rfl⟩ := hT
    simpa using hbw ds hds U hU

theorem dualBottomGates_count {n : ℕ} (C : Layered n)
    (hmc : BottomCount concreteTerms C) :
    ∀ cs ∈ dualBottomGates C, cs.length ≤ concreteTerms := by
  intro cs hcs
  rw [dualBottomGates, List.mem_append] at hcs
  rcases hcs with hcs | hcs
  · exact hmc cs hcs
  · rw [List.mem_map] at hcs
    obtain ⟨ds, hds, rfl⟩ := hcs
    simpa [negDNF] using hmc ds hds

theorem paddedDualBottomGates_width {n : ℕ} (C : Layered n)
    (hbw : BottomWidth concreteT C) :
    ∀ g, ∀ T ∈ paddedDualBottomGates C g, T.lits.length ≤ concreteT := by
  intro g T hT
  by_cases hg : g.1 < (dualBottomGates C).length
  · rw [paddedDualBottomGates,
      List.getD_eq_getElem (l := dualBottomGates C) (d := []) hg] at hT
    exact dualBottomGates_width C hbw _ (List.get_mem _ _) T hT
  · rw [paddedDualBottomGates, List.getD_eq_default _ _ (by omega)] at hT
    simp at hT

theorem paddedDualBottomGates_count {n : ℕ} (C : Layered n)
    (hmc : BottomCount concreteTerms C) :
    ∀ g, (paddedDualBottomGates C g).length ≤ concreteTerms := by
  intro g
  by_cases hg : g.1 < (dualBottomGates C).length
  · rw [paddedDualBottomGates,
      List.getD_eq_getElem (l := dualBottomGates C) (d := []) hg]
    exact dualBottomGates_count C hmc _ (List.get_mem _ _)
  · rw [paddedDualBottomGates, List.getD_eq_default _ _ (by omega)]
    simp

/-- Every good child of the padded real gate family performs a genuine semantic collapse and drops
one alternation level. -/
theorem padded_good_collapseRound {n k K threshold : ℕ} (C : Layered n)
    (hAlt : AltO (k + 3) C) (hcnt : (bottomGates C).length ≤ concreteM)
    (ρ : Restriction n) (hstars : stars ρ = K)
    (hgood : ρ ∉ circuitBad (paddedDualBottomGates C) K threshold) :
    EquivOn ρ C (collapseRound K ρ C) ∧
      AltO (k + 2) (collapseRound K ρ C) ∧
      BottomWidth threshold (collapseRound K ρ C) := by
  have hsh := good_implies_layered_shallows C (paddedDualBottomGates C) K threshold
    (paddedDualBottomGates_covers C hcnt) ρ hstars hgood
  exact ⟨collapseRound_EquivOn K (by omega) C,
    collapseRound_AltO K ρ hAlt, collapseRound_BottomWidth K ρ hsh⟩

/-- Exact contraction factor for recursively reusing a deterministic bucket: a parent at
scale `concreteScale * (concreteCoverB * r)` leaves exactly `concreteScale * r` live variables. -/
def concreteCoverB : ℕ := concreteScale / 20

theorem concreteScale_eq_twenty_mul_coverB : concreteScale = 20 * concreteCoverB := by
  norm_num [concreteScale, concreteCoverB, concreteG, concreteM, concreteT, concreteTerms]

theorem concreteCoverB_gt_three : 3 < concreteCoverB := by
  norm_num [concreteCoverB, concreteScale, concreteG, concreteM, concreteT, concreteTerms]

/-- The present deterministic schedule cannot reuse the constant-width `30` invariant after a
nontrivial parent contraction: its proved collapse width is `10*(concreteCoverB*r)`, already above
`30`.  A full recursive theorem therefore needs a constant-threshold deterministic tail or a
stronger multi-switching count; the current certificates alone do not close the induction. -/
theorem deterministic_parent_threshold_exceeds_closed (r : ℕ) (hr : 0 < r) :
    concreteT < 10 * (concreteCoverB * r) := by
  have hfour : 4 ≤ concreteCoverB := Nat.succ_le_iff.mpr concreteCoverB_gt_three
  have hrone : 1 ≤ r := hr
  have : 4 ≤ concreteCoverB * r := by nlinarith
  norm_num [concreteT]
  omega

theorem concreteCover_live_exact (r : ℕ) :
    20 * (concreteCoverB * r) = concreteScale * r := by
  rw [concreteScale_eq_twenty_mul_coverB]
  ac_rfl

/-- The deterministic depth schedule whose selected `20r`-star children have exactly the
ambient size required by the next recursive round. -/
def concreteCoverSched (d r i : ℕ) : ℕ := r * concreteCoverB ^ (d - i)

theorem concreteCoverSched_step {d r i : ℕ} (hi : i < d) :
    20 * concreteCoverSched d r i = concreteScale * concreteCoverSched d r (i + 1) := by
  rw [concreteCoverSched, concreteCoverSched]
  have hsub : d - i = (d - (i + 1)) + 1 := by omega
  rw [hsub, pow_succ]
  rw [concreteScale_eq_twenty_mul_coverB]
  ac_rfl

/-- Every child in the selected bucket at depth `i` has exactly the live size required by depth
`i+1` of the deterministic cover schedule. -/
theorem liftedSelectedBucket_coverSched_stars {n d r i : ℕ} (hi : i < d)
    (τ : Restriction n)
    (bucket : Fin ((stars τ).choose (20 * concreteCoverSched d r i)))
    {ρ : Restriction n}
    (hρ : ρ ∈ liftedSelectedBucket τ (20 * concreteCoverSched d r i) bucket) :
    stars ρ = concreteScale * concreteCoverSched d r (i + 1) := by
  rw [liftedSelectedBucket_stars τ bucket hρ]
  exact concreteCoverSched_step hi

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

/-- **Constant-threshold retry certificate from one natural shell inequality.**  Unlike the earlier
linear-threshold certificate, `threshold` and `K` are independent.  A shell budget of one half
selects a complete deterministic bucket with at most half of its `2^(N-K)` children genuinely bad.
This is exactly the local input consumed by `selectedRetryNode_work_le`. -/
theorem concreteRetry_strong_geometric_budget (r : ℕ) :
    ((2 : ℚ) ^ concreteT) * concreteG *
        (∑ t ∈ Finset.Icc concreteT (20 * r),
          ((4 : ℚ) / (49 * concreteG)) ^ t) ≤ 1 := by
  have ha0 : (0 : ℚ) ≤ (4 : ℚ) / (49 * concreteG) := by positivity
  have ha1 : (4 : ℚ) / (49 * concreteG) < 1 := by
    norm_num [concreteG, concreteM]
  have htail := geom_shell_tail_le ha0 ha1 concreteT (20 * r)
  calc
    ((2 : ℚ) ^ concreteT) * concreteG *
        (∑ t ∈ Finset.Icc concreteT (20 * r),
          ((4 : ℚ) / (49 * concreteG)) ^ t)
      ≤ (2 ^ concreteT) * concreteG *
          (((4 : ℚ) / (49 * concreteG)) ^ concreteT /
            (1 - (4 : ℚ) / (49 * concreteG))) := by gcongr
    _ ≤ 1 := by norm_num [concreteG, concreteM, concreteT]

/-- The reusable fixed-width retry round has at most half of its complete bucket bad.  The
ambient density is the same `20/(1000·G·w·m)` density as the linear-gap theorem, but the canonical
depth threshold is the independent constant `30`. -/
theorem concreteRetry_strong_shellBudget (r : ℕ) (hr : 0 < r) :
    (concreteG * (∑ t ∈ Finset.Icc concreteT (20 * r),
      (concreteScale * r).choose (20 * r - t) *
        2 ^ (concreteScale * r - (20 * r - t)) *
          (2 * concreteT * concreteTerms) ^ t)) * 2 ^ concreteT ≤
      (concreteScale * r).choose (20 * r) *
        2 ^ (concreteScale * r - 20 * r) := by
  let E : ℕ := concreteG * (concreteT * concreteTerms)
  have hE : 0 < E := by
    norm_num [E, concreteG, concreteM, concreteT, concreteTerms]
  have hK : 20 * r ≤ concreteScale * r := by
    norm_num [concreteScale, concreteG, concreteM, concreteT, concreteTerms]
    omega
  have hfull : (0 : ℚ) < (concreteScale * r).choose (20 * r) := by
    exact_mod_cast Nat.choose_pos hK
  have hterm : ∀ t ∈ Finset.Icc concreteT (20 * r),
      (((concreteScale * r).choose (20 * r - t) : ℕ) : ℚ) *
          (4 * concreteT * concreteTerms : ℕ) ^ t ≤
        ((concreteScale * r).choose (20 * r) : ℕ) *
          ((4 : ℚ) / (49 * concreteG)) ^ t := by
    intro t ht
    have htK : t ≤ 20 * r := (Finset.mem_Icc.mp ht).2
    have hratio := fixedTerm_choose_shell_ratio E r t hE hr htK
    have hscale : 1000 * E * r = concreteScale * r := by
      simp [E, concreteScale]
    rw [hscale] at hratio
    have hratio' :
        (((concreteScale * r).choose (20 * r - t) : ℕ) : ℚ) /
            (concreteScale * r).choose (20 * r) ≤
          ((1 : ℚ) / (49 * E)) ^ t := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hratio
    calc
      (((concreteScale * r).choose (20 * r - t) : ℕ) : ℚ) *
          (4 * concreteT * concreteTerms : ℕ) ^ t
        = ((((concreteScale * r).choose (20 * r - t) : ℚ) /
              (concreteScale * r).choose (20 * r)) *
                (concreteScale * r).choose (20 * r)) *
                  (4 * concreteT * concreteTerms : ℕ) ^ t := by
                    field_simp [ne_of_gt hfull]
      _ ≤ (((1 : ℚ) / (49 * E)) ^ t *
              (concreteScale * r).choose (20 * r)) *
                (4 * concreteT * concreteTerms : ℕ) ^ t := by
                  gcongr
      _ = ((concreteScale * r).choose (20 * r) : ℕ) *
          ((4 : ℚ) / (49 * concreteG)) ^ t := by
            have hcancel :
                ((1 : ℚ) / (49 * E)) ^ t *
                    ((4 * concreteT * concreteTerms : ℕ) : ℚ) ^ t =
                  ((4 : ℚ) / (49 * concreteG)) ^ t := by
              rw [← mul_pow]
              norm_num [E, concreteG, concreteM, concreteT, concreteTerms]
            rw [← hcancel]
            ring
  have hsum := Finset.sum_le_sum hterm
  have hgeom := concreteRetry_strong_geometric_budget r
  have hnormalized :
      ((2 : ℚ) ^ concreteT) * concreteG *
          (∑ t ∈ Finset.Icc concreteT (20 * r),
            (((concreteScale * r).choose (20 * r - t) : ℕ) : ℚ) *
              (4 * concreteT * concreteTerms : ℕ) ^ t) ≤
        ((concreteScale * r).choose (20 * r) : ℕ) := by
    calc
      ((2 : ℚ) ^ concreteT) * concreteG *
          (∑ t ∈ Finset.Icc concreteT (20 * r),
            (((concreteScale * r).choose (20 * r - t) : ℕ) : ℚ) *
              (4 * concreteT * concreteTerms : ℕ) ^ t)
        ≤ (2 ^ concreteT) * concreteG *
            ((concreteScale * r).choose (20 * r) *
              ∑ t ∈ Finset.Icc concreteT (20 * r),
                ((4 : ℚ) / (49 * concreteG)) ^ t) := by
                  gcongr
                  simpa [Finset.mul_sum] using hsum
      _ = ((concreteScale * r).choose (20 * r) : ℕ) *
          ((2 ^ concreteT) * concreteG *
            ∑ t ∈ Finset.Icc concreteT (20 * r),
              ((4 : ℚ) / (49 * concreteG)) ^ t) := by ring
      _ ≤ ((concreteScale * r).choose (20 * r) : ℕ) := by
        nlinarith
  have hnormalizedNat :
      ((2 ^ concreteT) * concreteG) *
          (∑ t ∈ Finset.Icc concreteT (20 * r),
            (concreteScale * r).choose (20 * r - t) *
              (4 * concreteT * concreteTerms) ^ t) ≤
        (concreteScale * r).choose (20 * r) := by
    exact_mod_cast hnormalized
  have hfactor :
      (∑ t ∈ Finset.Icc concreteT (20 * r),
        (concreteScale * r).choose (20 * r - t) *
          2 ^ (concreteScale * r - (20 * r - t)) *
            (2 * concreteT * concreteTerms) ^ t) =
        2 ^ (concreteScale * r - 20 * r) *
          (∑ t ∈ Finset.Icc concreteT (20 * r),
            (concreteScale * r).choose (20 * r - t) *
              (4 * concreteT * concreteTerms) ^ t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have htK : t ≤ 20 * r := (Finset.mem_Icc.mp ht).2
    have hpow :
        2 ^ t * (2 * concreteT * concreteTerms) ^ t =
          (4 * concreteT * concreteTerms) ^ t := by
      rw [← mul_pow]
      congr 1
    rw [show concreteScale * r - (20 * r - t) =
        (concreteScale * r - 20 * r) + t by omega, pow_add]
    calc
      (concreteScale * r).choose (20 * r - t) *
          (2 ^ (concreteScale * r - 20 * r) * 2 ^ t) *
            (2 * concreteT * concreteTerms) ^ t
        = 2 ^ (concreteScale * r - 20 * r) *
            ((concreteScale * r).choose (20 * r - t) *
              (2 ^ t * (2 * concreteT * concreteTerms) ^ t)) := by ring
      _ = 2 ^ (concreteScale * r - 20 * r) *
          ((concreteScale * r).choose (20 * r - t) *
            (4 * concreteT * concreteTerms) ^ t) := by rw [hpow]
  rw [hfactor]
  calc
    (concreteG *
        (2 ^ (concreteScale * r - 20 * r) *
          ∑ t ∈ Finset.Icc concreteT (20 * r),
            (concreteScale * r).choose (20 * r - t) *
              (4 * concreteT * concreteTerms) ^ t)) * 2 ^ concreteT
      = 2 ^ (concreteScale * r - 20 * r) *
          (((2 ^ concreteT) * concreteG) *
            ∑ t ∈ Finset.Icc concreteT (20 * r),
              (concreteScale * r).choose (20 * r - t) *
                (4 * concreteT * concreteTerms) ^ t) := by ring
    _ ≤ 2 ^ (concreteScale * r - 20 * r) *
        (concreteScale * r).choose (20 * r) :=
      Nat.mul_le_mul_left _ hnormalizedNat
    _ = (concreteScale * r).choose (20 * r) *
        2 ^ (concreteScale * r - 20 * r) := by ring

/-- The former half-budget is an immediate weakening of the 30-bit retry budget. -/
theorem concreteRetry_shellBudget (r : ℕ) (hr : 0 < r) :
    (concreteG * (∑ t ∈ Finset.Icc concreteT (20 * r),
      (concreteScale * r).choose (20 * r - t) *
        2 ^ (concreteScale * r - (20 * r - t)) *
          (2 * concreteT * concreteTerms) ^ t)) * 2 ≤
      (concreteScale * r).choose (20 * r) *
        2 ^ (concreteScale * r - 20 * r) := by
  apply le_trans (Nat.mul_le_mul_left _ (show 2 ≤ 2 ^ concreteT by
    norm_num [concreteT]))
  exact concreteRetry_strong_shellBudget r hr

theorem deterministicRetryCertificate_atSize
    (N G w m K threshold : ℕ) [NeZero w] [NeZero m]
    (hK : K ≤ N) (hq : 1 ≤ N - K)
    (gates : Fin G → List (Clause N))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ w)
    (hterms : ∀ g, (gates g).length ≤ m)
    (hbudget :
      (G * (∑ t ∈ Finset.Icc threshold K,
        N.choose (K - t) * 2 ^ (N - (K - t)) * (2 * w * m) ^ t)) * 2
        ≤ N.choose K * 2 ^ (N - K)) :
    ∃ i : Fin (N.choose K),
      concreteBadCount (K := K) (circuitBad gates K threshold) i ≤
        2 ^ ((N - K) - 1) := by
  have hstars : ∀ ρ ∈ circuitBad gates K threshold, stars ρ = K :=
    fun ρ hρ => circuitBad_stars gates K threshold ρ hρ
  have hcard := circuitBad_card_le_shellSum gates K threshold hwidth hterms
  have htail : (circuitBad gates K threshold).card * 2 ≤
      N.choose K * 2 ^ (N - K) :=
    le_trans (Nat.mul_le_mul_right 2 hcard) hbudget
  have hsum := sum_concreteBadCount (Bad := circuitBad gates K threshold) hstars
  apply exists_bucket_badCount_le (N.choose K) (N - K) 0
  · exact Nat.choose_pos hK
  · omega
  · rw [hsum]
    simpa using htail

/-- Saving-parameter version of the deterministic retry selector. -/
theorem deterministicRetryCertificateSaving_atSize
    (N G w m K threshold saving : ℕ) [NeZero w] [NeZero m]
    (hK : K ≤ N) (hsq : saving + 1 ≤ N - K)
    (gates : Fin G → List (Clause N))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ w)
    (hterms : ∀ g, (gates g).length ≤ m)
    (hbudget :
      (G * (∑ t ∈ Finset.Icc threshold K,
        N.choose (K - t) * 2 ^ (N - (K - t)) * (2 * w * m) ^ t)) *
          2 ^ (saving + 1) ≤ N.choose K * 2 ^ (N - K)) :
    ∃ i : Fin (N.choose K),
      concreteBadCount (K := K) (circuitBad gates K threshold) i ≤
        2 ^ ((N - K) - saving - 1) := by
  have hstars : ∀ ρ ∈ circuitBad gates K threshold, stars ρ = K :=
    fun ρ hρ => circuitBad_stars gates K threshold ρ hρ
  have hcard := circuitBad_card_le_shellSum gates K threshold hwidth hterms
  have htail : (circuitBad gates K threshold).card * 2 ^ (saving + 1) ≤
      N.choose K * 2 ^ (N - K) :=
    le_trans (Nat.mul_le_mul_right _ hcard) hbudget
  have hsum := sum_concreteBadCount (Bad := circuitBad gates K threshold) hstars
  apply exists_bucket_badCount_le (N.choose K) (N - K) saving
  · exact Nat.choose_pos hK
  · exact hsq
  · rw [hsum]
    exact htail

/-- The same half-bad retry certificate on an arbitrary current subcube, after exact localization
of its genuine ambient gate family. -/
theorem deterministicRetryCertificate_subcube
    {n G w m K threshold : ℕ} [NeZero w] [NeZero m]
    (τ : Restriction n) (hK : K ≤ stars τ) (hq : 1 ≤ stars τ - K)
    (gates : Fin G → List (Clause n))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ w)
    (hterms : ∀ g, (gates g).length ≤ m)
    (hbudget :
      (G * (∑ t ∈ Finset.Icc threshold K,
        (stars τ).choose (K - t) * 2 ^ (stars τ - (K - t)) * (2 * w * m) ^ t)) * 2
        ≤ (stars τ).choose K * 2 ^ (stars τ - K)) :
    ∃ i : Fin ((stars τ).choose K),
      concreteBadCount (K := K)
        (circuitBad (localizeLiveGates τ gates) K threshold) i ≤
          2 ^ ((stars τ - K) - 1) := by
  apply deterministicRetryCertificate_atSize (stars τ) G w m K threshold hK hq
    (localizeLiveGates τ gates)
  · exact localizeLiveGates_width_le τ gates hwidth
  · exact localizeLiveGates_count_le τ gates hterms
  · exact hbudget

theorem deterministicRetryCertificateSaving_subcube
    {n G w m K threshold saving : ℕ} [NeZero w] [NeZero m]
    (τ : Restriction n) (hK : K ≤ stars τ)
    (hsq : saving + 1 ≤ stars τ - K)
    (gates : Fin G → List (Clause n))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ w)
    (hterms : ∀ g, (gates g).length ≤ m)
    (hbudget :
      (G * (∑ t ∈ Finset.Icc threshold K,
        (stars τ).choose (K - t) * 2 ^ (stars τ - (K - t)) * (2 * w * m) ^ t)) *
          2 ^ (saving + 1) ≤ (stars τ).choose K * 2 ^ (stars τ - K)) :
    ∃ i : Fin ((stars τ).choose K),
      concreteBadCount (K := K)
        (circuitBad (localizeLiveGates τ gates) K threshold) i ≤
          2 ^ ((stars τ - K) - saving - 1) := by
  apply deterministicRetryCertificateSaving_atSize (stars τ) G w m K threshold saving
    hK hsq (localizeLiveGates τ gates)
  · exact localizeLiveGates_width_le τ gates hwidth
  · exact localizeLiveGates_count_le τ gates hterms
  · exact hbudget

/-- The numerical constant-threshold retry selector.  For every positive scale, one complete
`20r`-star bucket has at most half genuinely bad children at canonical depth `30`. -/
theorem concreteRetryCertificate (r : ℕ) [NeZero r]
    (gates : Fin concreteG → List (Clause (concreteScale * r)))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms) :
    ∃ i : Fin ((concreteScale * r).choose (20 * r)),
      concreteBadCount (K := 20 * r)
        (circuitBad gates (20 * r) concreteT) i ≤
          2 ^ (((concreteScale * r - 20 * r) - 1)) := by
  letI : NeZero concreteT := ⟨by norm_num [concreteT]⟩
  letI : NeZero concreteTerms :=
    ⟨by norm_num [concreteTerms, concreteM, concreteT]⟩
  apply deterministicRetryCertificate_atSize
    (concreteScale * r) concreteG concreteT concreteTerms (20 * r) concreteT
  · norm_num [concreteScale, concreteG, concreteM, concreteT, concreteTerms]
    omega
  · have hr := NeZero.pos r
    norm_num [concreteScale, concreteG, concreteM, concreteT, concreteTerms]
    omega
  · exact hwidth
  · exact hterms
  · exact concreteRetry_shellBudget r (NeZero.pos r)

/-- The actual depth-30 tail gives a 30-bit contraction, not merely a half-bad contraction. -/
theorem concreteRetryStrongCertificate (r : ℕ) [NeZero r]
    (gates : Fin concreteG → List (Clause (concreteScale * r)))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms) :
    ∃ i : Fin ((concreteScale * r).choose (20 * r)),
      concreteBadCount (K := 20 * r)
        (circuitBad gates (20 * r) concreteT) i ≤
          2 ^ ((concreteScale * r - 20 * r) - concreteT) := by
  letI : NeZero concreteT := ⟨by norm_num [concreteT]⟩
  letI : NeZero concreteTerms :=
    ⟨by norm_num [concreteTerms, concreteM, concreteT]⟩
  simpa [show concreteT - 1 + 1 = concreteT by norm_num [concreteT]] using
    (deterministicRetryCertificateSaving_atSize
      (concreteScale * r) concreteG concreteT concreteTerms (20 * r) concreteT
        (concreteT - 1)
      (by
        norm_num [concreteScale, concreteG, concreteM, concreteT, concreteTerms]
        omega)
      (by
        have hr := NeZero.pos r
        norm_num [concreteScale, concreteG, concreteM, concreteT, concreteTerms]
        omega)
      gates hwidth hterms (concreteRetry_strong_shellBudget r (NeZero.pos r)))

/-- The same numerical selector at an arbitrary current subcube of the matching live size. -/
theorem concreteRetryCertificate_subcube {n r : ℕ} [NeZero r]
    (τ : Restriction n) (hstars : stars τ = concreteScale * r)
    (gates : Fin concreteG → List (Clause n))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms) :
    ∃ i : Fin ((stars τ).choose (20 * r)),
      concreteBadCount (K := 20 * r)
        (circuitBad (localizeLiveGates τ gates) (20 * r) concreteT) i ≤
          2 ^ (((stars τ - 20 * r) - 1)) := by
  letI : NeZero concreteT := ⟨by norm_num [concreteT]⟩
  letI : NeZero concreteTerms :=
    ⟨by norm_num [concreteTerms, concreteM, concreteT]⟩
  apply deterministicRetryCertificate_subcube
    (G := concreteG) (w := concreteT) (m := concreteTerms)
    (K := 20 * r) (threshold := concreteT) τ
  · rw [hstars]
    norm_num [concreteScale, concreteG, concreteM, concreteT, concreteTerms]
    omega
  · rw [hstars]
    have hr := NeZero.pos r
    norm_num [concreteScale, concreteG, concreteM, concreteT, concreteTerms]
    omega
  · exact hwidth
  · exact hterms
  · simpa [hstars] using concreteRetry_shellBudget r (NeZero.pos r)

theorem concreteRetryStrongCertificate_subcube {n r : ℕ} [NeZero r]
    (τ : Restriction n) (hstars : stars τ = concreteScale * r)
    (gates : Fin concreteG → List (Clause n))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms) :
    ∃ i : Fin ((stars τ).choose (20 * r)),
      concreteBadCount (K := 20 * r)
        (circuitBad (localizeLiveGates τ gates) (20 * r) concreteT) i ≤
          2 ^ ((stars τ - 20 * r) - concreteT) := by
  letI : NeZero concreteT := ⟨by norm_num [concreteT]⟩
  letI : NeZero concreteTerms :=
    ⟨by norm_num [concreteTerms, concreteM, concreteT]⟩
  apply deterministicRetryCertificateSaving_subcube
    (G := concreteG) (w := concreteT) (m := concreteTerms)
    (K := 20 * r) (threshold := concreteT) (saving := concreteT - 1) τ
  · rw [hstars]
    norm_num [concreteScale, concreteG, concreteM, concreteT, concreteTerms]
    omega
  · rw [hstars]
    have hr := NeZero.pos r
    norm_num [concreteScale, concreteG, concreteM, concreteT, concreteTerms]
    omega
  · exact hwidth
  · exact hterms
  · simpa [hstars, show concreteT - 1 + 1 = concreteT by norm_num [concreteT]] using
      concreteRetry_strong_shellBudget r (NeZero.pos r)

/-- Closed worst-case work recurrence for `j` retry levels.  The zero case brute-forces the final
live frontier.  At a retry node all good children pay `goodCost`, while the exact half-bad bound
controls the recursively unresolved children. -/
def concreteRetryWorstWork : ℕ → ℕ → (ℕ → ℕ) → ℕ
  | 0, r, _ => 2 ^ (concreteScale * r)
  | j + 1, r, goodCost =>
      let s := r * concreteCoverB ^ (j + 1)
      let q := concreteScale * s - 20 * s
      retrySpliceWork (2 ^ q) (2 ^ (q - concreteT)) (goodCost s)
        (concreteRetryWorstWork j r goodCost)

private theorem two_mul_succ_le_two_pow_succ (j : ℕ) :
    2 * (j + 1) ≤ 2 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [pow_succ]
      omega

/-- Each retry level converts the 30-bit bad-set contraction into 29 new exponent-saving bits;
the remaining bit pays for adding the terminating-good and continuing-bad contributions. -/
theorem concreteRetryWorstWork_le (j r : ℕ) [NeZero r] (goodCost : ℕ → ℕ)
    (hgood : ∀ k < j,
      goodCost (r * concreteCoverB ^ (k + 1)) ≤
        2 ^ (20 * (r * concreteCoverB ^ (k + 1)) -
          ((k + 1) * (concreteT - 1)) - 1)) :
    concreteRetryWorstWork j r goodCost ≤
      2 ^ (concreteScale * (r * concreteCoverB ^ j) -
        j * (concreteT - 1)) := by
  induction j with
  | zero => simp [concreteRetryWorstWork]
  | succ j ih =>
      let s := r * concreteCoverB ^ (j + 1)
      let q := concreteScale * s - 20 * s
      have hspos : 0 < s := by
        exact Nat.mul_pos (NeZero.pos r) (pow_pos (by
          exact lt_trans (by omega) concreteCoverB_gt_three) _)
      have hKs : 20 * s ≤ concreteScale * s := by
        have hscale : 20 ≤ concreteScale := by
          rw [concreteScale_eq_twenty_mul_coverB]
          have := concreteCoverB_gt_three
          omega
        exact Nat.mul_le_mul_right s hscale
      have hchild :
          concreteRetryWorstWork j r goodCost ≤
            2 ^ (20 * s - j * (concreteT - 1)) := by
        have hi := ih (fun k hk => hgood k (by omega))
        rw [show 20 * s = concreteScale * (r * concreteCoverB ^ j) by
          simp [s, pow_succ]; rw [concreteScale_eq_twenty_mul_coverB]; ac_rfl]
        exact hi
      rw [concreteRetryWorstWork]
      change retrySpliceWork (2 ^ q) (2 ^ (q - concreteT)) (goodCost s)
          (concreteRetryWorstWork j r goodCost) ≤
        2 ^ (concreteScale * s - (j + 1) * (concreteT - 1))
      rw [show (j + 1) * (concreteT - 1) =
        j * (concreteT - 1) + concreteT - 1 by
          norm_num [concreteT]
          ring]
      apply retrySpliceWork_gain_le
        (concreteScale * s) q (20 * s) (2 ^ q) (2 ^ (q - concreteT))
        (goodCost s) (concreteRetryWorstWork j r goodCost)
        (j * (concreteT - 1)) concreteT
      · simp [q]
        omega
      · norm_num [concreteT]
      · simp [q]
        norm_num [concreteScale, concreteG, concreteM, concreteT, concreteTerms]
        omega
      · have hj : j * (concreteT - 1) + concreteT ≤ 20 * s := by
          have htwo := two_mul_succ_le_two_pow_succ j
          have hslarge : 2 * (j + 1) ≤ s := by
            dsimp [s]
            have hB : 2 ≤ concreteCoverB := by
              have := concreteCoverB_gt_three
              omega
            have hp : 2 ^ (j + 1) ≤ concreteCoverB ^ (j + 1) :=
              Nat.pow_le_pow_left hB _
            exact le_trans (le_trans htwo hp)
              (Nat.le_mul_of_pos_left _ (NeZero.pos r))
          norm_num [concreteT] at *
          nlinarith
        exact hj
      · exact le_rfl
      · rw [show j * (concreteT - 1) + concreteT - 1 =
          (j + 1) * (concreteT - 1) by
            norm_num [concreteT]
            ring]
        exact hgood j (by omega)
      · exact le_rfl
      · exact hchild

/-- A genuine finite retry tree of any prescribed height.  At every internal node the same
constant-depth certificate is selected on the current live cube; good children stop and every bad
child is recursively retried.  At height zero the remaining frontier is explicitly brute-forced.
The scale `concreteCoverB` makes the child dimension exactly the next recursive input. -/
theorem exists_concreteRetryCover {n : ℕ} (j r : ℕ) [NeZero r]
    (τ : Restriction n)
    (hstars : stars τ = concreteScale * (r * concreteCoverB ^ j))
    (gates : Fin concreteG → List (Clause n))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms)
    (goodCost : ℕ → ℕ) :
    ∃ cover : RetryCover n,
      cover.root = τ ∧ cover.height ≤ j ∧
      cover.work ≤ concreteRetryWorstWork j r goodCost ∧
      (j = 0 → cover.work = 2 ^ stars τ) := by
  classical
  induction j generalizing τ with
  | zero =>
      refine ⟨.leaf τ (2 ^ stars τ), rfl, by simp [RetryCover.height], ?_, ?_⟩
      · simp [RetryCover.work, concreteRetryWorstWork, hstars]
      · simp [RetryCover.work]
  | succ j ih =>
      let s : ℕ := r * concreteCoverB ^ (j + 1)
      have hspos : 0 < s := by
        exact Nat.mul_pos (NeZero.pos r) (pow_pos (by
          exact lt_trans (by omega) concreteCoverB_gt_three) _)
      letI : NeZero s := ⟨Nat.ne_of_gt hspos⟩
      have hstars' : stars τ = concreteScale * s := by
        simpa [s] using hstars
      obtain ⟨i, hi⟩ := concreteRetryStrongCertificate_subcube τ hstars' gates hwidth hterms
      let bad := selectedBadChildren (threshold := concreteT) τ gates i
      have hchildStars : ∀ ρ : {ρ : Restriction n // ρ ∈ bad},
          stars ρ.1 = concreteScale * (r * concreteCoverB ^ j) := by
        intro ρ
        have hbuck : ρ.1 ∈ liftedSelectedBucket τ (20 * s) i :=
          selectedBadChildren_subset (threshold := concreteT) τ gates i ρ.2
        rw [liftedSelectedBucket_stars τ i hbuck]
        rw [show s = concreteCoverB * (r * concreteCoverB ^ j) by
          simp [s, pow_succ]; ac_rfl]
        exact concreteCover_live_exact (r * concreteCoverB ^ j)
      choose retries hroot hheight hwork hleaf using
        fun ρ : {ρ : Restriction n // ρ ∈ bad} =>
        ih ρ.1 (hchildStars ρ)
      let cover := selectedRetryNode τ gates i (goodCost s) retries
      refine ⟨cover, ?_, ?_, ?_, ?_⟩
      · rfl
      · simp only [cover, selectedRetryNode, RetryCover.height]
        have hsup :
            ((selectedBadChildren (threshold := concreteT) τ gates i).attach.sup
              fun ρ => (retries ρ).height) ≤ j := by
          apply Finset.sup_le
          intro ρ hρ
          exact hheight ρ
        omega
      · apply le_trans (selectedRetryNode_work_le_splice τ gates i (goodCost s)
          (concreteRetryWorstWork j r goodCost) retries hwork)
        rw [concreteRetryWorstWork]
        apply Nat.add_le_add
        · apply Nat.mul_le_mul_right
          simpa [hstars'] using card_selectedGoodChildren_le τ gates i
        · apply Nat.mul_le_mul_right
          rw [card_selectedBadChildren]
          simpa [hstars'] using hi
      · omega

/-- End-to-end quantitative retry cash-out.  Under the displayed bound for each good child's
collapsed-layer solver, the actual exhaustive retry tree saves `29j` exponent bits. -/
theorem exists_concreteRetryCover_linearGap {n : ℕ} (j r : ℕ) [NeZero r]
    (τ : Restriction n)
    (hstars : stars τ = concreteScale * (r * concreteCoverB ^ j))
    (gates : Fin concreteG → List (Clause n))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms)
    (goodCost : ℕ → ℕ)
    (hgood : ∀ k < j,
      goodCost (r * concreteCoverB ^ (k + 1)) ≤
        2 ^ (20 * (r * concreteCoverB ^ (k + 1)) -
          ((k + 1) * (concreteT - 1)) - 1)) :
    ∃ cover : RetryCover n,
      cover.root = τ ∧ cover.height ≤ j ∧
      cover.work ≤ 2 ^ (stars τ - j * (concreteT - 1)) := by
  obtain ⟨cover, hroot, hheight, hwork, _⟩ :=
    exists_concreteRetryCover j r τ hstars gates hwidth hterms goodCost
  refine ⟨cover, hroot, hheight, hwork.trans ?_⟩
  simpa [hstars] using concreteRetryWorstWork_le j r goodCost hgood

/-- The stronger concrete certificate keeps the exceptional-count half-budget and the full work
bound attached to the same selected bucket. -/
theorem concreteDeterministicRoundCertificate_atSize (N r : ℕ) [NeZero r]
    (hN : N = concreteScale * r)
    (gates : Fin concreteG → List (Clause N))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms) :
    ∃ i : Fin (N.choose (20 * r)),
      concreteBadCount (K := 20 * r) (circuitBad gates (20 * r) (10 * r)) i ≤
        2 ^ ((N - 20 * r) - 9 * r - 1) ∧
      goodBadWork N (N - 20 * r) (2 ^ (N - 20 * r))
        (concreteBadCount (K := 20 * r) (circuitBad gates (20 * r) (10 * r)) i)
        (10 * r - 1) ≤ 2 ^ (N - 9 * r) := by
  subst N
  letI : NeZero concreteG := ⟨by norm_num [concreteG, concreteM]⟩
  letI : NeZero concreteT := ⟨by norm_num [concreteT]⟩
  letI : NeZero concreteTerms := ⟨by norm_num [concreteTerms, concreteM, concreteT]⟩
  simpa [concreteScale, concreteG] using
    wideCircuitLinearGap_selectedBucket_certificate concreteG concreteT concreteTerms r
      gates hwidth hterms

/-- The concrete selected-bucket theorem with its ambient dimension exposed as
an equality, so it can be instantiated at `stars τ` without hiding a cast. -/
theorem concreteDeterministicRoundGap_atSize (N r : ℕ) [NeZero r]
    (hN : N = concreteScale * r)
    (gates : Fin concreteG → List (Clause N))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms) :
    ∃ i : Fin (N.choose (20 * r)),
      goodBadWork N (N - 20 * r) (2 ^ (N - 20 * r))
        (concreteBadCount (K := 20 * r) (circuitBad gates (20 * r) (10 * r)) i)
        (10 * r - 1) ≤ 2 ^ (N - 9 * r) := by
  subst N
  exact concreteDeterministicRoundGap r gates hwidth hterms

/-- A deterministic, exhaustive, fully charged bucket on an arbitrary current
subcube of the required live size.  Its bad restrictions are exactly the local
representatives of genuine ambient bad extensions. -/
theorem concreteDeterministicRoundGap_subcube {n : ℕ} (r : ℕ) [NeZero r]
    (τ : Restriction n) (hstars : stars τ = concreteScale * r)
    (gates : Fin concreteG → List (Clause n))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms) :
    ∃ i : Fin ((stars τ).choose (20 * r)),
      goodBadWork (stars τ) (stars τ - 20 * r)
        (2 ^ (stars τ - 20 * r))
        (concreteBadCount (K := 20 * r)
          (circuitBad (localizeLiveGates τ gates) (20 * r) (10 * r)) i)
        (10 * r - 1) ≤ 2 ^ (stars τ - 9 * r) := by
  apply concreteDeterministicRoundGap_atSize (stars τ) r hstars
    (localizeLiveGates τ gates)
  · exact localizeLiveGates_width_le τ gates hwidth
  · exact localizeLiveGates_count_le τ gates hterms

/-- Shared selected-bucket certificate relativized to an arbitrary current subcube. -/
theorem concreteDeterministicRoundCertificate_subcube {n : ℕ} (r : ℕ) [NeZero r]
    (τ : Restriction n) (hstars : stars τ = concreteScale * r)
    (gates : Fin concreteG → List (Clause n))
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms) :
    ∃ i : Fin ((stars τ).choose (20 * r)),
      concreteBadCount (K := 20 * r)
          (circuitBad (localizeLiveGates τ gates) (20 * r) (10 * r)) i ≤
        2 ^ (((stars τ) - 20 * r) - 9 * r - 1) ∧
      goodBadWork (stars τ) (stars τ - 20 * r) (2 ^ (stars τ - 20 * r))
        (concreteBadCount (K := 20 * r)
          (circuitBad (localizeLiveGates τ gates) (20 * r) (10 * r)) i)
        (10 * r - 1) ≤ 2 ^ (stars τ - 9 * r) := by
  apply concreteDeterministicRoundCertificate_atSize (stars τ) r hstars
    (localizeLiveGates τ gates)
  · exact localizeLiveGates_width_le τ gates hwidth
  · exact localizeLiveGates_count_le τ gates hterms

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
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.deterministicRetryCertificate_atSize
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.deterministicRetryCertificate_subcube
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteRetry_strong_geometric_budget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteRetry_strong_shellBudget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteRetry_shellBudget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteRetryCertificate
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteRetryCertificate_subcube
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_concreteRetryCover
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteRetryWorstWork_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_concreteRetryCover_linearGap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteDeterministicRoundGap_atSize
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteDeterministicRoundGap_subcube
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteDeterministicRoundCertificate_subcube
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.stars_liftLiveRestriction
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.liveRestrictionEquiv
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveLiteral_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveGates_width_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveDnf_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveGates_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveClause_freeLits
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveClause_termFalsified
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveDnf_anyTermSat
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveDnf_activeTerm
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.liftLiveRestriction_fixVar
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.canonicalDT_depth_localize
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.mem_boundedTermBad_localize_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.mem_circuitBad_localize_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.liftedSelectedBucket_extends
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.liftedSelectedBucket_coverSched_stars
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_selectedBadChildren
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.selectedChargedNode_work_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.selectedRetryNode_work_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.padded_good_collapseRound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.deterministic_parent_threshold_exceeds_closed
