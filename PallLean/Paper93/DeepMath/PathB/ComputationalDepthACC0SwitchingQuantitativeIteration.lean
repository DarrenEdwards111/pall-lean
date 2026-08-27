import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingCircuitLinearGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingCompactPolynomialBudget
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3IteratedReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundCount2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvRoundREL2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecursiveTowerSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictionCardinality
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSkipCollision
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GeomTail
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingLayeredBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingNormalize
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingSupportSurvivor
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityCount

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
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermFamily
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellAveraging
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingTailIntegerBridge
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingFixedTermLinearGap
open PallLean.Paper93.DeepMath.PathB.MultiSwitching

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

/-- Extending a live-cube assignment to the ambient cube loses no information: every input bit
can be read back at its corresponding live ambient coordinate. -/
theorem liftLiveAssignment_injective {n : ℕ} (τ : Restriction n) :
    Function.Injective (liftLiveAssignment τ) := by
  intro x y hxy
  funext i
  have hi := congrFun hxy (liveCoordEquiv τ i)
  simpa using hi

/-! ### Parity phase under live-coordinate localization -/

/-- The number of ambient coordinates fixed to `true` by a restriction. -/
def fixedTrueCount {n : ℕ} (τ : Restriction n) : ℕ :=
  (Finset.univ.filter (fun v => τ v = some true)).card

/-- The fixed-coordinate phase acquired when ambient parity is restricted to the live cube. -/
def fixedParityPhase {n : ℕ} (τ : Restriction n) : Bool :=
  decide (Odd (fixedTrueCount τ))

/-- Oddness of a sum is Boolean xor of the two summands' oddness bits. -/
theorem decide_odd_add (a b : ℕ) :
    decide (Odd (a + b)) = xor (decide (Odd a)) (decide (Odd b)) := by
  by_cases ha : Odd a <;> by_cases hb : Odd b <;>
    simp [ha, hb, Nat.odd_add, Nat.not_odd_iff_even.mp]

/-- Extending a live assignment adds exactly the `true` coordinates already fixed by the
restriction.  This is the counting identity behind the parity phase. -/
theorem trueCount_liftLiveAssignment {n : ℕ} (τ : Restriction n)
    (x : Fin (stars τ) → Bool) :
    DTree.trueCount (liftLiveAssignment τ x) =
      DTree.trueCount x + fixedTrueCount τ := by
  classical
  let A := Finset.univ.filter (fun v => liftLiveAssignment τ x v = true)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := A) (fun v => v ∈ freeVars τ)
  have hlive :
      (A.filter (fun v => v ∈ freeVars τ)).card = DTree.trueCount x := by
    have hset :
        A.filter (fun v => v ∈ freeVars τ) =
          (Finset.univ.filter (fun i => x i = true)).image
            (fun i => (liveCoordEquiv τ i).1) := by
      ext v
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨hvtrue, hvfree⟩
        let i : Fin (stars τ) := (liveCoordEquiv τ).symm ⟨v, hvfree⟩
        refine ⟨i, ?_, ?_⟩
        · simpa [liftLiveAssignment, hvfree, i] using hvtrue
        · simp [i]
      · rintro ⟨i, hitrue, rfl⟩
        exact ⟨by simpa using hitrue, (liveCoordEquiv τ i).property⟩
    rw [hset, Finset.card_image_of_injective]
    · rfl
    · intro i j hij
      exact (liveCoordEquiv τ).injective (Subtype.ext hij)
  have hfixed :
      (A.filter (fun v => ¬ v ∈ freeVars τ)).card = fixedTrueCount τ := by
    congr 1
    ext v
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv : v ∈ freeVars τ
    · have hnone : τ v = none := by simpa [mem_freeVars] using hv
      simp [hv, hnone]
    · have hne : τ v ≠ none := by simpa [mem_freeVars] using hv
      cases hτ : τ v with
      | none => exact (hne hτ).elim
      | some b => cases b <;> simp [liftLiveAssignment, hv, hτ]
  rw [hlive, hfixed] at hsplit
  simpa [DTree.trueCount, A] using hsplit.symm

/-- Ambient parity on a restricted subcube is live-coordinate parity xor the phase of the
coordinates fixed to `true`. -/
theorem parity_liftLiveAssignment {n : ℕ} (τ : Restriction n)
    (x : Fin (stars τ) → Bool) :
    DTree.parity (liftLiveAssignment τ x) =
      xor (DTree.parity x) (fixedParityPhase τ) := by
  rw [DTree.parity, trueCount_liftLiveAssignment, decide_odd_add]
  rfl

/-- Complementing parity by an arbitrary fixed phase does not weaken the decision-tree lower
bound.  This is the localization-aware cashout interface: unlike the older same-ambient theorem,
it is stated directly on the relabelled live cube. -/
theorem DTree.shallow_dtree_not_parity_xor {m : ℕ} (t : DTree m) (phase : Bool)
    (hd : t.depth < m) :
    ∃ x, t.eval x ≠ xor (DTree.parity x) phase := by
  cases phase with
  | false => simpa using DTree.shallow_dtree_not_parity t hd
  | true =>
      have hdepth : (DTree.negTree t).depth < m := by
        simpa [DTree.negTree_depth] using hd
      obtain ⟨x, hx⟩ := DTree.shallow_dtree_not_parity (DTree.negTree t) hdepth
      refine ⟨x, ?_⟩
      rw [DTree.negTree_eval] at hx
      cases ht : t.eval x <;> cases hp : DTree.parity x <;> simp_all

/-- The image of the canonical live-cube embedding is exactly the set of total assignments
agreeing with the fixed coordinates of the restriction. -/
theorem exists_liftLiveAssignment_eq_iff_agrees {n : ℕ} (τ : Restriction n)
    (x : Fin n → Bool) :
    (∃ z : Fin (stars τ) → Bool, liftLiveAssignment τ z = x) ↔
      DTree.agreeRestriction τ x := by
  constructor
  · rintro ⟨z, rfl⟩
    exact liftLiveAssignment_agrees τ z
  · intro hx
    refine ⟨fun i => x (liveCoordEquiv τ i), ?_⟩
    funext v
    by_cases hv : v ∈ freeVars τ
    · simp [liftLiveAssignment, hv]
    · have hfixed : τ v ≠ none := by
        intro hnone
        apply hv
        rw [mem_freeVars, hnone]
      cases hτ : τ v with
      | none => exact (hfixed hτ).elim
      | some b =>
          simpa [liftLiveAssignment, hv, hτ] using (hx v b hτ).symm

/-- The finite cube of total assignments compatible with a restriction. -/
noncomputable def assignmentsAgreeingRestriction {n : ℕ} (τ : Restriction n) :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter fun x => DTree.agreeRestriction τ x

/-- A restriction with `stars τ` live coordinates has exactly `2 ^ stars τ` compatible total
assignments.  This is the assignment-side counterpart of the earlier binomial count of
restrictions compatible with one fixed assignment. -/
theorem card_assignments_agreeing_restriction {n : ℕ} (τ : Restriction n) :
    (assignmentsAgreeingRestriction τ).card = 2 ^ stars τ := by
  classical
  have himage :
      (Finset.univ : Finset (Fin (stars τ) → Bool)).image (liftLiveAssignment τ) =
        assignmentsAgreeingRestriction τ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      assignmentsAgreeingRestriction, Finset.mem_filter]
    exact exists_liftLiveAssignment_eq_iff_agrees τ x
  rw [← himage, Finset.card_image_of_injective _ (liftLiveAssignment_injective τ)]
  simp [Fintype.card_fin, Fintype.card_bool]

/-- The canonical restriction of an agreeing ambient assignment to the live coordinates lifts
back to that same ambient assignment. -/
theorem liftLiveAssignment_restrict_eq_of_agrees {n : ℕ} (τ : Restriction n)
    (x : Fin n → Bool) (hx : DTree.agreeRestriction τ x) :
    liftLiveAssignment τ (fun i => x (liveCoordEquiv τ i)) = x := by
  funext v
  by_cases hv : v ∈ freeVars τ
  · simp [liftLiveAssignment, hv]
  · have hfixed : τ v ≠ none := by
      intro hnone
      apply hv
      rw [mem_freeVars, hnone]
    cases hτ : τ v with
    | none => exact (hfixed hτ).elim
    | some b =>
        simpa [liftLiveAssignment, hv, hτ] using (hx v b hτ).symm

/-- Two restrictions are compatible when they never fix one ambient coordinate to opposite
Boolean values.  They may still have different live sets. -/
def RestrictionsCompatible {n : ℕ} (τ υ : Restriction n) : Prop :=
  ∀ v b c, τ v = some b → υ v = some c → b = c

/-- Compatibility is exactly the existence of a common total extension. -/
theorem restrictionsCompatible_iff_exists_agrees {n : ℕ} (τ υ : Restriction n) :
    RestrictionsCompatible τ υ ↔
      ∃ x : Fin n → Bool,
        DTree.agreeRestriction τ x ∧ DTree.agreeRestriction υ x := by
  constructor
  · intro hcompat
    let x : Fin n → Bool := fun v => (τ v).getD ((υ v).getD false)
    refine ⟨x, ?_, ?_⟩
    · intro v b hτ
      simp [x, hτ]
    · intro v b hυ
      cases hτ : τ v with
      | none => simp [x, hτ, hυ]
      | some c =>
          have hcb : c = b := hcompat v c b hτ hυ
          simp [x, hτ, hcb]
  · rintro ⟨x, hxτ, hxυ⟩ v b c hτ hυ
    exact (hxτ v b hτ).symm.trans (hxυ v c hυ)

/-- The unique restriction with prescribed live-variable set `S` that agrees with `x` on every
fixed coordinate. -/
def restrictionWithFreeSet {n : ℕ} (x : Fin n → Bool) (S : Finset (Fin n)) :
    Restriction n :=
  fun v => if v ∈ S then none else some (x v)

@[simp] theorem freeVars_restrictionWithFreeSet {n : ℕ} (x : Fin n → Bool)
    (S : Finset (Fin n)) :
    freeVars (restrictionWithFreeSet x S) = S := by
  ext v
  simp [mem_freeVars, restrictionWithFreeSet]

@[simp] theorem stars_restrictionWithFreeSet {n : ℕ} (x : Fin n → Bool)
    (S : Finset (Fin n)) :
    stars (restrictionWithFreeSet x S) = S.card := by
  simp [stars]

theorem agreeRestriction_restrictionWithFreeSet {n : ℕ} (x : Fin n → Bool)
    (S : Finset (Fin n)) :
    DTree.agreeRestriction (restrictionWithFreeSet x S) x := by
  intro v b hv
  simp only [restrictionWithFreeSet] at hv
  split at hv
  · simp at hv
  · simpa using hv

/-- Agreement makes the free-variable set a complete code for a restriction. -/
theorem restrictionWithFreeSet_freeVars_of_agrees {n : ℕ} (x : Fin n → Bool)
    (rho : Restriction n) (hrho : DTree.agreeRestriction rho x) :
    restrictionWithFreeSet x (freeVars rho) = rho := by
  funext v
  cases h : rho v with
  | none => simp [restrictionWithFreeSet, mem_freeVars, h]
  | some b =>
      have hxb : x v = b := hrho v b h
      simp [restrictionWithFreeSet, mem_freeVars, h, hxb]

/-- Exact stars-and-bars-free parametrization of all `K`-live restrictions compatible with one
total assignment: choosing the live set is the only remaining choice. -/
noncomputable def agreeingRestrictionEquivFreeSet {n K : ℕ} (x : Fin n → Bool) :
    {rho : Restriction n // stars rho = K ∧ DTree.agreeRestriction rho x} ≃
      {S : Finset (Fin n) // S.card = K} where
  toFun rho := ⟨freeVars rho, by simpa [stars] using rho.2.1⟩
  invFun S := ⟨restrictionWithFreeSet x S, by
    exact ⟨by simpa using S.2, agreeRestriction_restrictionWithFreeSet x S⟩⟩
  left_inv rho := by
    apply Subtype.ext
    exact restrictionWithFreeSet_freeVars_of_agrees x rho rho.2.2
  right_inv S := by
    apply Subtype.ext
    exact freeVars_restrictionWithFreeSet x S

/-- Exact ambient compatibility degree at live dimension `K`.  This counts all distinct
restriction cubes containing a fixed root assignment, so every generated path-tree family is a
subfamily of a set of this size. -/
theorem card_agreeing_restrictions_of_stars_eq {n K : ℕ} (x : Fin n → Bool) :
    Nat.card {rho : Restriction n //
      stars rho = K ∧ DTree.agreeRestriction rho x} = n.choose K := by
  rw [Nat.card_congr (agreeingRestrictionEquivFreeSet x)]
  rw [Nat.card_eq_fintype_card]
  simpa using (Fintype.card_finset_len (α := Fin n) K)

/-- Any finite injectively indexed family of distinct `K`-live restrictions whose cubes contain
one root assignment has compatibility degree at most `choose n K`. -/
theorem card_distinct_agreeing_restriction_family_le_choose
    {n K : ℕ} {I : Type} [Finite I] (x : Fin n → Bool)
    (root : I → Restriction n) (hinj : Function.Injective root)
    (hstars : ∀ i, stars (root i) = K)
    (hagrees : ∀ i, DTree.agreeRestriction (root i) x) :
    Nat.card I ≤ n.choose K := by
  let into : I → {rho : Restriction n //
      stars rho = K ∧ DTree.agreeRestriction rho x} :=
    fun i => ⟨root i, hstars i, hagrees i⟩
  have hinto : Function.Injective into := by
    intro i j hij
    apply hinj
    exact congrArg Subtype.val hij
  rw [← card_agreeing_restrictions_of_stars_eq x]
  exact Nat.card_le_card_of_injective into hinto

/-- Exact cross-branch overlap criterion for one localized edge: two live-cube images intersect
if and only if their fixed coordinates are compatible.  Distinct live sets therefore do not by
themselves supply disjoint branch labels. -/
theorem liftLiveAssignment_ranges_overlap_iff {n : ℕ} (τ υ : Restriction n) :
    (∃ z : Fin (stars τ) → Bool, ∃ w : Fin (stars υ) → Bool,
      liftLiveAssignment τ z = liftLiveAssignment υ w) ↔
      RestrictionsCompatible τ υ := by
  rw [restrictionsCompatible_iff_exists_agrees]
  constructor
  · rintro ⟨z, w, hzw⟩
    exact ⟨liftLiveAssignment τ z,
      liftLiveAssignment_agrees τ z,
      hzw ▸ liftLiveAssignment_agrees υ w⟩
  · rintro ⟨x, hxτ, hxυ⟩
    obtain ⟨z, hz⟩ := (exists_liftLiveAssignment_eq_iff_agrees τ x).2 hxτ
    obtain ⟨w, hw⟩ := (exists_liftLiveAssignment_eq_iff_agrees υ x).2 hxυ
    exact ⟨z, w, hz.trans hw.symm⟩

/-- Disjointness cannot be the generic cross-branch theorem: already on two coordinates there
are distinct restrictions with intersecting live-cube images.  The two branches fix complementary
coordinates, so their common all-false assignment is retained by both. -/
theorem exists_distinct_restrictions_with_overlapping_lift_ranges :
    ∃ τ υ : Restriction 2, τ ≠ υ ∧
      (∃ z : Fin (stars τ) → Bool, ∃ w : Fin (stars υ) → Bool,
        liftLiveAssignment τ z = liftLiveAssignment υ w) := by
  let τ : Restriction 2 := fun v => if v = 0 then some false else none
  let υ : Restriction 2 := fun v => if v = 1 then some false else none
  refine ⟨τ, υ, ?_, (liftLiveAssignment_ranges_overlap_iff τ υ).2 ?_⟩
  · intro h
    have h0 := congrFun h (0 : Fin 2)
    simp [τ, υ] at h0
  · intro v b c hτ hυ
    fin_cases v <;> simp [τ, υ] at hτ hυ

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

/-! ### Full layered-circuit transport to the live-coordinate cube -/

/-- Literal negation is an involution. -/
@[simp] theorem negLit_negLit {n : ℕ} (l : Rung4Literal n) :
    negLit (negLit l) = l := by
  cases l <;> rfl

/-- Negating every literal twice restores a bottom-gate list exactly. -/
theorem negDNF_negDNF {n : ℕ} (cs : List (Clause n)) :
    negDNF (negDNF cs) = cs := by
  simp [negDNF, List.map_map, Function.comp_def]

/-- CNF localization is DNF localization of the De Morgan dual, followed by dualization back. -/
noncomputable def localizeLiveCnf {n : ℕ} (τ : Restriction n)
    (cs : List (Clause n)) : List (Clause (stars τ)) :=
  negDNF (localizeLiveDnf τ (negDNF cs))

/-- The localized CNF computes the ambient CNF under the canonical lifted assignment. -/
theorem localizeLiveCnf_eval {n : ℕ} (τ : Restriction n)
    (x : Fin (stars τ) → Bool) (cs : List (Clause n)) :
    cnfValue (localizeLiveCnf τ cs) x =
      cnfValue cs (liftLiveAssignment τ x) := by
  rw [cnfValue_eq_not_dnfValue_negDNF, localizeLiveCnf, negDNF_negDNF,
    localizeLiveDnf_eval, cnfValue_eq_not_dnfValue_negDNF]

/-- Substitute fixed coordinates and canonically relabel every remaining variable of a layered
circuit.  Internal gates and their order are retained exactly; only bottom payloads are localized. -/
noncomputable def localizeLiveLayered {n : ℕ} (τ : Restriction n) :
    Layered n → Layered (stars τ)
  | Layered.dnf cs => Layered.dnf (localizeLiveDnf τ cs)
  | Layered.cnf cs => Layered.cnf (localizeLiveCnf τ cs)
  | Layered.gAnd gs => Layered.gAnd (gs.map (localizeLiveLayered τ))
  | Layered.gOr gs => Layered.gOr (gs.map (localizeLiveLayered τ))

mutual
/-- Full-circuit evaluation is preserved by live-coordinate transport. -/
theorem localizeLiveLayered_eval {n : ℕ} (τ : Restriction n) :
    ∀ (C : Layered n) (x : Fin (stars τ) → Bool),
      Layered.eval (localizeLiveLayered τ C) x =
        Layered.eval C (liftLiveAssignment τ x)
  | Layered.dnf cs, x => by
      simpa [localizeLiveLayered] using localizeLiveDnf_eval τ x cs
  | Layered.cnf cs, x => by
      simpa [localizeLiveLayered] using localizeLiveCnf_eval τ x cs
  | Layered.gAnd gs, x => by
      simp only [localizeLiveLayered, Layered.eval_gAnd]
      exact localizeLiveLayered_evalAll τ gs x
  | Layered.gOr gs, x => by
      simp only [localizeLiveLayered, Layered.eval_gOr]
      exact localizeLiveLayered_evalAny τ gs x
theorem localizeLiveLayered_evalAll {n : ℕ} (τ : Restriction n) :
    ∀ (gs : List (Layered n)) (x : Fin (stars τ) → Bool),
      (gs.map (localizeLiveLayered τ)).all (fun g => Layered.eval g x) =
        gs.all (fun g => Layered.eval g (liftLiveAssignment τ x))
  | [], _ => rfl
  | g :: gs, x => by
      simp only [List.map_cons, List.all_cons]
      rw [localizeLiveLayered_eval τ g x, localizeLiveLayered_evalAll τ gs x]
theorem localizeLiveLayered_evalAny {n : ℕ} (τ : Restriction n) :
    ∀ (gs : List (Layered n)) (x : Fin (stars τ) → Bool),
      (gs.map (localizeLiveLayered τ)).any (fun g => Layered.eval g x) =
        gs.any (fun g => Layered.eval g (liftLiveAssignment τ x))
  | [], _ => rfl
  | g :: gs, x => by
      simp only [List.map_cons, List.any_cons]
      rw [localizeLiveLayered_eval τ g x, localizeLiveLayered_evalAny τ gs x]
end

mutual
/-- Relabelling and bottom substitution do not change the layered alternation depth. -/
theorem localizeLiveLayered_depth {n : ℕ} (τ : Restriction n) :
    ∀ C : Layered n,
      Layered.depth (localizeLiveLayered τ C) = Layered.depth C
  | Layered.dnf _ => by simp [localizeLiveLayered, Layered.depth]
  | Layered.cnf _ => by simp [localizeLiveLayered, Layered.depth]
  | Layered.gAnd gs => by
      simp only [localizeLiveLayered, Layered.depth]
      rw [localizeLiveLayered_depthList τ gs]
  | Layered.gOr gs => by
      simp only [localizeLiveLayered, Layered.depth]
      rw [localizeLiveLayered_depthList τ gs]
theorem localizeLiveLayered_depthList {n : ℕ} (τ : Restriction n) :
    ∀ gs : List (Layered n),
      Layered.depthList (gs.map (localizeLiveLayered τ)) = Layered.depthList gs
  | [] => rfl
  | g :: gs => by
      simp only [List.map_cons, Layered.depthList]
      rw [localizeLiveLayered_depth τ g, localizeLiveLayered_depthList τ gs]
end

mutual
/-- Live-coordinate transport preserves the exact top-`OR` alternating shape.  In particular,
the nonempty internal gate lists carried by `AltO` survive localization, so a localized output can
feed the `NonEmptyGates` premise of the following switching round. -/
theorem localizeLiveLayered_AltO {n : ℕ} (τ : Restriction n) :
    ∀ {k : ℕ} {C : Layered n}, AltO k C → AltO k (localizeLiveLayered τ C)
  | _, _, AltO.dnf cs => by
      simpa only [localizeLiveLayered] using AltO.dnf (localizeLiveDnf τ cs)
  | _, _, AltO.gOr k gs hne h => by
      rw [localizeLiveLayered]
      refine AltO.gOr k (gs.map (localizeLiveLayered τ)) (by simpa using hne) ?_
      intro g' hg'
      rw [List.mem_map] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      exact localizeLiveLayered_AltA τ (h g hg)
/-- Live-coordinate transport preserves the exact top-`AND` alternating shape. -/
theorem localizeLiveLayered_AltA {n : ℕ} (τ : Restriction n) :
    ∀ {k : ℕ} {C : Layered n}, AltA k C → AltA k (localizeLiveLayered τ C)
  | _, _, AltA.cnf cs => by
      simpa only [localizeLiveLayered] using AltA.cnf (localizeLiveCnf τ cs)
  | _, _, AltA.gAnd k gs hne h => by
      rw [localizeLiveLayered]
      refine AltA.gAnd k (gs.map (localizeLiveLayered τ)) (by simpa using hne) ?_
      intro g' hg'
      rw [List.mem_map] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      exact localizeLiveLayered_AltO τ (h g hg)
end

/-- Collapse followed by exact live-coordinate transport still removes one alternating layer.
This is the structural handoff needed to derive `NonEmptyGates` for the next localized round. -/
theorem localizeLiveLayered_collapseRound_AltO {n fuel k : ℕ}
    (κ τ : Restriction n) {C : Layered n} (hAlt : AltO (k + 3) C) :
    AltO (k + 2) (localizeLiveLayered κ (collapseRound fuel τ C)) := by
  exact localizeLiveLayered_AltO κ (collapseRound_AltO fuel τ hAlt)

/-- The localized collapsed output has nonempty gates whenever it still has alternating shape,
discharging the one-round capstone's structural premise at the following iteration. -/
theorem localizeLiveLayered_collapseRound_NonEmptyGates {n fuel k : ℕ}
    (κ τ : Restriction n) {C : Layered n} (hAlt : AltO (k + 3) C) :
    NonEmptyGates (localizeLiveLayered κ (collapseRound fuel τ C)) := by
  exact AltO_NonEmptyGates (localizeLiveLayered_collapseRound_AltO κ τ hAlt)

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

/-- De Morgan dualization preserves the number of bottom clauses. -/
theorem negDNF_length {n : ℕ} (cs : List (Clause n)) :
    (negDNF cs).length = cs.length := by
  simp [negDNF]

/-- CNF localization cannot increase the number of bottom clauses. -/
theorem localizeLiveCnf_length_le {n : ℕ} (τ : Restriction n)
    (cs : List (Clause n)) :
    (localizeLiveCnf τ cs).length ≤ cs.length := by
  rw [localizeLiveCnf, negDNF_length]
  exact (localizeLiveDnf_length_le τ (negDNF cs)).trans_eq (negDNF_length cs)

/-- CNF localization cannot increase bottom-clause width. -/
theorem localizeLiveCnf_width_le {n w : ℕ} (τ : Restriction n)
    (cs : List (Clause n)) (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    ∀ T ∈ localizeLiveCnf τ cs, T.lits.length ≤ w := by
  have hneg : ∀ T ∈ negDNF cs, T.lits.length ≤ w := by
    intro T hT
    rw [negDNF, List.mem_map] at hT
    obtain ⟨U, hU, rfl⟩ := hT
    simpa using hw U hU
  intro T hT
  rw [localizeLiveCnf, negDNF, List.mem_map] at hT
  obtain ⟨U, hU, rfl⟩ := hT
  simpa using localizeLiveDnf_width_le τ (negDNF cs) hneg U hU

/-- Live-coordinate substitution does not increase the width of any syntactic bottom gate. -/
theorem localizeLiveLayered_BottomWidth {n w : ℕ} (τ : Restriction n) :
    ∀ C : Layered n, BottomWidth w C → BottomWidth w (localizeLiveLayered τ C)
  | Layered.dnf cs, hw => by
      intro cs' hcs'
      simp only [localizeLiveLayered, bottomGates, List.mem_singleton] at hcs'
      subst cs'
      exact localizeLiveDnf_width_le τ cs
        (fun T hT => hw cs (by simp [bottomGates]) T hT)
  | Layered.cnf cs, hw => by
      intro cs' hcs'
      simp only [localizeLiveLayered, bottomGates, List.mem_singleton] at hcs'
      subst cs'
      exact localizeLiveCnf_width_le τ cs
        (fun T hT => hw cs (by simp [bottomGates]) T hT)
  | Layered.gAnd gs, hw => by
      intro cs hcs T hT
      simp only [localizeLiveLayered, bottomGates, bottomGatesList_eq, List.map_map,
        List.mem_flatten] at hcs
      obtain ⟨css, hcss, hcs⟩ := hcs
      rw [List.mem_map] at hcss
      obtain ⟨g, hg, rfl⟩ := hcss
      exact localizeLiveLayered_BottomWidth τ g (BottomWidth_child_gAnd hw hg) cs hcs T hT
  | Layered.gOr gs, hw => by
      intro cs hcs T hT
      simp only [localizeLiveLayered, bottomGates, bottomGatesList_eq, List.map_map,
        List.mem_flatten] at hcs
      obtain ⟨css, hcss, hcs⟩ := hcs
      rw [List.mem_map] at hcss
      obtain ⟨g, hg, rfl⟩ := hcss
      exact localizeLiveLayered_BottomWidth τ g (BottomWidth_child_gOr hw hg) cs hcs T hT

/-- Live-coordinate substitution cannot increase the clause count of any syntactic bottom gate. -/
theorem localizeLiveLayered_BottomCount {n m : ℕ} (τ : Restriction n) :
    ∀ C : Layered n, BottomCount m C → BottomCount m (localizeLiveLayered τ C)
  | Layered.dnf cs, hcount => by
      intro cs' hcs'
      simp only [localizeLiveLayered, bottomGates, List.mem_singleton] at hcs'
      subst cs'
      exact (localizeLiveDnf_length_le τ cs).trans
        (hcount cs (by simp [bottomGates]))
  | Layered.cnf cs, hcount => by
      intro cs' hcs'
      simp only [localizeLiveLayered, bottomGates, List.mem_singleton] at hcs'
      subst cs'
      exact (localizeLiveCnf_length_le τ cs).trans
        (hcount cs (by simp [bottomGates]))
  | Layered.gAnd gs, hcount => by
      intro cs hcs
      simp only [localizeLiveLayered, bottomGates, bottomGatesList_eq, List.map_map,
        List.mem_flatten] at hcs
      obtain ⟨css, hcss, hcs⟩ := hcs
      rw [List.mem_map] at hcss
      obtain ⟨g, hg, rfl⟩ := hcss
      exact localizeLiveLayered_BottomCount τ g
        (fun cs' hcs' => hcount cs'
          (by simpa [bottomGates, bottomGatesList_eq] using
            List.mem_flatten.mpr ⟨bottomGates g,
              List.mem_map.mpr ⟨g, hg, rfl⟩, hcs'⟩)) cs hcs

  | Layered.gOr gs, hcount => by
      intro cs hcs
      simp only [localizeLiveLayered, bottomGates, bottomGatesList_eq, List.map_map,
        List.mem_flatten] at hcs
      obtain ⟨css, hcss, hcs⟩ := hcs
      rw [List.mem_map] at hcss
      obtain ⟨g, hg, rfl⟩ := hcss
      exact localizeLiveLayered_BottomCount τ g
        (fun cs' hcs' => hcount cs'
          (by simpa [bottomGates, bottomGatesList_eq] using
            List.mem_flatten.mpr ⟨bottomGates g,
              List.mem_map.mpr ⟨g, hg, rfl⟩, hcs'⟩)) cs hcs

mutual
/-- Live-coordinate localization preserves the number of syntactic bottom gates exactly. -/
theorem localizeLiveLayered_bottomGates_length {n : ℕ} (τ : Restriction n) :
    ∀ C : Layered n,
      (bottomGates (localizeLiveLayered τ C)).length = (bottomGates C).length
  | Layered.dnf cs => by simp [localizeLiveLayered, bottomGates]
  | Layered.cnf cs => by simp [localizeLiveLayered, bottomGates]
  | Layered.gAnd gs => by
      simpa [localizeLiveLayered, bottomGates, bottomGatesList_eq] using
        localizeLiveLayered_bottomGatesList_length τ gs
  | Layered.gOr gs => by
      simpa [localizeLiveLayered, bottomGates, bottomGatesList_eq] using
        localizeLiveLayered_bottomGatesList_length τ gs
theorem localizeLiveLayered_bottomGatesList_length {n : ℕ} (τ : Restriction n) :
    ∀ gs : List (Layered n),
      (bottomGatesList (gs.map (localizeLiveLayered τ))).length =
        (bottomGatesList gs).length
  | [] => by simp [bottomGatesList]
  | g :: gs => by
      simp only [List.map_cons, bottomGatesList, List.length_append]
      rw [localizeLiveLayered_bottomGates_length τ g,
        localizeLiveLayered_bottomGatesList_length τ gs]
end

mutual
/-- Live-coordinate substitution cannot increase the total number of bottom-clause
occurrences.  This is the occurrence-sensitive companion to
`localizeLiveLayered_bottomSlotCount_le`. -/
theorem localizeLiveLayered_bottomClauseCount_le {n : ℕ} (τ : Restriction n) :
    ∀ C : Layered n,
      bottomClauseCount (localizeLiveLayered τ C) ≤ bottomClauseCount C
  | Layered.dnf cs => by
      simpa [bottomClauseCount, bottomGates, localizeLiveLayered] using
        localizeLiveDnf_length_le τ cs
  | Layered.cnf cs => by
      simpa [bottomClauseCount, bottomGates, localizeLiveLayered] using
        localizeLiveCnf_length_le τ cs
  | Layered.gAnd gs => by
      simpa [bottomClauseCount, bottomGates, localizeLiveLayered] using
        localizeLiveLayered_bottomClauseCountList_le τ gs
  | Layered.gOr gs => by
      simpa [bottomClauseCount, bottomGates, localizeLiveLayered] using
        localizeLiveLayered_bottomClauseCountList_le τ gs
theorem localizeLiveLayered_bottomClauseCountList_le {n : ℕ} (τ : Restriction n) :
    ∀ gs : List (Layered n),
      ((bottomGatesList (gs.map (localizeLiveLayered τ))).map List.length).sum ≤
        ((bottomGatesList gs).map List.length).sum
  | [] => by simp [bottomGatesList]
  | g :: gs => by
      simp only [List.map_cons, bottomGatesList, List.map_append, List.sum_append]
      exact Nat.add_le_add (localizeLiveLayered_bottomClauseCount_le τ g)
        (localizeLiveLayered_bottomClauseCountList_le τ gs)
end

private theorem max_one_localizeLiveDnf_length_le {n : ℕ} (τ : Restriction n)
    (cs : List (Clause n)) :
    max 1 (localizeLiveDnf τ cs).length ≤ max 1 cs.length := by
  exact max_le_max le_rfl (localizeLiveDnf_length_le τ cs)

private theorem max_one_localizeLiveCnf_length_le {n : ℕ} (τ : Restriction n)
    (cs : List (Clause n)) :
    max 1 (localizeLiveCnf τ cs).length ≤ max 1 cs.length := by
  exact max_le_max le_rfl (localizeLiveCnf_length_le τ cs)

mutual
/-- Live-coordinate substitution cannot increase total bottom payload, including the unit charge
for an empty constant bottom gate. -/
theorem localizeLiveLayered_bottomSlotCount_le {n : ℕ} (τ : Restriction n) :
    ∀ C : Layered n,
      bottomSlotCount (localizeLiveLayered τ C) ≤ bottomSlotCount C
  | Layered.dnf cs => by
      simpa [bottomSlotCount, bottomGates, localizeLiveLayered] using
        max_one_localizeLiveDnf_length_le τ cs
  | Layered.cnf cs => by
      simpa [bottomSlotCount, bottomGates, localizeLiveLayered] using
        max_one_localizeLiveCnf_length_le τ cs
  | Layered.gAnd gs => by
      simpa [bottomSlotCount, bottomGates, localizeLiveLayered] using
        localizeLiveLayered_bottomSlotCountList_le τ gs
  | Layered.gOr gs => by
      simpa [bottomSlotCount, bottomGates, localizeLiveLayered] using
        localizeLiveLayered_bottomSlotCountList_le τ gs
theorem localizeLiveLayered_bottomSlotCountList_le {n : ℕ} (τ : Restriction n) :
    ∀ gs : List (Layered n),
      ((bottomGatesList (gs.map (localizeLiveLayered τ))).map
          (fun cs => max 1 cs.length)).sum ≤
        ((bottomGatesList gs).map (fun cs => max 1 cs.length)).sum
  | [] => by simp [bottomGatesList]
  | g :: gs => by
      simp only [List.map_cons, bottomGatesList, List.map_append, List.sum_append]
      exact Nat.add_le_add (localizeLiveLayered_bottomSlotCount_le τ g)
        (localizeLiveLayered_bottomSlotCountList_le τ gs)
end

/-! ### Bottom-support transport through live-coordinate localization -/

/-- Relabelling a localized clause back into ambient coordinates uses only variables that occurred
in the source clause and were live in the localizing restriction.  The reverse inclusion is not
valid in general: an otherwise-live variable may occur only in a clause killed by another fixed
literal, and localization discards that whole clause. -/
theorem image_clauseVariableSupport_localizeLiveClause_subset {n : ℕ}
    (τ : Restriction n) (T : Clause n) :
    (clauseVariableSupport (localizeLiveClause τ T)).image
        (fun i => (liveCoordEquiv τ i).1) ⊆
      clauseVariableSupport T ∩ freeVars τ := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  rw [clauseVariableSupport] at hi ⊢
  have hiList : i ∈ (localizeLiveClause τ T).lits.map litVarOf :=
    List.mem_toFinset.mp hi
  obtain ⟨ell', hell', hvar⟩ := List.mem_map.mp hiList
  obtain ⟨ell, hell, hloc⟩ := List.mem_filterMap.mp hell'
  have hamb : (liveCoordEquiv τ (litVarOf ell')).1 = litVarOf ell :=
    localizeLiveLiteral_litVar τ ell ell' hloc
  have hfree : litVarOf ell ∈ freeVars τ := by
    cases ell with
    | pos w =>
        simp only [localizeLiveLiteral] at hloc
        split at hloc
        · assumption
        · simp at hloc
    | neg w =>
        simp only [localizeLiveLiteral] at hloc
        split at hloc
        · assumption
        · simp at hloc
  rw [← hvar, hamb]
  exact Finset.mem_inter.mpr
    ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨ell, hell, rfl⟩), hfree⟩

/-- Gate-level localization law for DNF payloads. -/
theorem image_gateVariableSupport_localizeLiveDnf_subset {n : ℕ}
    (τ : Restriction n) (cs : List (Clause n)) :
    (gateVariableSupport (localizeLiveDnf τ cs)).image
        (fun i => (liveCoordEquiv τ i).1) ⊆
      gateVariableSupport cs ∩ freeVars τ := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  rw [gateVariableSupport] at hi ⊢
  obtain ⟨T', hT', hiT'⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp
    (show T' ∈ localizeLiveDnf τ cs from List.mem_toFinset.mp hT')
  have hlocal := image_clauseVariableSupport_localizeLiveClause_subset τ T
    (Finset.mem_image.mpr ⟨i, hiT', rfl⟩)
  exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr
    ⟨T, List.mem_toFinset.mpr (List.mem_filter.mp hT).1,
      (Finset.mem_inter.mp hlocal).1⟩, (Finset.mem_inter.mp hlocal).2⟩

/-- Gate-level localization law for CNF payloads. -/
theorem image_gateVariableSupport_localizeLiveCnf_subset {n : ℕ}
    (τ : Restriction n) (cs : List (Clause n)) :
    (gateVariableSupport (localizeLiveCnf τ cs)).image
        (fun i => (liveCoordEquiv τ i).1) ⊆
      gateVariableSupport cs ∩ freeVars τ := by
  rw [localizeLiveCnf, gateVariableSupport_negDNF]
  simpa using image_gateVariableSupport_localizeLiveDnf_subset τ (negDNF cs)

mutual
/-- Full localization image/intersection law, in its strongest generally valid direction. -/
theorem image_layeredBottomVariableSupport_localizeLiveLayered_subset {n : ℕ}
    (τ : Restriction n) : ∀ C : Layered n,
    (layeredBottomVariableSupport (localizeLiveLayered τ C)).image
        (fun i => (liveCoordEquiv τ i).1) ⊆
      layeredBottomVariableSupport C ∩ freeVars τ
  | Layered.dnf cs => by
      simpa [layeredBottomVariableSupport, bottomGates, localizeLiveLayered] using
        image_gateVariableSupport_localizeLiveDnf_subset τ cs
  | Layered.cnf cs => by
      simpa [layeredBottomVariableSupport, bottomGates, localizeLiveLayered] using
        image_gateVariableSupport_localizeLiveCnf_subset τ cs
  | Layered.gAnd gs => by
      rw [localizeLiveLayered]
      exact image_layeredBottomVariableSupport_localizeLiveLayeredList_subset τ gs
  | Layered.gOr gs => by
      rw [localizeLiveLayered]
      simpa [layeredBottomVariableSupport, bottomGates] using
        image_layeredBottomVariableSupport_localizeLiveLayeredList_subset τ gs
theorem image_layeredBottomVariableSupport_localizeLiveLayeredList_subset {n : ℕ}
    (τ : Restriction n) : ∀ gs : List (Layered n),
    (layeredBottomVariableSupport
        (Layered.gAnd (gs.map (localizeLiveLayered τ)))).image
        (fun i => (liveCoordEquiv τ i).1) ⊆
      layeredBottomVariableSupport (Layered.gAnd gs) ∩ freeVars τ
  | [] => by simp [layeredBottomVariableSupport, bottomGates, bottomGatesList]
  | g :: gs => by
      intro v hv
      have hlocal : layeredBottomVariableSupport
          (Layered.gAnd ((g :: gs).map (localizeLiveLayered τ))) =
          layeredBottomVariableSupport (localizeLiveLayered τ g) ∪
            layeredBottomVariableSupport
              (Layered.gAnd (gs.map (localizeLiveLayered τ))) := by
        ext i
        simp only [layeredBottomVariableSupport, bottomGates, bottomGatesList,
          List.map_cons, List.toFinset_append, Finset.mem_biUnion,
          Finset.mem_union, List.mem_toFinset]
        aesop
      have hsource : layeredBottomVariableSupport (Layered.gAnd (g :: gs)) =
          layeredBottomVariableSupport g ∪
            layeredBottomVariableSupport (Layered.gAnd gs) := by
        ext i
        simp only [layeredBottomVariableSupport, bottomGates, bottomGatesList,
          List.toFinset_append, Finset.mem_biUnion,
          Finset.mem_union, List.mem_toFinset]
        aesop
      rw [hlocal, Finset.image_union] at hv
      rw [hsource]
      rcases Finset.mem_union.mp hv with hg | hgs
      · have hg' := image_layeredBottomVariableSupport_localizeLiveLayered_subset τ g hg
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hg').1,
          (Finset.mem_inter.mp hg').2⟩
      · have hgs' := image_layeredBottomVariableSupport_localizeLiveLayeredList_subset τ gs hgs
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_inter.mp hgs').1,
          (Finset.mem_inter.mp hgs').2⟩
end

/-- Cardinal form of the localization law. -/
theorem layeredBottomVariableSupport_localizeLiveLayered_card_le_inter {n : ℕ}
    (τ : Restriction n) (C : Layered n) :
    (layeredBottomVariableSupport (localizeLiveLayered τ C)).card ≤
      (layeredBottomVariableSupport C ∩ freeVars τ).card := by
  have hinj : Function.Injective (fun i : Fin (stars τ) => (liveCoordEquiv τ i).1) := by
    intro a b hab
    exact (liveCoordEquiv τ).injective (Subtype.ext hab)
  rw [← Finset.card_image_of_injective _ hinj]
  exact Finset.card_le_card
    (image_layeredBottomVariableSupport_localizeLiveLayered_subset τ C)

/-- The exact support recurrence for the transformation used by a survivor round: collapse cannot
add ambient support, and localization retains only coordinates in the chosen survivor set. -/
theorem layeredBottomVariableSupport_localizeLiveLayered_collapseRound_card_le_inter
    {n fuel : ℕ} (τ κ : Restriction n) (C : Layered n) :
    (layeredBottomVariableSupport
        (localizeLiveLayered κ (collapseRound fuel τ C))).card ≤
      (layeredBottomVariableSupport C ∩ freeVars κ).card := by
  refine (layeredBottomVariableSupport_localizeLiveLayered_card_le_inter κ
    (collapseRound fuel τ C)).trans (Finset.card_le_card ?_)
  intro v hv
  exact Finset.mem_inter.mpr
    ⟨layeredBottomVariableSupport_collapseRound_subset τ C (Finset.mem_inter.mp hv).1,
      (Finset.mem_inter.mp hv).2⟩

/-! ### The exact-size survivor selector does not control support overlap -/

/-- A restriction extension can only remove live coordinates.  This pointwise form strengthens the
cardinality-only `stars_le_of_restrictionExtends` interface and is useful for auditing survivor
overlap. -/
theorem freeVars_subset_of_restrictionExtends {n : ℕ}
    {σ τ : Restriction n} (h : RestrictionExtends σ τ) :
    freeVars τ ⊆ freeVars σ := by
  intro v hv
  rw [mem_freeVars] at hv ⊢
  cases hσ : σ v with
  | none => rfl
  | some b =>
      rw [h v b hσ] at hv
      simp at hv

/-- If the current support already covers every base-live coordinate, every exact-size extension
has overlap equal to its complete live count.  No choice made by
`exists_restrictionExtends_stars_eq` can improve this case. -/
theorem support_inter_freeVars_card_eq_stars_of_cover {n : ℕ}
    {base ρ : Restriction n} {S : Finset (Fin n)}
    (hext : RestrictionExtends base ρ) (hcover : freeVars base ⊆ S) :
    (S ∩ freeVars ρ).card = stars ρ := by
  have hsub : freeVars ρ ⊆ S :=
    (freeVars_subset_of_restrictionExtends hext).trans hcover
  rw [Finset.inter_eq_right.mpr hsub, stars]

/-- A concrete globally sparse support occupying one of sixteen ambient coordinates. -/
def sparseSupport16 : Finset (Fin 16) := {0}

/-- The matching leaf has only that supported coordinate live. -/
def sparseSupportRoot16 : Restriction 16 :=
  fun i => if i = 0 then none else some false

theorem sparseSupport16_card : sparseSupport16.card = 1 := by decide

theorem sparseSupportRoot16_freeVars :
    freeVars sparseSupportRoot16 = sparseSupport16 := by decide

/-- The first-round global factor-sixteen density premise holds exactly in the example. -/
theorem sparseSupport16_global_density :
    16 * sparseSupport16.card ≤ 16 := by decide

/-- Nevertheless every exact one-survivor extension has overlap one, so the desired next-round
factor-sixteen premise is false.  This is a counterexample to deriving overlap control from global
support density plus the present arbitrary exact-cardinality selector. -/
theorem sparseSupport16_exact_survivor_overlap
    {ρ : Restriction 16} (hext : RestrictionExtends sparseSupportRoot16 ρ)
    (hstars : stars ρ = 1) :
    (sparseSupport16 ∩ freeVars ρ).card = 1 ∧
      ¬ 16 * (sparseSupport16 ∩ freeVars ρ).card ≤ 1 := by
  have hcover : freeVars sparseSupportRoot16 ⊆ sparseSupport16 := by
    rw [sparseSupportRoot16_freeVars]
  have hover := support_inter_freeVars_card_eq_stars_of_cover hext hcover
  rw [hstars] at hover
  constructor
  · exact hover
  · omega

/-- Outside-support capacity is sufficient for an overlap-aware exact survivor choice.  Keeping
`K - q` live coordinates outside `S`, then filling the remaining `q` positions arbitrarily from
the still-live coordinates, produces an extension whose support overlap is at most `q`. -/
theorem exists_restrictionExtends_stars_eq_inter_card_le {n K q : ℕ}
    (base : Restriction n) (S : Finset (Fin n))
    (hqK : q ≤ K) (hK : K ≤ stars base)
    (hout : K - q ≤ (freeVars base \ S).card) :
    ∃ rho : Restriction n,
      RestrictionExtends base rho ∧ stars rho = K ∧
        (S ∩ freeVars rho).card ≤ q := by
  classical
  obtain ⟨outside, houtsideSub, houtsideCard⟩ := Finset.exists_subset_card_eq
    (s := freeVars base \ S) (n := K - q) hout
  have houtsideLive : outside ⊆ freeVars base :=
    houtsideSub.trans Finset.sdiff_subset
  have hremaining : q ≤ (freeVars base \ outside).card := by
    rw [Finset.card_sdiff_of_subset houtsideLive, houtsideCard]
    rw [stars] at hK
    omega
  obtain ⟨fill, hfillSub, hfillCard⟩ := Finset.exists_subset_card_eq
    (s := freeVars base \ outside) (n := q) hremaining
  let keep := outside ∪ fill
  have hkeepLive : keep ⊆ freeVars base := by
    exact Finset.union_subset houtsideLive (hfillSub.trans Finset.sdiff_subset)
  have hdisjoint : Disjoint outside fill := by
    exact Finset.disjoint_left.mpr fun i hiOutside hiFill =>
      (Finset.mem_sdiff.mp (hfillSub hiFill)).2 hiOutside
  have hkeepCard : keep.card = K := by
    dsimp only [keep]
    rw [Finset.card_union_of_disjoint hdisjoint, houtsideCard, hfillCard]
    omega
  refine ⟨keepFreeExtension base keep,
    restrictionExtends_keepFreeExtension base hkeepLive, ?_, ?_⟩
  · simpa [hkeepCard] using stars_keepFreeExtension base keep
  · rw [freeVars_keepFreeExtension]
    refine (Finset.card_le_card ?_).trans_eq hfillCard
    intro i hi
    have hi' := Finset.mem_inter.mp hi
    have hikeep : i ∈ outside ∪ fill := hi'.2
    rcases Finset.mem_union.mp hikeep with hiOutside | hiFill
    · exact False.elim <| (Finset.mem_sdiff.mp (houtsideSub hiOutside)).2 hi'.1
    · exact hiFill

/-- Keep exactly `keep` live and fill every other coordinate from `x`.  Unlike the older
`keepFreeExtension`, this extension retains provenance from the assignment that selected the
canonical leaf. -/
def assignmentKeepFreeExtension {n : ℕ} (keep : Finset (Fin n))
    (x : Fin n → Bool) : Restriction n :=
  fun i => if i ∈ keep then none else some (x i)

@[simp] theorem freeVars_assignmentKeepFreeExtension {n : ℕ}
    (keep : Finset (Fin n)) (x : Fin n → Bool) :
    freeVars (assignmentKeepFreeExtension keep x) = keep := by
  ext i
  simp [mem_freeVars, assignmentKeepFreeExtension]

@[simp] theorem stars_assignmentKeepFreeExtension {n : ℕ}
    (keep : Finset (Fin n)) (x : Fin n → Bool) :
    stars (assignmentKeepFreeExtension keep x) = keep.card := by
  rw [stars, freeVars_assignmentKeepFreeExtension]

theorem restrictionExtends_assignmentKeepFreeExtension {n : ℕ}
    {base : Restriction n} {keep : Finset (Fin n)} {x : Fin n → Bool}
    (hkeep : keep ⊆ freeVars base) (hx : Rung4Restriction.Extends base x) :
    RestrictionExtends base (assignmentKeepFreeExtension keep x) := by
  intro i b hib
  have hinot : i ∉ keep := by
    intro hi
    have hilive := hkeep hi
    rw [mem_freeVars, hib] at hilive
    simp at hilive
  simp [assignmentKeepFreeExtension, hinot, hx i b hib]

theorem assignmentKeepFreeExtension_extends {n : ℕ}
    (keep : Finset (Fin n)) (x : Fin n → Bool) :
    Rung4Restriction.Extends (assignmentKeepFreeExtension keep x) x := by
  intro i b hib
  simp only [assignmentKeepFreeExtension] at hib
  split at hib
  · contradiction
  · exact Option.some.inj hib

/-- Assignment-following form of the overlap-aware exact survivor selector.  It has the same
size and overlap guarantees as `exists_restrictionExtends_stars_eq_inter_card_le`, and additionally
the selected survivor is extended by the assignment that chose the canonical branch. -/
theorem exists_assignmentExtending_stars_eq_inter_card_le {n K q : ℕ}
    (base : Restriction n) (S : Finset (Fin n)) (x : Fin n → Bool)
    (hx : Rung4Restriction.Extends base x)
    (hqK : q ≤ K) (hK : K ≤ stars base)
    (hout : K - q ≤ (freeVars base \ S).card) :
    ∃ rho : Restriction n,
      RestrictionExtends base rho ∧ Rung4Restriction.Extends rho x ∧
        stars rho = K ∧ (S ∩ freeVars rho).card ≤ q := by
  classical
  obtain ⟨outside, houtsideSub, houtsideCard⟩ := Finset.exists_subset_card_eq
    (s := freeVars base \ S) (n := K - q) hout
  have houtsideLive : outside ⊆ freeVars base :=
    houtsideSub.trans Finset.sdiff_subset
  have hremaining : q ≤ (freeVars base \ outside).card := by
    rw [Finset.card_sdiff_of_subset houtsideLive, houtsideCard]
    rw [stars] at hK
    omega
  obtain ⟨fill, hfillSub, hfillCard⟩ := Finset.exists_subset_card_eq
    (s := freeVars base \ outside) (n := q) hremaining
  let keep := outside ∪ fill
  have hkeepLive : keep ⊆ freeVars base :=
    Finset.union_subset houtsideLive (hfillSub.trans Finset.sdiff_subset)
  have hdisjoint : Disjoint outside fill := by
    exact Finset.disjoint_left.mpr fun i hiOutside hiFill =>
      (Finset.mem_sdiff.mp (hfillSub hiFill)).2 hiOutside
  have hkeepCard : keep.card = K := by
    dsimp only [keep]
    rw [Finset.card_union_of_disjoint hdisjoint, houtsideCard, hfillCard]
    omega
  refine ⟨assignmentKeepFreeExtension keep x,
    restrictionExtends_assignmentKeepFreeExtension hkeepLive hx,
    assignmentKeepFreeExtension_extends keep x, ?_, ?_⟩
  · simpa [hkeepCard] using stars_assignmentKeepFreeExtension keep x
  · rw [freeVars_assignmentKeepFreeExtension]
    refine (Finset.card_le_card ?_).trans_eq hfillCard
    intro i hi
    have hi' := Finset.mem_inter.mp hi
    rcases Finset.mem_union.mp hi'.2 with hiOutside | hiFill
    · exact False.elim <| (Finset.mem_sdiff.mp (houtsideSub hiOutside)).2 hi'.1
    · exact hiFill

/-- Conversely, any exact survivor extension must pay for every survivor not supplied by the
base-live coordinates outside `S`.  This is the deterministic necessity half of the same leaf
interface. -/
theorem stars_le_outside_add_inter_card_of_restrictionExtends {n : ℕ}
    {base rho : Restriction n} (S : Finset (Fin n))
    (hext : RestrictionExtends base rho) :
    stars rho ≤ (freeVars base \ S).card + (S ∩ freeVars rho).card := by
  rw [stars]
  have hpartition := Finset.card_sdiff_add_card_inter (freeVars rho) S
  have houtside : (freeVars rho \ S).card ≤ (freeVars base \ S).card := by
    apply Finset.card_le_card
    exact Finset.sdiff_subset_sdiff (freeVars_subset_of_restrictionExtends hext)
      (Finset.Subset.refl S)
  rw [Finset.inter_comm] at hpartition
  omega

/-- Hence factor-sixteen overlap density at an exact `K`-survivor leaf requires at least
`15/16` as much outside-support capacity.  This is the precise event that a strengthened
common-trunk count must force. -/
theorem fifteen_mul_stars_le_sixteen_mul_outside_of_overlap_density {n : ℕ}
    {base rho : Restriction n} (S : Finset (Fin n))
    (hext : RestrictionExtends base rho)
    (hdensity : 16 * (S ∩ freeVars rho).card ≤ stars rho) :
    15 * stars rho ≤ 16 * (freeVars base \ S).card := by
  have hcapacity := stars_le_outside_add_inter_card_of_restrictionExtends S hext
  omega

/-- Choosing any integer overlap allowance `q` with `16*q ≤ K` turns the escape selector into
the exact factor-sixteen density interface required by the next survivor round. -/
theorem exists_restrictionExtends_factorSixteen_overlap_density {n K q : ℕ}
    (base : Restriction n) (S : Finset (Fin n))
    (hqK : q ≤ K) (h16q : 16 * q ≤ K) (hK : K ≤ stars base)
    (hout : K - q ≤ (freeVars base \ S).card) :
    ∃ rho : Restriction n,
      RestrictionExtends base rho ∧ stars rho = K ∧
        16 * (S ∩ freeVars rho).card ≤ K := by
  obtain ⟨rho, hext, hstars, hoverlap⟩ :=
    exists_restrictionExtends_stars_eq_inter_card_le base S hqK hK hout
  exact ⟨rho, hext, hstars, (Nat.mul_le_mul_left 16 hoverlap).trans h16q⟩

/-! ### The correlated support-tail event supplies zero-overlap survivors -/

/-- Outside the strengthened root support tail, the canonical normalized-family prefix has two
properties at once: it is a residual-depth-zero common-shallow certificate, and every reached leaf
admits an exact half-shell survivor extension completely disjoint from the old bottom support.
Thus the correlated leaf-capacity problem reduces to the already counted root hypergeometric tail;
no additional leaf-wise probabilistic event is needed. -/
theorem normalizedCanonicalPrefix_zeroOverlapSurvivor_of_not_supportTail
    {n fuel R : ℕ} {C : Layered n} {sigma : Restriction n}
    (hstars : stars sigma = 20 * R) (hKfuel : 20 * R ≤ fuel)
    (hgood : sigma ∉ liveLayeredBottomSupportTail C (20 * R) (10 * R)) :
    CommonShallowAt (normalizedLayeredBottomFamily C) fuel sigma (10 * R) 0 ∧
      ∀ x : Fin n → Bool, Rung4Restriction.Extends sigma x →
        let tau := CommonTree.prefixEndpoint sigma
          (canonicalFamilyTree (normalizedLayeredBottomFamily C) fuel sigma) (10 * R) x
        ∃ rho : Restriction n,
          RestrictionExtends tau rho ∧ Rung4Restriction.Extends rho x ∧
            stars rho = 10 * R ∧
            (layeredBottomVariableSupport C ∩ freeVars rho).card = 0 := by
  have hliveSupport :
      ((layeredBottomVariableSupport C).filter fun i ↦ sigma i = none).card ≤ 10 * R := by
    apply Nat.le_of_not_gt
    intro hgt
    apply hgood
    rw [mem_liveLayeredBottomSupportTail_iff]
    exact ⟨hstars, hgt⟩
  have hfamilySupport :
      ((familyVariableSupport (normalizedLayeredBottomFamily C)).filter
        fun i ↦ sigma i = none).card ≤ 10 * R := by
    refine (Finset.card_le_card ?_).trans hliveSupport
    intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨normalizedLayeredBottomFamily_support_subset_bottomSupport C hi.1, hi.2⟩
  constructor
  · apply commonShallowAt_zero_of_live_support_le
    · simpa [hstars] using hKfuel
    · exact hfamilySupport
  · intro x hx
    dsimp only
    let tau := CommonTree.prefixEndpoint sigma
      (canonicalFamilyTree (normalizedLayeredBottomFamily C) fuel sigma) (10 * R) x
    have houtsideRoot : 10 * R ≤
        (freeVars sigma \ layeredBottomVariableSupport C).card := by
      have hpartition := Finset.card_sdiff_add_card_inter
        (freeVars sigma) (layeredBottomVariableSupport C)
      have hinter : (freeVars sigma ∩ layeredBottomVariableSupport C).card =
          ((layeredBottomVariableSupport C).filter fun i ↦ sigma i = none).card := by
        apply congrArg Finset.card
        ext i
        simp [mem_freeVars, and_comm]
      rw [stars] at hstars
      rw [hinter] at hpartition
      omega
    have houtsideSubset : freeVars sigma \ layeredBottomVariableSupport C ⊆
        freeVars tau \ layeredBottomVariableSupport C := by
      intro i hi
      rw [Finset.mem_sdiff] at hi ⊢
      refine ⟨?_, hi.2⟩
      apply freeVars_sdiff_familySupport_subset_canonicalPrefixEndpoint
        (normalizedLayeredBottomFamily C) fuel sigma (10 * R) x hx
      rw [Finset.mem_sdiff]
      exact ⟨hi.1, fun hfamily => hi.2
        (normalizedLayeredBottomFamily_support_subset_bottomSupport C hfamily)⟩
    have houtsideLeaf : 10 * R ≤
        (freeVars tau \ layeredBottomVariableSupport C).card :=
      houtsideRoot.trans (Finset.card_le_card houtsideSubset)
    have htargetStars : 10 * R ≤ stars tau := by
      rw [stars]
      exact houtsideLeaf.trans (Finset.card_le_card Finset.sdiff_subset)
    have htauExtends : Rung4Restriction.Extends tau x := by
      exact CommonTree.run_prefixEndpoints_extends sigma
        (canonicalFamilyTree (normalizedLayeredBottomFamily C) fuel sigma)
        (10 * R) x hx
    obtain ⟨rho, hext, hrhoExtends, hrhoStars, hoverlap⟩ :=
      exists_assignmentExtending_stars_eq_inter_card_le tau
        (layeredBottomVariableSupport C) (K := 10 * R) (q := 0)
        x htauExtends (by omega) htargetStars (by simpa using houtsideLeaf)
    exact ⟨rho, hext, hrhoExtends, hrhoStars, Nat.eq_zero_of_le_zero hoverlap⟩

/-- The strengthened support-tail complement now drives the complete localized survivor round.
The selected canonical leaf is shared by the depth-zero collapse certificate and the zero-overlap
survivor selector.  After localization, the next bottom support is therefore empty, so the
factor-sixteen density premise propagates with room to spare. -/
theorem supportTail_normalizedSurvivorRound_localized
    {n fuel R k : ℕ} {C : Layered n}
    (hKfuel : 20 * R ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (k + 3) C) :
    (liveLayeredBottomSupportTail C (20 * R) (10 * R)).card * 2 ^ (10 * R) ≤
        (Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * R).card ∧
      ∀ σ : Restriction n,
        stars σ = 20 * R →
        σ ∉ liveLayeredBottomSupportTail C (20 * R) (10 * R) →
        ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x →
          let trunk := CommonTree.prefixEndpoints σ
            (canonicalFamilyTree (normalizedLayeredBottomFamily C) fuel σ) (10 * R)
          let τ := CommonTree.run trunk x
          ∃ κ : Restriction n,
            RestrictionExtends τ κ ∧
            Rung4Restriction.Extends κ x ∧
            stars κ = 10 * R ∧
            stars κ ≤ fuel ∧
            let D := localizeLiveLayered κ (collapseRound fuel τ C)
            (∀ z : Fin (stars κ) → Bool,
              Layered.eval D z = Layered.eval C (liftLiveAssignment κ z)) ∧
            Layered.depth D = Layered.depth (collapseRound fuel τ C) ∧
            AltO (k + 2) D ∧
            NonEmptyGates D ∧
            BottomWidth 1 D ∧
            bottomSlotCount D ≤ bottomSlotCount C * 3 ∧
            (layeredBottomVariableSupport D).card = 0 ∧
            16 * (layeredBottomVariableSupport D).card ≤ stars κ := by
  refine ⟨liveLayeredBottomSupportTail_scaled_le_sixteen_density hsupport, ?_⟩
  intro σ hstars hgood x hx
  have hcert := normalizedCanonicalPrefix_zeroOverlapSurvivor_of_not_supportTail
    (C := C) (fuel := fuel) (R := R) hstars hKfuel hgood
  let trunk := CommonTree.prefixEndpoints σ
    (canonicalFamilyTree (normalizedLayeredBottomFamily C) fuel σ) (10 * R)
  let τ := CommonTree.run trunk x
  have hτeq : τ = CommonTree.prefixEndpoint σ
      (canonicalFamilyTree (normalizedLayeredBottomFamily C) fuel σ) (10 * R) x := rfl
  obtain ⟨κ, hext, hκextends, hκstars, hoverlap⟩ := hcert.2 x hx
  have hfuel : stars σ ≤ fuel := by simpa [hstars] using hKfuel
  have hliveSupport :
      ((layeredBottomVariableSupport C).filter fun i ↦ σ i = none).card ≤ 10 * R := by
    apply Nat.le_of_not_gt
    intro hgt
    apply hgood
    rw [mem_liveLayeredBottomSupportTail_iff]
    exact ⟨hstars, hgt⟩
  have hfamilySupport :
      ((familyVariableSupport (normalizedLayeredBottomFamily C)).filter
        fun i ↦ σ i = none).card ≤ 10 * R := by
    refine (Finset.card_le_card ?_).trans hliveSupport
    intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨normalizedLayeredBottomFamily_support_subset_bottomSupport C hi.1, hi.2⟩
  have hresidual : ∀ g,
      (canonicalDT ((normalizedLayeredBottomFamily C) g) fuel τ).depth = 0 := by
    intro g
    rw [hτeq]
    exact canonicalFamily_prefix_depth_eq_zero_of_live_support_le
      (normalizedLayeredBottomFamily C) fuel σ (10 * R) hfuel hfamilySupport x hx g
  have hshallow : Shallows fuel τ 1 C := by
    intro cs hcs
    obtain ⟨⟨g, hg⟩, ⟨gneg, hgneg⟩⟩ := normalizedLayeredBottomFamily_covers C cs hcs
    constructor
    · rw [← hg fuel τ, hresidual g]
      omega
    · rw [← hgneg fuel τ, hresidual gneg]
      omega
  have hτfuel : stars τ ≤ fuel := by
    refine (stars_le_of_restrictionExtends ?_).trans hfuel
    simpa [τ, trunk] using prefixEndpoint_restrictionExtends σ
      (canonicalFamilyTree (normalizedLayeredBottomFamily C) fuel σ) (10 * R) x hx
  have hκfuel : stars κ ≤ fuel := (stars_le_of_restrictionExtends hext).trans hτfuel
  have hequiv : Layered.EquivOn κ C (collapseRound fuel τ C) := by
    intro y hy
    exact collapseRound_EquivOn fuel hτfuel C y (fun i b hi => hy i b (hext i b hi))
  have hwidth : BottomWidth 1 (collapseRound fuel τ C) :=
    collapseRound_BottomWidth fuel τ hshallow
  have hslots : bottomSlotCount (collapseRound fuel τ C) ≤ bottomSlotCount C * 3 := by
    simpa using collapseRound_bottomSlotCount_le (AltO_NonEmptyGates hAlt) hshallow
  have hDalt : AltO (k + 2)
      (localizeLiveLayered κ (collapseRound fuel τ C)) :=
    localizeLiveLayered_collapseRound_AltO κ τ hAlt
  have hDnonempty : NonEmptyGates
      (localizeLiveLayered κ (collapseRound fuel τ C)) :=
    AltO_NonEmptyGates hDalt
  have hDsupport :
      (layeredBottomVariableSupport
        (localizeLiveLayered κ (collapseRound fuel τ C))).card = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact (layeredBottomVariableSupport_localizeLiveLayered_collapseRound_card_le_inter
      τ κ C).trans (by simpa using Nat.le_of_eq hoverlap)
  refine ⟨κ, hext, hκextends, hκstars, hκfuel, ?_, ?_, hDalt, hDnonempty, ?_, ?_,
    hDsupport, ?_⟩
  · intro z
    rw [localizeLiveLayered_eval]
    exact (hequiv (liftLiveAssignment κ z) (liftLiveAssignment_agrees κ z)).symm
  · exact localizeLiveLayered_depth κ _
  · exact localizeLiveLayered_BottomWidth κ _ hwidth
  · exact (localizeLiveLayered_bottomSlotCount_le κ _).trans hslots
  · rw [hDsupport]
    omega

/-! ### Exact shell schedule for iterating zero-support localized rounds -/

/-- Backward geometric scale for `d` remaining localized rounds.  Round `i` uses survivor
parameter `2^(d-i) * r`, so the scale halves exactly at every genuine transition. -/
def zeroSupportSurvivorScale (d r i : ℕ) : ℕ := 2 ^ (d - i) * r

@[simp] theorem zeroSupportSurvivorScale_zero (d r : ℕ) :
    zeroSupportSurvivorScale d r 0 = 2 ^ d * r := by
  simp [zeroSupportSurvivorScale]

@[simp] theorem zeroSupportSurvivorScale_terminal (d r : ℕ) :
    zeroSupportSurvivorScale d r d = r := by
  simp [zeroSupportSurvivorScale]

/-- The next round's entire `20R` shell is exactly the current round's `10R` survivor cube.
Thus shell fit introduces no slack loss and no slot-dependent actual-margin charge once the
localized bottom support has become empty. -/
theorem zeroSupportSurvivorScale_shell_exact
    (d r i : ℕ) (hi : i < d) :
    20 * zeroSupportSurvivorScale d r (i + 1) =
      10 * zeroSupportSurvivorScale d r i := by
  have hsub : d - i = (d - (i + 1)) + 1 := by omega
  simp only [zeroSupportSurvivorScale, hsub, pow_succ]
  ring

/-- Consequently every next shell fits, in the precise form consumed by a finite recurrence. -/
theorem zeroSupportSurvivorScale_shell_le
    (d r i : ℕ) (hi : i < d) :
    20 * zeroSupportSurvivorScale d r (i + 1) ≤
      10 * zeroSupportSurvivorScale d r i := by
  exact Nat.le_of_eq (zeroSupportSurvivorScale_shell_exact d r i hi)

/-- Positive terminal scale propagates backward through the whole finite schedule. -/
theorem zeroSupportSurvivorScale_pos
    (d r i : ℕ) (hr : 0 < r) : 0 < zeroSupportSurvivorScale d r i := by
  exact Nat.mul_pos (pow_pos (by omega) _) hr

/-! ### Dependent state for recursive zero-support rounds -/

/-- The data exported by a localized round and consumed by the next one.  The ambient dimension is
kept as a field, rather than definitionally fixed to `20 * R`, because the preceding round naturally
produces the coordinate type `Fin (stars κ)`.  The equality records the exact shell handoff without
requiring a lossy cast of the circuit. -/
structure ZeroSupportLocalizedState (R level slotBound : ℕ) where
  n : ℕ
  circuit : Layered n
  ambient_eq : n = 20 * R
  alt : AltO (level + 2) circuit
  width_one : BottomWidth 1 circuit
  slots_le : bottomSlotCount circuit ≤ slotBound
  support_zero : (layeredBottomVariableSupport circuit).card = 0

/-- A zero-support state at remaining level zero is an actual bottom DNF whose canonical tree is
a leaf under every restriction and every fuel budget.  This is stronger than the width-one bound:
the support invariant rules out every literal in the terminal DNF. -/
theorem ZeroSupportLocalizedState.exists_terminalDnf_depth_zero
    {R slotBound : ℕ} (S : ZeroSupportLocalizedState R 0 slotBound) :
    ∃ D : List (Clause S.n), S.circuit = Layered.dnf D ∧
      ∀ fuel σ, (canonicalDT D fuel σ).depth = 0 := by
  obtain ⟨D, hD⟩ := AltO_two_dnf (by simpa using S.alt)
  refine ⟨D, hD, ?_⟩
  have hsupport : (gateVariableSupport D).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hvCircuit : v ∈ layeredBottomVariableSupport S.circuit := by
      rw [layeredBottomVariableSupport]
      apply Finset.mem_biUnion.mpr
      refine ⟨D, List.mem_toFinset.mpr ?_, hv⟩
      rw [hD]
      exact List.mem_cons_self
    have hempty := Finset.card_eq_zero.mp S.support_zero
    rw [hempty] at hvCircuit
    simpa using hvCircuit
  exact fun fuel σ =>
    canonicalDT_depth_eq_zero_of_gateVariableSupport_card_eq_zero D hsupport fuel σ

/-! ### Provenance across the initial support-tail boundary -/

/-- The first nonzero-support shell selection, kept together with the zero-support child that it
produces.  Unlike `ZeroSupportLocalizedState`, this package deliberately remembers the genuine
root event and the assignment that selected the canonical prefix leaf.  The child restriction is
proved to extend the original shell root, not merely the intermediate trunk leaf. -/
structure InitialSupportTailSuccessor {n fuel R k : ℕ} (C : Layered n)
    (sigma : Restriction n) (x : Fin n → Bool) where
  root_stars : stars sigma = 20 * (2 * R)
  root_good : sigma ∉ liveLayeredBottomSupportTail C (20 * (2 * R)) (10 * (2 * R))
  root_assignment : Rung4Restriction.Extends sigma x
  restriction : Restriction n
  root_extends : RestrictionExtends sigma restriction
  restriction_assignment : Rung4Restriction.Extends restriction x
  circuit : Layered (stars restriction)
  ambient_eq : stars restriction = 20 * R
  eval_eq : ∀ z : Fin (stars restriction) → Bool,
    Layered.eval circuit z = Layered.eval C (liftLiveAssignment restriction z)
  alt : AltO (k + 2) circuit
  width_one : BottomWidth 1 circuit
  slots_le : bottomSlotCount circuit ≤ bottomSlotCount C * 3
  support_zero : (layeredBottomVariableSupport circuit).card = 0

/-- Forgetting the initial good-event provenance yields the exact state consumed by the geometric
zero-support iterator. -/
def InitialSupportTailSuccessor.toState {n fuel R k : ℕ} {C : Layered n}
    {sigma : Restriction n} {x : Fin n → Bool}
    (step : InitialSupportTailSuccessor (fuel := fuel) (R := R) (k := k) C sigma x) :
    ZeroSupportLocalizedState R k (bottomSlotCount C * 3) where
  n := stars step.restriction
  circuit := step.circuit
  ambient_eq := step.ambient_eq
  alt := step.alt
  width_one := step.width_one
  slots_le := step.slots_le
  support_zero := step.support_zero

/-- Slot-normalized presentation of the initial successor for the geometric iterator at index
zero.  Keeping the harmless `3^0` in the type avoids dependent casts at the path constructor. -/
def InitialSupportTailSuccessor.toInitialGeometricState
    {n fuel R k : ℕ} {C : Layered n}
    {sigma : Restriction n} {x : Fin n → Bool}
    (step : InitialSupportTailSuccessor (fuel := fuel) (R := R) (k := k) C sigma x) :
    ZeroSupportLocalizedState R k ((bottomSlotCount C * 3) * 3 ^ 0) where
  n := stars step.restriction
  circuit := step.circuit
  ambient_eq := step.ambient_eq
  alt := step.alt
  width_one := step.width_one
  slots_le := by simpa using step.slots_le
  support_zero := step.support_zero

/-- Every genuinely good root on the initial `40R` shell and every assignment extending it
produce a provenance-carrying zero-support state on the `20R` successor shell.  This is the
charging boundary that the later zero-support iterator had forgotten. -/
theorem exists_initialSupportTailSuccessor {n fuel R k : ℕ} {C : Layered n}
    {sigma : Restriction n} {x : Fin n → Bool}
    (hKfuel : 20 * (2 * R) ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (k + 3) C)
    (hstars : stars sigma = 20 * (2 * R))
    (hgood : sigma ∉ liveLayeredBottomSupportTail C (20 * (2 * R)) (10 * (2 * R)))
    (hx : Rung4Restriction.Extends sigma x) :
    Nonempty (InitialSupportTailSuccessor (fuel := fuel) (R := R) (k := k) C sigma x) := by
  have hround :=
    (supportTail_normalizedSurvivorRound_localized
      (C := C) (fuel := fuel) (R := 2 * R) (k := k)
      hKfuel hsupport hAlt).2 sigma hstars hgood x hx
  dsimp only at hround
  obtain ⟨kappa, hkappaExtendsTau, hkappaAssignment, hkappaStars, _hkappaFuel,
    heval, _hdepth, hDalt, _hne, hwidth, hslots, hsupportZero, _hdensity⟩ := hround
  let tau := CommonTree.run
    (CommonTree.prefixEndpoints sigma
      (canonicalFamilyTree (normalizedLayeredBottomFamily C) fuel sigma) (10 * (2 * R))) x
  have hsigmaExtendsTau : RestrictionExtends sigma tau := by
    exact prefixEndpoint_restrictionExtends sigma
      (canonicalFamilyTree (normalizedLayeredBottomFamily C) fuel sigma)
      (10 * (2 * R)) x hx
  have hsigmaExtendsKappa : RestrictionExtends sigma kappa := by
    intro v b hv
    exact hkappaExtendsTau v b (hsigmaExtendsTau v b hv)
  refine ⟨{
    root_stars := hstars
    root_good := hgood
    root_assignment := hx
    restriction := kappa
    root_extends := hsigmaExtendsKappa
    restriction_assignment := hkappaAssignment
    circuit := localizeLiveLayered kappa (collapseRound fuel tau C)
    ambient_eq := ?_
    eval_eq := heval
    alt := hDalt
    width_one := hwidth
    slots_le := hslots
    support_zero := hsupportZero }⟩
  calc
    stars kappa = 10 * (2 * R) := hkappaStars
    _ = 20 * R := by ring

/-! ### Exact multiplicity of the initial shell extension relation -/

/-- The finite fiber of `K`-star coarsenings of a fixed successor restriction.  These are exactly
the possible earlier shell roots whose fixed values are retained by `kappa`. -/
noncomputable def restrictionCoarseningShellFiber {n K : ℕ}
    (kappa : Restriction n) : Finset (Restriction n) := by
  classical
  exact Finset.univ.filter fun sigma =>
    RestrictionExtends sigma kappa ∧ stars sigma = K

/-- Two coarsenings of the same restriction are equal once their live sets agree.  The common
successor fixes every coordinate outside that live set, including its Boolean value. -/
theorem restriction_eq_of_extends_to_of_freeVars_eq {n : ℕ}
    {sigma tau kappa : Restriction n}
    (hsigma : RestrictionExtends sigma kappa)
    (htau : RestrictionExtends tau kappa)
    (hfree : freeVars sigma = freeVars tau) :
    sigma = tau := by
  funext v
  cases hs : sigma v with
  | none =>
      have hv : v ∈ freeVars sigma := mem_freeVars.mpr hs
      exact (mem_freeVars.mp (hfree ▸ hv)).symm
  | some b =>
      have hk : kappa v = some b := hsigma v b hs
      cases ht : tau v with
      | none =>
          have hv : v ∈ freeVars tau := mem_freeVars.mpr ht
          have : sigma v = none := mem_freeVars.mp (hfree.symm ▸ hv)
          simp [hs] at this
      | some c =>
          have hk' : kappa v = some c := htau v c ht
          rw [hk] at hk'
          simp only [Option.some.injEq] at hk'
          simpa [hs, ht, hk']

/-- A `K`-star predecessor of `kappa` is injectively labelled by the coordinates that it frees
beyond `kappa`.  Hence its fiber is bounded by the exact binomial choice
`choose (n - stars kappa) (K - stars kappa)`; there is no extra Boolean factor because all retained
fixed values are forced by `kappa`. -/
theorem card_restrictionCoarseningShellFiber_le_choose {n K : ℕ}
    (kappa : Restriction n) :
    (restrictionCoarseningShellFiber (K := K) kappa).card ≤
      Nat.choose (n - stars kappa) (K - stars kappa) := by
  classical
  let label : Restriction n → Finset (Fin n) := fun sigma =>
    freeVars sigma \ freeVars kappa
  let labels := (Finset.univ \ freeVars kappa).powersetCard (K - stars kappa)
  have hlabel : ∀ sigma ∈ restrictionCoarseningShellFiber (K := K) kappa,
      label sigma ∈ labels := by
    intro sigma hsigma
    have hsigma' := Finset.mem_filter.mp hsigma
    have hsub := freeVars_subset_of_restrictionExtends hsigma'.2.1
    rw [Finset.mem_powersetCard]
    constructor
    · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.rfl)
    · rw [Finset.card_sdiff_of_subset hsub]
      simpa only [stars] using congrArg (fun q => q - (freeVars kappa).card) hsigma'.2.2
  have hinj : Set.InjOn label
      (restrictionCoarseningShellFiber (K := K) kappa) := by
    intro sigma hsigma tau htau heq
    have hsigma' := (Finset.mem_filter.mp hsigma).2.1
    have htau' := (Finset.mem_filter.mp htau).2.1
    apply restriction_eq_of_extends_to_of_freeVars_eq hsigma' htau'
    have hsigmaSub := freeVars_subset_of_restrictionExtends hsigma'
    have htauSub := freeVars_subset_of_restrictionExtends htau'
    change freeVars sigma \ freeVars kappa = freeVars tau \ freeVars kappa at heq
    calc
      freeVars sigma = (freeVars sigma \ freeVars kappa) ∪ freeVars kappa :=
        (Finset.sdiff_union_of_subset hsigmaSub).symm
      _ = (freeVars tau \ freeVars kappa) ∪ freeVars kappa := by rw [heq]
      _ = freeVars tau := Finset.sdiff_union_of_subset htauSub
  calc
    (restrictionCoarseningShellFiber (K := K) kappa).card =
        ((restrictionCoarseningShellFiber (K := K) kappa).image label).card := by
          symm
          exact Finset.card_image_iff.mpr hinj
    _ ≤ labels.card := Finset.card_le_card (by
      intro S hS
      obtain ⟨sigma, hsigma, rfl⟩ := Finset.mem_image.mp hS
      exact hlabel sigma hsigma)
    _ = Nat.choose (n - stars kappa) (K - stars kappa) := by
      rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp [labels, stars]

/-- On the actual initial `40R -> 20R` boundary, each fixed successor has at most
`choose (n - 20R) (20R)` compatible shell roots.  This is the exact stars-and-bars multiplicity
available from `root_extends`. -/
theorem card_initialSupportTail_rootFiber_le {n R : ℕ}
    (kappa : Restriction n) (hkappa : stars kappa = 20 * R) :
    (restrictionCoarseningShellFiber (K := 20 * (2 * R)) kappa).card ≤
      Nat.choose (n - 20 * R) (20 * R) := by
  have h := card_restrictionCoarseningShellFiber_le_choose
    (K := 20 * (2 * R)) kappa
  have hsub : 20 * (2 * R) - 20 * R = 20 * R := by omega
  simpa only [hkappa, hsub] using h

/-- The genuine finite domain at the initial charging boundary: a good `40R` root together with
a total assignment extending it. -/
def InitialGoodRootAssignmentPair {n : ℕ} (C : Layered n) (R : ℕ)
    (p : Restriction n × (Fin n → Bool)) : Prop :=
  stars p.1 = 20 * (2 * R) ∧
    p.1 ∉ liveLayeredBottomSupportTail C (20 * (2 * R)) (10 * (2 * R)) ∧
    Rung4Restriction.Extends p.1 p.2

/-- The finite population of genuinely good roots on the initial `40R` shell. -/
noncomputable def initialGoodRoots {n : ℕ} (C : Layered n) (R : ℕ) :
    Finset (Restriction n) := by
  classical
  exact Finset.univ.filter fun sigma =>
    stars sigma = 20 * (2 * R) ∧
      sigma ∉ liveLayeredBottomSupportTail C (20 * (2 * R)) (10 * (2 * R))

/-- The complete initial `40R` root shell, before the genuine support-tail event is removed. -/
noncomputable def initialRootShell (n R : ℕ) : Finset (Restriction n) := by
  classical
  exact Finset.univ.filter fun sigma => stars sigma = 20 * (2 * R)

/-- Good and bad roots form an exact partition of the initial shell. -/
theorem card_initialGoodRoots_add_bad {n : ℕ} (C : Layered n) (R : ℕ) :
    (initialGoodRoots C R).card +
        (liveLayeredBottomSupportTail C (20 * (2 * R)) (10 * (2 * R))).card =
      (initialRootShell n R).card := by
  classical
  let bad := liveLayeredBottomSupportTail C (20 * (2 * R)) (10 * (2 * R))
  let shell := initialRootShell n R
  have hbad : bad ⊆ shell := by
    intro sigma hsigma
    change sigma ∈ Finset.univ.filter (fun tau : Restriction n =>
      stars tau = 20 * (2 * R))
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (mem_liveLayeredBottomSupportTail_iff.mp hsigma).1⟩
  have hgood : initialGoodRoots C R = shell \ bad := by
    ext sigma
    rw [Finset.mem_sdiff]
    change sigma ∈ Finset.univ.filter (fun tau : Restriction n =>
      stars tau = 20 * (2 * R) ∧ tau ∉ bad) ↔ sigma ∈ shell ∧ sigma ∉ bad
    change sigma ∈ Finset.univ.filter (fun tau : Restriction n =>
      stars tau = 20 * (2 * R) ∧ tau ∉ bad) ↔
        sigma ∈ Finset.univ.filter (fun tau : Restriction n =>
          stars tau = 20 * (2 * R)) ∧ sigma ∉ bad
    simp
  rw [hgood]
  exact Finset.card_sdiff_add_card_eq_card hbad

/-- At positive scale, the verified support-tail contraction says at least half of the initial
shell is genuinely good.  This is the direct population comparison needed before applying the
selected-successor fiber ceiling. -/
theorem initialRootShell_card_le_two_mul_good {n : ℕ} (C : Layered n) (R : ℕ)
    (hR : 0 < R)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n) :
    (initialRootShell n R).card ≤ 2 * (initialGoodRoots C R).card := by
  have hscaled := liveLayeredBottomSupportTail_scaled_le_sixteen_density
    (C := C) (R := 2 * R) hsupport
  have hpow : 2 ≤ 2 ^ (10 * (2 * R)) := by
    exact Nat.one_lt_pow (by omega) (by omega)
  have hbadTwo :
      (liveLayeredBottomSupportTail C (20 * (2 * R)) (10 * (2 * R))).card * 2 ≤
        (initialRootShell n R).card := by
    calc
      (liveLayeredBottomSupportTail C (20 * (2 * R)) (10 * (2 * R))).card * 2 ≤
          (liveLayeredBottomSupportTail C (20 * (2 * R)) (10 * (2 * R))).card *
            2 ^ (10 * (2 * R)) := Nat.mul_le_mul_left _ hpow
      _ ≤ (Finset.univ.filter fun sigma : Restriction n =>
          stars sigma = 20 * (2 * R)).card := hscaled
      _ = (initialRootShell n R).card := by rfl
  have hpartition := card_initialGoodRoots_add_bad C R
  omega

/-- The raw finite set underlying `InitialGoodRootAssignmentPair`.  Naming it separately makes
the uniform assignment fiber over every good root available to finite fiberwise counting. -/
noncomputable def initialGoodRootAssignmentPairs {n : ℕ} (C : Layered n) (R : ℕ) :
    Finset (Restriction n × (Fin n → Bool)) := by
  classical
  exact Finset.univ.filter fun p => InitialGoodRootAssignmentPair C R p

/-- Every good `40R` root has exactly its `2^(40R)`-element compatible assignment cube above it.
Thus the genuine initial charging domain has the exact product cardinality promised by the shell
interpretation, rather than merely an upper or lower estimate. -/
theorem card_initialGoodRootAssignmentPairs {n : ℕ} (C : Layered n) (R : ℕ) :
    (initialGoodRootAssignmentPairs C R).card =
      (initialGoodRoots C R).card * 2 ^ (20 * (2 * R)) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : Restriction n × (Fin n → Bool) => p.1)
    (t := initialGoodRoots C R)]
  · calc
      (∑ sigma ∈ initialGoodRoots C R,
          ((initialGoodRootAssignmentPairs C R).filter fun p => p.1 = sigma).card) =
          ∑ _sigma ∈ initialGoodRoots C R, 2 ^ (20 * (2 * R)) := by
            apply Finset.sum_congr rfl
            intro sigma hsigma
            have hsigma' := Finset.mem_filter.mp hsigma
            let fiber :=
              (initialGoodRootAssignmentPairs C R).filter (fun p => p.1 = sigma)
            have himage : fiber.image (fun p => p.2) = assignmentsAgreeingRestriction sigma := by
              ext x
              simp only [Finset.mem_image, fiber, Finset.mem_filter,
                initialGoodRootAssignmentPairs, Finset.mem_univ, true_and,
                assignmentsAgreeingRestriction]
              constructor
              · rintro ⟨p, ⟨hp, hpRoot⟩, rfl⟩
                change DTree.agreeRestriction sigma p.2
                simpa only [hpRoot] using hp.2.2
              · intro hx
                refine ⟨(sigma, x), ?_, rfl⟩
                exact ⟨⟨hsigma'.2.1, hsigma'.2.2, hx⟩, rfl⟩
            have hinj : Set.InjOn (fun p : Restriction n × (Fin n → Bool) => p.2) fiber := by
              intro p hp q hq hpq
              have hpRoot := (Finset.mem_filter.mp hp).2
              have hqRoot := (Finset.mem_filter.mp hq).2
              apply Prod.ext
              · exact hpRoot.trans hqRoot.symm
              · exact hpq
            calc
              fiber.card = (fiber.image (fun p => p.2)).card := by
                symm
                exact Finset.card_image_iff.mpr hinj
              _ = (assignmentsAgreeingRestriction sigma).card := by rw [himage]
              _ = 2 ^ (20 * (2 * R)) := by
                rw [card_assignments_agreeing_restriction, hsigma'.2.1]
      _ = (initialGoodRoots C R).card * 2 ^ (20 * (2 * R)) := by simp
  · intro p hp
    change p ∈ initialGoodRootAssignmentPairs C R at hp
    rw [initialGoodRootAssignmentPairs, Finset.mem_filter] at hp
    change p.1 ∈ initialGoodRoots C R
    rw [initialGoodRoots, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hp.2.1, hp.2.2.1⟩

/-- The finite subtype domain used by the selected-successor map. -/
noncomputable def initialGoodRootAssignmentPairDomain {n : ℕ} (C : Layered n) (R : ℕ) :
    Finset {p : Restriction n × (Fin n → Bool) // InitialGoodRootAssignmentPair C R p} := by
  classical
  exact Finset.univ

/-- Subtype presentation of the genuine domain has the same exact product cardinality. -/
theorem card_initialGoodRootAssignmentPairDomain {n : ℕ} (C : Layered n) (R : ℕ) :
    (initialGoodRootAssignmentPairDomain C R).card =
      (initialGoodRoots C R).card * 2 ^ (20 * (2 * R)) := by
  classical
  let forgetPair :
      {p : Restriction n × (Fin n → Bool) // InitialGoodRootAssignmentPair C R p} →
        Restriction n × (Fin n → Bool) := fun p => p.1
  have hinj : Function.Injective forgetPair := by
    intro p q hpq
    exact Subtype.ext hpq
  have himage : (initialGoodRootAssignmentPairDomain C R).image forgetPair =
      initialGoodRootAssignmentPairs C R := by
    ext p
    simp only [Finset.mem_image, initialGoodRootAssignmentPairDomain,
      Finset.mem_univ, true_and,
      initialGoodRootAssignmentPairs, Finset.mem_filter]
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2
    · intro hp
      exact ⟨⟨p, hp⟩, rfl⟩
  calc
    (initialGoodRootAssignmentPairDomain C R).card =
        ((initialGoodRootAssignmentPairDomain C R).image forgetPair).card := by
      symm
      exact Finset.card_image_of_injective _ hinj
    _ = (initialGoodRootAssignmentPairs C R).card := by rw [himage]
    _ = (initialGoodRoots C R).card * 2 ^ (20 * (2 * R)) :=
      card_initialGoodRootAssignmentPairs C R

/-- Choose the provenance-carrying initial successor for a member of the genuine finite domain. -/
noncomputable def selectedInitialSupportTailSuccessor {n fuel R k : ℕ} (C : Layered n)
    (hKfuel : 20 * (2 * R) ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (k + 3) C)
    (p : {p : Restriction n × (Fin n → Bool) // InitialGoodRootAssignmentPair C R p}) :
    InitialSupportTailSuccessor (fuel := fuel) (R := R) (k := k) C p.1.1 p.1.2 :=
  Classical.choice (exists_initialSupportTailSuccessor hKfuel hsupport hAlt
    p.2.1 p.2.2.1 p.2.2.2)

/-- The finite map from good initial roots with extending assignments to their selected `20R`
successor restrictions. -/
noncomputable def initialSupportTailSuccessorImage {n fuel R k : ℕ} (C : Layered n)
    (hKfuel : 20 * (2 * R) ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (k + 3) C) : Finset (Restriction n) := by
  classical
  exact Finset.univ.image fun p =>
    (selectedInitialSupportTailSuccessor C hKfuel hsupport hAlt p).restriction

/-- The fiber of the selected initial-successor map over one ambient restriction. -/
noncomputable def initialSupportTailSuccessorFiber {n fuel R k : ℕ} (C : Layered n)
    (hKfuel : 20 * (2 * R) ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (k + 3) C) (kappa : Restriction n) :
    Finset {p : Restriction n × (Fin n → Bool) // InitialGoodRootAssignmentPair C R p} := by
  classical
  exact Finset.univ.filter fun p =>
    (selectedInitialSupportTailSuccessor C hKfuel hsupport hAlt p).restriction = kappa

/-- Every selected-map fiber injects into the product of the exact root-coarsening fiber and the
assignment cube extending the successor. -/
theorem card_initialSupportTailSuccessorFiber_le_product {n fuel R k : ℕ}
    (C : Layered n)
    (hKfuel : 20 * (2 * R) ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (k + 3) C) (kappa : Restriction n) :
    (initialSupportTailSuccessorFiber C hKfuel hsupport hAlt kappa).card ≤
      (restrictionCoarseningShellFiber (K := 20 * (2 * R)) kappa).card *
        (assignmentsAgreeingRestriction kappa).card := by
  classical
  let target :=
    (restrictionCoarseningShellFiber (K := 20 * (2 * R)) kappa).product
      (assignmentsAgreeingRestriction kappa)
  let forgetPair :
      {p : Restriction n × (Fin n → Bool) // InitialGoodRootAssignmentPair C R p} →
        Restriction n × (Fin n → Bool) := fun p => p.1
  have hinj : Function.Injective forgetPair := by
    intro p q hpq
    exact Subtype.ext hpq
  have hsubset :
      (initialSupportTailSuccessorFiber C hKfuel hsupport hAlt kappa).image forgetPair ⊆
        target := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hpFiber := (Finset.mem_filter.mp hp).2
    let step := selectedInitialSupportTailSuccessor C hKfuel hsupport hAlt p
    have hrestriction : step.restriction = kappa := hpFiber
    change p.1 ∈ target
    change p.1 ∈
      (restrictionCoarseningShellFiber (K := 20 * (2 * R)) kappa).product
        (assignmentsAgreeingRestriction kappa)
    apply Finset.mem_product.mpr
    constructor
    · rw [restrictionCoarseningShellFiber, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hrestriction ▸ step.root_extends, step.root_stars⟩
    · rw [assignmentsAgreeingRestriction, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hrestriction ▸ step.restriction_assignment⟩
  calc
    (initialSupportTailSuccessorFiber C hKfuel hsupport hAlt kappa).card =
        ((initialSupportTailSuccessorFiber C hKfuel hsupport hAlt kappa).image
          forgetPair).card := by
            symm
            exact Finset.card_image_of_injective _ hinj
    _ ≤ target.card := Finset.card_le_card hsubset
    _ = (restrictionCoarseningShellFiber (K := 20 * (2 * R)) kappa).card *
        (assignmentsAgreeingRestriction kappa).card := by simp [target]

/-- Exact numerical fiber ceiling on the genuine `40R -> 20R` selected-successor map.  The
binomial term is root multiplicity; `2^(20R)` is precisely the assignment cube over the fixed
successor and cannot be removed by provenance alone. -/
theorem card_initialSupportTailSuccessorFiber_le {n fuel R k : ℕ}
    (C : Layered n)
    (hKfuel : 20 * (2 * R) ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (k + 3) C) (kappa : Restriction n)
    (hkappa : stars kappa = 20 * R) :
    (initialSupportTailSuccessorFiber C hKfuel hsupport hAlt kappa).card ≤
      Nat.choose (n - 20 * R) (20 * R) * 2 ^ (20 * R) := by
  calc
    (initialSupportTailSuccessorFiber C hKfuel hsupport hAlt kappa).card ≤
        (restrictionCoarseningShellFiber (K := 20 * (2 * R)) kappa).card *
          (assignmentsAgreeingRestriction kappa).card :=
      card_initialSupportTailSuccessorFiber_le_product C hKfuel hsupport hAlt kappa
    _ ≤ Nat.choose (n - 20 * R) (20 * R) * 2 ^ (20 * R) := by
      rw [card_assignments_agreeing_restriction, hkappa]
      exact Nat.mul_le_mul_right _ (card_initialSupportTail_rootFiber_le kappa hkappa)

/-- Exact-domain counting and the uniform successor-fiber ceiling give the first genuine image
lower bound at the initial charging boundary.  It retains both unavoidable multiplicities:
`choose (n-20R,20R)` from root coarsening and `2^(20R)` from assignments over one successor. -/
theorem initialGoodRoots_mul_assignments_le_successorImage {n fuel R k : ℕ}
    (C : Layered n)
    (hKfuel : 20 * (2 * R) ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (k + 3) C) :
    (initialGoodRoots C R).card * 2 ^ (20 * (2 * R)) ≤
      (Nat.choose (n - 20 * R) (20 * R) * 2 ^ (20 * R)) *
        (initialSupportTailSuccessorImage C hKfuel hsupport hAlt).card := by
  classical
  let domain := initialGoodRootAssignmentPairDomain C R
  let successor :
      {p : Restriction n × (Fin n → Bool) // InitialGoodRootAssignmentPair C R p} →
        Restriction n := fun p =>
      (selectedInitialSupportTailSuccessor C hKfuel hsupport hAlt p).restriction
  let cap := Nat.choose (n - 20 * R) (20 * R) * 2 ^ (20 * R)
  have himage : domain.image successor =
      initialSupportTailSuccessorImage C hKfuel hsupport hAlt := by
    simp [domain, successor, initialGoodRootAssignmentPairDomain,
      initialSupportTailSuccessorImage]
  have hfibers : ∀ kappa ∈ domain.image successor,
      (domain.filter fun p => successor p = kappa).card ≤ cap := by
    intro kappa hkappa
    obtain ⟨p, hp, hpImage⟩ := Finset.mem_image.mp hkappa
    have hkappaStars : stars kappa = 20 * R := by
      rw [← hpImage]
      exact (selectedInitialSupportTailSuccessor C hKfuel hsupport hAlt p).ambient_eq
    change (initialSupportTailSuccessorFiber C hKfuel hsupport hAlt kappa).card ≤ cap
    exact card_initialSupportTailSuccessorFiber_le C hKfuel hsupport hAlt kappa hkappaStars
  have hcount := Finset.card_le_mul_card_image domain cap hfibers
  calc
    (initialGoodRoots C R).card * 2 ^ (20 * (2 * R)) = domain.card := by
      symm
      exact card_initialGoodRootAssignmentPairDomain C R
    _ ≤ cap * (domain.image successor).card := hcount
    _ = (Nat.choose (n - 20 * R) (20 * R) * 2 ^ (20 * R)) *
        (initialSupportTailSuccessorImage C hKfuel hsupport hAlt).card := by
      rw [himage]

/-- Combining the genuine half-shell support-tail contraction with the exact assignment-domain
count and the selected-successor fiber ceiling yields a direct lower bound on the number of
distinct `20R` successors.  The leading factor `2` is exactly the price of discarding the bad
half-shell; the remaining cap records the root-coarsening and assignment collisions. -/
theorem initialRootShell_mul_assignments_le_two_mul_successorImage {n fuel R k : ℕ}
    (C : Layered n)
    (hR : 0 < R)
    (hKfuel : 20 * (2 * R) ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (k + 3) C) :
    (initialRootShell n R).card * 2 ^ (20 * (2 * R)) ≤
      2 * (Nat.choose (n - 20 * R) (20 * R) * 2 ^ (20 * R)) *
        (initialSupportTailSuccessorImage C hKfuel hsupport hAlt).card := by
  have hhalf := initialRootShell_card_le_two_mul_good C R hR hsupport
  have himage := initialGoodRoots_mul_assignments_le_successorImage
    C hKfuel hsupport hAlt
  calc
    (initialRootShell n R).card * 2 ^ (20 * (2 * R)) ≤
        (2 * (initialGoodRoots C R).card) * 2 ^ (20 * (2 * R)) :=
      Nat.mul_le_mul_right _ hhalf
    _ = 2 * ((initialGoodRoots C R).card * 2 ^ (20 * (2 * R))) := by ring
    _ ≤ 2 * ((Nat.choose (n - 20 * R) (20 * R) * 2 ^ (20 * R)) *
        (initialSupportTailSuccessorImage C hKfuel hsupport hAlt).card) :=
      Nat.mul_le_mul_left _ himage
    _ = 2 * (Nat.choose (n - 20 * R) (20 * R) * 2 ^ (20 * R)) *
        (initialSupportTailSuccessorImage C hKfuel hsupport hAlt).card := by ring

/-- A recursive zero-support state has no support-tail bad roots at any shell or trunk depth.
This makes explicit that the later geometric iterator is already past the probabilistic
support-tail selection: there is no nonempty round event on these states to which an additional
switching charge could be attached. -/
theorem ZeroSupportLocalizedState.liveLayeredBottomSupportTail_eq_empty
    {R level slotBound : ℕ} (S : ZeroSupportLocalizedState R level slotBound)
    (K trunkDepth : ℕ) :
    liveLayeredBottomSupportTail S.circuit K trunkDepth = ∅ := by
  have hsupport : layeredBottomVariableSupport S.circuit = ∅ :=
    Finset.card_eq_zero.mp S.support_zero
  ext σ
  rw [mem_liveLayeredBottomSupportTail_iff]
  simp [hsupport]

/-- The normalized-family common-shallow bad set is likewise empty on every zero-support state,
provided the shell fits the canonical-tree fuel.  Thus both the support-tail envelope used by the
localized round and the switching bad event it bounds vanish before geometric iteration begins. -/
theorem ZeroSupportLocalizedState.normalizedLayered_commonShallowBad_eq_empty
    {R level slotBound fuel K trunkDepth residualDepth : ℕ}
    (S : ZeroSupportLocalizedState R level slotBound) (hKfuel : K ≤ fuel) :
    commonShallowBad (normalizedLayeredBottomFamily S.circuit) fuel K trunkDepth residualDepth =
      ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro σ hσ
  have htail :=
    normalizedLayered_commonShallowBad_subset_liveBottomSupportTail hKfuel hσ
  rw [S.liveLayeredBottomSupportTail_eq_empty K trunkDepth] at htail
  simpa using htail

/-- A successor retains the actual restriction used to identify its live-coordinate cube.  This
semantic edge is essential for later composition: merely returning the child state would forget how
assignments on that child lift back to the parent circuit. -/
structure ZeroSupportLocalizedStep
    {R level slotBound : ℕ} (S : ZeroSupportLocalizedState R (level + 1) slotBound)
    (nextR nextSlotBound : ℕ) where
  restriction : Restriction S.n
  circuit : Layered (stars restriction)
  ambient_eq : stars restriction = 20 * nextR
  eval_eq : ∀ z : Fin (stars restriction) → Bool,
    Layered.eval circuit z = Layered.eval S.circuit (liftLiveAssignment restriction z)
  alt : AltO (level + 2) circuit
  width_one : BottomWidth 1 circuit
  slots_le : bottomSlotCount circuit ≤ nextSlotBound
  support_zero : (layeredBottomVariableSupport circuit).card = 0

/-- Forgetting the semantic edge of a successor yields exactly the state required by another
round. -/
def ZeroSupportLocalizedStep.toState
    {R level slotBound : ℕ} {S : ZeroSupportLocalizedState R (level + 1) slotBound}
    {nextR nextSlotBound : ℕ}
    (step : ZeroSupportLocalizedStep S nextR nextSlotBound) :
    ZeroSupportLocalizedState nextR level nextSlotBound where
  n := stars step.restriction
  circuit := step.circuit
  ambient_eq := step.ambient_eq
  alt := step.alt
  width_one := step.width_one
  slots_le := step.slots_le
  support_zero := step.support_zero

/-- Two composable localized edges.  The second restriction lives on the first edge's dependent
coordinate type, so retaining the intermediate step in the package is essential: there is no
single ambient restriction of the original type that can replace this data definitionally. -/
structure ZeroSupportLocalizedTwoStep
    {R level slotBound : ℕ} (S : ZeroSupportLocalizedState R (level + 2) slotBound)
    (middleR finalR middleSlotBound finalSlotBound : ℕ) where
  first : ZeroSupportLocalizedStep S middleR middleSlotBound
  second : ZeroSupportLocalizedStep first.toState finalR finalSlotBound

/-- View a final assignment on the intermediate live-coordinate cube.  Unfolding `toState` is the
only transport required: its ambient dimension is definitionally the first restriction's star
count. -/
noncomputable def ZeroSupportLocalizedTwoStep.middleAssignment
    {R level slotBound : ℕ} {S : ZeroSupportLocalizedState R (level + 2) slotBound}
    {middleR finalR middleSlotBound finalSlotBound : ℕ}
    (path : ZeroSupportLocalizedTwoStep S middleR finalR middleSlotBound finalSlotBound)
    (z : Fin (stars path.second.restriction) → Bool) :
    Fin (stars path.first.restriction) → Bool := by
  simpa [ZeroSupportLocalizedStep.toState] using
    liftLiveAssignment path.second.restriction z

/-- The assignment embedding carried by two dependent localized edges. -/
noncomputable def ZeroSupportLocalizedTwoStep.liftAssignment
    {R level slotBound : ℕ} {S : ZeroSupportLocalizedState R (level + 2) slotBound}
    {middleR finalR middleSlotBound finalSlotBound : ℕ}
    (path : ZeroSupportLocalizedTwoStep S middleR finalR middleSlotBound finalSlotBound)
    (z : Fin (stars path.second.restriction) → Bool) : Fin S.n → Bool :=
  liftLiveAssignment path.first.restriction (path.middleAssignment z)

/-- Semantic subcube equations compose transitively even though the two live-coordinate types are
branch dependent.  This is the first nontrivial path-composition law for the recursive state. -/
theorem ZeroSupportLocalizedTwoStep.eval_eq
    {R level slotBound : ℕ} {S : ZeroSupportLocalizedState R (level + 2) slotBound}
    {middleR finalR middleSlotBound finalSlotBound : ℕ}
    (path : ZeroSupportLocalizedTwoStep S middleR finalR middleSlotBound finalSlotBound)
    (z : Fin (stars path.second.restriction) → Bool) :
    Layered.eval path.second.circuit z =
      Layered.eval S.circuit (path.liftAssignment z) := by
  calc
    Layered.eval path.second.circuit z =
        Layered.eval path.first.circuit (path.middleAssignment z) := by
      simpa [ZeroSupportLocalizedStep.toState,
        ZeroSupportLocalizedTwoStep.middleAssignment] using path.second.eval_eq z
    _ = Layered.eval S.circuit (path.liftAssignment z) := by
      exact path.first.eval_eq (path.middleAssignment z)

/-! ### Length-indexed semantic paths through dependent live-coordinate cubes -/

/-- A finite path of localized semantic edges.  Each successor restriction is defined on the
previous edge's live-coordinate type, so both the endpoint dimension and endpoint circuit are
genuinely dependent on the retained branch data.  The zero-length path is the identity edge. -/
inductive LocalizedSemanticPath : {n : ℕ} → Layered n → ℕ → Type
  | nil {n : ℕ} (C : Layered n) : LocalizedSemanticPath C 0
  | cons {n length : ℕ} {C : Layered n} (restriction : Restriction n)
      (child : Layered (stars restriction))
      (eval_eq : ∀ z : Fin (stars restriction) → Bool,
        Layered.eval child z = Layered.eval C (liftLiveAssignment restriction z))
      (tail : LocalizedSemanticPath child length) :
      LocalizedSemanticPath C (length + 1)

/-- Ambient dimension at the final dependent endpoint. -/
def LocalizedSemanticPath.endpointN {n length : ℕ} {C : Layered n}
    (path : LocalizedSemanticPath C length) : ℕ := by
  cases path with
  | nil => exact n
  | cons _ _ _ tail => exact tail.endpointN

/-- Circuit at the final dependent endpoint. -/
def LocalizedSemanticPath.endpointCircuit {n length : ℕ} {C : Layered n}
    (path : LocalizedSemanticPath C length) : Layered path.endpointN := by
  cases path with
  | nil => exact C
  | cons _ _ _ tail => exact tail.endpointCircuit

/-- Fold all live-coordinate embeddings along a dependent path.  At a successor this first lifts
from the final endpoint to the child cube, then through the current restriction to the parent. -/
noncomputable def LocalizedSemanticPath.liftAssignment
    {n length : ℕ} {C : Layered n} (path : LocalizedSemanticPath C length)
    (z : Fin path.endpointN → Bool) : Fin n → Bool := by
  cases path with
  | nil => exact z
  | cons restriction _ _ tail =>
      exact liftLiveAssignment restriction (tail.liftAssignment z)

/-- The folded assignment embedding preserves semantics across an arbitrary finite dependent
path.  This induction is the length-indexed replacement for the special two-edge calculation. -/
theorem LocalizedSemanticPath.eval_eq
    {n length : ℕ} {C : Layered n} (path : LocalizedSemanticPath C length)
    (z : Fin path.endpointN → Bool) :
    Layered.eval path.endpointCircuit z = Layered.eval C (path.liftAssignment z) := by
  induction path with
  | nil => rfl
  | cons restriction child hedge tail ih =>
      exact (ih z).trans (hedge (tail.liftAssignment z))

/-- XOR phase accumulated from all fixed-true coordinates along a dependent semantic path. -/
def LocalizedSemanticPath.parityPhase
    {n length : ℕ} {C : Layered n} (path : LocalizedSemanticPath C length) : Bool :=
  match path with
  | .nil _ => false
  | .cons restriction _ _ tail => xor tail.parityPhase (fixedParityPhase restriction)

/-- Parity is transported through a whole dependent path by XOR with its accumulated fixed-bit
phase.  This is the iterated form of `parity_liftLiveAssignment`; retaining only the first edge's
phase is insufficient. -/
theorem LocalizedSemanticPath.parity_liftAssignment
    {n length : ℕ} {C : Layered n} (path : LocalizedSemanticPath C length)
    (z : Fin path.endpointN → Bool) :
    DTree.parity (path.liftAssignment z) =
      xor (DTree.parity z) path.parityPhase := by
  induction path with
  | nil => simp [LocalizedSemanticPath.liftAssignment,
      LocalizedSemanticPath.parityPhase]
  | cons restriction child hedge tail ih =>
      rw [LocalizedSemanticPath.liftAssignment,
        parity_liftLiveAssignment restriction, ih, Bool.xor_assoc]
      rfl

/-- Folding live-coordinate embeddings along a dependent path remains injective.  Thus a fixed
root assignment has at most one endpoint assignment preimage along any retained branch. -/
theorem LocalizedSemanticPath.liftAssignment_injective
    {n length : ℕ} {C : Layered n} (path : LocalizedSemanticPath C length) :
    Function.Injective path.liftAssignment := by
  induction path with
  | nil =>
      intro x y hxy
      exact hxy
  | cons restriction child hedge tail ih =>
      exact (liftLiveAssignment_injective restriction).comp ih

/-- Pointwise preimage form of path injectivity, convenient for later branch-fiber counts. -/
theorem LocalizedSemanticPath.eq_of_liftAssignment_eq
    {n length : ℕ} {C : Layered n} (path : LocalizedSemanticPath C length)
    {x y : Fin path.endpointN → Bool}
    (hxy : path.liftAssignment x = path.liftAssignment y) :
    x = y :=
  path.liftAssignment_injective hxy

/-- Exact finite-fiber consequence: over the endpoint Boolean cube, every root assignment has at
most one preimage along a fixed dependent path. -/
theorem LocalizedSemanticPath.liftAssignment_fiber_card_le_one
    {n length : ℕ} {C : Layered n} (path : LocalizedSemanticPath C length)
    (root : Fin n → Bool) :
    ((Finset.univ : Finset (Fin path.endpointN → Bool)).filter
      fun z => path.liftAssignment z = root).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  exact path.liftAssignment_injective (hx.trans hy.symm)

/-- Agreement with a lifted local restriction separates into agreement with the ambient
restriction and agreement, in canonical live coordinates, with the local restriction. -/
theorem agreeRestriction_liftLiveRestriction_iff {n : ℕ} (tau : Restriction n)
    (sigma : Restriction (stars tau)) (x : Fin n → Bool) :
    DTree.agreeRestriction (liftLiveRestriction tau sigma) x ↔
      DTree.agreeRestriction tau x ∧
        DTree.agreeRestriction sigma (fun i => x (liveCoordEquiv tau i)) := by
  constructor
  · intro h
    constructor
    · intro v b hv
      have hfixed : v ∉ freeVars tau := by
        rw [mem_freeVars, hv]
        simp
      exact h v b (by simpa [liftLiveRestriction, hfixed] using hv)
    · intro i b hi
      exact h (liveCoordEquiv tau i) b (by simpa using hi)
  · rintro ⟨htau, hsigma⟩ v b hv
    by_cases hlive : v ∈ freeVars tau
    · let i : Fin (stars tau) := (liveCoordEquiv tau).symm ⟨v, hlive⟩
      have hi : sigma i = some b := by
        simpa [liftLiveRestriction, hlive, i] using hv
      have := hsigma i b hi
      simpa [i] using this
    · have ht : tau v = some b := by
        simpa [liftLiveRestriction, hlive] using hv
      exact htau v b ht

/-- Fold every dependent edge restriction back into one restriction on the root cube.  The empty
path fixes nothing; a successor lifts the tail's composed restriction through the current edge. -/
noncomputable def LocalizedSemanticPath.rootRestriction
    {n length : ℕ} {C : Layered n} (path : LocalizedSemanticPath C length) : Restriction n := by
  cases path with
  | nil => exact fun _ => none
  | cons restriction _ _ tail =>
      exact liftLiveRestriction restriction tail.rootRestriction

/-- The folded assignment image of a dependent semantic path is exactly the extension cube of its
single composed root restriction.  This removes all canonical-coordinate transports from the
cross-branch overlap question. -/
theorem LocalizedSemanticPath.exists_liftAssignment_eq_iff_agrees
    {n length : ℕ} {C : Layered n} (path : LocalizedSemanticPath C length)
    (x : Fin n → Bool) :
    (∃ z : Fin path.endpointN → Bool, path.liftAssignment z = x) ↔
      DTree.agreeRestriction path.rootRestriction x := by
  induction path with
  | nil =>
      constructor
      · rintro ⟨z, rfl⟩
        intro v b h
        simp [LocalizedSemanticPath.rootRestriction] at h
      · intro _
        exact ⟨x, rfl⟩
  | cons restriction child hedge tail ih =>
      rw [LocalizedSemanticPath.rootRestriction,
        agreeRestriction_liftLiveRestriction_iff]
      constructor
      · rintro ⟨z, hz⟩
        have houter : DTree.agreeRestriction restriction x := by
          rw [← hz]
          exact liftLiveAssignment_agrees restriction (tail.liftAssignment z)
        refine ⟨houter, ?_⟩
        apply (ih _).mp
        refine ⟨z, ?_⟩
        funext i
        change liftLiveAssignment restriction (tail.liftAssignment z) = x at hz
        have hi := congrFun hz (liveCoordEquiv restriction i)
        simpa using hi
      · rintro ⟨houter, htail⟩
        obtain ⟨z, hz⟩ := (ih _).mpr htail
        obtain ⟨y, hy⟩ :=
          (exists_liftLiveAssignment_eq_iff_agrees restriction x).2 houter
        refine ⟨z, ?_⟩
        change liftLiveAssignment restriction (tail.liftAssignment z) = x
        rw [hz]
        have hycoord : y = fun i => x (liveCoordEquiv restriction i) := by
          funext i
          have hi := congrFun hy (liveCoordEquiv restriction i)
          simpa using hi
        rw [← hycoord]
        exact hy

/-- The composed restriction has exactly the endpoint number of live coordinates. -/
@[simp] theorem LocalizedSemanticPath.stars_rootRestriction
    {n length : ℕ} {C : Layered n} (path : LocalizedSemanticPath C length) :
    stars path.rootRestriction = path.endpointN := by
  induction path with
  | nil =>
      simp [LocalizedSemanticPath.rootRestriction, LocalizedSemanticPath.endpointN,
        stars, freeVars]
  | cons restriction child hedge tail ih =>
      change stars (liftLiveRestriction restriction tail.rootRestriction) = tail.endpointN
      rw [stars_liftLiveRestriction]
      exact ih

/-- Exact cross-branch overlap criterion for arbitrary dependent paths: their folded images meet
if and only if their composed root restrictions are compatible. -/
theorem LocalizedSemanticPath.liftAssignment_ranges_overlap_iff
    {n leftLength rightLength : ℕ} {C D : Layered n}
    (left : LocalizedSemanticPath C leftLength)
    (right : LocalizedSemanticPath D rightLength) :
    (∃ z : Fin left.endpointN → Bool, ∃ w : Fin right.endpointN → Bool,
      left.liftAssignment z = right.liftAssignment w) ↔
      RestrictionsCompatible left.rootRestriction right.rootRestriction := by
  rw [restrictionsCompatible_iff_exists_agrees]
  constructor
  · rintro ⟨z, w, hzw⟩
    exact ⟨left.liftAssignment z,
      (left.exists_liftAssignment_eq_iff_agrees _).1 ⟨z, rfl⟩,
      hzw ▸ (right.exists_liftAssignment_eq_iff_agrees _).1 ⟨w, rfl⟩⟩
  · rintro ⟨x, hxleft, hxright⟩
    obtain ⟨z, hz⟩ := (left.exists_liftAssignment_eq_iff_agrees x).2 hxleft
    obtain ⟨w, hw⟩ := (right.exists_liftAssignment_eq_iff_agrees x).2 hxright
    exact ⟨z, w, hz.trans hw.symm⟩

/-- Every state-transition edge supplies a one-edge semantic path. -/
def ZeroSupportLocalizedStep.toSemanticPath
    {R level slotBound : ℕ} {S : ZeroSupportLocalizedState R (level + 1) slotBound}
    {nextR nextSlotBound : ℕ}
    (step : ZeroSupportLocalizedStep S nextR nextSlotBound) :
    LocalizedSemanticPath S.circuit 1 := by
  simpa using LocalizedSemanticPath.cons step.restriction step.circuit step.eval_eq
    (LocalizedSemanticPath.nil step.circuit)

/-- The previously constructed two-step package embeds into the uniform length-indexed path. -/
def ZeroSupportLocalizedTwoStep.toSemanticPath
    {R level slotBound : ℕ} {S : ZeroSupportLocalizedState R (level + 2) slotBound}
    {middleR finalR middleSlotBound finalSlotBound : ℕ}
    (path : ZeroSupportLocalizedTwoStep S middleR finalR middleSlotBound finalSlotBound) :
    LocalizedSemanticPath S.circuit 2 := by
  refine LocalizedSemanticPath.cons path.first.restriction path.first.circuit
    path.first.eval_eq ?_
  simpa [ZeroSupportLocalizedStep.toState] using
    LocalizedSemanticPath.cons path.second.restriction path.second.circuit
      path.second.eval_eq (LocalizedSemanticPath.nil path.second.circuit)

/-- A zero-support state on shell `i` advances along every assignment to a dependent successor on
shell `i+1`.  This is one canonical-branch round with the assignment provenance that the earlier
`Nonempty` interface discarded: the returned survivor restriction is extended by the assignment
used to select the prefix-tree leaf.  The support-tail good condition is automatic at the all-free
root, while the exact geometric shell identity supplies the child's ambient dimension. -/
theorem ZeroSupportLocalizedState.exists_next_agreeing
    {d r i level slotBound fuel : ℕ} (hi : i < d)
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + 1) slotBound)
    (hfuel : 20 * zeroSupportSurvivorScale d r i ≤ fuel)
    (x : Fin S.n → Bool) :
    ∃ step : ZeroSupportLocalizedStep S
        (zeroSupportSurvivorScale d r (i + 1)) (slotBound * 3),
      Rung4Restriction.Extends step.restriction x := by
  let σ : Restriction S.n := fun _ => none
  have hstars : stars σ = 20 * zeroSupportSurvivorScale d r i := by
    calc
      stars σ = S.n := by simp [σ, stars, freeVars]
      _ = 20 * zeroSupportSurvivorScale d r i := S.ambient_eq
  have hsupport : 16 * (layeredBottomVariableSupport S.circuit).card ≤ S.n := by
    rw [S.support_zero]
    omega
  have hAlt : AltO (level + 3) S.circuit := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using S.alt
  have hgood : σ ∉ liveLayeredBottomSupportTail S.circuit
      (20 * zeroSupportSurvivorScale d r i)
      (10 * zeroSupportSurvivorScale d r i) := by
    intro hbad
    rw [mem_liveLayeredBottomSupportTail_iff] at hbad
    have hfiltered :
        ((layeredBottomVariableSupport S.circuit).filter fun j ↦ σ j = none).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact (Finset.card_filter_le _ _).trans_eq S.support_zero
    omega
  have hx : Rung4Restriction.Extends σ x := by
    intro j b hj
    simp [σ] at hj
  have hround :=
    (supportTail_normalizedSurvivorRound_localized
      (C := S.circuit) (fuel := fuel)
      (R := zeroSupportSurvivorScale d r i) (k := level)
      hfuel hsupport hAlt).2 σ hstars hgood x hx
  dsimp only at hround
  obtain ⟨κ, _hext, hκextends, hκstars, _hκfuel, heval, _hdepth, hDalt, _hne,
    hwidth, hslots, hDsupport, _hdensity⟩ := hround
  refine ⟨{
    restriction := κ
    circuit := localizeLiveLayered κ
      (collapseRound fuel
        (CommonTree.run
          (CommonTree.prefixEndpoints σ
            (canonicalFamilyTree (normalizedLayeredBottomFamily S.circuit) fuel σ)
            (10 * zeroSupportSurvivorScale d r i)) x)
        S.circuit)
    ambient_eq := ?_
    eval_eq := heval
    alt := hDalt
    width_one := hwidth
    slots_le := hslots.trans (by nlinarith [S.slots_le])
    support_zero := hDsupport }, hκextends⟩
  calc
    stars κ = 10 * zeroSupportSurvivorScale d r i := hκstars
    _ = 20 * zeroSupportSurvivorScale d r (i + 1) :=
      (zeroSupportSurvivorScale_shell_exact d r i hi).symm

/-- Fix one provenance-carrying successor for each total assignment.  The domain is the finite
Boolean cube, so this is an actual finite branch generator rather than another unlabelled
existence statement. -/
noncomputable def ZeroSupportLocalizedState.selectedNextStep
    {d r i level slotBound fuel : ℕ} (hi : i < d)
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + 1) slotBound)
    (hfuel : 20 * zeroSupportSurvivorScale d r i ≤ fuel)
    (x : Fin S.n → Bool) :
    ZeroSupportLocalizedStep S
      (zeroSupportSurvivorScale d r (i + 1)) (slotBound * 3) :=
  Classical.choose (S.exists_next_agreeing hi hfuel x)

/-- The selected successor keeps the assignment label that generated it: the root assignment
extends its survivor restriction. -/
theorem ZeroSupportLocalizedState.selectedNextStep_agreeing
    {d r i level slotBound fuel : ℕ} (hi : i < d)
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + 1) slotBound)
    (hfuel : 20 * zeroSupportSurvivorScale d r i ≤ fuel)
    (x : Fin S.n → Bool) :
    Rung4Restriction.Extends (S.selectedNextStep hi hfuel x).restriction x :=
  Classical.choose_spec (S.exists_next_agreeing hi hfuel x)

/-- The finite provenance labels for the one-round selector.  Keeping the full assignment cube,
rather than prematurely quotienting by the selected restriction, preserves collisions for the
later branch-fiber audit. -/
def ZeroSupportLocalizedState.generatedNextLabels
    {d r i level slotBound fuel : ℕ} (hi : i < d)
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + 1) slotBound)
    (hfuel : 20 * zeroSupportSurvivorScale d r i ≤ fuel) :
    Finset (Fin S.n → Bool) :=
  Finset.univ

/-- Root-assignment completeness of the finite generator.  Every assignment is a retained finite
label and extends the survivor restriction of its selected successor. -/
theorem ZeroSupportLocalizedState.generatedNextLabels_complete
    {d r i level slotBound fuel : ℕ} (hi : i < d)
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + 1) slotBound)
    (hfuel : 20 * zeroSupportSurvivorScale d r i ≤ fuel)
    (x : Fin S.n → Bool) :
    x ∈ S.generatedNextLabels hi hfuel ∧
      Rung4Restriction.Extends (S.selectedNextStep hi hfuel x).restriction x := by
  constructor
  · simp [ZeroSupportLocalizedState.generatedNextLabels]
  · exact S.selectedNextStep_agreeing hi hfuel x

/-- The finite generator has exactly one label for each Boolean root assignment. -/
@[simp] theorem ZeroSupportLocalizedState.card_generatedNextLabels
    {d r i level slotBound fuel : ℕ} (hi : i < d)
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + 1) slotBound)
    (hfuel : 20 * zeroSupportSurvivorScale d r i ≤ fuel) :
    (S.generatedNextLabels hi hfuel).card = 2 ^ S.n := by
  simp [ZeroSupportLocalizedState.generatedNextLabels]

/-- Compatibility wrapper preserving the original existential-only successor API. -/
theorem ZeroSupportLocalizedState.exists_next
    {d r i level slotBound fuel : ℕ} (hi : i < d)
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + 1) slotBound)
    (hfuel : 20 * zeroSupportSurvivorScale d r i ≤ fuel)
    (x : Fin S.n → Bool) :
    Nonempty (ZeroSupportLocalizedStep S
      (zeroSupportSurvivorScale d r (i + 1)) (slotBound * 3)) := by
  obtain ⟨step, _⟩ := S.exists_next_agreeing hi hfuel x
  exact ⟨step⟩

/-- Two successive calls to the one-round constructor produce a genuinely composable dependent
path.  The branch assignments are deliberately arbitrary here: their only role is to select the
canonical tree leaf used by each existential round, while the returned edge equations hold for
every assignment on the final live cube. -/
theorem ZeroSupportLocalizedState.exists_two_step
    {d r i level slotBound fuel₀ fuel₁ : ℕ}
    (hi₀ : i < d) (hi₁ : i + 1 < d)
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + 2) slotBound)
    (hfuel₀ : 20 * zeroSupportSurvivorScale d r i ≤ fuel₀)
    (hfuel₁ : 20 * zeroSupportSurvivorScale d r (i + 1) ≤ fuel₁) :
    Nonempty (ZeroSupportLocalizedTwoStep S
      (zeroSupportSurvivorScale d r (i + 1))
      (zeroSupportSurvivorScale d r (i + 2))
      (slotBound * 3) ((slotBound * 3) * 3)) := by
  obtain ⟨first⟩ := S.exists_next hi₀ hfuel₀ (fun _ => false)
  obtain ⟨second⟩ := first.toState.exists_next hi₁ hfuel₁ (fun _ => false)
  exact ⟨{ first := first, second := second }⟩

/-! ### Geometrically scheduled dependent localized paths -/

/-- A dependent localized path carrying the complete structural recurrence.  At shell `i` it
stores the exact geometric scale, `length` remaining alternation drops, and the forward slot
envelope `M * 3^i`.  The successor is therefore indexed by the next shell and by the exact next
slot envelope, rather than merely retaining those facts as propositions at the endpoint. -/
inductive ZeroSupportGeometricPath (d r level M : ℕ) :
    (i length : ℕ) →
      ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
        (level + length) (M * 3 ^ i) → Type
  | nil (i : ℕ)
      (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i) level
        (M * 3 ^ i)) :
      ZeroSupportGeometricPath d r level M i 0 S
  | cons {i length : ℕ}
      {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
        (level + (length + 1)) (M * 3 ^ i)}
      (step : ZeroSupportLocalizedStep S
        (zeroSupportSurvivorScale d r (i + 1)) (M * 3 ^ (i + 1)))
      (tail : ZeroSupportGeometricPath d r level M (i + 1) length step.toState) :
      ZeroSupportGeometricPath d r level M i (length + 1) S

/-- Forgetting the schedule and state invariants leaves the arbitrary dependent semantic path
constructed above.  In particular, its folded assignment embedding is immediately covered by
`LocalizedSemanticPath.eval_eq`. -/
def ZeroSupportGeometricPath.toSemanticPath
    {d r level M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i)}
    (path : ZeroSupportGeometricPath d r level M i length S) :
    LocalizedSemanticPath S.circuit length :=
  match path with
  | .nil _ S => LocalizedSemanticPath.nil S.circuit
  | .cons step tail =>
      LocalizedSemanticPath.cons step.restriction step.circuit step.eval_eq (by
        simpa [ZeroSupportLocalizedStep.toState] using tail.toSemanticPath)

/-- The endpoint again has a state, now at shell `i+length`, with all requested indices exposed in
its type: remaining level `level` and slot envelope `M * 3^(i+length)`. -/
def ZeroSupportGeometricPath.endpointState
    {d r level M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i)}
    (path : ZeroSupportGeometricPath d r level M i length S) :
    ZeroSupportLocalizedState (zeroSupportSurvivorScale d r (i + length)) level
      (M * 3 ^ (i + length)) :=
  match path with
  | .nil _ S => by simpa using S
  | .cons _ tail => by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail.endpointState

/-- At remaining level zero, every geometric endpoint is an exposed DNF with canonical depth
strictly below its positive scheduled dimension.  In fact the depth is exactly zero for every
fuel and restriction; positivity is used only to make the terminal inequality strict. -/
theorem ZeroSupportGeometricPath.exists_endpointDnf_depth_lt
    {d r M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (0 + length) (M * 3 ^ i)}
    (path : ZeroSupportGeometricPath d r 0 M i length S)
    (hR : 0 < zeroSupportSurvivorScale d r (i + length)) :
    ∃ D : List (Clause path.endpointState.n),
      path.endpointState.circuit = Layered.dnf D ∧
        ∀ fuel σ, (canonicalDT D fuel σ).depth < path.endpointState.n := by
  obtain ⟨D, hD, hdepth⟩ := path.endpointState.exists_terminalDnf_depth_zero
  refine ⟨D, hD, ?_⟩
  intro fuel σ
  rw [hdepth fuel σ, path.endpointState.ambient_eq]
  omega

/-- The semantic endpoint projection computes through one geometric successor without exposing
the dependent proof transports used to build the semantic tail. -/
@[simp] theorem ZeroSupportGeometricPath.toSemanticPath_endpointN_cons
    {d r level M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + (length + 1)) (M * 3 ^ i)}
    (step : ZeroSupportLocalizedStep S
      (zeroSupportSurvivorScale d r (i + 1)) (M * 3 ^ (i + 1)))
    (tail : ZeroSupportGeometricPath d r level M (i + 1) length step.toState) :
    (ZeroSupportGeometricPath.cons step tail).toSemanticPath.endpointN =
      tail.toSemanticPath.endpointN := rfl

/-- Any finite prefix fitting within the geometric horizon is generated by repeated applications
of `ZeroSupportLocalizedState.exists_next`.  Fuel may vary by shell; no uniform choice is hidden in
the construction. -/
theorem ZeroSupportLocalizedState.exists_geometric_path
    {d r level M i length : ℕ}
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i))
    (horizon : i + length ≤ d)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, i ≤ j → j < i + length →
      20 * zeroSupportSurvivorScale d r j ≤ fuel j) :
    Nonempty (ZeroSupportGeometricPath d r level M i length S) := by
  induction length generalizing i with
  | zero =>
      exact ⟨ZeroSupportGeometricPath.nil i S⟩
  | succ length ih =>
      have hi : i < d := by omega
      have hfueli : 20 * zeroSupportSurvivorScale d r i ≤ fuel i :=
        hfuel i (by omega) (by omega)
      obtain ⟨rawStep⟩ := S.exists_next hi hfueli (fun _ => false)
      have step : ZeroSupportLocalizedStep S
          (zeroSupportSurvivorScale d r (i + 1)) (M * 3 ^ (i + 1)) := by
        simpa only [pow_succ, Nat.mul_assoc] using rawStep
      have htailHorizon : i + 1 + length ≤ d := by omega
      have htailFuel : ∀ j, i + 1 ≤ j → j < i + 1 + length →
          20 * zeroSupportSurvivorScale d r j ≤ fuel j := by
        intro j hjlo hjhi
        exact hfuel j (by omega) (by omega)
      obtain ⟨tail⟩ := ih step.toState htailHorizon htailFuel
      exact ⟨ZeroSupportGeometricPath.cons step tail⟩

/-- A geometrically scheduled path can be selected coherently from one root assignment.  At each
round the same assignment is restricted to the current canonical live coordinates and used as the
next branch label.  The endpoint assignment therefore lifts all the way back to the original root
assignment, retaining the provenance that the existential-only path constructor discarded. -/
theorem ZeroSupportLocalizedState.exists_geometric_path_lifting_assignment
    {d r level M i length : ℕ}
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i))
    (horizon : i + length ≤ d)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, i ≤ j → j < i + length →
      20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (x : Fin S.n → Bool) :
    ∃ path : ZeroSupportGeometricPath d r level M i length S,
      ∃ z : Fin path.toSemanticPath.endpointN → Bool,
        path.toSemanticPath.liftAssignment z = x := by
  induction length generalizing i with
  | zero =>
      refine ⟨ZeroSupportGeometricPath.nil i S, x, rfl⟩
  | succ length ih =>
      have hi : i < d := by omega
      have hfueli : 20 * zeroSupportSurvivorScale d r i ≤ fuel i :=
        hfuel i (by omega) (by omega)
      let rawStep := S.selectedNextStep hi hfueli x
      have hrawAgree : Rung4Restriction.Extends rawStep.restriction x := by
        exact S.selectedNextStep_agreeing hi hfueli x
      have hslot : (M * 3 ^ i) * 3 = M * 3 ^ (i + 1) := by
        rw [pow_succ]
        ring
      let step : ZeroSupportLocalizedStep S
          (zeroSupportSurvivorScale d r (i + 1)) (M * 3 ^ (i + 1)) := {
        restriction := rawStep.restriction
        circuit := rawStep.circuit
        ambient_eq := rawStep.ambient_eq
        eval_eq := rawStep.eval_eq
        alt := rawStep.alt
        width_one := rawStep.width_one
        slots_le := by rw [← hslot]; exact rawStep.slots_le
        support_zero := rawStep.support_zero }
      have hstepAgree : DTree.agreeRestriction step.restriction x := by
        change Rung4Restriction.Extends rawStep.restriction x
        exact hrawAgree
      let localX : Fin step.toState.n → Bool :=
        fun j => x (liveCoordEquiv step.restriction j)
      have htailHorizon : i + 1 + length ≤ d := by omega
      have htailFuel : ∀ j, i + 1 ≤ j → j < i + 1 + length →
          20 * zeroSupportSurvivorScale d r j ≤ fuel j := by
        intro j hjlo hjhi
        exact hfuel j (by omega) (by omega)
      obtain ⟨tail, z, hz⟩ :=
        ih step.toState htailHorizon htailFuel localX
      refine ⟨ZeroSupportGeometricPath.cons step tail, z, ?_⟩
      change liftLiveAssignment step.restriction
          (tail.toSemanticPath.liftAssignment z) = x
      rw [hz]
      simpa [localX, ZeroSupportLocalizedStep.toState] using
        liftLiveAssignment_restrict_eq_of_agrees step.restriction x hstepAgree

/-- Deterministically select the provenance-carrying geometric path generated by a root
assignment.  Classical choice only removes the final existential packaging: every round inside
the witness was selected from the assignment restricted to that round's live coordinates. -/
noncomputable def ZeroSupportLocalizedState.selectedGeometricPath
    {d r level M i length : ℕ}
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i))
    (horizon : i + length ≤ d)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, i ≤ j → j < i + length →
      20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (x : Fin S.n → Bool) :
    ZeroSupportGeometricPath d r level M i length S :=
  Classical.choose (S.exists_geometric_path_lifting_assignment
    horizon fuel hfuel x)

/-- The composed root restriction of the assignment-selected path is extended by the same root
assignment.  This is the end-to-end provenance invariant needed before distinct generated fibers
can be counted. -/
theorem ZeroSupportLocalizedState.selectedGeometricPath_rootRestriction_agrees
    {d r level M i length : ℕ}
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i))
    (horizon : i + length ≤ d)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, i ≤ j → j < i + length →
      20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (x : Fin S.n → Bool) :
    DTree.agreeRestriction
      (S.selectedGeometricPath horizon fuel hfuel x).toSemanticPath.rootRestriction x := by
  have hlift := Classical.choose_spec
    (S.exists_geometric_path_lifting_assignment horizon fuel hfuel x)
  exact (LocalizedSemanticPath.exists_liftAssignment_eq_iff_agrees
    (S.selectedGeometricPath horizon fuel hfuel x).toSemanticPath x).1 hlift

/-- The generated scheduled path inherits the transitive semantic equation for its folded live-
coordinate embedding. -/
theorem ZeroSupportGeometricPath.eval_eq
    {d r level M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i)}
    (path : ZeroSupportGeometricPath d r level M i length S)
    (z : Fin path.toSemanticPath.endpointN → Bool) :
    Layered.eval path.toSemanticPath.endpointCircuit z =
      Layered.eval S.circuit (path.toSemanticPath.liftAssignment z) :=
  path.toSemanticPath.eval_eq z

/-- Forgetting the schedule and projecting the endpoint state compute the same final ambient
dimension. -/
theorem ZeroSupportGeometricPath.toSemanticPath_endpointN_scheduled
    {d r level M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i)}
    (path : ZeroSupportGeometricPath d r level M i length S) :
    path.toSemanticPath.endpointN =
      20 * zeroSupportSurvivorScale d r (i + length) := by
  induction path with
  | nil _ S => exact S.ambient_eq
  | cons step tail ih =>
      rw [ZeroSupportGeometricPath.toSemanticPath_endpointN_cons, ih]
      congr 2
      omega

@[simp] theorem ZeroSupportGeometricPath.semantic_endpointN_eq_endpointState_n
    {d r level M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i)}
    (path : ZeroSupportGeometricPath d r level M i length S) :
    path.toSemanticPath.endpointN = path.endpointState.n := by
  exact path.toSemanticPath_endpointN_scheduled.trans path.endpointState.ambient_eq.symm

/-- Terminal DNF extraction directly in the semantic endpoint presentation.  Recursing through
the geometric path avoids casting the entire dependent endpoint-state structure: both the DNF and
the decision tree now live definitionally on the same cube used by `LocalizedSemanticPath.eval_eq`.
-/
theorem ZeroSupportGeometricPath.exists_semantic_endpointDnf_depth_lt
    {d r M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (0 + length) (M * 3 ^ i)}
    (path : ZeroSupportGeometricPath d r 0 M i length S)
    (hR : 0 < zeroSupportSurvivorScale d r (i + length)) :
    ∃ D : List (Clause path.toSemanticPath.endpointN),
      path.toSemanticPath.endpointCircuit = Layered.dnf D ∧
        ∀ fuel σ, (canonicalDT D fuel σ).depth < path.toSemanticPath.endpointN := by
  induction path with
  | nil i S =>
      change ∃ D : List (Clause S.n), S.circuit = Layered.dnf D ∧
        ∀ fuel σ, (canonicalDT D fuel σ).depth < S.n
      obtain ⟨D, hD, hdepth⟩ := S.exists_terminalDnf_depth_zero
      refine ⟨D, hD, ?_⟩
      intro fuel σ
      rw [hdepth fuel σ, S.ambient_eq]
      simpa using hR
  | cons step tail ih =>
      change ∃ D : List (Clause tail.toSemanticPath.endpointN),
        tail.toSemanticPath.endpointCircuit = Layered.dnf D ∧
          ∀ fuel σ, (canonicalDT D fuel σ).depth < tail.toSemanticPath.endpointN
      apply ih
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hR

/-- A positive zero-support terminal path cannot compute live parity, even after an arbitrary
fixed XOR phase.  This is the localized structural cashout: the canonical tree is built at the
all-free endpoint restriction, computes the exposed semantic-endpoint DNF, and is too shallow for
parity on that same dependent live cube. -/
theorem ZeroSupportGeometricPath.exists_semantic_endpoint_disagrees_parity_xor
    {d r M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (0 + length) (M * 3 ^ i)}
    (path : ZeroSupportGeometricPath d r 0 M i length S)
    (hR : 0 < zeroSupportSurvivorScale d r (i + length))
    (phase : Bool) :
    ∃ z : Fin path.toSemanticPath.endpointN → Bool,
      Layered.eval path.toSemanticPath.endpointCircuit z ≠
        xor (DTree.parity z) phase := by
  obtain ⟨D, hD, hdepth⟩ := path.exists_semantic_endpointDnf_depth_lt hR
  let σ : Restriction path.toSemanticPath.endpointN := fun _ => none
  let fuel := path.toSemanticPath.endpointN
  have hstars : stars σ ≤ fuel := by
    simp [σ, fuel, stars, freeVars]
  have hext (z : Fin path.toSemanticPath.endpointN → Bool) :
      Rung4Restriction.Extends σ z := by
    intro v b hv
    simp [σ] at hv
  obtain ⟨z, hz⟩ := DTree.shallow_dtree_not_parity_xor
    (toDTree (canonicalDT D fuel σ)) phase (by
      rw [toDTree_depth]
      exact hdepth fuel σ)
  refine ⟨z, ?_⟩
  rw [hD, Layered.eval_dnf, ← dnfEval_eq_dnfValue,
    ← canonicalDT_eval fuel σ z hstars (hext z), ← toDTree_eval]
  exact hz

/-- Every structurally admissible geometric path ends on the scheduled shell.  This is the
dimension fact needed to place all of its composed root restrictions in one finite ambient
family. -/
@[simp] theorem ZeroSupportGeometricPath.semantic_endpointN
    {d r level M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i)}
    (path : ZeroSupportGeometricPath d r level M i length S) :
    path.toSemanticPath.endpointN =
      20 * zeroSupportSurvivorScale d r (i + length) := by
  exact path.toSemanticPath_endpointN_scheduled

/-! ### The assignment-generated composed-root image -/

/-- The distinct composed root restrictions actually selected by total root assignments.  Unlike
`admissibleGeometricRootRestrictions`, this image retains constructor provenance and therefore
supports a genuine fiber count for the selected geometric-path map. -/
noncomputable def generatedGeometricRootRestrictions
    {d r level M i length : ℕ}
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i))
    (horizon : i + length ≤ d)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, i ≤ j → j < i + length →
      20 * zeroSupportSurvivorScale d r j ≤ fuel j) :
    Finset (Restriction S.n) := by
  classical
  exact Finset.univ.image fun x =>
    (S.selectedGeometricPath horizon fuel hfuel x).toSemanticPath.rootRestriction

@[simp] theorem mem_generatedGeometricRootRestrictions_iff
    {d r level M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i)}
    {horizon : i + length ≤ d}
    {fuel : ℕ → ℕ}
    {hfuel : ∀ j, i ≤ j → j < i + length →
      20 * zeroSupportSurvivorScale d r j ≤ fuel j}
    {rho : Restriction S.n} :
    rho ∈ generatedGeometricRootRestrictions S horizon fuel hfuel ↔
      ∃ x : Fin S.n → Bool,
        (S.selectedGeometricPath horizon fuel hfuel x).toSemanticPath.rootRestriction = rho := by
  classical
  simp [generatedGeometricRootRestrictions]

/-- Every assignment-generated composed restriction lies on the scheduled final survivor shell. -/
theorem stars_eq_of_mem_generatedGeometricRootRestrictions
    {d r level M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i)}
    {horizon : i + length ≤ d}
    {fuel : ℕ → ℕ}
    {hfuel : ∀ j, i ≤ j → j < i + length →
      20 * zeroSupportSurvivorScale d r j ≤ fuel j}
    {rho : Restriction S.n}
    (hrho : rho ∈ generatedGeometricRootRestrictions S horizon fuel hfuel) :
    stars rho = 20 * zeroSupportSurvivorScale d r (i + length) := by
  obtain ⟨x, rfl⟩ := mem_generatedGeometricRootRestrictions_iff.mp hrho
  rw [LocalizedSemanticPath.stars_rootRestriction]
  exact (S.selectedGeometricPath horizon fuel hfuel x).semantic_endpointN

/-- Root assignments in one selected-map fiber. -/
noncomputable def generatedGeometricRootFiber
    {d r level M i length : ℕ}
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i))
    (horizon : i + length ≤ d)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, i ≤ j → j < i + length →
      20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (rho : Restriction S.n) : Finset (Fin S.n → Bool) := by
  classical
  exact Finset.univ.filter fun x =>
    (S.selectedGeometricPath horizon fuel hfuel x).toSemanticPath.rootRestriction = rho

/-- Provenance forces every assignment in a generated fiber to extend that fiber's root
restriction.  Thus a fiber cannot be larger than its endpoint Boolean cube. -/
theorem generatedGeometricRootFiber_subset_agreeing
    {d r level M i length : ℕ}
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i))
    (horizon : i + length ≤ d)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, i ≤ j → j < i + length →
      20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (rho : Restriction S.n) :
    generatedGeometricRootFiber S horizon fuel hfuel rho ⊆
      assignmentsAgreeingRestriction rho := by
  classical
  intro x hx
  rw [generatedGeometricRootFiber, Finset.mem_filter] at hx
  rw [assignmentsAgreeingRestriction, Finset.mem_filter]
  refine ⟨Finset.mem_univ x, ?_⟩
  rw [← hx.2]
  exact S.selectedGeometricPath_rootRestriction_agrees horizon fuel hfuel x

/-- Every generated-map fiber has size at most the final live cube. -/
theorem card_generatedGeometricRootFiber_le
    {d r level M i length : ℕ}
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i))
    (horizon : i + length ≤ d)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, i ≤ j → j < i + length →
      20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    {rho : Restriction S.n}
    (hrho : rho ∈ generatedGeometricRootRestrictions S horizon fuel hfuel) :
    (generatedGeometricRootFiber S horizon fuel hfuel rho).card ≤
      2 ^ (20 * zeroSupportSurvivorScale d r (i + length)) := by
  calc
    (generatedGeometricRootFiber S horizon fuel hfuel rho).card ≤
        (assignmentsAgreeingRestriction rho).card :=
      Finset.card_le_card
        (generatedGeometricRootFiber_subset_agreeing S horizon fuel hfuel rho)
    _ = 2 ^ stars rho := card_assignments_agreeing_restriction rho
    _ = 2 ^ (20 * zeroSupportSurvivorScale d r (i + length)) := by
      rw [stars_eq_of_mem_generatedGeometricRootRestrictions hrho]

/-- The selected restrictions must cover the whole root cube, and no selected fiber is larger
than the scheduled endpoint cube.  Consequently the generated image satisfies the exact product
lower bound expected from a partition into endpoint-sized fibers. -/
theorem generatedGeometricRootRestrictions_product_lower_bound
    {d r level M i length : ℕ}
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i))
    (horizon : i + length ≤ d)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, i ≤ j → j < i + length →
      20 * zeroSupportSurvivorScale d r j ≤ fuel j) :
    2 ^ S.n ≤
      2 ^ (20 * zeroSupportSurvivorScale d r (i + length)) *
        (generatedGeometricRootRestrictions S horizon fuel hfuel).card := by
  classical
  let root : (Fin S.n → Bool) → Restriction S.n := fun x =>
    (S.selectedGeometricPath horizon fuel hfuel x).toSemanticPath.rootRestriction
  have hcard := Finset.card_le_mul_card_image
    (Finset.univ : Finset (Fin S.n → Bool))
    (2 ^ (20 * zeroSupportSurvivorScale d r (i + length)))
    (fun rho hrho => by
      have hrho' : rho ∈ generatedGeometricRootRestrictions S horizon fuel hfuel := by
        simpa [root, generatedGeometricRootRestrictions] using hrho
      simpa [root, generatedGeometricRootFiber] using
        card_generatedGeometricRootFiber_le S horizon fuel hfuel hrho')
  simpa [root, generatedGeometricRootRestrictions, Fintype.card_fin,
    Fintype.card_bool] using hcard

/-! ### Composing the genuine initial event with the zero-support geometric path -/

/-- The selected provenance-carrying geometric path after the genuine initial support-tail
successor.  Earlier APIs exposed only its folded ambient restriction; retaining the path also
exposes the terminal localized circuit and every semantic edge used to reach it. -/
noncomputable def selectedInitialGeometricPath
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (p : {p : Restriction n × (Fin n → Bool) //
      InitialGoodRootAssignmentPair C (zeroSupportSurvivorScale d r 0) p}) :
    ZeroSupportGeometricPath d r level (bottomSlotCount C * 3) 0 d
      (selectedInitialSupportTailSuccessor C hKfuel₀ hsupport (by
        simpa only [Nat.add_assoc] using hAlt) p).toInitialGeometricState := by
  let step := selectedInitialSupportTailSuccessor C hKfuel₀ hsupport (by
    simpa only [Nat.add_assoc] using hAlt) p
  let S := step.toInitialGeometricState
  let localX : Fin S.n → Bool := fun i ↦ p.1.2 (liveCoordEquiv step.restriction i)
  exact S.selectedGeometricPath (d := d) (r := r) (level := level)
    (M := bottomSlotCount C * 3) (i := 0) (length := d) (by omega) fuel (by
      intro j _hjlo hjhi
      exact hfuel j (by omega)) localX

/-- The terminal localized circuit on the selected path is semantically equivalent to the
original circuit under the full dependent-coordinate embedding.  This is the semantic payload
that was absent from the restriction-only endpoint image. -/
theorem selectedInitialGeometricPath_eval_eq
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (p : {p : Restriction n × (Fin n → Bool) //
      InitialGoodRootAssignmentPair C (zeroSupportSurvivorScale d r 0) p})
    (z : Fin (selectedInitialGeometricPath C hKfuel₀ hsupport hAlt fuel hfuel p).toSemanticPath.endpointN →
      Bool) :
    Layered.eval
        (selectedInitialGeometricPath C hKfuel₀ hsupport hAlt fuel hfuel p).toSemanticPath.endpointCircuit z =
      Layered.eval C
        (liftLiveAssignment
          (selectedInitialSupportTailSuccessor C hKfuel₀ hsupport (by
            simpa only [Nat.add_assoc] using hAlt) p).restriction
          ((selectedInitialGeometricPath C hKfuel₀ hsupport hAlt fuel hfuel p).toSemanticPath.liftAssignment z)) := by
  let step := selectedInitialSupportTailSuccessor C hKfuel₀ hsupport (by
    simpa only [Nat.add_assoc] using hAlt) p
  let path := selectedInitialGeometricPath C hKfuel₀ hsupport hAlt fuel hfuel p
  calc
    Layered.eval path.toSemanticPath.endpointCircuit z =
        Layered.eval step.circuit (path.toSemanticPath.liftAssignment z) :=
      path.eval_eq z
    _ = Layered.eval C
        (liftLiveAssignment step.restriction (path.toSemanticPath.liftAssignment z)) :=
      step.eval_eq _

/-- End-to-end localized parity cashout for a selected genuine initial successor.  At residual
level zero and positive terminal scale, the original circuit disagrees with ambient parity at an
assignment in the selected endpoint subcube.  The fixed bits introduced by the initial
restriction are accounted for by `fixedParityPhase`; the remaining dependent path is consumed by
its composed semantic equation. -/
theorem selectedInitialGeometricPath_exists_disagrees_parity
    {n fuel₀ d r : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (0 + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (p : {p : Restriction n × (Fin n → Bool) //
      InitialGoodRootAssignmentPair C (zeroSupportSurvivorScale d r 0) p})
    (hr : 0 < r) :
    ∃ x : Fin n → Bool, Layered.eval C x ≠ DTree.parity x := by
  let step := selectedInitialSupportTailSuccessor (k := 0 + d)
    C hKfuel₀ hsupport hAlt p
  let S := step.toInitialGeometricState
  let localX : Fin S.n → Bool := fun j ↦ p.1.2 (liveCoordEquiv step.restriction j)
  let path := S.selectedGeometricPath (d := d) (r := r) (level := 0)
    (M := bottomSlotCount C * 3) (i := 0) (length := d) (by omega) fuel (by
      intro j _hjlo hjhi
      exact hfuel j (by omega)) localX
  have hR : 0 < zeroSupportSurvivorScale d r (0 + d) := by
    simpa [zeroSupportSurvivorScale] using hr
  obtain ⟨z, hz⟩ := path.exists_semantic_endpoint_disagrees_parity_xor hR
    (xor path.toSemanticPath.parityPhase (fixedParityPhase step.restriction))
  let x := liftLiveAssignment step.restriction (path.toSemanticPath.liftAssignment z)
  refine ⟨x, ?_⟩
  intro heq
  apply hz
  calc
    Layered.eval path.toSemanticPath.endpointCircuit z =
        Layered.eval step.circuit (path.toSemanticPath.liftAssignment z) := path.eval_eq z
    _ = Layered.eval C x := by
      simpa [x] using step.eval_eq (path.toSemanticPath.liftAssignment z)
    _ = DTree.parity x := heq
    _ = xor (DTree.parity (path.toSemanticPath.liftAssignment z))
          (fixedParityPhase step.restriction) :=
      by simpa [x] using
        parity_liftLiveAssignment step.restriction (path.toSemanticPath.liftAssignment z)
    _ = xor (xor (DTree.parity z) path.toSemanticPath.parityPhase)
          (fixedParityPhase step.restriction) := by
      rw [path.toSemanticPath.parity_liftAssignment]
    _ = xor (DTree.parity z)
          (xor path.toSemanticPath.parityPhase (fixedParityPhase step.restriction)) :=
      Bool.xor_assoc _ _ _

/-- Select the full ambient endpoint obtained by entering the zero-support iterator through the
genuine initial support-tail successor.  The initial scale is written as
`zeroSupportSurvivorScale d r 0`, so the successor state feeds the geometric schedule without an
index cast. -/
noncomputable def selectedInitialGeometricEndpointRestriction
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (p : {p : Restriction n × (Fin n → Bool) //
      InitialGoodRootAssignmentPair C (zeroSupportSurvivorScale d r 0) p}) :
    Restriction n := by
  let step := selectedInitialSupportTailSuccessor C hKfuel₀ hsupport (by
    simpa only [Nat.add_assoc] using hAlt) p
  let S := step.toInitialGeometricState
  let localX : Fin S.n → Bool := fun i ↦ p.1.2 (liveCoordEquiv step.restriction i)
  let path := S.selectedGeometricPath (d := d) (r := r) (level := level)
    (M := bottomSlotCount C * 3) (i := 0) (length := d) (by omega) fuel (by
    intro j _hjlo hjhi
    exact hfuel j (by omega)) localX
  exact liftLiveRestriction step.restriction path.toSemanticPath.rootRestriction

/-- The composed endpoint retains the scheduled final number of live coordinates. -/
theorem stars_selectedInitialGeometricEndpointRestriction
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (p : {p : Restriction n × (Fin n → Bool) //
      InitialGoodRootAssignmentPair C (zeroSupportSurvivorScale d r 0) p}) :
    stars (selectedInitialGeometricEndpointRestriction C hKfuel₀ hsupport hAlt fuel hfuel p) =
      20 * r := by
  simp only [selectedInitialGeometricEndpointRestriction, stars_liftLiveRestriction]
  rw [LocalizedSemanticPath.stars_rootRestriction]
  simpa using (ZeroSupportGeometricPath.semantic_endpointN
    (S := (selectedInitialSupportTailSuccessor C hKfuel₀ hsupport (by
      simpa only [Nat.add_assoc] using hAlt) p).toInitialGeometricState)
    ((selectedInitialSupportTailSuccessor C hKfuel₀ hsupport (by
      simpa only [Nat.add_assoc] using hAlt) p).toInitialGeometricState.selectedGeometricPath
      (d := d) (r := r) (level := level) (M := bottomSlotCount C * 3)
      (i := 0) (length := d) (by omega) fuel (by
        intro j _hjlo hjhi
        exact hfuel j (by omega))
      (fun i ↦ p.1.2 (liveCoordEquiv
        (selectedInitialSupportTailSuccessor C hKfuel₀ hsupport (by
          simpa only [Nat.add_assoc] using hAlt) p).restriction i))))

/-- The original assignment selecting the good initial successor also extends the fully composed
ambient endpoint.  This is the cross-boundary provenance statement used by the direct fiber
count. -/
theorem selectedInitialGeometricEndpointRestriction_assignment
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (p : {p : Restriction n × (Fin n → Bool) //
      InitialGoodRootAssignmentPair C (zeroSupportSurvivorScale d r 0) p}) :
    Rung4Restriction.Extends
      (selectedInitialGeometricEndpointRestriction C hKfuel₀ hsupport hAlt fuel hfuel p)
      p.1.2 := by
  let step := selectedInitialSupportTailSuccessor C hKfuel₀ hsupport (by
    simpa only [Nat.add_assoc] using hAlt) p
  let S := step.toInitialGeometricState
  let localX : Fin S.n → Bool := fun i ↦ p.1.2 (liveCoordEquiv step.restriction i)
  let path := S.selectedGeometricPath (d := d) (r := r) (level := level)
    (M := bottomSlotCount C * 3) (i := 0) (length := d) (by omega) fuel (by
    intro j _hjlo hjhi
    exact hfuel j (by omega)) localX
  change DTree.agreeRestriction
    (liftLiveRestriction step.restriction path.toSemanticPath.rootRestriction) p.1.2
  rw [agreeRestriction_liftLiveRestriction_iff]
  refine ⟨step.restriction_assignment, ?_⟩
  exact S.selectedGeometricPath_rootRestriction_agrees (d := d) (r := r)
    (level := level) (M := bottomSlotCount C * 3) (i := 0) (length := d)
    (by omega) fuel (by
      intro j _hjlo hjhi
      exact hfuel j (by omega)) localX

/-- The original `40R` shell root coarsens the fully composed endpoint. -/
theorem selectedInitialGeometricEndpointRestriction_root_extends
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (p : {p : Restriction n × (Fin n → Bool) //
      InitialGoodRootAssignmentPair C (zeroSupportSurvivorScale d r 0) p}) :
    RestrictionExtends p.1.1
      (selectedInitialGeometricEndpointRestriction C hKfuel₀ hsupport hAlt fuel hfuel p) := by
  let step := selectedInitialSupportTailSuccessor C hKfuel₀ hsupport (by
    simpa only [Nat.add_assoc] using hAlt) p
  let S := step.toInitialGeometricState
  let localX : Fin S.n → Bool := fun i ↦ p.1.2 (liveCoordEquiv step.restriction i)
  let path := S.selectedGeometricPath (d := d) (r := r) (level := level)
    (M := bottomSlotCount C * 3) (i := 0) (length := d) (by omega) fuel (by
      intro j _hjlo hjhi
      exact hfuel j (by omega)) localX
  change RestrictionExtends p.1.1
    (liftLiveRestriction step.restriction path.toSemanticPath.rootRestriction)
  intro v b hv
  exact liftLiveRestriction_extends step.restriction _ v b (step.root_extends v b hv)

/-- Distinct final ambient restrictions selected after the genuine initial event and `d`
zero-support rounds. -/
noncomputable def initialGeometricEndpointImage
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j) :
    Finset (Restriction n) := by
  classical
  exact Finset.univ.image fun p =>
    selectedInitialGeometricEndpointRestriction C hKfuel₀ hsupport hAlt fuel hfuel p

/-- Every member of the selected full-path image lies on the scheduled terminal shell. -/
theorem stars_eq_of_mem_initialGeometricEndpointImage
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    {rho : Restriction n}
    (hrho : rho ∈ initialGeometricEndpointImage C hKfuel₀ hsupport hAlt fuel hfuel) :
    stars rho = 20 * r := by
  classical
  rw [initialGeometricEndpointImage, Finset.mem_image] at hrho
  obtain ⟨p, _hp, rfl⟩ := hrho
  exact stars_selectedInitialGeometricEndpointRestriction
    C hKfuel₀ hsupport hAlt fuel hfuel p

/-- Full initial-domain fiber over one composed final endpoint. -/
noncomputable def initialGeometricEndpointFiber
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (rho : Restriction n) :
    Finset {p : Restriction n × (Fin n → Bool) //
      InitialGoodRootAssignmentPair C (zeroSupportSurvivorScale d r 0) p} := by
  classical
  exact Finset.univ.filter fun p =>
    selectedInitialGeometricEndpointRestriction C hKfuel₀ hsupport hAlt fuel hfuel p = rho

/-- Direct cross-boundary fiber bound.  A fixed final endpoint determines an extension cube;
every preimage contributes a distinct original `40R` root coarsening that endpoint and a distinct
assignment agreeing with it.  No product of intermediate-round collision caps is needed. -/
theorem card_initialGeometricEndpointFiber_le_product
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (rho : Restriction n) :
    (initialGeometricEndpointFiber C hKfuel₀ hsupport hAlt fuel hfuel rho).card ≤
      (restrictionCoarseningShellFiber
        (K := 20 * (2 * zeroSupportSurvivorScale d r 0)) rho).card *
        (assignmentsAgreeingRestriction rho).card := by
  classical
  let target :=
    (restrictionCoarseningShellFiber
      (K := 20 * (2 * zeroSupportSurvivorScale d r 0)) rho).product
      (assignmentsAgreeingRestriction rho)
  let forgetPair :
      {p : Restriction n × (Fin n → Bool) //
        InitialGoodRootAssignmentPair C (zeroSupportSurvivorScale d r 0) p} →
        Restriction n × (Fin n → Bool) := fun p ↦ p.1
  have hinj : Function.Injective forgetPair := by
    intro p q hpq
    exact Subtype.ext hpq
  have hsubset :
      (initialGeometricEndpointFiber C hKfuel₀ hsupport hAlt fuel hfuel rho).image
          forgetPair ⊆ target := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hpFiber := (Finset.mem_filter.mp hp).2
    change p.1 ∈ target
    apply Finset.mem_product.mpr
    constructor
    · rw [restrictionCoarseningShellFiber, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, p.2.1⟩
      rw [← hpFiber]
      exact selectedInitialGeometricEndpointRestriction_root_extends
        C hKfuel₀ hsupport hAlt fuel hfuel p
    · rw [assignmentsAgreeingRestriction, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hpFiber]
      exact selectedInitialGeometricEndpointRestriction_assignment
        C hKfuel₀ hsupport hAlt fuel hfuel p
  calc
    (initialGeometricEndpointFiber C hKfuel₀ hsupport hAlt fuel hfuel rho).card =
        ((initialGeometricEndpointFiber C hKfuel₀ hsupport hAlt fuel hfuel rho).image
          forgetPair).card := by
            symm
            exact Finset.card_image_of_injective _ hinj
    _ ≤ target.card := Finset.card_le_card hsubset
    _ = (restrictionCoarseningShellFiber
          (K := 20 * (2 * zeroSupportSurvivorScale d r 0)) rho).card *
        (assignmentsAgreeingRestriction rho).card := by simp [target]

/-- Numerical form of the complete initial-to-final fiber ceiling. -/
theorem card_initialGeometricEndpointFiber_le
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j)
    (rho : Restriction n) (hrho : stars rho = 20 * r) :
    (initialGeometricEndpointFiber C hKfuel₀ hsupport hAlt fuel hfuel rho).card ≤
      Nat.choose (n - 20 * r)
          (20 * (2 * zeroSupportSurvivorScale d r 0) - 20 * r) *
        2 ^ (20 * r) := by
  calc
    (initialGeometricEndpointFiber C hKfuel₀ hsupport hAlt fuel hfuel rho).card ≤
        (restrictionCoarseningShellFiber
          (K := 20 * (2 * zeroSupportSurvivorScale d r 0)) rho).card *
          (assignmentsAgreeingRestriction rho).card :=
      card_initialGeometricEndpointFiber_le_product
        C hKfuel₀ hsupport hAlt fuel hfuel rho
    _ ≤ Nat.choose (n - 20 * r)
          (20 * (2 * zeroSupportSurvivorScale d r 0) - 20 * r) *
        2 ^ (20 * r) := by
      rw [card_assignments_agreeing_restriction, hrho]
      exact Nat.mul_le_mul_right _ (by
        simpa only [hrho] using
          (card_restrictionCoarseningShellFiber_le_choose
            (K := 20 * (2 * zeroSupportSurvivorScale d r 0)) rho))

/-- The exact initial good domain and the direct composed fiber cap give a distinct-final-endpoint
lower bound after all `d` zero-support rounds. -/
theorem initialGoodRoots_mul_assignments_le_geometricEndpointImage
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j) :
    (initialGoodRoots C (zeroSupportSurvivorScale d r 0)).card *
        2 ^ (20 * (2 * zeroSupportSurvivorScale d r 0)) ≤
      (Nat.choose (n - 20 * r)
          (20 * (2 * zeroSupportSurvivorScale d r 0) - 20 * r) * 2 ^ (20 * r)) *
        (initialGeometricEndpointImage C hKfuel₀ hsupport hAlt fuel hfuel).card := by
  classical
  let domain := initialGoodRootAssignmentPairDomain C (zeroSupportSurvivorScale d r 0)
  let endpoint :
      {p : Restriction n × (Fin n → Bool) //
        InitialGoodRootAssignmentPair C (zeroSupportSurvivorScale d r 0) p} →
        Restriction n := fun p ↦
      selectedInitialGeometricEndpointRestriction C hKfuel₀ hsupport hAlt fuel hfuel p
  let cap := Nat.choose (n - 20 * r)
    (20 * (2 * zeroSupportSurvivorScale d r 0) - 20 * r) * 2 ^ (20 * r)
  have hfibers : ∀ rho ∈ domain.image endpoint,
      (domain.filter fun p ↦ endpoint p = rho).card ≤ cap := by
    intro rho hrho
    obtain ⟨p, _hp, hpEndpoint⟩ := Finset.mem_image.mp hrho
    have hstars : stars rho = 20 * r := by
      rw [← hpEndpoint]
      exact stars_selectedInitialGeometricEndpointRestriction
        C hKfuel₀ hsupport hAlt fuel hfuel p
    simpa [domain, endpoint, initialGoodRootAssignmentPairDomain,
      initialGeometricEndpointFiber, cap] using
      card_initialGeometricEndpointFiber_le
        C hKfuel₀ hsupport hAlt fuel hfuel rho hstars
  have hcount := Finset.card_le_mul_card_image domain cap hfibers
  calc
    (initialGoodRoots C (zeroSupportSurvivorScale d r 0)).card *
        2 ^ (20 * (2 * zeroSupportSurvivorScale d r 0)) = domain.card := by
      symm
      exact card_initialGoodRootAssignmentPairDomain C (zeroSupportSurvivorScale d r 0)
    _ ≤ cap * (domain.image endpoint).card := hcount
    _ = (Nat.choose (n - 20 * r)
          (20 * (2 * zeroSupportSurvivorScale d r 0) - 20 * r) * 2 ^ (20 * r)) *
        (initialGeometricEndpointImage C hKfuel₀ hsupport hAlt fuel hfuel).card := by
      simp [cap, domain, endpoint, initialGoodRootAssignmentPairDomain,
        initialGeometricEndpointImage]

/-- Final composition with the genuine support-tail contraction.  The only collision loss across
the complete initial-plus-geometric path is the direct root-coarsening binomial and the terminal
`20r` assignment cube. -/
theorem initialRootShell_mul_assignments_le_two_mul_geometricEndpointImage
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hr : 0 < r)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j) :
    (initialRootShell n (zeroSupportSurvivorScale d r 0)).card *
        2 ^ (20 * (2 * zeroSupportSurvivorScale d r 0)) ≤
      2 * (Nat.choose (n - 20 * r)
          (20 * (2 * zeroSupportSurvivorScale d r 0) - 20 * r) * 2 ^ (20 * r)) *
        (initialGeometricEndpointImage C hKfuel₀ hsupport hAlt fuel hfuel).card := by
  have hscale : 0 < zeroSupportSurvivorScale d r 0 :=
    zeroSupportSurvivorScale_pos d r 0 hr
  have hhalf := initialRootShell_card_le_two_mul_good
    C (zeroSupportSurvivorScale d r 0) hscale hsupport
  have himage := initialGoodRoots_mul_assignments_le_geometricEndpointImage
    C hKfuel₀ hsupport hAlt fuel hfuel
  calc
    (initialRootShell n (zeroSupportSurvivorScale d r 0)).card *
        2 ^ (20 * (2 * zeroSupportSurvivorScale d r 0)) ≤
      (2 * (initialGoodRoots C (zeroSupportSurvivorScale d r 0)).card) *
        2 ^ (20 * (2 * zeroSupportSurvivorScale d r 0)) :=
          Nat.mul_le_mul_right _ hhalf
    _ = 2 * ((initialGoodRoots C (zeroSupportSurvivorScale d r 0)).card *
        2 ^ (20 * (2 * zeroSupportSurvivorScale d r 0))) := by ring
    _ ≤ 2 * ((Nat.choose (n - 20 * r)
          (20 * (2 * zeroSupportSurvivorScale d r 0) - 20 * r) * 2 ^ (20 * r)) *
        (initialGeometricEndpointImage C hKfuel₀ hsupport hAlt fuel hfuel).card) :=
      Nat.mul_le_mul_left _ himage
    _ = 2 * (Nat.choose (n - 20 * r)
          (20 * (2 * zeroSupportSurvivorScale d r 0) - 20 * r) * 2 ^ (20 * r)) *
        (initialGeometricEndpointImage C hKfuel₀ hsupport hAlt fuel hfuel).card := by ring

/-- Exact shell normalization for a coarsening-fiber image bound.  Once the `K`-star source
shell, its assignment cube, and the direct `K -> L` coarsening cap are all expanded, the ambient
binomial and Boolean factors cancel.  The only remaining density loss inside the `L`-star shell
is `2 * choose K L`.

The explicit hypotheses `L ≤ K ≤ n` are essential: without them the source shell may be empty,
and natural-number subtraction would not describe an actual shell transition. -/
theorem terminalShell_card_le_two_mul_choose_mul_of_source_bound
    {n K L imageCard : ℕ} (hLK : L ≤ K) (hKn : K ≤ n)
    (hbound :
      (Finset.univ.filter fun sigma : Restriction n => stars sigma = K).card * 2 ^ K ≤
        2 * (Nat.choose (n - L) (K - L) * 2 ^ L) * imageCard) :
    (Finset.univ.filter fun rho : Restriction n => stars rho = L).card ≤
      2 * Nat.choose K L * imageCard := by
  have hchoose :
      Nat.choose n L * Nat.choose (n - L) (K - L) =
        Nat.choose n K * Nat.choose K L := by
    have hmul := Nat.choose_mul (n := n) (k := K) (s := L) hLK
    simpa [Nat.mul_comm] using hmul.symm
  have hnsub : (n - K) + K = n := by omega
  have hnsubL : (n - L) + L = n := by omega
  rw [card_stars_eq n K] at hbound
  rw [card_stars_eq n L]
  have hpowK : 2 ^ (n - K) * 2 ^ K = 2 ^ n := by
    rw [← pow_add, hnsub]
  have hpowL : 2 ^ (n - L) * 2 ^ L = 2 ^ n := by
    rw [← pow_add, hnsubL]
  have hbound' : Nat.choose K L * (Nat.choose n K * 2 ^ n) ≤
      Nat.choose K L * (2 * (Nat.choose (n - L) (K - L) * 2 ^ L) * imageCard) := by
    apply Nat.mul_le_mul_left
    simpa only [mul_assoc, hpowK] using hbound
  have hmult : 0 < Nat.choose (n - L) (K - L) * 2 ^ L := by
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (pow_pos (by omega) L)
  apply Nat.le_of_mul_le_mul_left (c := Nat.choose (n - L) (K - L) * 2 ^ L)
    (hc := hmult)
  calc
    (Nat.choose (n - L) (K - L) * 2 ^ L) *
          (Nat.choose n L * 2 ^ (n - L)) =
        Nat.choose K L * (Nat.choose n K * 2 ^ n) := by
          calc
            _ = (Nat.choose n L * Nat.choose (n - L) (K - L)) *
                  (2 ^ (n - L) * 2 ^ L) := by ring
            _ = (Nat.choose n K * Nat.choose K L) * 2 ^ n := by
              rw [hchoose, hpowL]
            _ = _ := by ring
    _ ≤ Nat.choose K L *
          (2 * (Nat.choose (n - L) (K - L) * 2 ^ L) * imageCard) := hbound'
    _ = (Nat.choose (n - L) (K - L) * 2 ^ L) *
          (2 * Nat.choose K L * imageCard) := by ring

/-- Normalized full-path endpoint density.  Relative to the exact terminal `20r` shell, the
currently verified construction loses precisely the root-coarsening factor
`choose (40 * 2^d * r) (20r)` and the genuine good-root factor two; all ambient-`n` binomials and
Boolean assignment cubes cancel. -/
theorem terminalRootShell_card_le_two_mul_choose_mul_geometricEndpointImage
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hr : 0 < r)
    (hKambient : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j) :
    (Finset.univ.filter fun rho : Restriction n => stars rho = 20 * r).card ≤
      2 * Nat.choose (20 * (2 * zeroSupportSurvivorScale d r 0)) (20 * r) *
        (initialGeometricEndpointImage C hKfuel₀ hsupport hAlt fuel hfuel).card := by
  have hrscale : r ≤ zeroSupportSurvivorScale d r 0 := by
    rw [zeroSupportSurvivorScale_zero]
    exact Nat.le_mul_of_pos_left r (pow_pos (by omega) d)
  apply terminalShell_card_le_two_mul_choose_mul_of_source_bound
    (K := 20 * (2 * zeroSupportSurvivorScale d r 0))
    (L := 20 * r) (imageCard :=
      (initialGeometricEndpointImage C hKfuel₀ hsupport hAlt fuel hfuel).card)
  · omega
  · exact hKambient
  · simpa only [initialRootShell] using
      initialRootShell_mul_assignments_le_two_mul_geometricEndpointImage
        C hr hKfuel₀ hsupport hAlt fuel hfuel

/-- The normalized density estimate is more than is needed for bare endpoint existence.  Whenever
the initial shell fits the ambient cube, it supplies an actual selected endpoint with exactly
`20r` survivors, despite the nonuniform cross-root binomial loss. -/
theorem exists_mem_initialGeometricEndpointImage
    {n fuel₀ d r level : ℕ} (C : Layered n)
    (hr : 0 < r)
    (hKambient : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (level + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j) :
    ∃ rho ∈ initialGeometricEndpointImage C hKfuel₀ hsupport hAlt fuel hfuel,
      stars rho = 20 * r := by
  have hrscale : r ≤ zeroSupportSurvivorScale d r 0 := by
    rw [zeroSupportSurvivorScale_zero]
    exact Nat.le_mul_of_pos_left r (pow_pos (by omega) d)
  have hterminalAmbient : 20 * r ≤ n := by omega
  have hshellPos : 0 <
      (Finset.univ.filter fun rho : Restriction n => stars rho = 20 * r).card := by
    rw [card_stars_eq n (20 * r)]
    exact Nat.mul_pos (Nat.choose_pos hterminalAmbient) (pow_pos (by omega) (n - 20 * r))
  have hbound := terminalRootShell_card_le_two_mul_choose_mul_geometricEndpointImage
    C hr hKambient hKfuel₀ hsupport hAlt fuel hfuel
  have himagePos : 0 <
      (initialGeometricEndpointImage C hKfuel₀ hsupport hAlt fuel hfuel).card := by
    by_contra hnot
    have hzero :
        (initialGeometricEndpointImage C hKfuel₀ hsupport hAlt fuel hfuel).card = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hbound
    simp only [mul_zero] at hbound
    omega
  obtain ⟨rho, hrho⟩ := Finset.card_pos.mp himagePos
  exact ⟨rho, hrho,
    stars_eq_of_mem_initialGeometricEndpointImage
      C hKfuel₀ hsupport hAlt fuel hfuel hrho⟩

/-- End-to-end parity contradiction under the audited geometric-shell hypotheses.  Endpoint-image
existence supplies a preimage in the genuine initial good-pair domain; the localized terminal
cashout for that selected preimage then produces an ambient disagreement witness. -/
theorem zeroSupportGeometric_exists_disagrees_parity
    {n fuel₀ d r : ℕ} (C : Layered n)
    (hr : 0 < r)
    (hKambient : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ n)
    (hKfuel₀ : 20 * (2 * zeroSupportSurvivorScale d r 0) ≤ fuel₀)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hAlt : AltO (0 + d + 3) C)
    (fuel : ℕ → ℕ)
    (hfuel : ∀ j, j < d → 20 * zeroSupportSurvivorScale d r j ≤ fuel j) :
    ∃ x : Fin n → Bool, Layered.eval C x ≠ DTree.parity x := by
  classical
  obtain ⟨rho, hrho, _hstars⟩ := exists_mem_initialGeometricEndpointImage
    C hr hKambient hKfuel₀ hsupport hAlt fuel hfuel
  rw [initialGeometricEndpointImage, Finset.mem_image] at hrho
  obtain ⟨p, _hp, _hrho⟩ := hrho
  exact selectedInitialGeometricPath_exists_disagrees_parity
    C hKfuel₀ hsupport hAlt fuel hfuel p hr

/-! ### Applicability audit for the sparse-support hypothesis -/

/-- If the syntactic bottom support omits even one ambient coordinate, the whole layered circuit
is blind to a flip of that coordinate and therefore cannot compute parity.  This is independent of
switching, depth, width, fuel, or shell parameters. -/
theorem exists_disagrees_parity_of_bottomSupport_card_lt
    {n : ℕ} (C : Layered n)
    (hcard : (layeredBottomVariableSupport C).card < n) :
    ∃ x : Fin n → Bool, Layered.eval C x ≠ DTree.parity x := by
  classical
  have hmissing : ∃ j : Fin n, j ∉ layeredBottomVariableSupport C := by
    by_contra hnot
    push_neg at hnot
    have hall : layeredBottomVariableSupport C = Finset.univ :=
      Finset.eq_univ_of_forall hnot
    rw [hall] at hcard
    simpa using hcard
  obtain ⟨j, hj⟩ := hmissing
  let x : Fin n → Bool := fun _ => false
  let y : Fin n → Bool := Function.update x j (!x j)
  have hagree : ∀ v ∈ layeredBottomVariableSupport C, x v = y v := by
    intro v hv
    have hvj : v ≠ j := by
      intro h
      subst v
      exact hj hv
    simp [y, hvj]
  have heval : Layered.eval C x = Layered.eval C y :=
    MultiSwitching.Layered.eval_eq_of_agree_on_bottomSupport C hagree
  have hparity : DTree.parity y = !DTree.parity x := by
    exact DTree.parity_flip x j
  by_cases hx : Layered.eval C x = DTree.parity x
  · refine ⟨y, ?_⟩
    intro hy
    have hcontra : DTree.parity x = !DTree.parity x := by
      calc
        DTree.parity x = Layered.eval C x := hx.symm
        _ = Layered.eval C y := heval
        _ = DTree.parity y := hy
        _ = !DTree.parity x := hparity
    cases hpx : DTree.parity x <;> simp [hpx] at hcontra
  · exact ⟨x, hx⟩

/-- The exact density premise used by the geometric capstone is already a direct parity
obstruction whenever the ambient cube is nonempty.  Consequently this sparse-support regime
cannot contain a circuit that computes parity on all inputs; reaching a nontrivial parity lower
bound requires replacing the initial support-tail hypothesis for dense-support circuits. -/
theorem sparseSupport16_exists_disagrees_parity
    {n : ℕ} (C : Layered n) (hn : 0 < n)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n) :
    ∃ x : Fin n → Bool, Layered.eval C x ≠ DTree.parity x := by
  apply exists_disagrees_parity_of_bottomSupport_card_lt C
  omega

/-- The finite image of every *structurally admissible* scheduled path under composed ambient
restriction.  This deliberately does not claim constructor provenance: the current
`exists_geometric_path` interface proves inhabitation but does not record which inhabitants arise
from its fixed branch choices. -/
noncomputable def admissibleGeometricRootRestrictions
    {d r level M i length : ℕ}
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i)) : Finset (Restriction S.n) := by
  classical
  exact Finset.univ.filter fun rho =>
    ∃ path : ZeroSupportGeometricPath d r level M i length S,
      path.toSemanticPath.rootRestriction = rho

@[simp] theorem mem_admissibleGeometricRootRestrictions_iff
    {d r level M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i)}
    {rho : Restriction S.n} :
    rho ∈ admissibleGeometricRootRestrictions S ↔
      ∃ path : ZeroSupportGeometricPath d r level M i length S,
        path.toSemanticPath.rootRestriction = rho := by
  classical
  rw [admissibleGeometricRootRestrictions, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- Every restriction in the admissible image has exactly the common scheduled endpoint
dimension. -/
theorem stars_eq_of_mem_admissibleGeometricRootRestrictions
    {d r level M i length : ℕ}
    {S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i)}
    {rho : Restriction S.n}
    (hrho : rho ∈ admissibleGeometricRootRestrictions S) :
    stars rho = 20 * zeroSupportSurvivorScale d r (i + length) := by
  obtain ⟨path, rfl⟩ := mem_admissibleGeometricRootRestrictions_iff.mp hrho
  rw [LocalizedSemanticPath.stars_rootRestriction]
  exact path.semantic_endpointN

/-- The compatible portion of the admissible root-restriction image.  Keeping its classical
decidability inside a noncomputable definition avoids imposing a spurious decidability premise on
the counting theorem. -/
noncomputable def admissibleGeometricRootRestrictionsAgreeing
    {d r level M i length : ℕ}
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i))
    (x : Fin S.n → Bool) : Finset (Restriction S.n) := by
  classical
  exact (admissibleGeometricRootRestrictions S).filter fun rho =>
    DTree.agreeRestriction rho x

/-- Filtering the finite admissible image by one root assignment has degree at most the exact
ambient binomial ceiling.  This packages the strongest compatibility estimate justified by the
current path interface; an improvement must use constructor provenance or an additional retained
label. -/
theorem card_admissibleGeometricRootRestrictions_agreeing_le_choose
    {d r level M i length : ℕ}
    (S : ZeroSupportLocalizedState (zeroSupportSurvivorScale d r i)
      (level + length) (M * 3 ^ i))
    (x : Fin S.n → Bool) :
    (admissibleGeometricRootRestrictionsAgreeing S x).card ≤
        S.n.choose (20 * zeroSupportSurvivorScale d r (i + length)) := by
  classical
  let roots := admissibleGeometricRootRestrictionsAgreeing S x
  have h := card_distinct_agreeing_restriction_family_le_choose
    (K := 20 * zeroSupportSurvivorScale d r (i + length))
    (I := {rho : Restriction S.n // rho ∈ roots}) x Subtype.val
    Subtype.val_injective
    (fun rho => by
      have hrho : rho.1 ∈ admissibleGeometricRootRestrictions S ∧
          DTree.agreeRestriction rho.1 x := by
        have hrho' : rho.1 ∈ admissibleGeometricRootRestrictionsAgreeing S x := by
          simpa only [roots] using rho.2
        rw [admissibleGeometricRootRestrictionsAgreeing, Finset.mem_filter] at hrho'
        exact hrho'
      exact stars_eq_of_mem_admissibleGeometricRootRestrictions hrho.1)
    (fun rho => by
      have hrho : rho.1 ∈ admissibleGeometricRootRestrictions S ∧
          DTree.agreeRestriction rho.1 x := by
        have hrho' : rho.1 ∈ admissibleGeometricRootRestrictionsAgreeing S x := by
          simpa only [roots] using rho.2
        rw [admissibleGeometricRootRestrictionsAgreeing, Finset.mem_filter] at hrho'
        exact hrho'
      exact hrho.2)
  simpa [roots, Nat.card_eq_fintype_card] using h

/-! ### Exact-subcube round packaged on the next coordinate type -/

/-- One actual-margin survivor round, with the reached collapse immediately transported to the
exact `10 * R`-coordinate cube.  The witness records the four interfaces consumed by another
round: evaluation, depth, bottom width, and bottom-slot count. -/
theorem actualMargin_normalizedSurvivorRound_localized
    {n fuel R residualDepth : ℕ} {C : Layered n}
    (hKfuel : 20 * R ≤ fuel)
    (hne : NonEmptyGates C)
    (hexact :
      (commonShallowBad (normalizedLayeredBottomFamily C) fuel (20 * R) (10 * R)
          residualDepth).card * 2 ^ (10 * R) ≤
          (Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * R).card ∧
        ∀ σ : Restriction n,
          stars σ = 20 * R →
          σ ∉ commonShallowBad (normalizedLayeredBottomFamily C) fuel
            (20 * R) (10 * R) residualDepth →
          ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x →
            ∃ trunk : CommonTree n (Restriction n),
              CommonTree.depth trunk ≤ 10 * R ∧
              let τ := CommonTree.run trunk x
              ∃ κ : Restriction n,
                RestrictionExtends τ κ ∧
                stars κ = 10 * R ∧
                stars κ ≤ fuel ∧
                Layered.EquivOn κ C (collapseRound fuel τ C) ∧
                bottomSlotCount (collapseRound fuel τ C) ≤
                  bottomSlotCount C * (2 ^ (residualDepth + 1) + 1)) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel (20 * R) (10 * R)
        residualDepth).card * 2 ^ (10 * R) ≤
        (Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * R).card ∧
      ∀ σ : Restriction n,
        stars σ = 20 * R →
        σ ∉ commonShallowBad (normalizedLayeredBottomFamily C) fuel
          (20 * R) (10 * R) residualDepth →
        ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x →
          ∃ trunk : CommonTree n (Restriction n),
            CommonTree.depth trunk ≤ 10 * R ∧
            let τ := CommonTree.run trunk x
            ∃ κ : Restriction n,
              RestrictionExtends τ κ ∧
              stars κ = 10 * R ∧
              stars κ ≤ fuel ∧
              let D := localizeLiveLayered κ (collapseRound fuel τ C)
              (∀ z : Fin (stars κ) → Bool,
                Layered.eval D z = Layered.eval C (liftLiveAssignment κ z)) ∧
              Layered.depth D = Layered.depth (collapseRound fuel τ C) ∧
              BottomWidth (residualDepth + 1) D ∧
              bottomSlotCount D ≤
                bottomSlotCount C * (2 ^ (residualDepth + 1) + 1) := by
  obtain ⟨hbad, _⟩ := hexact
  refine ⟨hbad, ?_⟩
  intro σ hstars hgood x hx
  have hcommon : CommonShallowAt (normalizedLayeredBottomFamily C) fuel σ
      (10 * R) residualDepth := by
    by_contra hnot
    apply hgood
    rw [mem_commonShallowBad]
    exact ⟨hstars, hnot⟩
  have hfuel : stars σ ≤ fuel := by
    rw [hstars]
    exact hKfuel
  obtain ⟨trunk, hdepth, hlower, hleafStars, hshallow⟩ :=
    hcommon.leaf_shallows (normalizedLayeredBottomFamily_covers C) x hx
  have hlive : 10 * R ≤ stars (CommonTree.run trunk x) := by
    rw [hstars] at hlower
    omega
  obtain ⟨κ, hext, hκstars⟩ :=
    exists_restrictionExtends_stars_eq (CommonTree.run trunk x) hlive
  have hleafFuel : stars (CommonTree.run trunk x) ≤ fuel := hleafStars.trans hfuel
  have hκfuel : stars κ ≤ fuel := (stars_le_of_restrictionExtends hext).trans hleafFuel
  have hequiv : Layered.EquivOn κ C (collapseRound fuel (CommonTree.run trunk x) C) := by
    intro y hy
    exact collapseRound_EquivOn fuel hleafFuel C y
      (fun i b hi => hy i b (hext i b hi))
  have hwidth : BottomWidth (residualDepth + 1)
      (collapseRound fuel (CommonTree.run trunk x) C) :=
    collapseRound_BottomWidth fuel (CommonTree.run trunk x) hshallow
  have hslots : bottomSlotCount (collapseRound fuel (CommonTree.run trunk x) C) ≤
      bottomSlotCount C * (2 ^ (residualDepth + 1) + 1) :=
    collapseRound_bottomSlotCount_le hne hshallow
  refine ⟨trunk, hdepth, κ, hext, hκstars, hκfuel, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [localizeLiveLayered_eval]
    exact (hequiv (liftLiveAssignment κ z) (liftLiveAssignment_agrees κ z)).symm
  · exact localizeLiveLayered_depth κ _
  · exact localizeLiveLayered_BottomWidth κ _ hwidth
  · exact (localizeLiveLayered_bottomSlotCount_le κ _).trans hslots

/-- Fully localized survivor round whose density premise counts distinct variables in the
unpolarized bottom support rather than clause slots.  This is the interface needed by circuits
with a large syntactic bottom layer but strongly overlapping variable support. -/
theorem supportDensity_normalizedSurvivorRound_localized
    {n fuel R residualDepth : ℕ} {C : Layered n}
    (hKfuel : 20 * R ≤ fuel)
    (hsupport : 16 * (layeredBottomVariableSupport C).card ≤ n)
    (hne : NonEmptyGates C) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel (20 * R) (10 * R)
        residualDepth).card * 2 ^ (10 * R) ≤
        (Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * R).card ∧
      ∀ σ : Restriction n,
        stars σ = 20 * R →
        σ ∉ commonShallowBad (normalizedLayeredBottomFamily C) fuel
          (20 * R) (10 * R) residualDepth →
        ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x →
          ∃ trunk : CommonTree n (Restriction n),
            CommonTree.depth trunk ≤ 10 * R ∧
            let τ := CommonTree.run trunk x
            ∃ κ : Restriction n,
              RestrictionExtends τ κ ∧
              stars κ = 10 * R ∧
              stars κ ≤ fuel ∧
              let D := localizeLiveLayered κ (collapseRound fuel τ C)
              (∀ z : Fin (stars κ) → Bool,
                Layered.eval D z = Layered.eval C (liftLiveAssignment κ z)) ∧
              Layered.depth D = Layered.depth (collapseRound fuel τ C) ∧
              BottomWidth (residualDepth + 1) D ∧
              bottomSlotCount D ≤
                bottomSlotCount C * (2 ^ (residualDepth + 1) + 1) := by
  exact actualMargin_normalizedSurvivorRound_localized hKfuel hne
    (supportDensity_normalizedSurvivorRound_exactSubcube hKfuel hsupport hne)

/-- One dense-support parity round at realized rectangular density.  The circuit-specialized good
root is followed by the existing layered collapse and exact live-coordinate transport.  The
successor computes parity with the accumulated fixed-coordinate phase, so its normalized bottom
family again has full support.  This packages the semantic handoff needed by a next-round density
audit without invoking the incompatible support-tail complement. -/
theorem exists_denseParity_normalizedCollapseSuccessor_of_realized_density
    {n m r fuel residualDepth : ℕ} {C : Layered n} (phase : Bool)
    (hr : 0 < r)
    (hw : BottomWidth 2 C) (hcount : BottomCount m C)
    (hKfuel : 20 * r ≤ fuel) (hKn : 20 * r ≤ n)
    (hdensity :
      (4 * ((2 + 1) * ((layeredBottomFamilyList C).length * m + 1))) *
          (20 * r) + 20 * r ≤ n + 1)
    (hne : NonEmptyGates C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase) :
    familyVariableSupport (normalizedLayeredBottomFamily C) = Finset.univ ∧
      ∃ σ : Restriction n,
        stars σ = 20 * r ∧
        CommonShallowAt (normalizedLayeredBottomFamily C) fuel σ
          (10 * r) residualDepth ∧
        ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x →
          ∃ trunk : CommonTree n (Restriction n),
            CommonTree.depth trunk ≤ 10 * r ∧
            let τ := CommonTree.run trunk x
            ∃ κ : Restriction n,
              RestrictionExtends τ κ ∧
              stars κ = 10 * r ∧
              stars κ ≤ fuel ∧
              let D := localizeLiveLayered κ (collapseRound fuel τ C)
              (∀ z : Fin (stars κ) → Bool,
                Layered.eval D z =
                  xor (DTree.parity z) (xor (fixedParityPhase κ) phase)) ∧
              familyVariableSupport (normalizedLayeredBottomFamily D) = Finset.univ ∧
              BottomWidth (residualDepth + 1) D ∧
              bottomSlotCount D ≤
                bottomSlotCount C * (2 ^ (residualDepth + 1) + 1) := by
  refine ⟨normalizedLayeredBottomFamily_support_eq_univ_of_eval_eq_parity_xor
    C phase hparity, ?_⟩
  obtain ⟨σ, hstars, hcommon⟩ :=
    exists_normalizedLayered_commonShallowAt_of_realized_density
      hr hw hcount hKfuel hKn hdensity
  refine ⟨σ, hstars, hcommon, ?_⟩
  intro x hx
  obtain ⟨trunk, hdepth, hlower, hleafStars, hshallow⟩ :=
    hcommon.leaf_shallows (normalizedLayeredBottomFamily_covers C) x hx
  have hlive : 10 * r ≤ stars (CommonTree.run trunk x) := by
    rw [hstars] at hlower
    omega
  obtain ⟨κ, hext, hκstars⟩ :=
    exists_restrictionExtends_stars_eq (CommonTree.run trunk x) hlive
  have hfuel : stars σ ≤ fuel := by simpa [hstars] using hKfuel
  have hleafFuel : stars (CommonTree.run trunk x) ≤ fuel := hleafStars.trans hfuel
  have hκfuel : stars κ ≤ fuel :=
    (stars_le_of_restrictionExtends hext).trans hleafFuel
  have hequiv : Layered.EquivOn κ C
      (collapseRound fuel (CommonTree.run trunk x) C) := by
    intro y hy
    exact collapseRound_EquivOn fuel hleafFuel C y
      (fun i b hi => hy i b (hext i b hi))
  let D := localizeLiveLayered κ (collapseRound fuel (CommonTree.run trunk x) C)
  have hDeval : ∀ z : Fin (stars κ) → Bool,
      Layered.eval D z =
        xor (DTree.parity z) (xor (fixedParityPhase κ) phase) := by
    intro z
    calc
      Layered.eval D z = Layered.eval C (liftLiveAssignment κ z) := by
        rw [show D = localizeLiveLayered κ
          (collapseRound fuel (CommonTree.run trunk x) C) by rfl,
          localizeLiveLayered_eval]
        exact (hequiv (liftLiveAssignment κ z) (liftLiveAssignment_agrees κ z)).symm
      _ = xor (DTree.parity (liftLiveAssignment κ z)) phase := hparity _
      _ = xor (xor (DTree.parity z) (fixedParityPhase κ)) phase := by
        rw [parity_liftLiveAssignment]
      _ = xor (DTree.parity z) (xor (fixedParityPhase κ) phase) := by
        rw [Bool.xor_assoc]
  have hDsupport :
      familyVariableSupport (normalizedLayeredBottomFamily D) = Finset.univ :=
    normalizedLayeredBottomFamily_support_eq_univ_of_eval_eq_parity_xor
      D (xor (fixedParityPhase κ) phase) hDeval
  have hwidth : BottomWidth (residualDepth + 1) D := by
    exact localizeLiveLayered_BottomWidth κ _
      (collapseRound_BottomWidth fuel (CommonTree.run trunk x) hshallow)
  have hslots : bottomSlotCount D ≤
      bottomSlotCount C * (2 ^ (residualDepth + 1) + 1) := by
    exact (localizeLiveLayered_bottomSlotCount_le κ _).trans
      (collapseRound_bottomSlotCount_le hne hshallow)
  exact ⟨trunk, hdepth, κ, hext, hκstars, hκfuel, hDeval, hDsupport, hwidth, hslots⟩

/-- Strict production form of the exact ragged-alphabet density theorem.  This is the
occurrence-sensitive analogue of
`exists_normalizedLayered_storedCommonTerminalAt_of_realized_density`: it charges the sum of the
actual normalized gate lengths rather than a rectangular family-length times maximum-length
envelope. -/
theorem exists_normalizedLayered_storedCommonTerminalAt_of_actual_density
    {n r fuel : ℕ} {C : Layered n}
    (hr : 0 < r) (hw : BottomWidth 2 C)
    (hKfuel : 20 * r ≤ fuel) (hKn : 20 * r ≤ n)
    (hdensity :
      (4 * ((2 + 1) *
        ((∑ g, (normalizedLayeredBottomFamily C g).length) + 1))) *
          (20 * r) + 20 * r ≤ n + 1) :
    ∃ sigma : Restriction n,
      stars sigma = 20 * r ∧
      StoredCommonTerminalAt (normalizedLayeredBottomFamily C) sigma (10 * r) := by
  let shell := Finset.univ.filter fun σ : Restriction n ↦ stars σ = 20 * r
  let bad := commonShallowBad (normalizedLayeredBottomFamily C) fuel
    (20 * r) (10 * r) 0
  have hscaled : bad.card * 2 ^ (10 * r) ≤ shell.card := by
    have hbound := normalizedLayered_commonShallowBad_scaled_le_of_actual_density
      (d := 10 * r) (residualDepth := 0) (savingNum := 1) (savingDen := 2)
      hw hKfuel (by omega) (by omega) hKn (by omega) hdensity
    have hhalf : (20 * r) / 2 = 10 * r := by omega
    simp only [one_mul] at hbound
    rw [hhalf] at hbound
    simpa [bad, shell] using hbound
  have hshellPos : 0 < shell.card := by
    rw [show shell.card = Nat.choose n (20 * r) * 2 ^ (n - 20 * r) by
      simpa [shell] using card_stars_eq n (20 * r)]
    exact Nat.mul_pos (Nat.choose_pos hKn) (pow_pos (by omega) _)
  have hsaving : 2 ≤ 2 ^ (10 * r) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (10 * r) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcard : bad.card < shell.card := by nlinarith
  obtain ⟨sigma, hsigmaShell, hsigmaBad⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcard
  have hstars : stars sigma = 20 * r := by simpa [shell] using hsigmaShell
  have hcommon : CommonShallowAt (normalizedLayeredBottomFamily C) fuel sigma
      (10 * r) 0 := by
    by_contra hnot
    apply hsigmaBad
    rw [mem_commonShallowBad]
    exact ⟨hstars, hnot⟩
  refine ⟨sigma, hstars, hcommon.toStoredCommonTerminalAt_zero ?_⟩
  simpa [hstars] using hKfuel

/-- Conditional successor-state constructor for a stored terminal trunk.  After consuming the
stored certificate, the collapsed circuit is relabelled to the reached leaf's live cube.  If that
actual next circuit satisfies the realized-density premise on a smaller scheduled shell, the
counting theorem supplies a fresh stored certificate for the new normalized bottom family.  Its
local root lifts to a genuine ambient extension of the reached leaf; the old certificate is never
reused across the family change. -/
theorem StoredCommonTerminalAt.exists_localized_collapse_successor_of_realized_density
    {n M r fuel trunkDepth : ℕ} {C : Layered n} {τ : Restriction n}
    (h : StoredCommonTerminalAt (normalizedLayeredBottomFamily C) τ trunkDepth)
    (hfuel : stars τ ≤ fuel)
    (hM1 : 1 ≤ M) (hC : NonEmptyGates C) (hcnt : (bottomGates C).length ≤ M)
    (hr : 0 < r) (hnextFuel : 20 * r ≤ fuel)
    (x : Fin n → Bool) (hx : Rung4Restriction.Extends τ x) :
    ∃ trunk : CommonTree n (Restriction n),
      CommonTree.depth trunk ≤ trunkDepth ∧
      let υ := CommonTree.run trunk x
      stars υ ≤ fuel ∧
      let D := localizeLiveLayered υ (collapseRound fuel υ C)
      BottomWidth 2 D ∧ BottomCount (2 * M) D ∧
      (layeredBottomFamilyList D).length ≤ 2 * M ∧
      (∑ g, (normalizedLayeredBottomFamily D g).length) ≤
        layeredRoundActualKeyCap M 0 ∧
      (20 * r ≤ stars υ →
        (4 * ((2 + 1) *
            ((∑ g, (normalizedLayeredBottomFamily D g).length) + 1))) *
              (20 * r) + 20 * r ≤ stars υ + 1 →
        ∃ next : Restriction (stars υ),
          stars next = 20 * r ∧
          RestrictionExtends υ (liftLiveRestriction υ next) ∧
          StoredCommonTerminalAt (normalizedLayeredBottomFamily D) next (10 * r)) := by
  have hcommon := h.toCommonShallowAt fuel
  obtain ⟨trunk, hdepth, _hlower, hleafStars, hshallow⟩ :=
    hcommon.leaf_shallows (normalizedLayeredBottomFamily_covers C) x hx
  refine ⟨trunk, hdepth, ?_⟩
  dsimp only
  have hυfuel : stars (CommonTree.run trunk x) ≤ fuel := hleafStars.trans hfuel
  refine ⟨hυfuel, ?_, ?_, ?_, ?_, ?_⟩
  · exact localizeLiveLayered_BottomWidth (CommonTree.run trunk x) _
      (BottomWidth_mono (by omega)
        (collapseRound_BottomWidth fuel (CommonTree.run trunk x) hshallow))
  · apply localizeLiveLayered_BottomCount (CommonTree.run trunk x)
    simpa [Nat.mul_comm] using
      (collapseRound_BottomCount fuel (CommonTree.run trunk x)
        hM1 hC hshallow hcnt)
  · rw [layeredBottomFamilyList_length,
      localizeLiveLayered_bottomGates_length]
    exact Nat.mul_le_mul_left 2
      ((collapseRound_count_le fuel (CommonTree.run trunk x) hC).trans hcnt)
  · have hnorm := normalizedLayeredBottomFamily_total_length_le
      (localizeLiveLayered (CommonTree.run trunk x)
        (collapseRound fuel (CommonTree.run trunk x) C))
    have hlocal := localizeLiveLayered_bottomClauseCount_le
      (CommonTree.run trunk x) (collapseRound fuel (CommonTree.run trunk x) C)
    have hcollapse := collapseRound_bottomClauseCount_le hcnt hshallow
    exact hnorm.trans ((Nat.mul_le_mul_left 2 (hlocal.trans hcollapse)).trans_eq (by
      simp [layeredRoundActualKeyCap]
      ring))
  · intro hnextShell hnextDensity
    let D := localizeLiveLayered (CommonTree.run trunk x)
      (collapseRound fuel (CommonTree.run trunk x) C)
    have hDwidth : BottomWidth 2 D := by
      exact localizeLiveLayered_BottomWidth (CommonTree.run trunk x) _
        (BottomWidth_mono (by omega)
          (collapseRound_BottomWidth fuel (CommonTree.run trunk x) hshallow))
    have hDcount : BottomCount (2 * M) D := by
      apply localizeLiveLayered_BottomCount (CommonTree.run trunk x)
      simpa [Nat.mul_comm] using
        (collapseRound_BottomCount fuel (CommonTree.run trunk x)
          hM1 hC hshallow hcnt)
    have hnextResult :
        ∃ next : Restriction (stars (CommonTree.run trunk x)),
          stars next = 20 * r ∧
          StoredCommonTerminalAt (normalizedLayeredBottomFamily D) next (10 * r) := by
      exact exists_normalizedLayered_storedCommonTerminalAt_of_actual_density
        (n := stars (CommonTree.run trunk x)) (C := D)
        hr hDwidth hnextFuel hnextShell hnextDensity
    obtain ⟨next, hnextStars, hnextStored⟩ := hnextResult
    exact ⟨next, hnextStars, liftLiveRestriction_extends _ _, hnextStored⟩

/-! ### Finite backward survivor schedules -/

/-! ### Sound conditioned first-round codes -/

/-- A conditioned first-round code with list-decoding ambiguity at most `L`.  Unlike
`ConditionedFirstRoundCode`, this interface does not require the endpoint/label pair to recover a
unique bad root.  It records exactly the weaker counting obligation: at most `L` roots may share
any one endpoint/label pair. -/
structure BoundedAmbiguityFirstRoundCode {n : ℕ} (bad : Finset (Restriction n)) (L : ℕ) where
  Label : Type
  labelFintype : Fintype Label
  endpoint : ↑bad → Restriction n
  encode : ↑bad → Label
  pairFiberCard_le : ∀ kappa label,
    Nat.card {root : ↑bad // endpoint root = kappa ∧ encode root = label} ≤ L

namespace BoundedAmbiguityFirstRoundCode

/-- The label alphabet charged by a bounded-ambiguity code. -/
def labelCard {n L : ℕ} {bad : Finset (Restriction n)}
    (code : BoundedAmbiguityFirstRoundCode bad L) : ℕ :=
  @Fintype.card code.Label code.labelFintype

/-- Bounded-ambiguity shell accounting.  Weakening exact decoding to lists of size at most `L`
introduces exactly one multiplicative factor `L`; no semantic or encoder-specific assumption is
used. -/
theorem bad_card_le_ambiguity_mul_labelCard_mul_endpointShell_card
    {n K' L : ℕ} {bad : Finset (Restriction n)}
    (code : BoundedAmbiguityFirstRoundCode bad L)
    (hendpoint : ∀ root, stars (code.endpoint root) = K') :
    bad.card ≤ L * (code.labelCard *
      (Finset.univ.filter fun kappa : Restriction n => stars kappa = K').card) := by
  classical
  letI : Fintype code.Label := code.labelFintype
  let domain : Finset ↑bad := Finset.univ
  let pair : ↑bad → Restriction n × code.Label :=
    fun root => (code.endpoint root, code.encode root)
  let endpointShell : Finset (Restriction n) :=
    Finset.univ.filter fun kappa => stars kappa = K'
  let pairShell : Finset (Restriction n × code.Label) :=
    endpointShell.product Finset.univ
  have hfibers : ∀ key ∈ domain.image pair,
      (domain.filter fun root => pair root = key).card ≤ L := by
    intro key _
    calc
      (domain.filter fun root => pair root = key).card =
          Fintype.card ↑(domain.filter fun root => pair root = key) := by
            rw [Fintype.card_coe]
      _ ≤ Fintype.card {root : ↑bad //
          code.endpoint root = key.1 ∧ code.encode root = key.2} := by
        apply Fintype.card_le_of_injective
          (fun root : ↑(domain.filter fun root => pair root = key) =>
            (⟨root.1,
              congrArg Prod.fst (Finset.mem_filter.mp root.2).2,
              congrArg Prod.snd (Finset.mem_filter.mp root.2).2⟩ :
              {candidate : ↑bad // code.endpoint candidate = key.1 ∧
                code.encode candidate = key.2}))
        intro root₁ root₂ h
        apply Subtype.ext
        exact congrArg (fun candidate => candidate.1) h
      _ ≤ L := by
        simpa [Nat.card_eq_fintype_card] using code.pairFiberCard_le key.1 key.2
  have himage : domain.image pair ⊆ pairShell := by
    intro key hkey
    obtain ⟨root, _, rfl⟩ := Finset.mem_image.mp hkey
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hendpoint root⟩, Finset.mem_univ _⟩
  have hcount := Finset.card_le_mul_card_image domain L hfibers
  calc
    bad.card ≤ L * (domain.image pair).card := by
      simpa [domain, Nat.mul_comm] using hcount
    _ ≤ L * pairShell.card := Nat.mul_le_mul_left L (Finset.card_le_card himage)
    _ = L * (code.labelCard * endpointShell.card) := by
      simp [pairShell, labelCard, Nat.mul_comm]
    _ = L * (code.labelCard *
        (Finset.univ.filter fun kappa : Restriction n => stars kappa = K').card) := rfl

end BoundedAmbiguityFirstRoundCode

/-- A finite label code for a circuit round, conditioned on its produced endpoint.  The source is
the actual finite bad-root set, rather than the whole restriction shell.  Soundness says that the
decoder reconstructs every bad root from the pair consisting of its endpoint and its label.

This interface deliberately imposes no particular encoder construction and no density bound.  It
isolates the minimum semantic obligation that any proposed restriction- or survivor-conditioned
alphabet must discharge before its cardinality can be inserted into the product-aware recurrence. -/
structure ConditionedFirstRoundCode {n : ℕ} (bad : Finset (Restriction n)) where
  Label : Type
  labelFintype : Fintype Label
  endpoint : ↑bad → Restriction n
  encode : ↑bad → Label
  decode : Restriction n → Label → Option ↑bad
  decode_encode : ∀ root, decode (endpoint root) (encode root) = some root

namespace ConditionedFirstRoundCode

/-- The finite cardinality charged to the product-aware recurrence. -/
def labelCard {n : ℕ} {bad : Finset (Restriction n)}
    (code : ConditionedFirstRoundCode bad) : ℕ :=
  @Fintype.card code.Label code.labelFintype

/-- Decoder soundness makes `(endpoint, label)` injective on the actual bad roots. -/
theorem endpoint_encode_injective {n : ℕ} {bad : Finset (Restriction n)}
    (code : ConditionedFirstRoundCode bad) :
    Function.Injective (fun root ↦ (code.endpoint root, code.encode root)) := by
  intro root₁ root₂ h
  have hendpoint : code.endpoint root₁ = code.endpoint root₂ := congrArg Prod.fst h
  have hencode : code.encode root₁ = code.encode root₂ := congrArg Prod.snd h
  have hdecode := code.decode_encode root₁
  rw [hendpoint, hencode, code.decode_encode root₂] at hdecode
  exact Option.some.inj hdecode.symm

/-- On each fixed endpoint fiber, labels alone are injective. -/
theorem encode_injective_on_endpoint_fiber {n : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad)
    (kappa : Restriction n) :
    Set.InjOn code.encode {root | code.endpoint root = kappa} := by
  intro root₁ hroot₁ root₂ hroot₂ hencode
  apply code.endpoint_encode_injective
  exact Prod.ext (hroot₁.trans hroot₂.symm) hencode

/-- Every endpoint fiber fits inside the finite label alphabet.  This exposes the quantitative
obligation behind conditioned compression: the largest realized bad-root fiber is a lower bound
on the number of charged labels. -/
theorem endpointFiberCard_le_labelCard {n : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad)
    (kappa : Restriction n) :
    Fintype.card {root : ↑bad // code.endpoint root = kappa} ≤ code.labelCard := by
  letI : Fintype code.Label := code.labelFintype
  let encodeFiber : {root : ↑bad // code.endpoint root = kappa} → code.Label :=
    fun root ↦ code.encode root.1
  apply Fintype.card_le_of_injective encodeFiber
  intro root₁ root₂ hencode
  apply Subtype.ext
  exact code.encode_injective_on_endpoint_fiber kappa root₁.property root₂.property hencode

/-- A nonempty actual bad set forces every sound conditioned code to have a nonempty label
alphabet.  This is the minimal bridge needed to replace the optimistic zero-label audit by the
positive-alphabet floor. -/
theorem labelCard_pos_of_bad_nonempty {n : ℕ} {bad : Finset (Restriction n)}
    (code : ConditionedFirstRoundCode bad) (hbad : bad.Nonempty) :
    0 < code.labelCard := by
  obtain ⟨root, hroot⟩ := hbad
  let root' : ↑bad := ⟨root, hroot⟩
  exact @Fintype.card_pos_iff code.Label code.labelFintype |>.2 ⟨code.encode root'⟩

/-- Package any finite endpoint/label pair known to be injective as a decoder-sound conditioned
code.  The decoder is deliberately extensional: it searches the finite source for the unique root
with the requested pair.  Concrete encoders therefore only need to prove their existing
reconstruction/injectivity theorem once. -/
noncomputable def ofInjectivePair {n : ℕ} {bad : Finset (Restriction n)}
    {Label : Type} [Fintype Label]
    (endpoint : ↑bad → Restriction n) (encode : ↑bad → Label)
    (hinj : Function.Injective fun root ↦ (endpoint root, encode root)) :
    ConditionedFirstRoundCode bad where
  Label := Label
  labelFintype := inferInstance
  endpoint := endpoint
  encode := encode
  decode := by
    classical
    exact fun kappa label =>
      if h : ∃ root : ↑bad, endpoint root = kappa ∧ encode root = label then
        some (Classical.choose h)
      else none
  decode_encode := by
    intro root
    rw [dif_pos ⟨root, rfl, rfl⟩]
    congr 1
    apply hinj
    exact Prod.ext
      (Classical.choose_spec (show ∃ candidate : ↑bad,
        endpoint candidate = endpoint root ∧ encode candidate = encode root from
          ⟨root, rfl, rfl⟩)).1
      (Classical.choose_spec (show ∃ candidate : ↑bad,
        endpoint candidate = endpoint root ∧ encode candidate = encode root from
          ⟨root, rfl, rfl⟩)).2

/-- The existing circuit-owned ragged symmetric-prefix encoder is a sound conditioned code on
the actual common-shallow bad set.  Its endpoint is the canonical first-`d` fresh-variable
endpoint selected by the semantic bad assignment; its label records fresh positions and the
multiset of realized `(gate, term)` keys. -/
noncomputable def commonShallowBadPrefixCode
    {n G w fuel K d residualDepth : ℕ} (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    ConditionedFirstRoundCode (commonShallowBad gates fuel K d residualDepth) := by
  let assignment := commonShallowBadAssignment gates fuel K d residualDepth
  let endpoint :
      ↑(commonShallowBad gates fuel K d residualDepth) → Restriction n := fun root ↦
    freshTaggedPrefixEndpoint gates fuel root.1 (assignment root.1) d
  let encode : ↑(commonShallowBad gates fuel K d residualDepth) →
      PrefixActualSymLabel w d gates := fun root ↦
    canonicalPrefixActualSymLabel (d := d) gates hnd hw fuel root.1 (assignment root.1)
  apply ofInjectivePair endpoint encode
  intro root₁ root₂ hpairs
  apply Subtype.ext
  apply freshTaggedPrefixEndpoint_inj_of_vars_eq gates fuel
    (commonShallowBadAssignment_spec root₁.property).1
    (commonShallowBadAssignment_spec root₂.property).1
    (congrArg Prod.fst hpairs)
  apply freshTaggedPrefixVars_eq_of_prefixActualSymLabel_eq gates hnd hw fuel
    root₁.1 root₂.1 (assignment root₁.1) (assignment root₂.1)
    (commonShallowBadAssignment_spec root₁.property).1
    (commonShallowBadAssignment_spec root₂.property).1
    (commonShallowBadAssignment_long_of_le_fuel hKfuel root₁.property)
    (commonShallowBadAssignment_long_of_le_fuel hKfuel root₂.property)
    (congrArg Prod.snd hpairs)

/-- Exact first-round alphabet charged by the concrete ragged symmetric-prefix code.  This is an
ambient alphabet bound, not yet the smaller endpoint-conditioned realized image. -/
theorem commonShallowBadPrefixCode_labelCard
    {n G w fuel K d residualDepth : ℕ} (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    (commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
      gates hnd hw hKfuel).labelCard =
      (w + 1) ^ d * (((∑ g, (gates g).length) + d - 1).choose d + 1) := by
  change Fintype.card (PrefixActualSymLabel w d gates) = _
  exact card_prefixActualSymLabel w d gates

/-- The labels actually used by a conditioned code on its finite bad-root domain.  This is the
global union of the endpoint-local realized label images, represented without paying for unused
elements of the ambient label type. -/
noncomputable def realizedLabelImage {n : ℕ} {bad : Finset (Restriction n)}
    (code : ConditionedFirstRoundCode bad) : Finset code.Label := by
  classical
  letI : Fintype code.Label := code.labelFintype
  exact Finset.univ.image code.encode

/-- Restrict a decoder-sound conditioned code to the finite subtype of labels it actually uses.
Labels may still be reused at different endpoints; decoder soundness only requires injectivity
inside each endpoint fiber. -/
noncomputable def restrictToRealizedLabels {n : ℕ} {bad : Finset (Restriction n)}
    (code : ConditionedFirstRoundCode bad) : ConditionedFirstRoundCode bad := by
  classical
  letI : Fintype code.Label := code.labelFintype
  let encode : ↑bad → ↑code.realizedLabelImage := fun root ↦
    ⟨code.encode root, by
      rw [realizedLabelImage, Finset.mem_image]
      exact ⟨root, Finset.mem_univ _, rfl⟩⟩
  apply ofInjectivePair code.endpoint encode
  intro root₁ root₂ hpairs
  have hendpoint : code.endpoint root₁ = code.endpoint root₂ :=
    congrArg (fun pair : Restriction n × ↑code.realizedLabelImage ↦ pair.1) hpairs
  have hencode : encode root₁ = encode root₂ :=
    congrArg (fun pair : Restriction n × ↑code.realizedLabelImage ↦ pair.2) hpairs
  apply code.endpoint_encode_injective
  exact Prod.ext hendpoint (congrArg Subtype.val hencode)

/-- The restricted code charges exactly the number of globally realized labels. -/
theorem restrictToRealizedLabels_labelCard {n : ℕ} {bad : Finset (Restriction n)}
    (code : ConditionedFirstRoundCode bad) :
    code.restrictToRealizedLabels.labelCard = code.realizedLabelImage.card := by
  classical
  letI : Fintype code.Label := code.labelFintype
  change Fintype.card ↑code.realizedLabelImage = code.realizedLabelImage.card
  exact Fintype.card_coe _

/-- Removing unused labels never enlarges the charged alphabet. -/
theorem realizedLabelImage_card_le_labelCard {n : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad) :
    code.realizedLabelImage.card ≤ code.labelCard := by
  classical
  letI : Fintype code.Label := code.labelFintype
  calc
    code.realizedLabelImage.card ≤ (Finset.univ : Finset code.Label).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = code.labelCard := rfl

/-- The realized alphabet is also no larger than the actual semantic bad-root set that generates
it. -/
theorem realizedLabelImage_card_le_bad_card {n : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad) :
    code.realizedLabelImage.card ≤ bad.card := by
  classical
  letI : Fintype code.Label := code.labelFintype
  change ((Finset.univ : Finset ↑bad).image code.encode).card ≤ bad.card
  calc
    ((Finset.univ : Finset ↑bad).image code.encode).card ≤
        (Finset.univ : Finset ↑bad).card := Finset.card_image_le
    _ = bad.card := Fintype.card_coe bad

/-- The number of bad roots producing one fixed endpoint. -/
def endpointFiberCard {n : ℕ} {bad : Finset (Restriction n)}
    (code : ConditionedFirstRoundCode bad) (kappa : Restriction n) : ℕ :=
  Fintype.card {root : ↑bad // code.endpoint root = kappa}

/-- The largest endpoint fiber that is actually realized by a bad root.  Taking the supremum over
the finite bad-root domain, rather than over the much larger ambient endpoint type, makes the
empty-bad-set case definitionally harmless and charges no unrealized endpoint. -/
noncomputable def maxRealizedEndpointFiberCard {n : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad) : ℕ := by
  classical
  exact Finset.univ.sup (fun root : ↑bad => code.endpointFiberCard (code.endpoint root))

/-- Every realized endpoint fiber is bounded by the realized maximum. -/
theorem endpointFiberCard_le_maxRealized {n : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad)
    (root : ↑bad) :
    code.endpointFiberCard (code.endpoint root) ≤ code.maxRealizedEndpointFiberCard := by
  classical
  exact Finset.le_sup (s := (Finset.univ : Finset ↑bad))
    (f := fun candidate : ↑bad => code.endpointFiberCard (code.endpoint candidate))
    (Finset.mem_univ root)

/-- Unrealized endpoint fibers are empty, so every endpoint fiber—not only those presented by a
chosen root—is bounded by the maximum over realized endpoints. -/
theorem endpointFiberCard_le_maxRealized_any {n : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad)
    (kappa : Restriction n) :
    code.endpointFiberCard kappa ≤ code.maxRealizedEndpointFiberCard := by
  classical
  by_cases h : ∃ root : ↑bad, code.endpoint root = kappa
  · obtain ⟨root, hroot⟩ := h
    simpa [hroot] using code.endpointFiberCard_le_maxRealized root
  · have hempty : IsEmpty {root : ↑bad // code.endpoint root = kappa} :=
      ⟨fun root => h ⟨root.1, root.property⟩⟩
    letI := hempty
    simp [endpointFiberCard]

/-- A fixed injection of each endpoint fiber into the largest realized fiber.  Choosing the
injection as a function of the endpoint makes it shared by all roots in that fiber. -/
noncomputable def maxFiberEmbedding {n : ℕ} {bad : Finset (Restriction n)}
    (code : ConditionedFirstRoundCode bad) (kappa : Restriction n) :
    {root : ↑bad // code.endpoint root = kappa} ↪ Fin code.maxRealizedEndpointFiberCard := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa [endpointFiberCard] using code.endpointFiberCard_le_maxRealized_any kappa

/-- Reindex a root inside its own endpoint fiber.  Distinct endpoints deliberately reuse the same
ranks. -/
noncomputable def maxFiberEncode {n : ℕ} {bad : Finset (Restriction n)}
    (code : ConditionedFirstRoundCode bad) (root : ↑bad) :
    Fin code.maxRealizedEndpointFiberCard :=
  code.maxFiberEmbedding (code.endpoint root) ⟨root, rfl⟩

theorem maxFiberEncode_eq_embedding {n : ℕ} {bad : Finset (Restriction n)}
    (code : ConditionedFirstRoundCode bad) (root : ↑bad) (kappa : Restriction n)
    (hendpoint : code.endpoint root = kappa) :
    code.maxFiberEncode root = code.maxFiberEmbedding kappa ⟨root, hendpoint⟩ := by
  subst kappa
  rfl

/-- Endpoint-local ranks are injective once the endpoint is fixed. -/
theorem endpoint_maxFiberEncode_injective {n : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad) :
    Function.Injective (fun root => (code.endpoint root, code.maxFiberEncode root)) := by
  intro root₁ root₂ hpairs
  have hendpoint : code.endpoint root₁ = code.endpoint root₂ := congrArg Prod.fst hpairs
  have hencode : code.maxFiberEncode root₁ = code.maxFiberEncode root₂ := congrArg Prod.snd hpairs
  rw [code.maxFiberEncode_eq_embedding root₁ (code.endpoint root₂) hendpoint,
    code.maxFiberEncode_eq_embedding root₂ (code.endpoint root₂) rfl] at hencode
  have hfiber := (code.maxFiberEmbedding (code.endpoint root₂)).injective hencode
  exact congrArg Subtype.val hfiber

/-- The optimal endpoint-conditioned code: labels are reused independently at different
endpoints, so its alphabet is exactly the largest realized endpoint-fiber cardinality. -/
noncomputable def restrictToMaxEndpointFiber {n : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad) :
    ConditionedFirstRoundCode bad := by
  classical
  exact ofInjectivePair code.endpoint code.maxFiberEncode code.endpoint_maxFiberEncode_injective

/-- The optimally reindexed code charges exactly the maximum realized endpoint fiber. -/
theorem restrictToMaxEndpointFiber_labelCard {n : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad) :
    code.restrictToMaxEndpointFiber.labelCard = code.maxRealizedEndpointFiberCard := by
  change Fintype.card (Fin code.maxRealizedEndpointFiberCard) = _
  exact Fintype.card_fin _

/-- No decoder-sound code can use fewer labels than its largest realized endpoint fiber.  Together
with `restrictToMaxEndpointFiber_labelCard`, this proves that the reindexed construction is exactly
optimal among codes using the same endpoint map. -/
theorem maxRealizedEndpointFiberCard_le_labelCard {n : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad) :
    code.maxRealizedEndpointFiberCard ≤ code.labelCard := by
  classical
  rw [maxRealizedEndpointFiberCard]
  apply Finset.sup_le
  intro root _
  exact code.endpointFiberCard_le_labelCard (code.endpoint root)

/-- Finite pigeonhole accounting for an endpoint-conditioned code.  The actual bad-root
population is at most the largest realized endpoint fiber times the number of distinct endpoints
that occur.  This form deliberately counts the endpoint image exactly, before any ambient-shell
relaxation. -/
theorem bad_card_le_maxRealizedEndpointFiberCard_mul_endpointImage_card {n : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad) :
    bad.card ≤ code.maxRealizedEndpointFiberCard *
      ((Finset.univ : Finset ↑bad).image code.endpoint).card := by
  classical
  let domain : Finset ↑bad := Finset.univ
  have hfibers : ∀ kappa ∈ domain.image code.endpoint,
      (domain.filter fun root => code.endpoint root = kappa).card ≤
        code.maxRealizedEndpointFiberCard := by
    intro kappa _
    calc
      (domain.filter fun root => code.endpoint root = kappa).card =
          Fintype.card ↑(domain.filter fun root => code.endpoint root = kappa) := by
            rw [Fintype.card_coe]
      _ ≤ code.endpointFiberCard kappa := by
        let embedFilter : ↑(domain.filter fun root => code.endpoint root = kappa) →
            {candidate : ↑bad // code.endpoint candidate = kappa} := fun root =>
          ⟨root.1, (Finset.mem_filter.mp root.2).2⟩
        apply Fintype.card_le_of_injective embedFilter
        intro root₁ root₂ h
        apply Subtype.ext
        exact congrArg
          (fun candidate : {candidate : ↑bad // code.endpoint candidate = kappa} => candidate.1) h
      _ ≤ code.maxRealizedEndpointFiberCard :=
        code.endpointFiberCard_le_maxRealized_any kappa
  have hcount := Finset.card_le_mul_card_image domain
    code.maxRealizedEndpointFiberCard hfibers
  simpa [domain, Nat.mul_comm] using hcount

/-- Encoder-independent shell accounting.  If every produced endpoint lies in one prescribed
live-variable shell, then decoder soundness alone forces the bad-root population to fit inside
the product of the charged label alphabet and that endpoint shell.  Unlike the canonical-prefix
specialization below, this theorem does not inspect the assignment, selector, or label format. -/
theorem bad_card_le_labelCard_mul_endpointShell_card {n K' : ℕ}
    {bad : Finset (Restriction n)} (code : ConditionedFirstRoundCode bad)
    (hendpoint : ∀ root, stars (code.endpoint root) = K') :
    bad.card ≤ code.labelCard *
      (Finset.univ.filter fun kappa : Restriction n => stars kappa = K').card := by
  classical
  have himage : ((Finset.univ : Finset ↑bad).image code.endpoint) ⊆
      Finset.univ.filter (fun kappa : Restriction n => stars kappa = K') := by
    intro kappa hkappa
    obtain ⟨root, _, rfl⟩ := Finset.mem_image.mp hkappa
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hendpoint root⟩
  calc
    bad.card ≤ code.maxRealizedEndpointFiberCard *
        ((Finset.univ : Finset ↑bad).image code.endpoint).card :=
      code.bad_card_le_maxRealizedEndpointFiberCard_mul_endpointImage_card
    _ ≤ code.labelCard *
        (Finset.univ.filter fun kappa : Restriction n => stars kappa = K').card :=
      Nat.mul_le_mul code.maxRealizedEndpointFiberCard_le_labelCard
        (Finset.card_le_card himage)

/-- The concrete ragged prefix code with labels independently reindexed inside each realized
endpoint fiber. -/
noncomputable def commonShallowBadMaxFiberPrefixCode
    {n G w fuel K d residualDepth : ℕ} (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    ConditionedFirstRoundCode (commonShallowBad gates fuel K d residualDepth) :=
  (commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
    gates hnd hw hKfuel).restrictToMaxEndpointFiber

/-- Its charged alphabet is exactly the maximum cardinality of an actually realized endpoint
fiber of the original ragged-prefix endpoint map. -/
theorem commonShallowBadMaxFiberPrefixCode_labelCard
    {n G w fuel K d residualDepth : ℕ} (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    (commonShallowBadMaxFiberPrefixCode (d := d) (residualDepth := residualDepth)
      gates hnd hw hKfuel).labelCard =
      (commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
        gates hnd hw hKfuel).maxRealizedEndpointFiberCard := by
  exact restrictToMaxEndpointFiber_labelCard _

/-- A fixed endpoint fiber of the canonical bad-root prefix code injects into the `d`-subsets of
the coordinates fixed at that endpoint.  This is the first circuit-independent quantitative
bound on the optimal endpoint-conditioned alphabet: it charges neither the ambient symmetric
label type nor all `d`-subsets of the original `n` coordinates. -/
theorem commonShallowBadPrefixCode_endpointFiberCard_le_choose_fixed
    {n G w fuel K d residualDepth : ℕ} (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) (kappa : Restriction n) :
    (commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
      gates hnd hw hKfuel).endpointFiberCard kappa ≤
      Nat.choose (n - stars kappa) d := by
  classical
  let assignment := commonShallowBadAssignment gates fuel K d residualDepth
  let code := commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
    gates hnd hw hKfuel
  let fixed := (Finset.univ : Finset (Fin n)) \ freeVars kappa
  let encodeFiber : {root : ↑(commonShallowBad gates fuel K d residualDepth) //
      code.endpoint root = kappa} → ↑(fixed.powersetCard d) := fun root ↦
    ⟨freshTaggedPrefixVars gates fuel root.1.1 (assignment root.1.1) d, by
      rw [Finset.mem_powersetCard]
      constructor
      · intro v hv
        simp only [fixed, Finset.mem_sdiff]
        refine ⟨Finset.mem_univ v, ?_⟩
        have hendpoint : freshTaggedPrefixEndpoint gates fuel root.1.1
            (assignment root.1.1) d = kappa := by
          exact root.property
        rw [← hendpoint, freeVars_freshTaggedPrefixEndpoint]
        simp [hv]
      · exact freshTaggedPrefixVars_card_eq_of_le_trace gates fuel root.1.1
          (assignment root.1.1) d
          (commonShallowBadAssignment_spec root.1.property).1
          (commonShallowBadAssignment_long_of_le_fuel hKfuel root.1.property)⟩
  calc
    code.endpointFiberCard kappa ≤ Fintype.card ↑(fixed.powersetCard d) := by
      apply Fintype.card_le_of_injective encodeFiber
      intro root₁ root₂ hvars
      apply Subtype.ext
      apply Subtype.ext
      apply freshTaggedPrefixEndpoint_inj_of_vars_eq gates fuel
        (commonShallowBadAssignment_spec root₁.1.property).1
        (commonShallowBadAssignment_spec root₂.1.property).1
      · exact root₁.property.trans root₂.property.symm
      · exact congrArg Subtype.val hvars
    _ = Nat.choose (n - stars kappa) d := by
      rw [Fintype.card_coe, Finset.card_powersetCard]
      congr 2
      simp only [fixed]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin]
      rfl

/-- The exact semantic candidate family inside one canonical bad-prefix endpoint fiber.  Unlike
the binomial ceiling above, this finset retains all three conditions that determine realization:
the reconstructed root is semantically bad, its canonical selected-variable set is exactly `S`,
and its selected prefix returns to `kappa`.  The ambient powerset is localized to coordinates
fixed at the endpoint. -/
noncomputable def commonShallowBadPrefixCandidateSets
    {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel K d residualDepth : ℕ) (kappa : Restriction n) :
    Finset (Finset (Fin n)) := by
  classical
  let assignment := commonShallowBadAssignment gates fuel K d residualDepth
  let fixed := (Finset.univ : Finset (Fin n)) \ freeVars kappa
  exact (fixed.powersetCard d).filter fun S =>
    let root := freeOn kappa S
    root ∈ commonShallowBad gates fuel K d residualDepth ∧
      freshTaggedPrefixVars gates fuel root (assignment root) d = S ∧
      freshTaggedPrefixEndpoint gates fuel root (assignment root) d = kappa

/-- The filtered powerset above is not merely an upper-bound device: it is exactly equivalent to
the corresponding bad-root endpoint fiber.  This exposes the semantic predicate that must be
counted for a concrete dense-support parity family, while preserving the endpoint-local reuse of
the optimal conditioned alphabet. -/
theorem commonShallowBadPrefixCandidateSets_card_eq_endpointFiberCard
    {n G w fuel K d residualDepth : ℕ} (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) (kappa : Restriction n) :
    (commonShallowBadPrefixCandidateSets gates fuel K d residualDepth kappa).card =
      (commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
        gates hnd hw hKfuel).endpointFiberCard kappa := by
  classical
  let assignment := commonShallowBadAssignment gates fuel K d residualDepth
  let code := commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
    gates hnd hw hKfuel
  let toCandidates : {root : ↑(commonShallowBad gates fuel K d residualDepth) //
      code.endpoint root = kappa} →
      ↑(commonShallowBadPrefixCandidateSets gates fuel K d residualDepth kappa) :=
    fun root => ⟨freshTaggedPrefixVars gates fuel root.1.1 (assignment root.1.1) d, by
      rw [commonShallowBadPrefixCandidateSets, Finset.mem_filter]
      constructor
      · rw [Finset.mem_powersetCard]
        constructor
        · intro v hv
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ v, ?_⟩
          have hendpoint := root.property
          change freshTaggedPrefixEndpoint gates fuel root.1.1
            (assignment root.1.1) d = kappa at hendpoint
          rw [← hendpoint, freeVars_freshTaggedPrefixEndpoint]
          simp [hv]
        · exact freshTaggedPrefixVars_card_eq_of_le_trace gates fuel root.1.1
            (assignment root.1.1) d
            (commonShallowBadAssignment_spec root.1.property).1
            (commonShallowBadAssignment_long_of_le_fuel hKfuel root.1.property)
      · dsimp only
        have hendpoint := root.property
        change freshTaggedPrefixEndpoint gates fuel root.1.1
          (assignment root.1.1) d = kappa at hendpoint
        have hrecover := freeOn_freshTaggedPrefixEndpoint gates fuel root.1.1
          (assignment root.1.1) d
          (commonShallowBadAssignment_spec root.1.property).1
        have hroot : freeOn kappa (freshTaggedPrefixVars gates fuel root.1.1
            (assignment root.1.1) d) = root.1.1 := by
          simpa only [hendpoint] using hrecover
        rw [hroot]
        exact ⟨root.1.property, rfl, hendpoint⟩⟩
  let fromCandidates :
      ↑(commonShallowBadPrefixCandidateSets gates fuel K d residualDepth kappa) →
      {root : ↑(commonShallowBad gates fuel K d residualDepth) //
        code.endpoint root = kappa} := fun candidate => by
    have hc := candidate.property
    simp only [commonShallowBadPrefixCandidateSets, Finset.mem_filter] at hc
    refine ⟨⟨freeOn kappa candidate.1, hc.2.1⟩, ?_⟩
    change freshTaggedPrefixEndpoint gates fuel (freeOn kappa candidate.1)
      (assignment (freeOn kappa candidate.1)) d = kappa
    exact hc.2.2.2
  let fiberEquiv :
      {root : ↑(commonShallowBad gates fuel K d residualDepth) //
        code.endpoint root = kappa} ≃
      ↑(commonShallowBadPrefixCandidateSets gates fuel K d residualDepth kappa) := {
    toFun := toCandidates
    invFun := fromCandidates
    left_inv := by
      intro root
      apply Subtype.ext
      apply Subtype.ext
      change freeOn kappa (freshTaggedPrefixVars gates fuel root.1.1
        (assignment root.1.1) d) = root.1.1
      have hendpoint := root.property
      change freshTaggedPrefixEndpoint gates fuel root.1.1
        (assignment root.1.1) d = kappa at hendpoint
      simpa only [hendpoint] using
        (freeOn_freshTaggedPrefixEndpoint gates fuel root.1.1
        (assignment root.1.1) d
        (commonShallowBadAssignment_spec root.1.property).1)
    right_inv := by
      intro candidate
      apply Subtype.ext
      have hc := candidate.property
      simp only [commonShallowBadPrefixCandidateSets, Finset.mem_filter] at hc
      exact hc.2.2.1
    }
  rw [← Fintype.card_coe]
  exact Fintype.card_congr fiberEquiv.symm

/-- Exact endpoint-local formula for the optimal conditioned alphabet: take the largest filtered
semantic candidate family among endpoints actually reached by bad roots.  This is the executable
finite counting target that replaces the previous unfiltered binomial ceiling. -/
theorem commonShallowBadMaxFiberPrefixCode_labelCard_eq_sup_candidateSets
    {n G w fuel K d residualDepth : ℕ} (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    (commonShallowBadMaxFiberPrefixCode (d := d) (residualDepth := residualDepth)
      gates hnd hw hKfuel).labelCard =
      Finset.univ.sup (fun root :
          ↑(commonShallowBad gates fuel K d residualDepth) =>
        (commonShallowBadPrefixCandidateSets gates fuel K d residualDepth
          ((commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
            gates hnd hw hKfuel).endpoint root)).card) := by
  rw [commonShallowBadMaxFiberPrefixCode_labelCard,
    ConditionedFirstRoundCode.maxRealizedEndpointFiberCard]
  apply Finset.sup_congr rfl
  intro root _
  exact (commonShallowBadPrefixCandidateSets_card_eq_endpointFiberCard
    gates hnd hw hKfuel
    ((commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
      gates hnd hw hKfuel).endpoint root)).symm

/-- Consequently, the exact optimal alphabet is at most the largest fixed-coordinate binomial
fiber over its realized endpoints.  On the exact `K`-live bad shell, every such endpoint has
`K-d` live variables, so the uniform bound simplifies to `choose (n-(K-d)) d`. -/
theorem commonShallowBadPrefixCode_maxRealizedEndpointFiberCard_le_choose
    {n G w fuel K d residualDepth : ℕ} (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    (commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
      gates hnd hw hKfuel).maxRealizedEndpointFiberCard ≤
      Nat.choose (n - (K - d)) d := by
  classical
  let code := commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
    gates hnd hw hKfuel
  rw [ConditionedFirstRoundCode.maxRealizedEndpointFiberCard]
  apply Finset.sup_le
  intro root _
  calc
    code.endpointFiberCard (code.endpoint root) ≤
        Nat.choose (n - stars (code.endpoint root)) d :=
      commonShallowBadPrefixCode_endpointFiberCard_le_choose_fixed
        gates hnd hw hKfuel (code.endpoint root)
    _ = Nat.choose (n - (K - d)) d := by
      congr 2
      have hext : Rung4Restriction.Extends root.1
          (commonShallowBadAssignment gates fuel K d residualDepth root.1) :=
        (commonShallowBadAssignment_spec root.property).1
      change stars (freshTaggedPrefixEndpoint gates fuel root.1
        (commonShallowBadAssignment gates fuel K d residualDepth root.1) d) = K - d
      rw [stars_freshTaggedPrefixEndpoint gates fuel root.1
          (commonShallowBadAssignment gates fuel K d residualDepth root.1) d hext,
        (mem_commonShallowBad.mp root.property).1,
        freshTaggedPrefixVars_card_eq_of_le_trace gates fuel root.1
          (commonShallowBadAssignment gates fuel K d residualDepth root.1) d
          (commonShallowBadAssignment_spec root.property).1
          (commonShallowBadAssignment_long_of_le_fuel hKfuel root.property)]

/-- Exact-shell pigeonhole lower bound for the canonical prefix endpoint map.  Every bad root has
`K` live coordinates, while its first-`d` fresh-variable endpoint has exactly `K-d`; hence the
whole bad population must fit into at most the `(K-d)`-live shell, with multiplicity bounded by
the largest realized endpoint fiber. -/
theorem commonShallowBad_card_le_maxFiber_mul_endpointShell_card
    {n G w fuel K d residualDepth : ℕ} (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      (commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
        gates hnd hw hKfuel).maxRealizedEndpointFiberCard *
      (Finset.univ.filter fun kappa : Restriction n => stars kappa = K - d).card := by
  classical
  let code := commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
    gates hnd hw hKfuel
  have himage : ((Finset.univ :
      Finset ↑(commonShallowBad gates fuel K d residualDepth)).image code.endpoint) ⊆
      Finset.univ.filter (fun kappa : Restriction n => stars kappa = K - d) := by
    intro kappa hkappa
    obtain ⟨root, _, rfl⟩ := Finset.mem_image.mp hkappa
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hext : Rung4Restriction.Extends root.1
        (commonShallowBadAssignment gates fuel K d residualDepth root.1) :=
      (commonShallowBadAssignment_spec root.property).1
    change stars (freshTaggedPrefixEndpoint gates fuel root.1
      (commonShallowBadAssignment gates fuel K d residualDepth root.1) d) = K - d
    rw [stars_freshTaggedPrefixEndpoint gates fuel root.1
        (commonShallowBadAssignment gates fuel K d residualDepth root.1) d hext,
      (mem_commonShallowBad.mp root.property).1,
      freshTaggedPrefixVars_card_eq_of_le_trace gates fuel root.1
        (commonShallowBadAssignment gates fuel K d residualDepth root.1) d
        (commonShallowBadAssignment_spec root.property).1
        (commonShallowBadAssignment_long_of_le_fuel hKfuel root.property)]
  calc
    (commonShallowBad gates fuel K d residualDepth).card ≤
        code.maxRealizedEndpointFiberCard *
          ((Finset.univ : Finset ↑(commonShallowBad gates fuel K d residualDepth)).image
            code.endpoint).card :=
      code.bad_card_le_maxRealizedEndpointFiberCard_mul_endpointImage_card
    _ ≤ code.maxRealizedEndpointFiberCard *
        (Finset.univ.filter fun kappa : Restriction n => stars kappa = K - d).card :=
      Nat.mul_le_mul_left _ (Finset.card_le_card himage)

/-- Direct alphabet form of the fixed-coordinate binomial bound. -/
theorem commonShallowBadMaxFiberPrefixCode_labelCard_le_choose
    {n G w fuel K d residualDepth : ℕ} (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    (commonShallowBadMaxFiberPrefixCode (d := d) (residualDepth := residualDepth)
      gates hnd hw hKfuel).labelCard ≤ Nat.choose (n - (K - d)) d := by
  rw [commonShallowBadMaxFiberPrefixCode_labelCard]
  exact commonShallowBadPrefixCode_maxRealizedEndpointFiberCard_le_choose
    gates hnd hw hKfuel

/-- The concrete ragged symmetric-prefix code with every unused ambient label removed. -/
noncomputable def commonShallowBadRealizedPrefixCode
    {n G w fuel K d residualDepth : ℕ} (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    ConditionedFirstRoundCode (commonShallowBad gates fuel K d residualDepth) :=
  (commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
    gates hnd hw hKfuel).restrictToRealizedLabels

/-- Its alphabet cardinality is the exact global image of ragged prefix labels realized by
semantic bad roots. -/
theorem commonShallowBadRealizedPrefixCode_labelCard
    {n G w fuel K d residualDepth : ℕ} (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    (commonShallowBadRealizedPrefixCode (d := d) (residualDepth := residualDepth)
      gates hnd hw hKfuel).labelCard =
      (commonShallowBadPrefixCode (d := d) (residualDepth := residualDepth)
        gates hnd hw hKfuel).realizedLabelImage.card := by
  exact restrictToRealizedLabels_labelCard _

end ConditionedFirstRoundCode

/-- The exact ambient-coordinate margin demanded by the following normalized round when its
residual depth is `r` and its current bottom-slot envelope is `M`. -/
def nextRoundActualMargin (r M : ℕ) : ℕ :=
  8 * (r + 2) * M * 2 ^ (r + 1) + 4 * (r + 2)

/-- The two inequalities currently stored in `FiniteBackwardSurvivorSchedule` do not by
themselves discharge even one successor's rectangular realized-density premise.  With one bottom
gate, residual depth zero, current survivor parameter four, and next parameter one, both schedule
inequalities hold exactly, but the width-two `G ≤ 2*M`, `m ≤ 2*M` density envelope exceeds the
entire current live cube. -/
theorem finiteBackwardSchedule_obligations_do_not_imply_successor_rectangular_density :
    let survivor : ℕ → ℕ := fun i => if i = 0 then 4 else 1
    (20 * survivor 1 ≤ 10 * survivor 0 ∧
      nextRoundActualMargin 0 1 ≤ 10 * survivor 0) ∧
    ¬(4 * ((2 + 1) * ((2 * 1) * (2 * 1) + 1)) *
        (20 * survivor 1) + 20 * survivor 1 ≤ 10 * survivor 0 + 1) := by
  norm_num [nextRoundActualMargin]

/-- Full occurrence-sensitive density demand for a width-two successor with exact ragged
alphabet cap `A` and survivor parameter `r`.  Unlike `nextRoundActualMargin`, this retains the
essential product with the next shell size. -/
def nextRoundProductDemand (A r : ℕ) : ℕ :=
  4 * ((2 + 1) * (A + 1)) * (20 * r) + 20 * r

/-- Product-aware replacement for the old finite backward schedule.  The first conjunct nests
the next shell in the current ten-times-survivor cube; the second pays the complete ragged
density demand, including its next-shell multiplier. -/
def FiniteProductAwareSurvivorSchedule
    (d : ℕ) (actualKeys survivor : ℕ → ℕ) : Prop :=
  ∀ i < d,
    20 * survivor (i + 1) ≤ 10 * survivor i ∧
    nextRoundProductDemand (actualKeys (i + 1)) (survivor (i + 1)) ≤
      10 * survivor i + 1

/-- Ceiling that converts a density demand `x` into the least ten-times-survivor cube whose
dimension plus one can contain `x`. -/
def ceilDensityBudget (x : ℕ) : ℕ := (x + 8) / 10

/-- On the product demand, the apparent ceiling is exact: the demand is a multiple of ten and
the added eight is precisely the harmless remainder. -/
theorem ceilDensityBudget_nextRoundProductDemand (A next : ℕ) :
    ceilDensityBudget (nextRoundProductDemand A next) = (24 * A + 26) * next := by
  simp only [ceilDensityBudget, nextRoundProductDemand]
  rw [show 4 * ((2 + 1) * (A + 1)) * (20 * next) + 20 * next + 8 =
      10 * ((24 * A + 26) * next) + 8 by ring]
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < 10),
    Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem le_ten_mul_ceilDensityBudget_add_one (x : ℕ) :
    x ≤ 10 * ceilDensityBudget x + 1 := by
  have hdiv := Nat.div_add_mod (x + 8) 10
  have hmod := Nat.mod_lt (x + 8) (by omega : 0 < 10)
  simp only [ceilDensityBudget]
  omega

/-- `ceilDensityBudget` is exact: every survivor parameter paying `x` is at least this value. -/
theorem ceilDensityBudget_le_of_le_ten_mul_add_one {x R : ℕ}
    (h : x ≤ 10 * R + 1) : ceilDensityBudget x ≤ R := by
  rw [ceilDensityBudget, Nat.div_le_iff_le_mul (by omega : 0 < 10)]
  omega

/-- The least current survivor parameter for a fixed one-step ragged successor, jointly paying
shell nesting and the full density product. -/
def leastProductAwarePredecessor (A next : ℕ) : ℕ :=
  max (2 * next) (ceilDensityBudget (nextRoundProductDemand A next))

/-- Closed form of the least product-aware predecessor.  The density term always dominates the
separate shell-nesting term, so one round is exactly multiplication by `24*A+26`. -/
theorem leastProductAwarePredecessor_eq (A next : ℕ) :
    leastProductAwarePredecessor A next = (24 * A + 26) * next := by
  simp only [leastProductAwarePredecessor, ceilDensityBudget_nextRoundProductDemand]
  apply max_eq_right
  nlinarith

theorem leastProductAwarePredecessor_pays (A next : ℕ) :
    20 * next ≤ 10 * leastProductAwarePredecessor A next ∧
    nextRoundProductDemand A next ≤
      10 * leastProductAwarePredecessor A next + 1 := by
  constructor
  · have h := Nat.le_max_left (2 * next)
      (ceilDensityBudget (nextRoundProductDemand A next))
    simp only [leastProductAwarePredecessor]
    omega
  · exact (le_ten_mul_ceilDensityBudget_add_one _).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 10
        (Nat.le_max_right (2 * next)
          (ceilDensityBudget (nextRoundProductDemand A next)))) 1)

theorem leastProductAwarePredecessor_le_of_pays {A next current : ℕ}
    (hnest : 20 * next ≤ 10 * current)
    (hdensity : nextRoundProductDemand A next ≤ 10 * current + 1) :
    leastProductAwarePredecessor A next ≤ current := by
  rw [leastProductAwarePredecessor, Nat.max_le]
  constructor
  · omega
  · exact ceilDensityBudget_le_of_le_ten_mul_add_one hdensity

theorem ceilDensityBudget_mono {x y : ℕ} (hxy : x ≤ y) :
    ceilDensityBudget x ≤ ceilDensityBudget y := by
  exact Nat.div_le_div_right (c := 10) (Nat.add_le_add_right hxy 8)

theorem nextRoundProductDemand_mono_right (A : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    nextRoundProductDemand A x ≤ nextRoundProductDemand A y := by
  simp only [nextRoundProductDemand]
  gcongr

/-- The exact one-step predecessor is monotone in the requested next survivor. -/
theorem leastProductAwarePredecessor_mono_right (A : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    leastProductAwarePredecessor A x ≤ leastProductAwarePredecessor A y := by
  simp only [leastProductAwarePredecessor]
  exact max_le_max (Nat.mul_le_mul_left 2 hxy)
    (ceilDensityBudget_mono (nextRoundProductDemand_mono_right A hxy))

/-- Exact finite product-aware backward budget with an explicit terminal survivor.  Key index
`i+1` is the ragged alphabet charged by transition `i`. -/
def leastFiniteProductAwareBudget : ℕ → (ℕ → ℕ) → ℕ → ℕ
  | 0, _, terminal => terminal
  | d + 1, actualKeys, terminal =>
      leastProductAwarePredecessor (actualKeys 1)
        (leastFiniteProductAwareBudget d (fun i => actualKeys (i + 1)) terminal)

@[simp] theorem leastFiniteProductAwareBudget_zero (actualKeys : ℕ → ℕ) (terminal : ℕ) :
    leastFiniteProductAwareBudget 0 actualKeys terminal = terminal := rfl

@[simp] theorem leastFiniteProductAwareBudget_succ
    (d : ℕ) (actualKeys : ℕ → ℕ) (terminal : ℕ) :
    leastFiniteProductAwareBudget (d + 1) actualKeys terminal =
      leastProductAwarePredecessor (actualKeys 1)
        (leastFiniteProductAwareBudget d (fun i => actualKeys (i + 1)) terminal) := rfl

/-- The exact recursive budget is attained, including the prescribed terminal survivor. -/
theorem exists_finiteProductAwareSurvivorSchedule_least
    (d : ℕ) (actualKeys : ℕ → ℕ) (terminal : ℕ) :
    ∃ survivor : ℕ → ℕ,
      FiniteProductAwareSurvivorSchedule d actualKeys survivor ∧
      survivor 0 = leastFiniteProductAwareBudget d actualKeys terminal ∧
      survivor d = terminal := by
  induction d generalizing actualKeys with
  | zero =>
      exact ⟨fun _ => terminal, by intro i hi; omega, rfl, rfl⟩
  | succ d ih =>
      obtain ⟨tail, htail, htail0, htailEnd⟩ :=
        ih (fun i => actualKeys (i + 1))
      let survivor : ℕ → ℕ
        | 0 => leastProductAwarePredecessor (actualKeys 1) (tail 0)
        | i + 1 => tail i
      refine ⟨survivor, ?_, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
            simpa only [survivor, Nat.zero_add] using
              leastProductAwarePredecessor_pays (actualKeys 1) (tail 0)
        | succ i =>
            have hi : i < d := by omega
            simpa only [survivor, Nat.add_assoc] using htail i hi
      · simp only [survivor, leastFiniteProductAwareBudget_succ]
        rw [← htail0]
      · simpa only [survivor] using htailEnd

/-- No product-aware schedule ending at or above `terminal` can start below the exact recursive
budget.  Together with attainment this proves finite-horizon minimality. -/
theorem leastFiniteProductAwareBudget_le_initial
    (d : ℕ) (actualKeys survivor : ℕ → ℕ) (terminal : ℕ)
    (hschedule : FiniteProductAwareSurvivorSchedule d actualKeys survivor)
    (hterminal : terminal ≤ survivor d) :
    leastFiniteProductAwareBudget d actualKeys terminal ≤ survivor 0 := by
  induction d generalizing actualKeys survivor with
  | zero => simpa using hterminal
  | succ d ih =>
      have hfirst := hschedule 0 (by omega)
      have htail : FiniteProductAwareSurvivorSchedule d
          (fun i => actualKeys (i + 1)) (fun i => survivor (i + 1)) := by
        intro i hi
        simpa only [Nat.add_assoc] using hschedule (i + 1) (by omega)
      have hleastTail :
          leastFiniteProductAwareBudget d (fun i => actualKeys (i + 1)) terminal ≤
            survivor 1 := by
        apply ih _ _ htail
        simpa only [Nat.add_assoc] using hterminal
      rw [leastFiniteProductAwareBudget_succ]
      exact (leastProductAwarePredecessor_mono_right (actualKeys 1) hleastTail).trans
        (leastProductAwarePredecessor_le_of_pays hfirst.1 hfirst.2)

theorem leastFiniteProductAwareBudget_pos
    (d : ℕ) (actualKeys : ℕ → ℕ) {terminal : ℕ} (hterminal : 0 < terminal) :
    0 < leastFiniteProductAwareBudget d actualKeys terminal := by
  induction d generalizing actualKeys with
  | zero => simpa using hterminal
  | succ d ih =>
      rw [leastFiniteProductAwareBudget_succ]
      have hnext := ih (fun i => actualKeys (i + 1))
      have hle := Nat.le_max_left
        (2 * leastFiniteProductAwareBudget d (fun i => actualKeys (i + 1)) terminal)
        (ceilDensityBudget (nextRoundProductDemand (actualKeys 1)
          (leastFiniteProductAwareBudget d (fun i => actualKeys (i + 1)) terminal)))
      simp only [leastProductAwarePredecessor]
      omega

/-- Even an empty charged alphabet costs a factor `26` per product-aware transition.  This is the
alphabet-independent floor hidden by positivity of the tail in the first-round audit. -/
theorem leastFiniteProductAwareBudget_baseline_lower
    (d : ℕ) (actualKeys : ℕ → ℕ) (terminal : ℕ) :
    26 ^ d * terminal ≤ leastFiniteProductAwareBudget d actualKeys terminal := by
  induction d generalizing actualKeys with
  | zero => simp
  | succ d ih =>
      rw [leastFiniteProductAwareBudget_succ, leastProductAwarePredecessor_eq, pow_succ]
      calc
        26 ^ d * 26 * terminal = 26 * (26 ^ d * terminal) := by ring
        _ ≤ 26 * leastFiniteProductAwareBudget d
            (fun i => actualKeys (i + 1)) terminal := Nat.mul_le_mul_left 26 (ih _)
        _ ≤ (24 * actualKeys 1 + 26) *
            leastFiniteProductAwareBudget d (fun i => actualKeys (i + 1)) terminal := by
          gcongr
          omega

/-- Exact calibration of the smallest corrected transition.  With one incoming bottom gate,
the proved residual-zero ragged cap is four keys.  Keeping one unit of survivor parameter in the
next round requires current parameter `122`, hence an initial shell of `2440` stars—not `80`. -/
theorem leastProductAwarePredecessor_one_shallow_gate :
    leastProductAwarePredecessor (layeredRoundActualKeyCap 1 0) 1 = 122 := by
  norm_num [leastProductAwarePredecessor, ceilDensityBudget, nextRoundProductDemand,
    layeredRoundActualKeyCap]

theorem leastProductAwareInitialShell_one_shallow_gate :
    20 * leastProductAwarePredecessor (layeredRoundActualKeyCap 1 0) 1 = 2440 := by
  rw [leastProductAwarePredecessor_one_shallow_gate]

/-- The circuit-owned density premise cannot even start when the bottom-slot envelope is at least
the ambient dimension.  This preserves the first broad incompatible regime explicitly: the
present actual-margin theorem requires a genuinely sparse initial bottom layer, not merely a
polynomial-size one. -/
theorem nextRoundActualMargin_not_le_ambient_of_ambient_le_slots
    (r n M : ℕ) (hnM : n ≤ M) : ¬ nextRoundActualMargin r M ≤ n := by
  have hr : 2 ≤ r + 2 := by omega
  have hp : 2 ≤ 2 ^ (r + 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ r + 1)
  have hlower : 32 * M + 8 ≤ nextRoundActualMargin r M := by
    simp only [nextRoundActualMargin]
    apply Nat.add_le_add
    · calc
        32 * M = 8 * 2 * M * 2 := by ring
        _ ≤ 8 * (r + 2) * M * 2 ^ (r + 1) := by gcongr
    · omega
  omega

/-- Forward worst-case slot envelope generated by successive residual-depth bounds. -/
def iteratedSlotBound (M₀ : ℕ) (residual : ℕ → ℕ) : ℕ → ℕ
  | 0 => M₀
  | i + 1 => iteratedSlotBound M₀ residual i * (2 ^ (residual i + 1) + 1)

@[simp] theorem iteratedSlotBound_zero (M₀ : ℕ) (residual : ℕ → ℕ) :
    iteratedSlotBound M₀ residual 0 = M₀ := rfl

@[simp] theorem iteratedSlotBound_succ (M₀ : ℕ) (residual : ℕ → ℕ) (i : ℕ) :
    iteratedSlotBound M₀ residual (i + 1) =
      iteratedSlotBound M₀ residual i * (2 ^ (residual i + 1) + 1) := rfl

/-- Closed forward slot envelope for the quantitatively cheapest choice, residual depth zero at
every round. -/
def shallowSlotBound (M : ℕ) (i : ℕ) : ℕ := M * 3 ^ i

@[simp] theorem shallowSlotBound_zero (M : ℕ) : shallowSlotBound M 0 = M := by
  simp [shallowSlotBound]

theorem shallowSlotBound_succ (M i : ℕ) :
    shallowSlotBound M (i + 1) = shallowSlotBound (M * 3) i := by
  simp [shallowSlotBound, pow_succ]
  ring

/-- At residual depth zero the exact forward recurrence is `M_i = M₀ * 3^i`. -/
theorem iteratedSlotBound_zero_residual (M i : ℕ) :
    iteratedSlotBound M (fun _ => 0) i = shallowSlotBound M i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [iteratedSlotBound_succ, ih, shallowSlotBound_succ]
      simp only [shallowSlotBound]
      ring

/-- Forward ragged-key cap generated by the cheapest verified slot recurrence.  Transition `i`
charges the collapse of `M_i = M₀*3^i`, so its successor key is stored at index `i+1`. -/
def shallowForwardActualKeys (M₀ : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => layeredRoundActualKeyCap (shallowSlotBound M₀ i) 0

/-- Closed multiplicative form of the shallow product-aware recurrence.  At round `i`, the
forward slot envelope has acquired the factor `3^i`, so the backward survivor is multiplied by
the affine factor `96*M_i+26`. -/
def shallowProductBudget : ℕ → ℕ → ℕ → ℕ
  | 0, _, terminal => terminal
  | d + 1, M, terminal =>
      (96 * M + 26) * shallowProductBudget d (M * 3) terminal

/-- Any key sequence with the exact shallow forward values computes the closed product budget.
This formulation makes the index shift explicit and can also be reused for extensionally equal
key schedules. -/
theorem leastFiniteProductAwareBudget_eq_shallowProductBudget_of_keys
    (d : ℕ) (actualKeys : ℕ → ℕ) (M terminal : ℕ)
    (hkeys : ∀ i < d, actualKeys (i + 1) = 4 * M * 3 ^ i) :
    leastFiniteProductAwareBudget d actualKeys terminal =
      shallowProductBudget d M terminal := by
  induction d generalizing actualKeys M with
  | zero => rfl
  | succ d ih =>
      rw [leastFiniteProductAwareBudget_succ, leastProductAwarePredecessor_eq,
        hkeys 0 (by omega)]
      simp only [pow_zero, mul_one]
      rw [show 24 * (4 * M) + 26 = 96 * M + 26 by ring]
      simp only [shallowProductBudget]
      congr 1
      apply ih
      intro i hi
      rw [hkeys (i + 1) (by omega), pow_succ]
      ring

/-- The forward-specialized least budget is exactly the affine product recurrence, for arbitrary
depth, initial bottom-slot envelope, and terminal survivor. -/
theorem leastFiniteProductAwareBudget_shallowForward_eq
    (d M terminal : ℕ) :
    leastFiniteProductAwareBudget d (shallowForwardActualKeys M) terminal =
      shallowProductBudget d M terminal := by
  apply leastFiniteProductAwareBudget_eq_shallowProductBudget_of_keys
  intro i _hi
  simp [shallowForwardActualKeys, layeredRoundActualKeyCap, shallowSlotBound]
  ring

/-- Degree-`d` lower envelope in the initial slot parameter.  The exact recurrence is at least
the product of `d` copies of its first round's homogeneous term. -/
theorem shallowProductBudget_lower (d M terminal : ℕ) :
    (96 * M) ^ d * terminal ≤ shallowProductBudget d M terminal := by
  induction d generalizing M with
  | zero => simp [shallowProductBudget]
  | succ d ih =>
      simp only [shallowProductBudget, pow_succ]
      calc
        (96 * M) ^ d * (96 * M) * terminal =
            (96 * M) * ((96 * M) ^ d * terminal) := by ring
        _ ≤ (96 * M + 26) * shallowProductBudget d (M * 3) terminal := by
          apply Nat.mul_le_mul (by omega)
          exact (Nat.mul_le_mul_right terminal
            (Nat.pow_le_pow_left (by nlinarith : 96 * M ≤ 96 * (M * 3)) d)).trans
              (ih (M * 3))

/-- Matching degree-`d` upper envelope for fixed depth.  Every affine round factor is bounded by
the final forward slot scale, so no hidden super-polynomial dependence on `M` occurs when `d` is
fixed. -/
theorem shallowProductBudget_upper (d M terminal : ℕ) :
    shallowProductBudget d M terminal ≤
      (96 * M * 3 ^ d + 26) ^ d * terminal := by
  induction d generalizing M with
  | zero => simp [shallowProductBudget]
  | succ d ih =>
      simp only [shallowProductBudget]
      have htail := ih (M * 3)
      have hbase : 96 * (M * 3) * 3 ^ d + 26 =
          96 * M * 3 ^ (d + 1) + 26 := by
        rw [pow_succ]
        ring
      rw [hbase] at htail
      rw [pow_succ]
      have hfactor : 96 * M + 26 ≤ 96 * M * 3 ^ (d + 1) + 26 := by
        have hpow : 1 ≤ 3 ^ (d + 1) := one_le_pow₀ (by omega)
        nlinarith
      calc
        (96 * M + 26) * shallowProductBudget d (M * 3) terminal ≤
            (96 * M * 3 ^ (d + 1) + 26) *
              ((96 * M * 3 ^ (d + 1) + 26) ^ d * terminal) :=
          Nat.mul_le_mul hfactor htail
        _ = (96 * M * 3 ^ (d + 1) + 26) ^ d *
              (96 * M * 3 ^ (d + 1) + 26) * terminal := by ring

/-- Direct lower bound on the actual round-zero shell demanded by the forward-specialized
schedule.  This is the comparison quantity that must fit both the original ambient dimension and
the rebuild fuel. -/
theorem leastFiniteProductAwareInitialShell_shallow_lower (d M terminal : ℕ) :
    20 * ((96 * M) ^ d * terminal) ≤
      20 * leastFiniteProductAwareBudget d (shallowForwardActualKeys M) terminal := by
  rw [leastFiniteProductAwareBudget_shallowForward_eq]
  exact Nat.mul_le_mul_left 20 (shallowProductBudget_lower d M terminal)

/-- Consequently, an ambient cube below the homogeneous degree-`d` floor cannot host this
whole-family product-aware iteration. -/
theorem shallowProductAwareSchedule_not_fit_of_ambient_lt
    {d M terminal n : ℕ} (hn : n < 20 * ((96 * M) ^ d * terminal)) :
    ¬20 * leastFiniteProductAwareBudget d (shallowForwardActualKeys M) terminal ≤ n := by
  intro hfit
  have hle := (leastFiniteProductAwareInitialShell_shallow_lower d M terminal).trans hfit
  omega

/-- A positive-depth whole-family run cannot fit if its chosen round-zero bottom-slot envelope is
already at least the ambient dimension.  This is a statement about using such an envelope in the
verified schedule: it does not assert that every circuit has linearly many bottom gates. -/
theorem shallowProductAwareSchedule_not_fit_of_ambient_le_slots
    {d M terminal n : ℕ} (hd : 0 < d) (hterminal : 0 < terminal) (hnM : n ≤ M) :
    ¬20 * leastFiniteProductAwareBudget d (shallowForwardActualKeys M) terminal ≤ n := by
  by_cases hn : n = 0
  · subst n
    have hbudget := leastFiniteProductAwareBudget_pos d (shallowForwardActualKeys M) hterminal
    omega
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hMpos : 0 < M := hnpos.trans_le hnM
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    have hpow : 1 ≤ (96 * M) ^ e := one_le_pow₀ (by omega)
    apply shallowProductAwareSchedule_not_fit_of_ambient_lt
    rw [pow_succ]
    calc
      n ≤ M := hnM
      _ < 96 * M := by omega
      _ = 1 * (96 * M) * 1 := by ring
      _ ≤ (96 * M) ^ e * (96 * M) * terminal := by
        exact Nat.mul_le_mul (Nat.mul_le_mul hpow (le_refl _)) (by omega)
      _ ≤ 20 * ((96 * M) ^ e * (96 * M) * terminal) :=
        Nat.le_mul_of_pos_left _ (by omega)

/-- The actual escape window is much narrower than `M < n`: at positive depth and with a
positive terminal survivor, the schedule already fails whenever the ambient dimension is at most
the `d`th power of the round-zero slot envelope.  Thus a circuit-specific replacement must be
strictly `d`th-root sparse before constants are even considered. -/
theorem shallowProductAwareSchedule_not_fit_of_ambient_le_slots_pow
    {d M terminal n : ℕ} (hd : 0 < d) (hterminal : 0 < terminal) (hnM : n ≤ M ^ d) :
    ¬20 * leastFiniteProductAwareBudget d (shallowForwardActualKeys M) terminal ≤ n := by
  by_cases hM : M = 0
  · subst M
    have hdpow : 0 ^ d = 0 := Nat.zero_pow hd
    rw [hdpow] at hnM
    have hbudget := leastFiniteProductAwareBudget_pos d (shallowForwardActualKeys 0) hterminal
    omega
  · apply shallowProductAwareSchedule_not_fit_of_ambient_lt
    have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have hbase : M ≤ 96 * M := by omega
    have hpow : M ^ d ≤ (96 * M) ^ d := Nat.pow_le_pow_left hbase d
    have hscaledPos : 0 < (96 * M) ^ d * terminal :=
      Nat.mul_pos (pow_pos (by omega) d) hterminal
    calc
      n ≤ M ^ d := hnM
      _ ≤ (96 * M) ^ d := hpow
      _ ≤ (96 * M) ^ d * terminal := Nat.le_mul_of_pos_right _ hterminal
      _ < 20 * ((96 * M) ^ d * terminal) := by omega

/-- Necessary sparsity condition for every fitting positive-depth schedule.  It is the direct
contrapositive of the power obstruction and exposes the quantitative target for any proposed
semantics-preserving circuit-specific reduction. -/
theorem slots_pow_lt_ambient_of_shallowProductAwareSchedule_fit
    {d M terminal n : ℕ} (hd : 0 < d) (hterminal : 0 < terminal)
    (hfit : 20 * leastFiniteProductAwareBudget d (shallowForwardActualKeys M) terminal ≤ n) :
    M ^ d < n := by
  by_contra hnot
  exact shallowProductAwareSchedule_not_fit_of_ambient_le_slots_pow hd hterminal
    (Nat.le_of_not_gt hnot) hfit

/-- In particular, the standard uniform polynomial slot envelope `M = n^k` is incompatible with
the present whole-family product-aware iteration at every positive depth and positive terminal
survivor, on every nonempty ambient cube.  Smaller circuit-specific envelopes remain outside this
obstruction. -/
theorem shallowProductAwareSchedule_not_fit_of_polynomial_slot_envelope
    {d k terminal n : ℕ} (hd : 0 < d) (hk : 0 < k) (hterminal : 0 < terminal)
    (hn : 0 < n) :
    ¬20 * leastFiniteProductAwareBudget d (shallowForwardActualKeys (n ^ k)) terminal ≤ n := by
  apply shallowProductAwareSchedule_not_fit_of_ambient_le_slots hd hterminal
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [pow_succ]
  have hpow : 1 ≤ n ^ e := one_le_pow₀ hn
  nlinarith

/-- Every width-two layered representative of parity (up to a fixed output phase) has a linear
bottom-slot floor.  This is circuit-specific rather than an external size envelope: full semantic
support costs at most two variables per bottom-clause occurrence, and occurrences are bounded by
the actual slot count. -/
theorem widthTwoParity_ambient_le_two_mul_bottomSlotCount
    {n : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase) :
    n ≤ 2 * bottomSlotCount C := by
  calc
    n = (layeredBottomVariableSupport C).card :=
      (Layered.bottomSupport_card_eq_of_eval_eq_parity_xor C phase hparity).symm
    _ ≤ 2 * bottomClauseCount C := layeredBottomVariableSupport_card_le hw
    _ ≤ 2 * bottomSlotCount C :=
      Nat.mul_le_mul_left 2 (bottomClauseCount_le_bottomSlotCount C)

/-- The exact whole-family product-aware schedule is incompatible with every width-two parity
representative at every positive iteration depth, even when it charges the circuit's actual
bottom-slot count instead of a worst-case polynomial envelope.  The semantic linear slot floor
already exceeds the schedule's much smaller constant-adjusted escape window. -/
theorem widthTwoParity_shallowProductAwareSchedule_not_fit
    {n d terminal : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hd : 0 < d) (hterminal : 0 < terminal) :
    ¬20 * leastFiniteProductAwareBudget d
      (shallowForwardActualKeys (bottomSlotCount C)) terminal ≤ n := by
  by_cases hn : n = 0
  · subst n
    have hbudget := leastFiniteProductAwareBudget_pos d
      (shallowForwardActualKeys (bottomSlotCount C)) hterminal
    omega
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hlinear := widthTwoParity_ambient_le_two_mul_bottomSlotCount C phase hw hparity
    have hslots : 0 < bottomSlotCount C := by omega
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    apply shallowProductAwareSchedule_not_fit_of_ambient_lt
    rw [pow_succ]
    have hpow : 1 ≤ (96 * bottomSlotCount C) ^ e := one_le_pow₀ (by omega)
    calc
      n ≤ 2 * bottomSlotCount C := hlinear
      _ < 20 * (96 * bottomSlotCount C) := by omega
      _ = 20 * (1 * (96 * bottomSlotCount C) * 1) := by ring
      _ ≤ 20 *
          ((96 * bottomSlotCount C) ^ e * (96 * bottomSlotCount C) * terminal) := by
        exact Nat.mul_le_mul_left 20
          (Nat.mul_le_mul (Nat.mul_le_mul hpow (le_refl _)) (by omega))

/-- Any product-aware schedule for width-two parity, even with an arbitrary future key sequence,
must compress the first-round alphabet by more than the full density constant.  If `A` is the
first charged alphabet and `M` is the circuit's actual bottom-slot count, fitting even one positive
round forces `240*A + 260 ≤ M`.  This isolates the quantitative target for a replacement encoder:
merely reducing the current constant multiple of `M` is insufficient. -/
theorem widthTwoParity_firstKey_compression_of_productAwareSchedule_fit
    {n d terminal : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hd : 0 < d) (hterminal : 0 < terminal)
    (actualKeys : ℕ → ℕ)
    (hfit : 20 * leastFiniteProductAwareBudget d actualKeys terminal ≤ n) :
    240 * actualKeys 1 + 260 ≤ bottomSlotCount C := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have htail : 0 < leastFiniteProductAwareBudget e
      (fun i => actualKeys (i + 1)) terminal :=
    leastFiniteProductAwareBudget_pos e (fun i => actualKeys (i + 1)) hterminal
  have hfirst : 20 * (24 * actualKeys 1 + 26) ≤ n := by
    calc
      20 * (24 * actualKeys 1 + 26) ≤
          20 * ((24 * actualKeys 1 + 26) *
            leastFiniteProductAwareBudget e
              (fun i => actualKeys (i + 1)) terminal) := by
        exact Nat.mul_le_mul_left 20 (Nat.le_mul_of_pos_right _ htail)
      _ = 20 * leastFiniteProductAwareBudget (e + 1) actualKeys terminal := by
        rw [leastFiniteProductAwareBudget_succ, leastProductAwarePredecessor_eq]
      _ ≤ n := hfit
  have hsupport := widthTwoParity_ambient_le_two_mul_bottomSlotCount C phase hw hparity
  omega

/-- Exact tail-sensitive strengthening of the first-key threshold.  If `B` is the least budget
still required after the first transition, fitting width-two parity forces
`(240*A + 260) * B ≤ M`.  The earlier `240*A + 260 ≤ M` bound is the special consequence `B ≥ 1`;
this form retains all later-round expenditure. -/
theorem widthTwoParity_firstKey_tail_budget_of_productAwareSchedule_fit
    {n d terminal : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hd : 0 < d)
    (actualKeys : ℕ → ℕ)
    (hfit : 20 * leastFiniteProductAwareBudget d actualKeys terminal ≤ n) :
    (240 * actualKeys 1 + 260) *
        leastFiniteProductAwareBudget (d - 1) (fun i => actualKeys (i + 1)) terminal ≤
      bottomSlotCount C := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have htotal :
      20 * ((24 * actualKeys 1 + 26) *
        leastFiniteProductAwareBudget e (fun i => actualKeys (i + 1)) terminal) ≤ n := by
    simpa only [leastFiniteProductAwareBudget_succ, leastProductAwarePredecessor_eq] using hfit
  have hsupport := widthTwoParity_ambient_le_two_mul_bottomSlotCount C phase hw hparity
  have hdouble :
      2 * (10 * ((24 * actualKeys 1 + 26) *
        leastFiniteProductAwareBudget e (fun i => actualKeys (i + 1)) terminal)) ≤
        2 * bottomSlotCount C := by
    calc
      2 * (10 * ((24 * actualKeys 1 + 26) *
          leastFiniteProductAwareBudget e (fun i => actualKeys (i + 1)) terminal)) =
          20 * ((24 * actualKeys 1 + 26) *
            leastFiniteProductAwareBudget e (fun i => actualKeys (i + 1)) terminal) := by ring
      _ ≤ n := htotal
      _ ≤ 2 * bottomSlotCount C := hsupport
  have hcancel := Nat.le_of_mul_le_mul_left hdouble (by omega : 0 < 2)
  simpa only [Nat.add_sub_cancel] using (show
    (240 * actualKeys 1 + 260) *
        leastFiniteProductAwareBudget e (fun i => actualKeys (i + 1)) terminal ≤
      bottomSlotCount C by
    calc
      (240 * actualKeys 1 + 260) *
          leastFiniteProductAwareBudget e (fun i => actualKeys (i + 1)) terminal =
          10 * ((24 * actualKeys 1 + 26) *
            leastFiniteProductAwareBudget e (fun i => actualKeys (i + 1)) terminal) := by ring
      _ ≤ bottomSlotCount C := hcancel)

/-- Round-count form of the tail-sensitive threshold.  Independently of every later alphabet,
`d` positive rounds and terminal survivor `T` force the first alphabet to fit after multiplication
by the unavoidable baseline tail `26^(d-1) * T`. -/
theorem widthTwoParity_firstKey_depth_compression_of_productAwareSchedule_fit
    {n d terminal : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hd : 0 < d)
    (actualKeys : ℕ → ℕ)
    (hfit : 20 * leastFiniteProductAwareBudget d actualKeys terminal ≤ n) :
    (240 * actualKeys 1 + 260) * (26 ^ (d - 1) * terminal) ≤ bottomSlotCount C := by
  have htail := leastFiniteProductAwareBudget_baseline_lower
    (d - 1) (fun i => actualKeys (i + 1)) terminal
  exact (Nat.mul_le_mul_left (240 * actualKeys 1 + 260) htail).trans
    (widthTwoParity_firstKey_tail_budget_of_productAwareSchedule_fit
      C phase hw hparity hd actualKeys hfit)

/-- Alphabet-independent contrapositive of the depth-sensitive threshold.  Even granting the
proposed conditioned encoder an empty first alphabet, the product-demand form cannot fit unless
the actual bottom-slot count pays the additive transition floor through every remaining round. -/
theorem widthTwoParity_productAwareSchedule_not_fit_of_depth_baseline
    {n d terminal : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hd : 0 < d)
    (actualKeys : ℕ → ℕ)
    (hsmall : bottomSlotCount C < 260 * (26 ^ (d - 1) * terminal)) :
    ¬20 * leastFiniteProductAwareBudget d actualKeys terminal ≤ n := by
  intro hfit
  have hnecessary :=
    widthTwoParity_firstKey_depth_compression_of_productAwareSchedule_fit
      C phase hw hparity hd actualKeys hfit
  have hbaseline : 260 * (26 ^ (d - 1) * terminal) ≤
      (240 * actualKeys 1 + 260) * (26 ^ (d - 1) * terminal) := by
    exact Nat.mul_le_mul_right _ (by omega)
  omega

/-- If a sound conditioned first-round code is known merely to have at least one label, its exact
depth-sensitive floor rises from `260` to `500`.  This theorem deliberately assumes only
nonemptiness of the charged alphabet and no occurrence-sensitive lower bound. -/
theorem widthTwoParity_productAwareSchedule_not_fit_of_positive_firstKey
    {n d terminal : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hd : 0 < d)
    (actualKeys : ℕ → ℕ)
    (hkey : 0 < actualKeys 1)
    (hsmall : bottomSlotCount C < 500 * (26 ^ (d - 1) * terminal)) :
    ¬20 * leastFiniteProductAwareBudget d actualKeys terminal ≤ n := by
  intro hfit
  have hnecessary :=
    widthTwoParity_firstKey_depth_compression_of_productAwareSchedule_fit
      C phase hw hparity hd actualKeys hfit
  have hpositive : 500 * (26 ^ (d - 1) * terminal) ≤
      (240 * actualKeys 1 + 260) * (26 ^ (d - 1) * terminal) := by
    exact Nat.mul_le_mul_right _ (by omega)
  omega

/-- Circuit-level conditioned-code specialization of the positive-alphabet obstruction.  Once a
decoder-sound code is supplied for a nonempty actual bad-root set and its label cardinality is the
first charged alphabet, the stronger `500` floor follows without any additional assumption about
the encoder. -/
theorem widthTwoParity_conditionedCodeSchedule_not_fit_of_nonempty_bad
    {n d terminal : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hd : 0 < d)
    (bad : Finset (Restriction n)) (code : ConditionedFirstRoundCode bad)
    (hbad : bad.Nonempty)
    (actualKeys : ℕ → ℕ)
    (hfirst : actualKeys 1 = code.labelCard)
    (hsmall : bottomSlotCount C < 500 * (26 ^ (d - 1) * terminal)) :
    ¬20 * leastFiniteProductAwareBudget d actualKeys terminal ≤ n := by
  apply widthTwoParity_productAwareSchedule_not_fit_of_positive_firstKey
    C phase hw hparity hd actualKeys
  · rw [hfirst]
    exact code.labelCard_pos_of_bad_nonempty hbad
  · exact hsmall

/-- Exact depth-sensitive obligation for the existing ragged symmetric-prefix construction.
Unlike the abstract nonempty-code floor, this substitutes the full concrete ambient label
cardinality into the first charged alphabet.  It does not claim that the ambient alphabet is
optimal: endpoint-local realized label images may be smaller. -/
theorem widthTwoParity_commonShallowBadPrefixCode_firstKey_bound
    {n d terminal G w fuel K prefixDepth residualDepth : ℕ}
    (C : Layered n) (phase : Bool)
    (hwC : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hd : 0 < d)
    (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel)
    (actualKeys : ℕ → ℕ)
    (hfirst : actualKeys 1 =
      (ConditionedFirstRoundCode.commonShallowBadPrefixCode
        (d := prefixDepth) (residualDepth := residualDepth) gates hnd hw hKfuel).labelCard)
    (hfit : 20 * leastFiniteProductAwareBudget d actualKeys terminal ≤ n) :
    (240 * ((w + 1) ^ prefixDepth *
        (((∑ g, (gates g).length) + prefixDepth - 1).choose prefixDepth + 1)) + 260) *
      (26 ^ (d - 1) * terminal) ≤ bottomSlotCount C := by
  rw [← ConditionedFirstRoundCode.commonShallowBadPrefixCode_labelCard
    gates hnd hw hKfuel, ← hfirst]
  exact widthTwoParity_firstKey_depth_compression_of_productAwareSchedule_fit
    C phase hwC hparity hd actualKeys hfit

/-- Exact depth-sensitive obligation after removing every unused ambient ragged-prefix label.
This tests the cardinality of the global realized-label image itself; no ambient stars-and-bars
alphabet remains in the bound. -/
theorem widthTwoParity_commonShallowBadRealizedPrefixCode_firstKey_bound
    {n d terminal G w fuel K prefixDepth residualDepth : ℕ}
    (C : Layered n) (phase : Bool)
    (hwC : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hd : 0 < d)
    (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel)
    (actualKeys : ℕ → ℕ)
    (hfirst : actualKeys 1 =
      (ConditionedFirstRoundCode.commonShallowBadRealizedPrefixCode
        (d := prefixDepth) (residualDepth := residualDepth)
        gates hnd hw hKfuel).labelCard)
    (hfit : 20 * leastFiniteProductAwareBudget d actualKeys terminal ≤ n) :
    (240 *
        (ConditionedFirstRoundCode.commonShallowBadPrefixCode
          (d := prefixDepth) (residualDepth := residualDepth)
          gates hnd hw hKfuel).realizedLabelImage.card + 260) *
      (26 ^ (d - 1) * terminal) ≤ bottomSlotCount C := by
  rw [← ConditionedFirstRoundCode.commonShallowBadRealizedPrefixCode_labelCard
    gates hnd hw hKfuel, ← hfirst]
  exact widthTwoParity_firstKey_depth_compression_of_productAwareSchedule_fit
    C phase hwC hparity hd actualKeys hfit

/-- Exact depth-sensitive obligation for the optimal endpoint-conditioned first-round alphabet.
The maximum fiber is both achievable by independent endpoint-local reindexing and necessary for
every decoder-sound code retaining this endpoint map. -/
theorem widthTwoParity_commonShallowBadMaxFiberPrefixCode_firstKey_bound
    {n d terminal G w fuel K prefixDepth residualDepth : ℕ}
    (C : Layered n) (phase : Bool)
    (hwC : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hd : 0 < d)
    (gates : Fin G → List (Clause n))
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel)
    (actualKeys : ℕ → ℕ)
    (hfirst : actualKeys 1 =
      (ConditionedFirstRoundCode.commonShallowBadMaxFiberPrefixCode
        (d := prefixDepth) (residualDepth := residualDepth)
        gates hnd hw hKfuel).labelCard)
    (hfit : 20 * leastFiniteProductAwareBudget d actualKeys terminal ≤ n) :
    (240 *
        (ConditionedFirstRoundCode.commonShallowBadPrefixCode
          (d := prefixDepth) (residualDepth := residualDepth)
          gates hnd hw hKfuel).maxRealizedEndpointFiberCard + 260) *
      (26 ^ (d - 1) * terminal) ≤ bottomSlotCount C := by
  rw [← ConditionedFirstRoundCode.commonShallowBadMaxFiberPrefixCode_labelCard
    gates hnd hw hKfuel, ← hfirst]
  exact widthTwoParity_firstKey_depth_compression_of_productAwareSchedule_fit
    C phase hwC hparity hd actualKeys hfit

/-- Circuit-specialized acceptance audit for the normalized width-two parity first round.  Every
realized endpoint's exact filtered candidate count must satisfy the depth-sensitive first-key
budget whenever the product-aware schedule fits.  Thus a concrete endpoint whose accepted
`prefixDepth`-subsets exceed this bound is already a complete obstruction to the present schedule;
no ambient stars-and-bars alphabet enters the statement. -/
theorem widthTwoParity_normalizedCandidateSets_firstKey_bound
    {n rounds terminal fuel K prefixDepth residualDepth : ℕ}
    (C : Layered n) (phase : Bool)
    (hwC : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hrounds : 0 < rounds) (hKfuel : K ≤ fuel)
    (actualKeys : ℕ → ℕ)
    (hfirst : actualKeys 1 =
      (ConditionedFirstRoundCode.commonShallowBadMaxFiberPrefixCode
        (d := prefixDepth) (residualDepth := residualDepth)
        (normalizedLayeredBottomFamily C)
        (normalizedLayeredBottomFamily_nodup C)
        (normalizedLayeredBottomFamily_width_le hwC) hKfuel).labelCard)
    (hfit : 20 * leastFiniteProductAwareBudget rounds actualKeys terminal ≤ n)
    (root : ↑(commonShallowBad (normalizedLayeredBottomFamily C)
      fuel K prefixDepth residualDepth)) :
    (240 *
        (ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets
          (normalizedLayeredBottomFamily C)
          fuel K prefixDepth residualDepth
          ((ConditionedFirstRoundCode.commonShallowBadPrefixCode
            (d := prefixDepth) (residualDepth := residualDepth)
            (normalizedLayeredBottomFamily C)
            (normalizedLayeredBottomFamily_nodup C)
            (normalizedLayeredBottomFamily_width_le hwC) hKfuel).endpoint root)).card + 260) *
      (26 ^ (rounds - 1) * terminal) ≤ bottomSlotCount C := by
  let code := ConditionedFirstRoundCode.commonShallowBadPrefixCode
    (d := prefixDepth) (residualDepth := residualDepth)
    (normalizedLayeredBottomFamily C)
    (normalizedLayeredBottomFamily_nodup C)
    (normalizedLayeredBottomFamily_width_le hwC) hKfuel
  have hcandidates :
      (ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets
        (normalizedLayeredBottomFamily C)
        fuel K prefixDepth residualDepth (code.endpoint root)).card ≤
        code.maxRealizedEndpointFiberCard := by
    rw [ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets_card_eq_endpointFiberCard
      (normalizedLayeredBottomFamily C)
      (normalizedLayeredBottomFamily_nodup C)
      (normalizedLayeredBottomFamily_width_le hwC) hKfuel]
    exact code.endpointFiberCard_le_maxRealized root
  have hmax := widthTwoParity_commonShallowBadMaxFiberPrefixCode_firstKey_bound
    C phase hwC hparity hrounds
    (normalizedLayeredBottomFamily C)
    (normalizedLayeredBottomFamily_nodup C)
    (normalizedLayeredBottomFamily_width_le hwC) hKfuel actualKeys hfirst hfit
  exact (Nat.mul_le_mul_right (26 ^ (rounds - 1) * terminal)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 240 hcandidates) 260)).trans hmax

/-- Witness form of the normalized acceptance audit.  An explicitly realized endpoint with too
many accepted candidate subsets refutes the current depth-sensitive product schedule. -/
theorem widthTwoParity_normalizedCandidateSets_not_fit_of_oversized
    {n rounds terminal fuel K prefixDepth residualDepth : ℕ}
    (C : Layered n) (phase : Bool)
    (hwC : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hrounds : 0 < rounds) (hKfuel : K ≤ fuel)
    (actualKeys : ℕ → ℕ)
    (hfirst : actualKeys 1 =
      (ConditionedFirstRoundCode.commonShallowBadMaxFiberPrefixCode
        (d := prefixDepth) (residualDepth := residualDepth)
        (normalizedLayeredBottomFamily C)
        (normalizedLayeredBottomFamily_nodup C)
        (normalizedLayeredBottomFamily_width_le hwC) hKfuel).labelCard)
    (root : ↑(commonShallowBad (normalizedLayeredBottomFamily C)
      fuel K prefixDepth residualDepth))
    (hlarge : bottomSlotCount C <
      (240 *
          (ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets
            (normalizedLayeredBottomFamily C)
            fuel K prefixDepth residualDepth
            ((ConditionedFirstRoundCode.commonShallowBadPrefixCode
              (d := prefixDepth) (residualDepth := residualDepth)
              (normalizedLayeredBottomFamily C)
              (normalizedLayeredBottomFamily_nodup C)
              (normalizedLayeredBottomFamily_width_le hwC) hKfuel).endpoint root)).card + 260) *
        (26 ^ (rounds - 1) * terminal)) :
    ¬20 * leastFiniteProductAwareBudget rounds actualKeys terminal ≤ n := by
  intro hfit
  exact (Nat.not_lt_of_ge
    (widthTwoParity_normalizedCandidateSets_firstKey_bound C phase hwC hparity
      hrounds hKfuel actualKeys hfirst hfit root)) hlarge

/-! ### A concrete normalized parity endpoint -/

/-- At ample fuel, a zero-depth canonical tree makes its DNF constant across the entire
restriction subcube.  This is the semantic fact needed to turn residual-depth-zero common
shallowness into a parity contradiction. -/
theorem dnfValue_eq_of_canonicalDT_depth_eq_zero {n fuel : ℕ}
    (cs : List (Clause n)) (rho : Restriction n) (hstars : stars rho ≤ fuel)
    (hdepth : (canonicalDT cs fuel rho).depth = 0)
    (x y : Fin n → Bool) (hx : Rung4Restriction.Extends rho x)
    (hy : Rung4Restriction.Extends rho y) :
    DTree.dnfValue cs x = DTree.dnfValue cs y := by
  have heval : (canonicalDT cs fuel rho).eval x = (canonicalDT cs fuel rho).eval y := by
    cases htree : canonicalDT cs fuel rho with
    | leaf b => rfl
    | query i lo hi =>
        rw [htree] at hdepth
        simp [BoolDecisionTree.depth] at hdepth
  rw [canonicalDT_eval fuel rho x hstars hx,
    canonicalDT_eval fuel rho y hstars hy, dnfEval_eq_dnfValue,
    dnfEval_eq_dnfValue] at heval
  exact heval

/-- If both polarities of every syntactic bottom gate have zero canonical depth, the whole
layered circuit is constant on the restriction subcube. -/
theorem Layered.eval_eq_of_bottom_canonicalDT_depth_eq_zero {n fuel : ℕ}
    (rho : Restriction n) (hstars : stars rho ≤ fuel)
    (x y : Fin n → Bool) (hx : Rung4Restriction.Extends rho x)
    (hy : Rung4Restriction.Extends rho y) :
    ∀ C : Layered n,
      (∀ cs ∈ bottomGates C,
        (canonicalDT cs fuel rho).depth = 0 ∧
          (canonicalDT (negDNF cs) fuel rho).depth = 0) →
      Layered.eval C x = Layered.eval C y
  | Layered.dnf cs, hzero => by
      rw [Layered.eval_dnf, Layered.eval_dnf]
      exact dnfValue_eq_of_canonicalDT_depth_eq_zero cs rho hstars
        (hzero cs (by simp [bottomGates])).1 x y hx hy
  | Layered.cnf cs, hzero => by
      rw [Layered.eval_cnf, Layered.eval_cnf,
        cnfValue_eq_not_dnfValue_negDNF, cnfValue_eq_not_dnfValue_negDNF]
      rw [dnfValue_eq_of_canonicalDT_depth_eq_zero (negDNF cs) rho hstars
        (hzero cs (by simp [bottomGates])).2 x y hx hy]
  | Layered.gAnd gs, hzero => by
      rw [Layered.eval_gAnd, Layered.eval_gAnd]
      apply list_all_apply_eq_of_forall_eq
      intro C hC
      apply Layered.eval_eq_of_bottom_canonicalDT_depth_eq_zero rho hstars x y hx hy C
      intro cs hcs
      exact hzero cs (bottomGates_mem_gAnd hC hcs)
  | Layered.gOr gs, hzero => by
      rw [Layered.eval_gOr, Layered.eval_gOr]
      apply list_any_apply_eq_of_forall_eq
      intro C hC
      apply Layered.eval_eq_of_bottom_canonicalDT_depth_eq_zero rho hstars x y hx hy C
      intro cs hcs
      exact hzero cs (bottomGates_mem_gOr hC hcs)

/-- Residual depth zero is uniformly impossible for parity whenever the common family covers both
polarities of every circuit bottom gate and the requested trunk is shorter than the live shell.
This isolates the exact representation interface used by the parity argument: the family need
not be the circuit-owned normalized indexing and no width bound is required. -/
theorem parity_mem_covered_commonShallowBad_zero
    {n G fuel K trunkDepth : ℕ} (gates : Fin G → List (Clause n))
    (C : Layered n) (phase : Bool) (hcovers : CoversLayeredBottoms gates C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K)
    (sigma : Restriction n) (hstars : stars sigma = K) :
    sigma ∈ commonShallowBad gates fuel K trunkDepth 0 := by
  rw [mem_commonShallowBad]
  refine ⟨hstars, ?_⟩
  intro hcommon
  let x : Fin n → Bool := fun i => (sigma i).getD false
  have hx : Rung4Restriction.Extends sigma x := by
    intro i b hi
    simp [x, hi]
  obtain ⟨trunk, hdepth, hleafData⟩ := hcommon
  let rho := CommonTree.run trunk x
  have hlive : stars sigma - trunkDepth ≤ stars rho := by
    exact CommonTree.stars_run_ge_sub_of_leaf_agreement trunk sigma trunkDepth x hx hdepth
      (fun z hz => (hleafData z hz).2.1)
  have hrhoStars : stars rho ≤ fuel := by
    exact (stars_le_of_restrictionExtends (hleafData x hx).1).trans
      (by simpa [hstars] using hKfuel)
  have hrhoPos : 0 < stars rho := by
    have : 0 < K - trunkDepth := by omega
    have hlive' : K - trunkDepth ≤ stars rho := by simpa [hstars] using hlive
    exact this.trans_le hlive'
  obtain ⟨j, hj⟩ : ∃ j, j ∈ freeVars rho := by
    exact Finset.card_pos.mp (by simpa [stars] using hrhoPos)
  let y : Fin n → Bool := Function.update x j (!x j)
  have hxrho : Rung4Restriction.Extends rho x := (hleafData x hx).2.1
  have hyrho : Rung4Restriction.Extends rho y := by
    intro i b hi
    have hij : i ≠ j := by
      intro hij
      subst i
      rw [mem_freeVars] at hj
      rw [hj] at hi
      simp at hi
    simpa [y, Function.update_of_ne hij] using hxrho i b hi
  have hzero : ∀ cs ∈ bottomGates C,
      (canonicalDT cs fuel rho).depth = 0 ∧
        (canonicalDT (negDNF cs) fuel rho).depth = 0 := by
    intro cs hcs
    obtain ⟨⟨g, hg⟩, ⟨gneg, hgneg⟩⟩ :=
      hcovers cs hcs
    constructor
    · rw [← hg fuel rho]
      exact Nat.eq_zero_of_le_zero ((hleafData x hx).2.2 g)
    · rw [← hgneg fuel rho]
      exact Nat.eq_zero_of_le_zero ((hleafData x hx).2.2 gneg)
  have heval : Layered.eval C x = Layered.eval C y :=
    Layered.eval_eq_of_bottom_canonicalDT_depth_eq_zero rho hrhoStars
      x y hxrho hyrho C hzero
  rw [hparity x, hparity y, DTree.parity_flip] at heval
  cases hp : DTree.parity x <;> cases phase <;> simp [hp] at heval

/-- The normalized circuit-owned family is the standard specialization of the general coverage
theorem. -/
theorem parity_mem_normalized_commonShallowBad_zero
    {n fuel K trunkDepth : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K)
    (sigma : Restriction n) (hstars : stars sigma = K) :
    sigma ∈ commonShallowBad (normalizedLayeredBottomFamily C)
      fuel K trunkDepth 0 := by
  exact parity_mem_covered_commonShallowBad_zero
    (normalizedLayeredBottomFamily C) C phase
    (normalizedLayeredBottomFamily_covers C) hparity hKfuel htrunk sigma hstars

/-- Any covering family has the entire exact shell as its residual-depth-zero parity bad event. -/
theorem parity_covered_commonShallowBad_zero_eq_shell
    {n G fuel K trunkDepth : ℕ} (gates : Fin G → List (Clause n))
    (C : Layered n) (phase : Bool) (hcovers : CoversLayeredBottoms gates C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K) :
    commonShallowBad gates fuel K trunkDepth 0 =
      Finset.univ.filter fun sigma : Restriction n => stars sigma = K := by
  ext sigma
  simp only [mem_commonShallowBad, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.1
  · intro hstars
    exact mem_commonShallowBad.mp
      (parity_mem_covered_commonShallowBad_zero gates C phase hcovers hparity
        hKfuel htrunk sigma hstars)

/-- Exact cardinality of the covering-family bad event. -/
theorem parity_covered_commonShallowBad_zero_card
    {n G fuel K trunkDepth : ℕ} (gates : Fin G → List (Clause n))
    (C : Layered n) (phase : Bool) (hcovers : CoversLayeredBottoms gates C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K) :
    (commonShallowBad gates fuel K trunkDepth 0).card =
      Nat.choose n K * 2 ^ (n - K) := by
  rw [parity_covered_commonShallowBad_zero_eq_shell gates C phase hcovers hparity
    hKfuel htrunk, card_stars_eq]

/-- Therefore, below the live dimension, the semantic bad event is the entire exact shell.  At
residual depth zero the filtered endpoint problem receives no acceptance-rate saving from
common-shallow badness itself; only the canonical-prefix endpoint equations can shrink a fiber. -/
theorem parity_normalized_commonShallowBad_zero_eq_shell
    {n fuel K trunkDepth : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K) :
    commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth 0 =
      Finset.univ.filter fun sigma : Restriction n => stars sigma = K := by
  ext sigma
  simp only [mem_commonShallowBad, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.1
  · intro hstars
    exact (mem_commonShallowBad.mp
      (parity_mem_normalized_commonShallowBad_zero C phase hparity hKfuel htrunk
        sigma hstars))

/-- Exact cardinal form of the full-shell obstruction. -/
theorem parity_normalized_commonShallowBad_zero_card
    {n fuel K trunkDepth : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth 0).card =
      Nat.choose n K * 2 ^ (n - K) := by
  rw [parity_normalized_commonShallowBad_zero_eq_shell C phase hparity hKfuel htrunk,
    card_stars_eq]

/-! ### Survivor conditioning can concentrate on the bad event -/

/-- The smallest natural assignment-covering survivor atlas with one prescribed live-coordinate
set.  It contains all Boolean settings of the fixed coordinates and no other live-set choice. -/
noncomputable def fixedFreeSetSurvivors {n : ℕ} (S : Finset (Fin n)) :
    Finset (Restriction n) := by
  classical
  exact Finset.univ.filter fun rho => freeVars rho = S

@[simp] theorem mem_fixedFreeSetSurvivors {n : ℕ} {S : Finset (Fin n)}
    {rho : Restriction n} :
    rho ∈ fixedFreeSetSurvivors S ↔ freeVars rho = S := by
  classical
  simp [fixedFreeSetSurvivors]

/-- The atlas pays only for the settings outside its one fixed live set. -/
theorem card_fixedFreeSetSurvivors {n : ℕ} (S : Finset (Fin n)) :
    (fixedFreeSetSurvivors S).card = 2 ^ (n - S.card) := by
  classical
  exact card_freeVars_eq S

/-- Despite using only one live-coordinate set, the atlas covers every total assignment: retain
`S` as live and copy the assignment on every coordinate outside `S`. -/
theorem fixedFreeSetSurvivors_covers_assignments {n : ℕ} (S : Finset (Fin n))
    (x : Fin n → Bool) :
    ∃ rho ∈ fixedFreeSetSurvivors S, DTree.agreeRestriction rho x := by
  let rho := restrictionWithFreeSet x S
  refine ⟨rho, ?_, agreeRestriction_restrictionWithFreeSet x S⟩
  rw [mem_fixedFreeSetSurvivors]
  exact freeVars_restrictionWithFreeSet x S

/-- For residual-depth-zero parity, every member of an assignment-covering fixed-free-set atlas is
bad.  Thus semantic coverage by survivors does not imply that the survivor population inherits
the good fraction of the uniform shell. -/
theorem fixedFreeSetSurvivors_subset_parity_normalized_commonShallowBad_zero
    {n fuel K trunkDepth : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K)
    (S : Finset (Fin n)) (hScard : S.card = K) :
    fixedFreeSetSurvivors S ⊆
      commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth 0 := by
  intro rho hrho
  apply parity_mem_normalized_commonShallowBad_zero C phase hparity hKfuel htrunk
  rw [stars, (mem_fixedFreeSetSurvivors.mp hrho), hScard]

/-- A full-shell contraction by `2^d` is numerically compatible with the entire selected survivor
atlas being bad whenever `2^d ≤ choose(n,K)`.  This is the precise conditioning gap: the binomial
live-set multiplicity can absorb the advertised shell saving while the selected atlas uses only
one live set. -/
theorem fixedFreeSetSurvivors_contraction_compatible
    {n K d : ℕ} (S : Finset (Fin n)) (hScard : S.card = K)
    (hchoose : 2 ^ d ≤ Nat.choose n K) :
    (fixedFreeSetSurvivors S).card * 2 ^ d ≤
      (Finset.univ.filter fun rho : Restriction n => stars rho = K).card := by
  rw [card_fixedFreeSetSurvivors, hScard, card_stars_eq]
  calc
    2 ^ (n - K) * 2 ^ d ≤ 2 ^ (n - K) * Nat.choose n K :=
      Nat.mul_le_mul_left _ hchoose
    _ = Nat.choose n K * 2 ^ (n - K) := by ring

/-- Concrete survivor-conditioning no-go package.  Even with assignment coverage and a valid
`2^d` global shell contraction, the selected survivor population may be wholly bad.  Any valid
transfer theorem therefore needs an additional anti-concentration or sampler property relating
the selector to the shell measure. -/
theorem parity_fixedFreeSet_survivor_conditioning_gap
    {n fuel K trunkDepth d : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K)
    (S : Finset (Fin n)) (hScard : S.card = K)
    (hchoose : 2 ^ d ≤ Nat.choose n K) :
    (∀ x : Fin n → Bool, ∃ rho ∈ fixedFreeSetSurvivors S,
        DTree.agreeRestriction rho x) ∧
    fixedFreeSetSurvivors S ⊆
      commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth 0 ∧
    (fixedFreeSetSurvivors S).card * 2 ^ d ≤
      (Finset.univ.filter fun rho : Restriction n => stars rho = K).card := by
  exact ⟨fixedFreeSetSurvivors_covers_assignments S,
    fixedFreeSetSurvivors_subset_parity_normalized_commonShallowBad_zero
      C phase hparity hKfuel htrunk S hScard,
    fixedFreeSetSurvivors_contraction_compatible S hScard hchoose⟩

/-- Encoder-independent first-alphabet balance for residual-depth-zero parity.  This applies to
any decoder-sound conditioned code on the full parity bad shell, provided only that its endpoints
have the live-variable count required of a `trunkDepth`-step round.  In particular, changing the
assignment or label representation cannot evade this population bound while preserving that
structural endpoint invariant. -/
theorem parity_normalized_labelCard_mul_endpointShell_lower
    {n fuel K trunkDepth : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K)
    (code : ConditionedFirstRoundCode
      (commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth 0))
    (hendpoint : ∀ root, stars (code.endpoint root) = K - trunkDepth) :
    Nat.choose n K * 2 ^ (n - K) ≤
      code.labelCard * (Nat.choose n (K - trunkDepth) *
        2 ^ (n - (K - trunkDepth))) := by
  have hcount := code.bad_card_le_labelCard_mul_endpointShell_card hendpoint
  rw [parity_normalized_commonShallowBad_zero_card C phase hparity hKfuel htrunk,
    card_stars_eq] at hcount
  exact hcount

/-- Cleared-denominator encoder-independent consequence of the parity shell balance.  Every
sound `trunkDepth`-step code must pay enough labels that `labelCard * (2*K)^trunkDepth` covers the
shell-growth numerator `(n-K+1)^trunkDepth`. -/
theorem parity_normalized_labelCard_power_lower
    {n fuel K trunkDepth : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K) (hKn : K ≤ n)
    (code : ConditionedFirstRoundCode
      (commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth 0))
    (hendpoint : ∀ root, stars (code.endpoint root) = K - trunkDepth) :
    (n - K + 1) ^ trunkDepth ≤ code.labelCard * (2 * K) ^ trunkDepth := by
  have hbalance := parity_normalized_labelCard_mul_endpointShell_lower
    C phase hparity hKfuel htrunk code hendpoint
  have hshell := shell_ratio_nat (n := n) K trunkDepth (by omega) hKn
  have hexponent : n - K + trunkDepth = n - (K - trunkDepth) := by omega
  rw [hexponent] at hshell
  have hendpointPos : 0 < Nat.choose n (K - trunkDepth) *
      2 ^ (n - (K - trunkDepth)) := by
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (pow_pos (by omega) _)
  apply Nat.le_of_mul_le_mul_left
    (c := Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth)))
    (hc := hendpointPos)
  calc
    (Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth))) *
          (n - K + 1) ^ trunkDepth ≤
        (Nat.choose n K * 2 ^ (n - K)) * (2 * K) ^ trunkDepth := hshell
    _ ≤ (code.labelCard *
          (Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth)))) *
          (2 * K) ^ trunkDepth := Nat.mul_le_mul_right _ hbalance
    _ = (Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth))) *
          (code.labelCard * (2 * K) ^ trunkDepth) := by ring

/-- Arithmetic core of the intended-density audit.  If a first-round alphabet satisfies the
encoder-independent shell-growth power balance at `n = 1000*A*r`, `K = 20*r`, and
`trunkDepth = 10*r`, then its one-step product-aware demand already exceeds the entire ambient
dimension.

The proof retains a deliberately coarse but robust quantitative consequence:
`240*A*r ≤ labelCard`.  It follows by comparing the shell numerator base with
`(24*A)*(40*r)`, raising to `10*r`, cancelling the positive `(40*r)^(10*r)` factor, and using
`a*b ≤ a^b` for `a = 24*A` and `b = 10*r`. -/
theorem intended_power_lower_forces_firstRoundDemand
    {A r labelCard : ℕ} (hA : 0 < A) (hr : 0 < r)
    (hpower :
      (1000 * A * r - 20 * r + 1) ^ (10 * r) ≤
        labelCard * (40 * r) ^ (10 * r)) :
    1000 * A * r < 20 * (24 * labelCard + 26) := by
  have hbase : (24 * A) * (40 * r) ≤ 1000 * A * r - 20 * r + 1 := by
    have hbefore : (24 * A) * (40 * r) + 20 * r ≤ 1000 * A * r := by
      nlinarith
    exact (Nat.le_sub_of_add_le hbefore).trans (Nat.le_add_right _ _)
  have hpowMul : ((24 * A) * (40 * r)) ^ (10 * r) ≤
      (1000 * A * r - 20 * r + 1) ^ (10 * r) :=
    Nat.pow_le_pow_left hbase _
  have hcancel : (24 * A) ^ (10 * r) * (40 * r) ^ (10 * r) ≤
      labelCard * (40 * r) ^ (10 * r) := by
    rw [← Nat.mul_pow]
    exact hpowMul.trans hpower
  have hfactor : 0 < (40 * r) ^ (10 * r) := by positivity
  have halphabet : (24 * A) ^ (10 * r) ≤ labelCard :=
    Nat.le_of_mul_le_mul_right hcancel hfactor
  have hgrowth : (24 * A) * (10 * r) ≤ (24 * A) ^ (10 * r) := by
    exact Nat.mul_le_pow (by omega) _
  have hlinear : 240 * A * r ≤ labelCard := by
    calc
      240 * A * r = (24 * A) * (10 * r) := by ring
      _ ≤ (24 * A) ^ (10 * r) := hgrowth
      _ ≤ labelCard := halphabet
  nlinarith

/-- Variable-expenditure form of the intended-density audit.  The original `10*r` is not the
source of the obstruction: every first round spending at least `r` live coordinates already has
an oversized effective alphabet.  Hence merely reducing the trunk from `10*r` to any `d ≥ r`
cannot make the recurrence fit. -/
theorem intended_variable_power_lower_forces_firstRoundDemand
    {A r d effectiveCard : ℕ} (hA : 0 < A) (hr : 0 < r) (hrd : r ≤ d)
    (hpower :
      (1000 * A * r - 20 * r + 1) ^ d ≤
        effectiveCard * (40 * r) ^ d) :
    1000 * A * r < 20 * (24 * effectiveCard + 26) := by
  have hbase : (24 * A) * (40 * r) ≤ 1000 * A * r - 20 * r + 1 := by
    have hbefore : (24 * A) * (40 * r) + 20 * r ≤ 1000 * A * r := by
      nlinarith
    exact (Nat.le_sub_of_add_le hbefore).trans (Nat.le_add_right _ _)
  have hpowMul : ((24 * A) * (40 * r)) ^ d ≤
      (1000 * A * r - 20 * r + 1) ^ d :=
    Nat.pow_le_pow_left hbase _
  have hcancel : (24 * A) ^ d * (40 * r) ^ d ≤
      effectiveCard * (40 * r) ^ d := by
    rw [← Nat.mul_pow]
    exact hpowMul.trans hpower
  have hfactor : 0 < (40 * r) ^ d := by positivity
  have halphabet : (24 * A) ^ d ≤ effectiveCard :=
    Nat.le_of_mul_le_mul_right hcancel hfactor
  have hgrowth : (24 * A) * d ≤ (24 * A) ^ d := by
    exact Nat.mul_le_pow (by omega) _
  have hlinear : 24 * A * r ≤ effectiveCard := by
    calc
      24 * A * r ≤ (24 * A) * d := by nlinarith
      _ ≤ (24 * A) ^ d := hgrowth
      _ ≤ effectiveCard := halphabet
  nlinarith

/-- Encoder-independent resolution of the intended first-round comparison.  Every decoder-sound
code for the full residual-zero parity bad shell whose endpoints spend exactly `10*r` live
coordinates has first-round product-aware demand strictly larger than the ambient dimension. -/
theorem parity_normalized_intended_labelCard_demand_exceeds_ambient
    {A r fuel : ℕ} (C : Layered (1000 * A * r)) (phase : Bool)
    (hparity : ∀ x : Fin (1000 * A * r) → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hA : 0 < A) (hr : 0 < r) (hKfuel : 20 * r ≤ fuel)
    (code : ConditionedFirstRoundCode
      (commonShallowBad (normalizedLayeredBottomFamily C)
        fuel (20 * r) (10 * r) 0))
    (hendpoint : ∀ root, stars (code.endpoint root) = 10 * r) :
    1000 * A * r < 20 * (24 * code.labelCard + 26) := by
  apply intended_power_lower_forces_firstRoundDemand hA hr
  simpa only [show 2 * (20 * r) = 40 * r by ring] using
    (parity_normalized_labelCard_power_lower C phase hparity hKfuel
      (by nlinarith) (by nlinarith) code
      (by simpa only [show 20 * r - 10 * r = 10 * r by omega] using hendpoint))

/-- The encoder-independent shell balance propagates through the exact product-aware recurrence.
No positive-round schedule with positive terminal survivor can fit once its first key is the label
cardinality of a decoder-sound parity-shell code spending exactly `10*r` live coordinates.  Later
alphabets are arbitrary; only positivity of the remaining least budget is used. -/
theorem parity_normalized_intended_conditionedCode_productAware_not_fit
    {A r fuel rounds terminal : ℕ}
    (C : Layered (1000 * A * r)) (phase : Bool)
    (hparity : ∀ x : Fin (1000 * A * r) → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hA : 0 < A) (hr : 0 < r) (hKfuel : 20 * r ≤ fuel)
    (hrounds : 0 < rounds) (hterminal : 0 < terminal)
    (code : ConditionedFirstRoundCode
      (commonShallowBad (normalizedLayeredBottomFamily C)
        fuel (20 * r) (10 * r) 0))
    (hendpoint : ∀ root, stars (code.endpoint root) = 10 * r)
    (actualKeys : ℕ → ℕ) (hfirst : actualKeys 1 = code.labelCard) :
    ¬20 * leastFiniteProductAwareBudget rounds actualKeys terminal ≤ 1000 * A * r := by
  intro hfit
  obtain ⟨remainingRounds, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrounds)
  have htail : 0 < leastFiniteProductAwareBudget remainingRounds
      (fun i ↦ actualKeys (i + 1)) terminal :=
    leastFiniteProductAwareBudget_pos remainingRounds _ hterminal
  have hfirstDemand : 20 * (24 * actualKeys 1 + 26) ≤ 1000 * A * r := by
    calc
      20 * (24 * actualKeys 1 + 26) ≤
          20 * ((24 * actualKeys 1 + 26) *
            leastFiniteProductAwareBudget remainingRounds
              (fun i ↦ actualKeys (i + 1)) terminal) := by
        exact Nat.mul_le_mul_left 20 (Nat.le_mul_of_pos_right _ htail)
      _ = 20 * leastFiniteProductAwareBudget (remainingRounds + 1)
          actualKeys terminal := by
        rw [leastFiniteProductAwareBudget_succ, leastProductAwarePredecessor_eq]
      _ ≤ 1000 * A * r := hfit
  rw [hfirst] at hfirstDemand
  have htooLarge := parity_normalized_intended_labelCard_demand_exceeds_ambient
    C phase hparity hA hr hKfuel code hendpoint
  omega

/-! ### Bounded ambiguity does not remove the parity shell charge -/

/-- Encoder-independent shell balance with list-decoding ambiguity `L`.  The only change from
exact decoding is that the endpoint/label population is multiplied by `L`. -/
theorem parity_normalized_ambiguity_mul_labelCard_mul_endpointShell_lower
    {n fuel K trunkDepth L : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K)
    (code : BoundedAmbiguityFirstRoundCode
      (commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth 0) L)
    (hendpoint : ∀ root, stars (code.endpoint root) = K - trunkDepth) :
    Nat.choose n K * 2 ^ (n - K) ≤
      L * (code.labelCard * (Nat.choose n (K - trunkDepth) *
        2 ^ (n - (K - trunkDepth)))) := by
  have hcount := code.bad_card_le_ambiguity_mul_labelCard_mul_endpointShell_card hendpoint
  rw [parity_normalized_commonShallowBad_zero_card C phase hparity hKfuel htrunk,
    card_stars_eq] at hcount
  exact hcount

/-- Cleared-denominator form of the bounded-ambiguity balance.  It shows that the effective
alphabet is the product `L * labelCard`; ambiguity is quantitative information that must be
charged, not a free weakening of decoder soundness. -/
theorem parity_normalized_ambiguity_mul_labelCard_power_lower
    {n fuel K trunkDepth L : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K) (hKn : K ≤ n)
    (code : BoundedAmbiguityFirstRoundCode
      (commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth 0) L)
    (hendpoint : ∀ root, stars (code.endpoint root) = K - trunkDepth) :
    (n - K + 1) ^ trunkDepth ≤
      (L * code.labelCard) * (2 * K) ^ trunkDepth := by
  have hbalance := parity_normalized_ambiguity_mul_labelCard_mul_endpointShell_lower
    C phase hparity hKfuel htrunk code hendpoint
  have hshell := shell_ratio_nat (n := n) K trunkDepth (by omega) hKn
  have hexponent : n - K + trunkDepth = n - (K - trunkDepth) := by omega
  rw [hexponent] at hshell
  have hendpointPos : 0 < Nat.choose n (K - trunkDepth) *
      2 ^ (n - (K - trunkDepth)) := by
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (pow_pos (by omega) _)
  apply Nat.le_of_mul_le_mul_left
    (c := Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth)))
    (hc := hendpointPos)
  calc
    (Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth))) *
          (n - K + 1) ^ trunkDepth ≤
        (Nat.choose n K * 2 ^ (n - K)) * (2 * K) ^ trunkDepth := hshell
    _ ≤ (L * (code.labelCard *
          (Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth))))) *
          (2 * K) ^ trunkDepth := Nat.mul_le_mul_right _ hbalance
    _ = (Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth))) *
          ((L * code.labelCard) * (2 * K) ^ trunkDepth) := by ring

/-- At the intended density, charging the ambiguity factor restores the same strict first-round
ambient obstruction as exact decoding. -/
theorem parity_normalized_intended_effectiveAlphabet_demand_exceeds_ambient
    {A r fuel L : ℕ} (C : Layered (1000 * A * r)) (phase : Bool)
    (hparity : ∀ x : Fin (1000 * A * r) → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hA : 0 < A) (hr : 0 < r) (hKfuel : 20 * r ≤ fuel)
    (code : BoundedAmbiguityFirstRoundCode
      (commonShallowBad (normalizedLayeredBottomFamily C)
        fuel (20 * r) (10 * r) 0) L)
    (hendpoint : ∀ root, stars (code.endpoint root) = 10 * r) :
    1000 * A * r < 20 * (24 * (L * code.labelCard) + 26) := by
  apply intended_power_lower_forces_firstRoundDemand hA hr
  simpa only [show 2 * (20 * r) = 40 * r by ring] using
    (parity_normalized_ambiguity_mul_labelCard_power_lower C phase hparity hKfuel
      (by nlinarith) (by nlinarith) code
      (by simpa only [show 20 * r - 10 * r = 10 * r by omega] using hendpoint))

/-- The bounded-ambiguity parity obstruction holds for every variable expenditure in the entire
range `r ≤ d < 20*r`.  Therefore the only expenditure regime not eliminated by this population
argument is the strictly sub-`r` regime. -/
theorem parity_normalized_intended_variable_effectiveAlphabet_demand_exceeds_ambient
    {A r d fuel L : ℕ} (C : Layered (1000 * A * r)) (phase : Bool)
    (hparity : ∀ x : Fin (1000 * A * r) → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hA : 0 < A) (hr : 0 < r) (hrd : r ≤ d) (hdK : d < 20 * r)
    (hKfuel : 20 * r ≤ fuel)
    (code : BoundedAmbiguityFirstRoundCode
      (commonShallowBad (normalizedLayeredBottomFamily C)
        fuel (20 * r) d 0) L)
    (hendpoint : ∀ root, stars (code.endpoint root) = 20 * r - d) :
    1000 * A * r < 20 * (24 * (L * code.labelCard) + 26) := by
  apply intended_variable_power_lower_forces_firstRoundDemand hA hr hrd
  simpa only [show 2 * (20 * r) = 40 * r by ring] using
    (parity_normalized_ambiguity_mul_labelCard_power_lower C phase hparity hKfuel
      hdK (by nlinarith) code hendpoint)

/-- Consequently no positive product-aware schedule fits when its first key honestly charges both
the label alphabet and the maximum list size.  Later keys remain arbitrary. -/
theorem parity_normalized_intended_boundedAmbiguity_productAware_not_fit
    {A r fuel rounds terminal L : ℕ}
    (C : Layered (1000 * A * r)) (phase : Bool)
    (hparity : ∀ x : Fin (1000 * A * r) → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hA : 0 < A) (hr : 0 < r) (hKfuel : 20 * r ≤ fuel)
    (hrounds : 0 < rounds) (hterminal : 0 < terminal)
    (code : BoundedAmbiguityFirstRoundCode
      (commonShallowBad (normalizedLayeredBottomFamily C)
        fuel (20 * r) (10 * r) 0) L)
    (hendpoint : ∀ root, stars (code.endpoint root) = 10 * r)
    (actualKeys : ℕ → ℕ) (hfirst : actualKeys 1 = L * code.labelCard) :
    ¬20 * leastFiniteProductAwareBudget rounds actualKeys terminal ≤ 1000 * A * r := by
  intro hfit
  obtain ⟨remainingRounds, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrounds)
  have htail : 0 < leastFiniteProductAwareBudget remainingRounds
      (fun i ↦ actualKeys (i + 1)) terminal :=
    leastFiniteProductAwareBudget_pos remainingRounds _ hterminal
  have hfirstDemand : 20 * (24 * actualKeys 1 + 26) ≤ 1000 * A * r := by
    calc
      20 * (24 * actualKeys 1 + 26) ≤
          20 * ((24 * actualKeys 1 + 26) *
            leastFiniteProductAwareBudget remainingRounds
              (fun i ↦ actualKeys (i + 1)) terminal) := by
        exact Nat.mul_le_mul_left 20 (Nat.le_mul_of_pos_right _ htail)
      _ = 20 * leastFiniteProductAwareBudget (remainingRounds + 1)
          actualKeys terminal := by
        rw [leastFiniteProductAwareBudget_succ, leastProductAwarePredecessor_eq]
      _ ≤ 1000 * A * r := hfit
  rw [hfirst] at hfirstDemand
  have htooLarge := parity_normalized_intended_effectiveAlphabet_demand_exceeds_ambient
    C phase hparity hA hr hKfuel code hendpoint
  omega

/-- No positive product-aware schedule can fit for any first-round expenditure `d` between `r`
and `20*r`.  This closes the entire linear-in-`r` smaller-trunk escape hatch, not merely the
original choice `d = 10*r`. -/
theorem parity_normalized_intended_variable_boundedAmbiguity_productAware_not_fit
    {A r d fuel rounds terminal L : ℕ}
    (C : Layered (1000 * A * r)) (phase : Bool)
    (hparity : ∀ x : Fin (1000 * A * r) → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hA : 0 < A) (hr : 0 < r) (hrd : r ≤ d) (hdK : d < 20 * r)
    (hKfuel : 20 * r ≤ fuel) (hrounds : 0 < rounds) (hterminal : 0 < terminal)
    (code : BoundedAmbiguityFirstRoundCode
      (commonShallowBad (normalizedLayeredBottomFamily C)
        fuel (20 * r) d 0) L)
    (hendpoint : ∀ root, stars (code.endpoint root) = 20 * r - d)
    (actualKeys : ℕ → ℕ) (hfirst : actualKeys 1 = L * code.labelCard) :
    ¬20 * leastFiniteProductAwareBudget rounds actualKeys terminal ≤ 1000 * A * r := by
  intro hfit
  obtain ⟨remainingRounds, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrounds)
  have htail : 0 < leastFiniteProductAwareBudget remainingRounds
      (fun i ↦ actualKeys (i + 1)) terminal :=
    leastFiniteProductAwareBudget_pos remainingRounds _ hterminal
  have hfirstDemand : 20 * (24 * actualKeys 1 + 26) ≤ 1000 * A * r := by
    calc
      20 * (24 * actualKeys 1 + 26) ≤
          20 * ((24 * actualKeys 1 + 26) *
            leastFiniteProductAwareBudget remainingRounds
              (fun i ↦ actualKeys (i + 1)) terminal) := by
        exact Nat.mul_le_mul_left 20 (Nat.le_mul_of_pos_right _ htail)
      _ = 20 * leastFiniteProductAwareBudget (remainingRounds + 1)
          actualKeys terminal := by
        rw [leastFiniteProductAwareBudget_succ, leastProductAwarePredecessor_eq]
      _ ≤ 1000 * A * r := hfit
  rw [hfirst] at hfirstDemand
  have htooLarge :=
    parity_normalized_intended_variable_effectiveAlphabet_demand_exceeds_ambient
      C phase hparity hA hr hrd hdK hKfuel code hendpoint
  omega

/-- Representation-independent largest-fiber balance for residual-depth-zero parity.  The exact
`K`-live bad shell must pass through canonical endpoints in the `(K-trunkDepth)`-live shell, so its
population is bounded by that endpoint-shell population times the largest realized fiber. -/
theorem parity_normalized_maxFiber_mul_endpointShell_lower
    {n w fuel K trunkDepth : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth w C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K) :
    Nat.choose n K * 2 ^ (n - K) ≤
      (ConditionedFirstRoundCode.commonShallowBadPrefixCode
        (d := trunkDepth) (residualDepth := 0)
        (normalizedLayeredBottomFamily C)
        (normalizedLayeredBottomFamily_nodup C)
        (normalizedLayeredBottomFamily_width_le hw) hKfuel).maxRealizedEndpointFiberCard *
      (Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth))) := by
  have hcount :=
    ConditionedFirstRoundCode.commonShallowBad_card_le_maxFiber_mul_endpointShell_card
      (d := trunkDepth) (residualDepth := 0)
      (normalizedLayeredBottomFamily C)
      (normalizedLayeredBottomFamily_nodup C)
      (normalizedLayeredBottomFamily_width_le hw) hKfuel
  rw [parity_normalized_commonShallowBad_zero_card C phase hparity hKfuel htrunk,
    card_stars_eq] at hcount
  exact hcount

/-- Cancellation-friendly form of the endpoint-shell balance.  After multiplying by the exact
number of ways to restore the `trunkDepth` live coordinates, the two restriction-shell factors
cancel.  Thus the largest realized canonical endpoint fiber must absorb the remaining binomial
ratio, including the Boolean assignment cost `2^trunkDepth`.

The explicit hypothesis `K ≤ n` is essential: without it the source shell can be empty and no
positive factor is available for cancellation. -/
theorem parity_normalized_endpointShell_ratio_lower
    {n w fuel K trunkDepth : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth w C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K) (hKn : K ≤ n) :
    Nat.choose (n - (K - trunkDepth)) trunkDepth ≤
      (ConditionedFirstRoundCode.commonShallowBadPrefixCode
        (d := trunkDepth) (residualDepth := 0)
        (normalizedLayeredBottomFamily C)
        (normalizedLayeredBottomFamily_nodup C)
        (normalizedLayeredBottomFamily_width_le hw) hKfuel).maxRealizedEndpointFiberCard *
      (Nat.choose K trunkDepth * 2 ^ trunkDepth) := by
  let code := ConditionedFirstRoundCode.commonShallowBadPrefixCode
    (d := trunkDepth) (residualDepth := 0)
    (normalizedLayeredBottomFamily C)
    (normalizedLayeredBottomFamily_nodup C)
    (normalizedLayeredBottomFamily_width_le hw) hKfuel
  have hbalance := parity_normalized_maxFiber_mul_endpointShell_lower
    C phase hw hparity hKfuel htrunk
  have hrestore := endpointFiber_coordinateSet_exact_count
    (n := n) (K := K) (d := trunkDepth) (by omega) hKn
  have hsource : 0 < Nat.choose n K * 2 ^ (n - K) :=
    Nat.mul_pos (Nat.choose_pos hKn) (pow_pos (by omega) _)
  apply Nat.le_of_mul_le_mul_left
    (c := Nat.choose n K * 2 ^ (n - K)) (hc := hsource)
  calc
    (Nat.choose n K * 2 ^ (n - K)) *
          Nat.choose (n - (K - trunkDepth)) trunkDepth ≤
        (code.maxRealizedEndpointFiberCard *
          (Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth)))) *
          Nat.choose (n - (K - trunkDepth)) trunkDepth :=
      Nat.mul_le_mul_right _ hbalance
    _ = code.maxRealizedEndpointFiberCard *
          ((Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth))) *
            Nat.choose (n - (K - trunkDepth)) trunkDepth) := by ring
    _ = code.maxRealizedEndpointFiberCard *
          ((Nat.choose n K * 2 ^ (n - K)) *
            (Nat.choose K trunkDepth * 2 ^ trunkDepth)) := by
      rw [hrestore]
      ring
    _ = (Nat.choose n K * 2 ^ (n - K)) *
          (code.maxRealizedEndpointFiberCard *
            (Nat.choose K trunkDepth * 2 ^ trunkDepth)) := by ring

/-- Coarser but immediately comparable power form of the exact endpoint-shell ratio.  Every
canonical endpoint scheme for residual-zero parity must have a realized fiber large enough that
`maxFiber * (2*K)^trunkDepth` covers `(n-K+1)^trunkDepth`.  This is the cleared-denominator form of
the familiar per-step shell ratio `(n-K+1)/(2*K)` and avoids all natural-number division. -/
theorem parity_normalized_endpointShell_power_lower
    {n w fuel K trunkDepth : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth w C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K) (hKn : K ≤ n) :
    (n - K + 1) ^ trunkDepth ≤
      (ConditionedFirstRoundCode.commonShallowBadPrefixCode
        (d := trunkDepth) (residualDepth := 0)
        (normalizedLayeredBottomFamily C)
        (normalizedLayeredBottomFamily_nodup C)
        (normalizedLayeredBottomFamily_width_le hw) hKfuel).maxRealizedEndpointFiberCard *
      (2 * K) ^ trunkDepth := by
  let code := ConditionedFirstRoundCode.commonShallowBadPrefixCode
    (d := trunkDepth) (residualDepth := 0)
    (normalizedLayeredBottomFamily C)
    (normalizedLayeredBottomFamily_nodup C)
    (normalizedLayeredBottomFamily_width_le hw) hKfuel
  have hbalance := parity_normalized_maxFiber_mul_endpointShell_lower
    C phase hw hparity hKfuel htrunk
  have hshell := shell_ratio_nat (n := n) K trunkDepth (by omega) hKn
  have hexponent : n - K + trunkDepth = n - (K - trunkDepth) := by omega
  rw [hexponent] at hshell
  have hendpoint : 0 < Nat.choose n (K - trunkDepth) *
      2 ^ (n - (K - trunkDepth)) := by
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (pow_pos (by omega) _)
  apply Nat.le_of_mul_le_mul_left
    (c := Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth)))
    (hc := hendpoint)
  calc
    (Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth))) *
          (n - K + 1) ^ trunkDepth ≤
        (Nat.choose n K * 2 ^ (n - K)) * (2 * K) ^ trunkDepth := hshell
    _ ≤ (code.maxRealizedEndpointFiberCard *
          (Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth)))) *
          (2 * K) ^ trunkDepth := Nat.mul_le_mul_right _ hbalance
    _ = (Nat.choose n (K - trunkDepth) * 2 ^ (n - (K - trunkDepth))) *
          (code.maxRealizedEndpointFiberCard * (2 * K) ^ trunkDepth) := by ring

/-- The power lower bound at the density used by the verified realized-prefix contraction:
`n = 1000*A*r`, `K = 20*r`, and prefix depth `10*r`.  The left base is the exact shell numerator;
the comparison base on the fiber side is only `40*r`. -/
theorem parity_normalized_intended_endpointShell_power_lower
    {A r w fuel : ℕ} (C : Layered (1000 * A * r)) (phase : Bool)
    (hw : BottomWidth w C)
    (hparity : ∀ x : Fin (1000 * A * r) → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hA : 0 < A) (hr : 0 < r) (hKfuel : 20 * r ≤ fuel) :
    (1000 * A * r - 20 * r + 1) ^ (10 * r) ≤
      (ConditionedFirstRoundCode.commonShallowBadPrefixCode
        (d := 10 * r) (residualDepth := 0)
        (normalizedLayeredBottomFamily C)
        (normalizedLayeredBottomFamily_nodup C)
        (normalizedLayeredBottomFamily_width_le hw) hKfuel).maxRealizedEndpointFiberCard *
      (40 * r) ^ (10 * r) := by
  have htrunk : 10 * r < 20 * r := by nlinarith
  have hKn : 20 * r ≤ 1000 * A * r := by nlinarith
  simpa only [show 2 * (20 * r) = 40 * r by ring] using
    (parity_normalized_endpointShell_power_lower
      C phase hw hparity hKfuel htrunk hKn)

/-- Direct comparison between the forced canonical endpoint fiber and the product-aware slot
budget at the intended density.  If the optimal endpoint-local first alphabet is used and the
schedule fits, then the circuit's actual bottom-slot count must pay both the forced fiber scale
and the alphabet-independent transition floor, including the unavoidable later-round factor.

This is deliberately cleared of division: it relates `A`, `r`, `rounds`, `terminal`, and the
actual circuit size without assuming an a priori upper bound on `bottomSlotCount C`. -/
theorem parity_normalized_intended_productAware_slot_lower
    {A r fuel rounds terminal : ℕ}
    (C : Layered (1000 * A * r)) (phase : Bool)
    (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin (1000 * A * r) → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hA : 0 < A) (hr : 0 < r) (hKfuel : 20 * r ≤ fuel)
    (hrounds : 0 < rounds)
    (actualKeys : ℕ → ℕ)
    (hfirst : actualKeys 1 =
      (ConditionedFirstRoundCode.commonShallowBadMaxFiberPrefixCode
        (d := 10 * r) (residualDepth := 0)
        (normalizedLayeredBottomFamily C)
        (normalizedLayeredBottomFamily_nodup C)
        (normalizedLayeredBottomFamily_width_le hw) hKfuel).labelCard)
    (hfit : 20 * leastFiniteProductAwareBudget rounds actualKeys terminal ≤
      1000 * A * r) :
    (240 * (1000 * A * r - 20 * r + 1) ^ (10 * r) +
        260 * (40 * r) ^ (10 * r)) *
          (26 ^ (rounds - 1) * terminal) ≤
      bottomSlotCount C * (40 * r) ^ (10 * r) := by
  let code := ConditionedFirstRoundCode.commonShallowBadPrefixCode
    (d := 10 * r) (residualDepth := 0)
    (normalizedLayeredBottomFamily C)
    (normalizedLayeredBottomFamily_nodup C)
    (normalizedLayeredBottomFamily_width_le hw) hKfuel
  have hpower :
      (1000 * A * r - 20 * r + 1) ^ (10 * r) ≤
        code.maxRealizedEndpointFiberCard * (40 * r) ^ (10 * r) := by
    exact parity_normalized_intended_endpointShell_power_lower
      C phase hw hparity hA hr hKfuel
  have hbudget :
      (240 * code.maxRealizedEndpointFiberCard + 260) *
          (26 ^ (rounds - 1) * terminal) ≤ bottomSlotCount C := by
    exact widthTwoParity_commonShallowBadMaxFiberPrefixCode_firstKey_bound
      C phase hw hparity hrounds
      (normalizedLayeredBottomFamily C)
      (normalizedLayeredBottomFamily_nodup C)
      (normalizedLayeredBottomFamily_width_le hw) hKfuel
      actualKeys hfirst hfit
  calc
    (240 * (1000 * A * r - 20 * r + 1) ^ (10 * r) +
          260 * (40 * r) ^ (10 * r)) *
        (26 ^ (rounds - 1) * terminal) ≤
      (240 * (code.maxRealizedEndpointFiberCard * (40 * r) ^ (10 * r)) +
          260 * (40 * r) ^ (10 * r)) *
        (26 ^ (rounds - 1) * terminal) := by
          exact Nat.mul_le_mul_right _
            (Nat.add_le_add_right (Nat.mul_le_mul_left 240 hpower) _)
    _ = ((240 * code.maxRealizedEndpointFiberCard + 260) *
          (26 ^ (rounds - 1) * terminal)) * (40 * r) ^ (10 * r) := by ring
    _ ≤ bottomSlotCount C * (40 * r) ^ (10 * r) :=
      Nat.mul_le_mul_right _ hbudget

/-- Contrapositive form of the exact intended-density comparison.  It identifies the concrete
size regime in which even the optimal endpoint-local canonical-prefix alphabet cannot make the
current product-aware schedule fit. -/
theorem parity_normalized_intended_productAware_not_fit_of_slot_gap
    {A r fuel rounds terminal : ℕ}
    (C : Layered (1000 * A * r)) (phase : Bool)
    (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin (1000 * A * r) → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hA : 0 < A) (hr : 0 < r) (hKfuel : 20 * r ≤ fuel)
    (hrounds : 0 < rounds)
    (actualKeys : ℕ → ℕ)
    (hfirst : actualKeys 1 =
      (ConditionedFirstRoundCode.commonShallowBadMaxFiberPrefixCode
        (d := 10 * r) (residualDepth := 0)
        (normalizedLayeredBottomFamily C)
        (normalizedLayeredBottomFamily_nodup C)
        (normalizedLayeredBottomFamily_width_le hw) hKfuel).labelCard)
    (hgap : bottomSlotCount C * (40 * r) ^ (10 * r) <
      (240 * (1000 * A * r - 20 * r + 1) ^ (10 * r) +
        260 * (40 * r) ^ (10 * r)) *
          (26 ^ (rounds - 1) * terminal)) :
    ¬20 * leastFiniteProductAwareBudget rounds actualKeys terminal ≤
      1000 * A * r := by
  intro hfit
  have hneeded := parity_normalized_intended_productAware_slot_lower
    C phase hw hparity hA hr hKfuel hrounds actualKeys hfirst hfit
  omega

/-! ### An explicit parameterized width-one parity representative -/

/-- The literal that accepts exactly the value prescribed by `a` at coordinate `i`. -/
def assignmentLiteral {n : ℕ} (a : Fin n → Bool) (i : Fin n) : Rung4Literal n :=
  if a i then Rung4Literal.pos i else Rung4Literal.neg i

/-- A one-slot bottom DNF computing the prescribed literal. -/
def assignmentAtom {n : ℕ} (a : Fin n → Bool) (i : Fin n) : Layered n :=
  Layered.dnf [⟨[assignmentLiteral a i]⟩]

/-- The conjunction of all prescribed coordinate literals. -/
def assignmentConjunction {n : ℕ} (a : Fin n → Bool) : Layered n :=
  Layered.gAnd (List.ofFn (assignmentAtom a))

/-- An explicit parity circuit: OR together the exact-assignment conjunctions of odd parity.
Every syntactic bottom gate is a one-literal, one-clause DNF. -/
noncomputable def widthOneParityLayered (n : ℕ) : Layered n :=
  Layered.gOr (((Finset.univ.filter fun a : Fin n → Bool => DTree.parity a = true).toList).map
    assignmentConjunction)

theorem assignmentAtom_eval {n : ℕ} (a x : Fin n → Bool) (i : Fin n) :
    Layered.eval (assignmentAtom a i) x = decide (x i = a i) := by
  cases hai : a i <;> cases hxi : x i <;>
    simp [assignmentAtom, assignmentLiteral, DTree.dnfValue,
      Rung4Literal.eval, hai, hxi]

/-- An assignment conjunction is the Boolean singleton indicator of its assignment. -/
theorem assignmentConjunction_eval {n : ℕ} (a x : Fin n → Bool) :
    Layered.eval (assignmentConjunction a) x = decide (x = a) := by
  classical
  rw [assignmentConjunction, Layered.eval_gAnd]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rw [decide_eq_true_eq]
    apply funext
    intro i
    have hi := (List.all_eq_true.mp h) (assignmentAtom a i)
      (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rw [assignmentAtom_eval, decide_eq_true_eq] at hi
    exact hi
  · intro h
    rw [decide_eq_true_eq] at h
    rw [List.all_eq_true]
    intro atom hatom
    rw [List.mem_ofFn] at hatom
    obtain ⟨i, rfl⟩ := hatom
    rw [assignmentAtom_eval, decide_eq_true_eq]
    exact congrFun h i

/-- The explicit family computes parity on every input. -/
theorem widthOneParityLayered_eval (n : ℕ) (x : Fin n → Bool) :
    Layered.eval (widthOneParityLayered n) x = DTree.parity x := by
  classical
  rw [widthOneParityLayered]
  apply Bool.eq_iff_iff.mpr
  rw [Layered.eval_gOr, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hcx⟩
    rw [List.mem_map] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    rw [assignmentConjunction_eval, decide_eq_true_eq] at hcx
    subst a
    simpa using ha
  · intro hx
    refine ⟨assignmentConjunction x, ?_, ?_⟩
    · rw [List.mem_map]
      exact ⟨x, by simp [hx], rfl⟩
    · rw [assignmentConjunction_eval, decide_eq_true_eq]

theorem assignmentAtom_bottomSlotCount {n : ℕ} (a : Fin n → Bool) (i : Fin n) :
    bottomSlotCount (assignmentAtom a i) = 1 := by
  simp [assignmentAtom, bottomSlotCount, bottomGates]

theorem bottomSlotCount_gAnd_list {n : ℕ} (gs : List (Layered n)) :
    bottomSlotCount (Layered.gAnd gs) = (gs.map bottomSlotCount).sum := by
  unfold bottomSlotCount
  rw [bottomGates, bottomGatesList_eq, List.map_flatten, List.sum_flatten,
    List.map_map]
  simp [Function.comp_def]

theorem bottomSlotCount_gOr_list {n : ℕ} (gs : List (Layered n)) :
    bottomSlotCount (Layered.gOr gs) = (gs.map bottomSlotCount).sum := by
  unfold bottomSlotCount
  rw [bottomGates, bottomGatesList_eq, List.map_flatten, List.sum_flatten,
    List.map_map]
  simp [Function.comp_def]

theorem assignmentConjunction_bottomSlotCount {n : ℕ} (a : Fin n → Bool) :
    bottomSlotCount (assignmentConjunction a) = n := by
  rw [assignmentConjunction, bottomSlotCount_gAnd_list]
  simp [Function.comp_def, assignmentAtom_bottomSlotCount]

/-- Exact slot count of the explicit representative.  It pays one bottom slot per input
coordinate for each of the `2^(n-1)` satisfying parity assignments. -/
theorem widthOneParityLayered_bottomSlotCount {n : ℕ} (hn : 1 ≤ n) :
    bottomSlotCount (widthOneParityLayered n) = n * 2 ^ (n - 1) := by
  classical
  rw [widthOneParityLayered, bottomSlotCount_gOr_list, List.map_map]
  simp [assignmentConjunction_bottomSlotCount, Depth3.parity_true_card hn, Nat.mul_comm]

/-- The representative satisfies the width-two interface (in fact every clause has width one). -/
theorem widthOneParityLayered_bottomWidth_two (n : ℕ) :
    BottomWidth 2 (widthOneParityLayered n) := by
  intro cs hcs T hT
  simp [widthOneParityLayered, assignmentConjunction, assignmentAtom, bottomGates,
    bottomGatesList_eq] at hcs
  rcases hcs with ⟨a, ha, i, rfl⟩
  simp at hT
  subst T
  simp

/-- Every singleton bottom clause is consistent and variable-duplicate-free, so the explicit
representative also satisfies the normalization invariant used by collapse iteration. -/
theorem widthOneParityLayered_bottomClean (n : ℕ) :
    BottomClean (widthOneParityLayered n) := by
  constructor <;> intro cs hcs T hT
  · simp [widthOneParityLayered, assignmentConjunction, assignmentAtom, bottomGates,
      bottomGatesList_eq] at hcs
    rcases hcs with ⟨a, ha, i, rfl⟩
    simp at hT
    subst T
    cases h : a i <;> simp [assignmentLiteral, h, Consistent]
  · simp [widthOneParityLayered, assignmentConjunction, assignmentAtom, bottomGates,
      bottomGatesList_eq] at hcs
    rcases hcs with ⟨a, ha, i, rfl⟩
    simp at hT
    subst T
    simp

/-! Although `widthOneParityLayered` contains one singleton atom for every coordinate of every
odd assignment, its bottom-gate *values* have only two possibilities per coordinate.  The compact
family below indexes those positive and negative singleton gates directly.  This removes the
exponential syntactic-occurrence charge before any endpoint-image estimate is attempted. -/

/-- The two singleton polarities on every coordinate, indexed by `Fin (n + n)`. -/
def widthOneParityCompactFamily (n : ℕ) : Fin (n + n) → List (Clause n) :=
  Fin.addCases
    (fun i ↦ [⟨[Rung4Literal.pos i]⟩])
    (fun i ↦ [⟨[Rung4Literal.neg i]⟩])

@[simp] theorem widthOneParityCompactFamily_left {n : ℕ} (i : Fin n) :
    widthOneParityCompactFamily n (Fin.castAdd n i) =
      [⟨[Rung4Literal.pos i]⟩] := by
  simp [widthOneParityCompactFamily]

@[simp] theorem widthOneParityCompactFamily_right {n : ℕ} (i : Fin n) :
    widthOneParityCompactFamily n (Fin.natAdd n i) =
      [⟨[Rung4Literal.neg i]⟩] := by
  rw [widthOneParityCompactFamily, Fin.addCases_right]

@[simp] theorem widthOneParityCompactFamily_right_addNat {n : ℕ} (i : Fin n) :
    widthOneParityCompactFamily n (Fin.addNat i n) =
      [⟨[Rung4Literal.neg i]⟩] := by
  have hi : Fin.addNat i n = Fin.natAdd n i := by
    apply Fin.ext
    simp [Nat.add_comm]
  rw [hi, widthOneParityCompactFamily_right]

/-- Every compact gate has exactly one clause. -/
theorem widthOneParityCompactFamily_length (n : ℕ) (g : Fin (n + n)) :
    (widthOneParityCompactFamily n g).length = 1 := by
  refine Fin.addCases (motive := fun g ↦
    (widthOneParityCompactFamily n g).length = 1) ?_ ?_ g <;> simp

/-- The compact family is duplicate-free and genuinely width one. -/
theorem widthOneParityCompactFamily_normalized (n : ℕ) :
    (∀ g, (widthOneParityCompactFamily n g).Nodup) ∧
      (∀ g T, T ∈ widthOneParityCompactFamily n g → T.lits.length ≤ 1) := by
  constructor
  · intro g
    refine Fin.addCases (motive := fun g ↦
      (widthOneParityCompactFamily n g).Nodup) ?_ ?_ g <;> simp
  · intro g
    refine Fin.addCases (motive := fun g ↦
      ∀ T, T ∈ widthOneParityCompactFamily n g → T.lits.length ≤ 1) ?_ ?_ g <;>
        simp

/-- The whole ragged term-key alphabet has exact size `2*n`, rather than the exponential number
of syntactic singleton occurrences in the circuit. -/
theorem widthOneParityCompactFamily_total_length (n : ℕ) :
    (∑ g, (widthOneParityCompactFamily n g).length) = 2 * n := by
  simp [widthOneParityCompactFamily_length, Nat.two_mul]

/-- A fixed positive singleton is already decided and makes no witness query. -/
theorem runWitSeq_positive_singleton_of_fixed {n : ℕ} (fuel : ℕ)
    (sigma : Restriction n) (x : Fin n → Bool) (i : Fin n) (hi : sigma i ≠ none) :
    runWitSeq [⟨[Rung4Literal.pos i]⟩] fuel sigma x = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases his : sigma i with
      | none => exact (hi his).elim
      | some b =>
          cases b <;>
            simp [runWitSeq, anyTermSat, activeTerm, termSat, termFalsified, freeLits,
              litFree, litTrue, litFalse, litFixedVal, his]

/-- A fixed negative singleton is likewise already decided and makes no witness query. -/
theorem runWitSeq_negative_singleton_of_fixed {n : ℕ} (fuel : ℕ)
    (sigma : Restriction n) (x : Fin n → Bool) (i : Fin n) (hi : sigma i ≠ none) :
    runWitSeq [⟨[Rung4Literal.neg i]⟩] fuel sigma x = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases his : sigma i with
      | none => exact (hi his).elim
      | some b =>
          cases b <;>
            simp [runWitSeq, anyTermSat, activeTerm, termSat, termFalsified, freeLits,
              litFree, litTrue, litFalse, litFixedVal, his]

/-- A live positive singleton contributes exactly one canonical witness query, independently of
the extending assignment.  This is the local selector calculation behind the compact family's
global coordinate order. -/
theorem runWitSeq_positive_singleton_of_free {n fuel : ℕ} (sigma : Restriction n)
    (x : Fin n → Bool) (i : Fin n) (hi : sigma i = none) :
    runWitSeq [⟨[Rung4Literal.pos i]⟩] (fuel + 1) sigma x = [(0, 0)] := by
  simp [runWitSeq, anyTermSat, activeTerm, termSat, termFalsified, freeLits,
    freeLitPos, activeTermIdx, termActivePred, litFree, litTrue, litFalse,
    litFixedVal, litVar, fixVar, hi]
  split <;> apply runWitSeq_positive_singleton_of_fixed <;> simp

/-- The negative singleton has the same one-query behavior while its coordinate is live. -/
theorem runWitSeq_negative_singleton_of_free {n fuel : ℕ} (sigma : Restriction n)
    (x : Fin n → Bool) (i : Fin n) (hi : sigma i = none) :
    runWitSeq [⟨[Rung4Literal.neg i]⟩] (fuel + 1) sigma x = [(0, 0)] := by
  simp [runWitSeq, anyTermSat, activeTerm, termSat, termFalsified, freeLits,
    freeLitPos, activeTermIdx, termActivePred, litFree, litTrue, litFalse,
    litFixedVal, litVar, fixVar, hi]
  split <;> apply runWitSeq_negative_singleton_of_fixed <;> simp

/-- Exact selector law for the positive singleton: at positive fuel it emits its sole witness iff
the coordinate is live. -/
theorem runWitSeq_positive_singleton (n fuel : ℕ) (sigma : Restriction n)
    (x : Fin n → Bool) (i : Fin n) :
    runWitSeq [⟨[Rung4Literal.pos i]⟩] (fuel + 1) sigma x =
      if sigma i = none then [(0, 0)] else [] := by
  cases hi : sigma i with
  | none => simp [hi, runWitSeq_positive_singleton_of_free sigma x i hi]
  | some b =>
      cases b <;>
        simp [runWitSeq, anyTermSat, activeTerm, termSat, termFalsified, freeLits,
          freeLitPos, activeTermIdx, termActivePred, litFree, litTrue, litFalse,
          litFixedVal, litVar, fixVar, hi]

/-- Exact selector law for the negative singleton.  Its live/fixed behavior is identical to the
positive copy; polarity does not affect whether the coordinate enters the raw witness stream. -/
theorem runWitSeq_negative_singleton (n fuel : ℕ) (sigma : Restriction n)
    (x : Fin n → Bool) (i : Fin n) :
    runWitSeq [⟨[Rung4Literal.neg i]⟩] (fuel + 1) sigma x =
      if sigma i = none then [(0, 0)] else [] := by
  cases hi : sigma i with
  | none => simp [hi, runWitSeq_negative_singleton_of_free sigma x i hi]
  | some b =>
      cases b <;>
        simp [runWitSeq, anyTermSat, activeTerm, termSat, termFalsified, freeLits,
          freeLitPos, activeTermIdx, termActivePred, litFree, litTrue, litFalse,
          litFixedVal, litVar, fixVar, hi]

/-- The compact index convention puts every positive singleton before every negative singleton.
Consequently, when the stable freshness filter sees both copies of a live coordinate, the positive
copy is the canonical winner; there is no cross-polarity `Fin (n+n)` tie. -/
theorem widthOneParityCompactFamily_positive_before_negative {n : ℕ}
    (i j : Fin n) :
    (Fin.castAdd n i : Fin (n + n)).val < (Fin.natAdd n j : Fin (n + n)).val := by
  simp
  omega

/-- Both polarity witnesses decode to their shared underlying coordinate. -/
theorem widthOneParityCompactFamily_taggedWitVar {n : ℕ} (i : Fin n) :
    taggedWitVar? (widthOneParityCompactFamily n)
        (Fin.castAdd n i, (0, 0)) = some i ∧
      taggedWitVar? (widthOneParityCompactFamily n)
        (Fin.natAdd n i, (0, 0)) = some i := by
  simp [taggedWitVar?]
  constructor <;> rfl

/-! The local singleton laws can now be lifted through the actual list constructors used by the
common-switching encoder.  We keep the exact tagged entries as well as their decoded coordinates:
the stronger statement records that the positive copy is the stable first-occurrence winner. -/

/-- Positive compact-family entries at the live coordinates, in ambient coordinate order. -/
def widthOneParityCompactPositiveEntries {n : ℕ} (sigma : Restriction n) :
    List (TaggedWitEntry (n + n)) :=
  (List.finRange n).filterMap fun i =>
    if sigma i = none then some (Fin.castAdd n i, (0, 0)) else none

/-- The corresponding negative entries.  They name the same live coordinates but occur in the
second half of the compact family. -/
def widthOneParityCompactNegativeEntries {n : ℕ} (sigma : Restriction n) :
    List (TaggedWitEntry (n + n)) :=
  (List.finRange n).filterMap fun i =>
    if sigma i = none then some (Fin.natAdd n i, (0, 0)) else none

private theorem flatten_map_ite_singleton_eq_filterMap {alpha beta : Type}
    (l : List alpha) (p : alpha → Prop) [DecidablePred p] (f : alpha → beta) :
    (l.map fun i => if p i then [f i] else []).flatten =
      l.filterMap fun i => if p i then some (f i) else none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : p a <;> simp [h, ih]

private theorem filterMap_ite_some_eq_filter_map {alpha beta : Type}
    (l : List alpha) (p : alpha → Prop) [DecidablePred p] (f : alpha → beta) :
    (l.filterMap fun i => if p i then some (f i) else none) =
      (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : p a <;> simp [h, ih]

/-- Before freshness filtering, the compact selector is exactly the increasing positive live pass
followed by the increasing negative live pass.  It is independent of the extending assignment. -/
theorem widthOneParityCompactFamily_taggedRawWitSeq {n fuel : ℕ}
    (sigma : Restriction n) (x : Fin n → Bool) :
    taggedRawWitSeq (widthOneParityCompactFamily n) (fuel + 1) sigma x =
      widthOneParityCompactPositiveEntries sigma ++
        widthOneParityCompactNegativeEntries sigma := by
  rw [taggedRawWitSeq, List.ofFn_add]
  simp only [List.flatten_append]
  congr 1
  · unfold widthOneParityCompactPositiveEntries
    calc
      _ = (List.ofFn fun i : Fin n =>
            if sigma i = none then
              [((Fin.castAdd n i : Fin (n + n)), (0, 0))]
            else []).flatten := by
          apply congrArg List.flatten
          apply List.ofFn_inj.mpr
          funext i
          have hcast : Fin.castLE (Nat.le_add_right n n) i = Fin.castAdd n i := by
            apply Fin.ext
            rfl
          rw [hcast]
          by_cases h : sigma i = none <;>
            simp [h, runWitSeq_positive_singleton]
      _ = _ := by
        rw [List.ofFn_eq_map]
        exact flatten_map_ite_singleton_eq_filterMap (List.finRange n)
          (fun i => sigma i = none) (fun i => (Fin.castAdd n i, (0, 0)))
  · unfold widthOneParityCompactNegativeEntries
    calc
      _ = (List.ofFn fun i : Fin n =>
            if sigma i = none then
              [((Fin.natAdd n i : Fin (n + n)), (0, 0))]
            else []).flatten := by
          apply congrArg List.flatten
          apply List.ofFn_inj.mpr
          funext i
          by_cases h : sigma i = none <;>
            simp [h, runWitSeq_negative_singleton]
      _ = _ := by
        rw [List.ofFn_eq_map]
        exact flatten_map_ite_singleton_eq_filterMap (List.finRange n)
          (fun i => sigma i = none) (fun i => (Fin.natAdd n i, (0, 0)))

theorem widthOneParityCompactPositiveEntries_eq {n : ℕ} (sigma : Restriction n) :
    widthOneParityCompactPositiveEntries sigma =
      ((List.finRange n).filter fun i => sigma i = none).map
        fun i => (Fin.castAdd n i, (0, 0)) := by
  exact filterMap_ite_some_eq_filter_map (List.finRange n)
    (fun i => sigma i = none) (fun i => (Fin.castAdd n i, (0, 0)))

theorem widthOneParityCompactNegativeEntries_eq {n : ℕ} (sigma : Restriction n) :
    widthOneParityCompactNegativeEntries sigma =
      ((List.finRange n).filter fun i => sigma i = none).map
        fun i => (Fin.natAdd n i, (0, 0)) := by
  exact filterMap_ite_some_eq_filter_map (List.finRange n)
    (fun i => sigma i = none) (fun i => (Fin.natAdd n i, (0, 0)))

theorem widthOneParityCompactPositiveEntries_decode {n : ℕ}
    (sigma : Restriction n) :
    (widthOneParityCompactPositiveEntries sigma).filterMap
        (taggedWitVar? (widthOneParityCompactFamily n)) =
      (List.finRange n).filter fun i => sigma i = none := by
  rw [widthOneParityCompactPositiveEntries_eq, List.filterMap_map]
  have hdecode :
      taggedWitVar? (widthOneParityCompactFamily n) ∘
          (fun i => (Fin.castAdd n i, (0, 0))) = some := by
    funext i
    exact (widthOneParityCompactFamily_taggedWitVar i).1
  rw [hdecode, List.filterMap_some]

theorem widthOneParityCompactNegativeEntries_decode {n : ℕ}
    (sigma : Restriction n) :
    (widthOneParityCompactNegativeEntries sigma).filterMap
        (taggedWitVar? (widthOneParityCompactFamily n)) =
      (List.finRange n).filter fun i => sigma i = none := by
  rw [widthOneParityCompactNegativeEntries_eq, List.filterMap_map]
  have hdecode :
      taggedWitVar? (widthOneParityCompactFamily n) ∘
          (fun i => (Fin.natAdd n i, (0, 0))) = some := by
    funext i
    exact (widthOneParityCompactFamily_taggedWitVar i).2
  rw [hdecode, List.filterMap_some]

/-- Fresh filtering composes over append when the second pass starts with every variable decoded
by the first pass marked as seen. -/
private theorem freshTaggedAux_append_exact {n G : ℕ}
    (gates : Fin G → List (Clause n)) :
    ∀ (seen : Finset (Fin n)) (as bs : List (TaggedWitEntry G)),
      freshTaggedAux gates seen (as ++ bs) =
        freshTaggedAux gates seen as ++
          freshTaggedAux gates
            (seen ∪ (as.filterMap (taggedWitVar? gates)).toFinset) bs := by
  intro seen as
  induction as generalizing seen with
  | nil => simp [freshTaggedAux]
  | cons a as ih =>
      intro bs
      cases hvar : taggedWitVar? gates a with
      | none => simpa [freshTaggedAux, hvar] using ih seen bs
      | some v =>
          by_cases hv : v ∈ seen
          · simp [freshTaggedAux, hvar, hv, ih]
          · simp [freshTaggedAux, hvar, hv, ih, Finset.insert_union]

private theorem freshTaggedAux_eq_self_of_nodup_disjoint {n G : ℕ}
    (gates : Fin G → List (Clause n)) :
    ∀ (seen : Finset (Fin n)) (as : List (TaggedWitEntry G)),
      (∀ e ∈ as, ∃ v, taggedWitVar? gates e = some v) →
      (as.filterMap (taggedWitVar? gates)).Nodup →
      Disjoint (as.filterMap (taggedWitVar? gates)).toFinset seen →
      freshTaggedAux gates seen as = as := by
  intro seen as
  induction as generalizing seen with
  | nil => simp [freshTaggedAux]
  | cons a as ih =>
      intro hsome hnodup hdisj
      obtain ⟨v, hv⟩ := hsome a (by simp)
      rw [freshTaggedAux, hv]
      have hvseen : v ∉ seen := by
        intro h
        have hav : v ∈
            (List.filterMap (taggedWitVar? gates) (a :: as)).toFinset := by
          simp [hv]
        exact Finset.disjoint_left.mp hdisj hav h
      simp only [hvseen, if_false]
      congr 1
      apply ih (insert v seen)
      · intro e he
        exact hsome e (by simp [he])
      · simp only [List.filterMap_cons, hv] at hnodup
        exact (List.nodup_cons.mp hnodup).2
      · apply Finset.disjoint_left.mpr
        intro q hq hqseen
        simp only [Finset.mem_insert] at hqseen
        rcases hqseen with rfl | hqseen
        · simp only [List.filterMap_cons, hv] at hnodup
          exact (List.nodup_cons.mp hnodup).1 (by simpa using hq)
        · have hqcons :
              q ∈ (List.filterMap (taggedWitVar? gates) (a :: as)).toFinset := by
            rw [List.filterMap_cons, hv, List.toFinset_cons]
            exact Finset.mem_insert_of_mem hq
          exact Finset.disjoint_left.mp hdisj hqcons hqseen

private theorem freshTaggedAux_eq_nil_of_vars_subset {n G : ℕ}
    (gates : Fin G → List (Clause n)) :
    ∀ (seen : Finset (Fin n)) (as : List (TaggedWitEntry G)),
      (as.filterMap (taggedWitVar? gates)).toFinset ⊆ seen →
      freshTaggedAux gates seen as = [] := by
  intro seen as
  induction as generalizing seen with
  | nil => simp [freshTaggedAux]
  | cons a as ih =>
      intro hsub
      rw [freshTaggedAux]
      cases hvar : taggedWitVar? gates a with
      | none =>
          apply ih seen
          simpa [hvar] using hsub
      | some v =>
          have hvseen : v ∈ seen := hsub (by simp [hvar])
          simp only [hvseen, if_true]
          apply ih seen
          intro q hq
          apply hsub
          rw [List.filterMap_cons, hvar, List.toFinset_cons]
          exact Finset.mem_insert_of_mem hq

/-- Exact tagged selector stream: every live coordinate occurs once, in increasing order, and is
represented by its positive compact-family index.  The negative copy is completely removed. -/
theorem widthOneParityCompactFamily_freshTaggedWitSeq {n fuel : ℕ}
    (sigma : Restriction n) (x : Fin n → Bool) :
    freshTaggedWitSeq (widthOneParityCompactFamily n) (fuel + 1) sigma x =
      widthOneParityCompactPositiveEntries sigma := by
  rw [freshTaggedWitSeq, widthOneParityCompactFamily_taggedRawWitSeq,
    freshTaggedAux_append_exact]
  have hpos : freshTaggedAux (widthOneParityCompactFamily n) ∅
      (widthOneParityCompactPositiveEntries sigma) =
        widthOneParityCompactPositiveEntries sigma := by
    apply freshTaggedAux_eq_self_of_nodup_disjoint
    · intro e he
      rw [widthOneParityCompactPositiveEntries_eq] at he
      simp only [List.mem_map] at he
      obtain ⟨i, hi, rfl⟩ := he
      exact ⟨i, (widthOneParityCompactFamily_taggedWitVar i).1⟩
    · rw [widthOneParityCompactPositiveEntries_decode]
      exact (List.nodup_finRange n).filter _
    · simp
  rw [hpos]
  have hneg : freshTaggedAux (widthOneParityCompactFamily n)
      (∅ ∪ ((widthOneParityCompactPositiveEntries sigma).filterMap
        (taggedWitVar? (widthOneParityCompactFamily n))).toFinset)
      (widthOneParityCompactNegativeEntries sigma) = [] := by
    apply freshTaggedAux_eq_nil_of_vars_subset
    rw [widthOneParityCompactPositiveEntries_decode,
      widthOneParityCompactNegativeEntries_decode]
    simp
  rw [hneg, List.append_nil]

/-- Decoding the exact fresh selector stream gives precisely the increasing list of live ambient
coordinates.  In particular, the result is independent of the extending assignment. -/
theorem widthOneParityCompactFamily_freshTaggedWitSeq_decode {n fuel : ℕ}
    (sigma : Restriction n) (x : Fin n → Bool) :
    (freshTaggedWitSeq (widthOneParityCompactFamily n) (fuel + 1) sigma x).filterMap
        (taggedWitVar? (widthOneParityCompactFamily n)) =
      (List.finRange n).filter fun i => sigma i = none := by
  rw [widthOneParityCompactFamily_freshTaggedWitSeq,
    widthOneParityCompactPositiveEntries_decode]

/-- The budgeted compact-family selector fixes exactly the first `d` live coordinates in ambient
`Fin` order.  This is the set-level form needed to make the endpoint map combinatorial. -/
theorem widthOneParityCompactFamily_freshTaggedPrefixVars_eq_take
    {n fuel d : ℕ} (sigma : Restriction n) (x : Fin n → Bool) :
    freshTaggedPrefixVars (widthOneParityCompactFamily n) (fuel + 1) sigma x d =
      (((List.finRange n).filter fun i => sigma i = none).take d).toFinset := by
  rw [freshTaggedPrefixVars,
    widthOneParityCompactFamily_freshTaggedWitSeq,
    widthOneParityCompactPositiveEntries_eq, ← List.map_take, List.filterMap_map]
  have hdecode :
      taggedWitVar? (widthOneParityCompactFamily n) ∘
          (fun i => (Fin.castAdd n i, (0, 0))) = some := by
    funext i
    exact (widthOneParityCompactFamily_taggedWitVar i).1
  rw [hdecode, List.filterMap_some]

/-- Consequently the compact prefix endpoint is literally the root restriction with the first
`d` live coordinates fixed according to the extending assignment.  Neither polarity nor any
other circuit occurrence enters the endpoint. -/
theorem widthOneParityCompactFamily_freshTaggedPrefixEndpoint_eq_fixOn
    {n fuel d : ℕ} (sigma : Restriction n) (x : Fin n → Bool) :
    freshTaggedPrefixEndpoint (widthOneParityCompactFamily n) (fuel + 1) sigma x d =
      fixOn sigma
        (((List.finRange n).filter fun i => sigma i = none).take d).toFinset x := by
  rw [freshTaggedPrefixEndpoint,
    widthOneParityCompactFamily_freshTaggedPrefixVars_eq_take]

/-- The `finRange` presentation used by the compact parity family is the same increasing live-set
order already used by the independent-singleton endpoint audit. -/
theorem independentLiveOrder_eq_finRange_filter_mem {n : ℕ} (S : Finset (Fin n)) :
    independentLiveOrder S = (List.finRange n).filter fun i => i ∈ S := by
  simp only [independentLiveOrder, List.ofFn_eq_map]
  have aux : ∀ L : List (Fin n),
      (L.map (fun i => if i ∈ S then [i] else [])).flatten =
        L.filter fun i => i ∈ S := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
        by_cases ha : a ∈ S <;> simp [ha, ih]
  exact aux _

/-! ### The actual canonical parity selector is maximally concentrated on a fixed-live-set atlas -/

/-- The residual live set produced by the compact parity selector from a prescribed initial live
set.  The selector fixes the first `d` coordinates in ambient order. -/
def orderedParityResidualLiveSet {n : ℕ} (S : Finset (Fin n)) (d : ℕ) :
    Finset (Fin n) :=
  S \ ((independentLiveOrder S).take d).toFinset

/-- On the explicit compact parity family, the *actual canonical tagged selector* sends every
root with live set `S` to the same residual live set, independently of both the root's fixed
values and the extending assignment. -/
theorem widthOneParityCompactFamily_fixedFreeSet_endpoint_freeVars
    {n fuel d : ℕ} {S : Finset (Fin n)} {rho : Restriction n}
    (hrho : rho ∈ fixedFreeSetSurvivors S) (x : Fin n → Bool) :
    freeVars (freshTaggedPrefixEndpoint (widthOneParityCompactFamily n)
      (fuel + 1) rho x d) = orderedParityResidualLiveSet S d := by
  rw [freeVars_freshTaggedPrefixEndpoint,
    widthOneParityCompactFamily_freshTaggedPrefixVars_eq_take]
  have hfree : freeVars rho = S := mem_fixedFreeSetSurvivors.mp hrho
  have horder : independentLiveOrder (freeVars rho) =
      (List.finRange n).filter (fun i => rho i = none) := by
    simpa only [mem_freeVars] using
      independentLiveOrder_eq_finRange_filter_mem (freeVars rho)
  rw [← horder, hfree]
  rfl

/-- Hence the endpoint live-set image of this assignment-covering atlas has cardinality one in
the strongest possible pointwise sense. -/
theorem widthOneParityCompactFamily_canonicalSelector_concentrates
    {n fuel d : ℕ} (S : Finset (Fin n)) :
    ∃ E : Finset (Fin n),
      ∀ rho ∈ fixedFreeSetSurvivors S, ∀ x : Fin n → Bool,
        freeVars (freshTaggedPrefixEndpoint (widthOneParityCompactFamily n)
          (fuel + 1) rho x d) = E := by
  exact ⟨orderedParityResidualLiveSet S d,
    fun rho hrho x =>
      widthOneParityCompactFamily_fixedFreeSet_endpoint_freeVars hrho x⟩

/-- Full canonical-selector obstruction package: the survivor atlas covers all assignments, lies
wholly in the parity bad event, satisfies the advertised global contraction, and the actual
canonical selector maps all of its roots to one residual live-coordinate set. -/
theorem parity_canonicalSelector_sampler_gap
    {n fuel K trunkDepth d selectorFuel : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K)
    (S : Finset (Fin n)) (hScard : S.card = K)
    (hchoose : 2 ^ d ≤ Nat.choose n K) :
    (∀ x : Fin n → Bool, ∃ rho ∈ fixedFreeSetSurvivors S,
        DTree.agreeRestriction rho x) ∧
    fixedFreeSetSurvivors S ⊆
      commonShallowBad (normalizedLayeredBottomFamily C) fuel K trunkDepth 0 ∧
    (fixedFreeSetSurvivors S).card * 2 ^ d ≤
      (Finset.univ.filter fun rho : Restriction n => stars rho = K).card ∧
    ∃ E : Finset (Fin n),
      ∀ rho ∈ fixedFreeSetSurvivors S, ∀ x : Fin n → Bool,
        freeVars (freshTaggedPrefixEndpoint (widthOneParityCompactFamily n)
          (selectorFuel + 1) rho x d) = E := by
  obtain ⟨hcover, hbad, hcontract⟩ := parity_fixedFreeSet_survivor_conditioning_gap
    C phase hparity hKfuel htrunk S hScard hchoose
  exact ⟨hcover, hbad, hcontract,
    widthOneParityCompactFamily_canonicalSelector_concentrates S⟩

/-! ### Randomized coordinate orders cannot repair the parity conditioning gap

The preceding obstruction did not actually depend on the increasing order once badness was
conditioned on the fixed-live-set atlas.  The whole atlas is already contained in the residual
depth-zero bad event.  Consequently adding a finite random seed, allowing the coordinate order
or selected prefix to depend arbitrarily on that seed, cannot lower the conditioned bad mass:
every seed sees exactly the same all-bad atlas.

This is the relevant quantifier order for an averaging repair.  A randomized construction would
need some seed with a small conditioned bad slice before fixing the public randomness.  The next
two theorems show that no such seed exists for the explicit compact parity family. -/

/-- Every random seed retains the complete fixed-live-set atlas inside the parity bad event.
The selector itself is deliberately absent from the conclusion: membership in the bad event is
decided at the root and hence precedes any seeded choice of coordinate order. -/
theorem parity_fixedFreeSet_every_seed_all_bad
    {Seed : Type} {n fuel K trunkDepth : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K)
    (S : Finset (Fin n)) (hScard : S.card = K) :
    ∀ _seed : Seed,
      (fixedFreeSetSurvivors S).filter (fun rho =>
        rho ∈ commonShallowBad (normalizedLayeredBottomFamily C)
          fuel K trunkDepth 0) = fixedFreeSetSurvivors S := by
  intro seed
  apply Finset.filter_eq_self.mpr
  intro rho hrho
  exact (fixedFreeSetSurvivors_subset_parity_normalized_commonShallowBad_zero
    C phase hparity hKfuel htrunk S hScard) hrho

/-- Exact finite-seed formulation: the bad seed/root pairs are the entire Cartesian product.
Thus uniform random seeds, nonuniform distributions after clearing denominators, and an averaging
argument all have conditioned bad probability one on this atlas. -/
theorem parity_fixedFreeSet_randomSeed_bad_pairs_eq_product
    {Seed : Type} [DecidableEq Seed]
    {n fuel K trunkDepth : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K)
    (S : Finset (Fin n)) (hScard : S.card = K) (seeds : Finset Seed) :
    (seeds.product (fixedFreeSetSurvivors S)).filter (fun pair =>
      pair.2 ∈ commonShallowBad (normalizedLayeredBottomFamily C)
        fuel K trunkDepth 0) =
      seeds.product (fixedFreeSetSurvivors S) := by
  apply Finset.filter_eq_self.mpr
  intro pair hpair
  have hrho : pair.2 ∈ fixedFreeSetSurvivors S :=
    (Finset.mem_product.mp hpair).2
  exact (fixedFreeSetSurvivors_subset_parity_normalized_commonShallowBad_zero
    C phase hparity hKfuel htrunk S hScard) hrho

/-- Cardinality form of the randomized obstruction.  There is no balancing loss to estimate:
the conditioned bad-pair count is exactly `|seeds| * 2^(n-K)`. -/
theorem parity_fixedFreeSet_randomSeed_bad_pairs_card
    {Seed : Type} [DecidableEq Seed]
    {n fuel K trunkDepth : ℕ} (C : Layered n) (phase : Bool)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K)
    (S : Finset (Fin n)) (hScard : S.card = K) (seeds : Finset Seed) :
    ((seeds.product (fixedFreeSetSurvivors S)).filter (fun pair =>
      pair.2 ∈ commonShallowBad (normalizedLayeredBottomFamily C)
        fuel K trunkDepth 0)).card = seeds.card * 2 ^ (n - K) := by
  rw [parity_fixedFreeSet_randomSeed_bad_pairs_eq_product
    C phase hparity hKfuel htrunk S hScard seeds]
  calc
    (seeds.product (fixedFreeSetSurvivors S)).card =
        seeds.card * (fixedFreeSetSurvivors S).card := by
      simpa only using Finset.card_product seeds (fixedFreeSetSurvivors S)
    _ = seeds.card * 2 ^ (n - K) := by
      rw [card_fixedFreeSetSurvivors S, hScard]

/-- Every exact candidate in a compact-family endpoint fiber is obtained by re-freeing a
`d`-set strictly below every residual live coordinate.  This includes the empty-residual case:
`independentStrictBelow ∅` is the whole ambient coordinate set.

The result is deliberately an inclusion, not an equality.  The endpoint also records the values
chosen by `commonShallowBadAssignment` on the re-freed coordinates, and an arbitrary compatible
ordered `d`-set need not reproduce those fixed Boolean values. -/
theorem widthOneParityCompactFamily_candidateSets_subset_ordered
    {n fuel K d : ℕ} (kappa : Restriction n) :
    ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets
        (widthOneParityCompactFamily n)
        (fuel + 1) K d 0 kappa ⊆
      (independentStrictBelow (freeVars kappa)).powersetCard d := by
  classical
  intro S hS
  let assignment := commonShallowBadAssignment (widthOneParityCompactFamily n)
    (fuel + 1) K d 0
  have hc := hS
  simp only [ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets,
    Finset.mem_filter] at hc
  have hcard : S.card = d := (Finset.mem_powersetCard.mp hc.1).2
  let root : Restriction n := freeOn kappa S
  have hvars : freshTaggedPrefixVars (widthOneParityCompactFamily n) (fuel + 1)
      root (assignment root) d = S := hc.2.2.1
  have hendpoint : freshTaggedPrefixEndpoint (widthOneParityCompactFamily n) (fuel + 1)
      root (assignment root) d = kappa := hc.2.2.2
  have horder : ((independentLiveOrder (freeVars root)).take d).toFinset = S := by
    rw [independentLiveOrder_eq_finRange_filter_mem]
    simpa only [mem_freeVars] using
      (widthOneParityCompactFamily_freshTaggedPrefixVars_eq_take
        root (assignment root) |>.symm.trans hvars)
  have hSfree : S ⊆ freeVars root := by
    intro i hi
    simp [root, mem_freeVars, freeOn, hi]
  have hdroot : d ≤ (freeVars root).card := by
    rw [← hcard]
    exact Finset.card_le_card hSfree
  have hresidual :
      freeVars root \ ((independentLiveOrder (freeVars root)).take d).toFinset =
        freeVars kappa := by
    rw [horder]
    have hfree := freeVars_freshTaggedPrefixEndpoint
      (widthOneParityCompactFamily n) (fuel + 1) root (assignment root) d
    rw [hendpoint] at hfree
    rw [hvars] at hfree
    exact hfree.symm
  have hconv := independentLiteral_prefixEndpoint_converse
    (freeVars root) (freeVars kappa) hdroot
    (show freshTaggedPrefixEndpoint (independentLiteralGates n) 1
        (independentRoot (freeVars root)) (independentAssignment n) d =
          independentRoot (freeVars kappa) by
      rw [independentLiteral_freshTaggedPrefixEndpoint_eq_sdiff, hresidual])
  rw [Finset.mem_powersetCard]
  refine ⟨?_, hcard⟩
  simpa only [horder] using hconv.2.1

/-- Ordered fixing replaces the ambient fixed-coordinate ceiling by the exact initial-segment
binomial envelope at each endpoint.  The remaining gap to equality is only the endpoint-value
compatibility described above. -/
theorem widthOneParityCompactFamily_candidateSets_card_le_orderedChoose
    {n fuel K d : ℕ} (kappa : Restriction n) :
    (ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets
      (widthOneParityCompactFamily n)
      (fuel + 1) K d 0 kappa).card ≤
        Nat.choose (independentStrictBelow (freeVars kappa)).card d := by
  calc
    _ ≤ ((independentStrictBelow (freeVars kappa)).powersetCard d).card :=
      Finset.card_le_card
        (widthOneParityCompactFamily_candidateSets_subset_ordered kappa)
    _ = Nat.choose (independentStrictBelow (freeVars kappa)).card d :=
      Finset.card_powersetCard d _

/-- Nonempty residual endpoints expose the ceiling as `choose(min(E),d)`. -/
theorem widthOneParityCompactFamily_candidateSets_card_le_choose_min'
    {n fuel K d : ℕ} (kappa : Restriction n)
    (hfree : (freeVars kappa).Nonempty) :
    (ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets
      (widthOneParityCompactFamily n)
      (fuel + 1) K d 0 kappa).card ≤ Nat.choose ((freeVars kappa).min' hfree).val d := by
  simpa [independentStrictBelow_eq_Iio_min' (freeVars kappa) hfree, Fin.card_Iio] using
    widthOneParityCompactFamily_candidateSets_card_le_orderedChoose kappa

/-- Empty residual endpoints are the boundary case: every ambient coordinate is strictly below
the empty set, so the ordered envelope is the full `choose(n,d)`. -/
theorem widthOneParityCompactFamily_candidateSets_card_le_choose_of_freeVars_eq_empty
    {n fuel K d : ℕ} (kappa : Restriction n)
    (hfree : freeVars kappa = ∅) :
    (ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets
      (widthOneParityCompactFamily n)
      (fuel + 1) K d 0 kappa).card ≤ Nat.choose n d := by
  simpa [hfree, independentStrictBelow] using
    widthOneParityCompactFamily_candidateSets_card_le_orderedChoose kappa

/-- On a nonempty `(K-d)`-live endpoint shell, the least possible residual coordinate recovers
the previous uniform ceiling.  Thus coordinate ordering sharpens individual fibers but does not,
by itself, improve the worst-case product-aware alphabet bound. -/
theorem widthOneParityCompactFamily_candidateSets_card_le_shellChoose
    {n fuel K d : ℕ} (kappa : Restriction n) (hstars : stars kappa = K - d)
    (hresidual : 0 < K - d) :
    (ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets
      (widthOneParityCompactFamily n) (fuel + 1) K d 0 kappa).card ≤
        Nat.choose (n - (K - d)) d := by
  have hfree : (freeVars kappa).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have : stars kappa = 0 := by simp [stars, hempty]
    omega
  calc
    _ ≤ Nat.choose ((freeVars kappa).min' hfree).val d :=
      widthOneParityCompactFamily_candidateSets_card_le_choose_min' kappa hfree
    _ ≤ Nat.choose (n - (K - d)) d := by
      apply Nat.choose_le_choose
      apply min'_val_le_card_complement (freeVars kappa)
      · simpa [stars] using hstars

/-! The preceding upper bound still uses the opaque semantic choice made by
`commonShallowBadAssignment`.  The next two results test whether that opacity is essential by
switching to the explicit coherent all-false extension on the independent-root slice. -/

/-- On an all-false independent root, the compact two-polarity family and the positive-only
independent singleton family have exactly the same prefix endpoint.  This is uniform in the
prefix budget and positive fuel; it follows from the already computed assignment-independent
compact selector stream. -/
theorem widthOneParityCompactFamily_independentRoot_prefixEndpoint
    {n fuel d : ℕ} (S : Finset (Fin n)) :
    freshTaggedPrefixEndpoint (widthOneParityCompactFamily n) (fuel + 1)
        (independentRoot S) (independentAssignment n) d =
      freshTaggedPrefixEndpoint (independentLiteralGates n) 1
        (independentRoot S) (independentAssignment n) d := by
  rw [widthOneParityCompactFamily_freshTaggedPrefixEndpoint_eq_fixOn,
    freshTaggedPrefixEndpoint,
    independentLiteral_freshTaggedPrefixVars_eq_take,
    independentLiveOrder_eq_finRange_filter_mem]
  congr 1
  ext i
  simp [independentRoot]

/-- The compact family still contains both canonical polarities of every syntactic bottom gate,
so it can be fed directly to the existing layered common-trunk collapse bridge. -/
theorem widthOneParityCompactFamily_covers (n : ℕ) :
    CoversLayeredBottoms (widthOneParityCompactFamily n)
      (widthOneParityLayered n) := by
  intro cs hcs
  simp [widthOneParityLayered, assignmentConjunction, assignmentAtom, bottomGates,
    bottomGatesList_eq] at hcs
  obtain ⟨a, ha, i, rfl⟩ := hcs
  cases h : a i
  · constructor
    · refine ⟨Fin.natAdd n i, fun fuel sigma ↦ ?_⟩
      simp [assignmentLiteral, h]
    · refine ⟨Fin.castAdd n i, fun fuel sigma ↦ ?_⟩
      simp [assignmentLiteral, h, negDNF, negLit]
  · constructor
    · refine ⟨Fin.castAdd n i, fun fuel sigma ↦ ?_⟩
      simp [assignmentLiteral, h]
    · refine ⟨Fin.natAdd n i, fun fuel sigma ↦ ?_⟩
      simp [assignmentLiteral, h, negDNF, negLit]

/-- Compacting the two-polarity alphabet does not remove any semantic bad roots: below the live
dimension, residual depth zero is still impossible on every exact-shell restriction. -/
theorem widthOneParityCompactFamily_commonShallowBad_zero_eq_shell
    {n fuel K trunkDepth : ℕ} (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K) :
    commonShallowBad (widthOneParityCompactFamily n) fuel K trunkDepth 0 =
      Finset.univ.filter fun sigma : Restriction n => stars sigma = K := by
  apply parity_covered_commonShallowBad_zero_eq_shell
    (widthOneParityCompactFamily n) (widthOneParityLayered n) false
    (widthOneParityCompactFamily_covers n)
  · intro x
    simpa using widthOneParityLayered_eval n x
  · exact hKfuel
  · exact htrunk

/-- Exact full-shell count for the compact `2n` first-round gate alphabet. -/
theorem widthOneParityCompactFamily_commonShallowBad_zero_card
    {n fuel K trunkDepth : ℕ} (hKfuel : K ≤ fuel) (htrunk : trunkDepth < K) :
    (commonShallowBad (widthOneParityCompactFamily n) fuel K trunkDepth 0).card =
      Nat.choose n K * 2 ^ (n - K) := by
  rw [widthOneParityCompactFamily_commonShallowBad_zero_eq_shell hKfuel htrunk,
    card_stars_eq]

/-- The sharp ordered binomial envelope is genuinely attained by a coherent explicit assignment
on an actual residual-depth-zero parity bad slice.  For every nonempty residual live set `E`, all
roots obtained by adjoining a `d`-set strictly below `E` are bad roots on the same exact shell and
the all-false extension sends every one of them to the common endpoint `independentRoot E`.

Thus the worst ordered multiplicity is not caused by the arbitrary values hidden in
`commonShallowBadAssignment`: a parity-specific coherent witness realizes the entire ordered
subfiber. -/
theorem widthOneParityCompactFamily_orderedFiber_bad_and_endpoint
    {n fuel d : ℕ} (E : Finset (Fin n)) (hE : E.Nonempty)
    (hfuel : d + E.card ≤ fuel + 1) :
    (independentOrderedFiber E d).card =
        Nat.choose (independentStrictBelow E).card d ∧
      ∀ rho ∈ independentOrderedFiber E d,
        rho ∈ commonShallowBad (widthOneParityCompactFamily n)
            (fuel + 1) (d + E.card) d 0 ∧
          freshTaggedPrefixEndpoint (widthOneParityCompactFamily n) (fuel + 1)
            rho (independentAssignment n) d = independentRoot E := by
  constructor
  · exact (independentOrderedFiber_card_and_endpoint E).1
  · intro rho hrho
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hrho
    have hDcard : D.card = d := (Finset.mem_powersetCard.mp hD).2
    have hDsub : D ⊆ independentStrictBelow E :=
      (Finset.mem_powersetCard.mp hD).1
    have hdisjoint : Disjoint D E := by
      rw [Finset.disjoint_left]
      intro i hiD hiE
      exact ((Finset.mem_filter.mp (hDsub hiD)).2 i hiE).false
    have hunionCard : (D ∪ E).card = d + E.card := by
      rw [Finset.card_union_of_disjoint hdisjoint, hDcard]
    have hstars : stars (independentRoot (D ∪ E)) = d + E.card := by
      rw [stars, freeVars_independentRoot, hunionCard]
    constructor
    · rw [widthOneParityCompactFamily_commonShallowBad_zero_eq_shell hfuel (by
          have hEpos : 0 < E.card := Finset.card_pos.mpr hE
          omega)]
      simp [hstars]
    · rw [widthOneParityCompactFamily_independentRoot_prefixEndpoint]
      exact (independentOrderedFiber_card_and_endpoint E).2
        (independentRoot (D ∪ E)) (by
          rw [independentOrderedFiber, Finset.mem_image]
          exact ⟨D, hD, rfl⟩)

/-- In the proportional `K = 2*d` shell, a terminal residual segment attains the previous uniform
ceiling `choose (n-d) d` inside the compact parity family's actual bad event.  This is the exact
worst-case calibration needed by the product-aware shell audit for the coherent all-false
assignment. -/
theorem exists_widthOneParityCompactFamily_orderedFiber_maximum_bad
    {n fuel d : ℕ} (hd : 0 < d) (h2dn : 2 * d ≤ n)
    (hfuel : 2 * d ≤ fuel + 1) :
    ∃ (E : Finset (Fin n)) (hE : E.Nonempty),
      E.card = d ∧
        (independentOrderedFiber E d).card = Nat.choose (n - d) d ∧
        ∀ rho ∈ independentOrderedFiber E d,
          rho ∈ commonShallowBad (widthOneParityCompactFamily n)
              (fuel + 1) (2 * d) d 0 ∧
            freshTaggedPrefixEndpoint (widthOneParityCompactFamily n) (fuel + 1)
              rho (independentAssignment n) d = independentRoot E := by
  obtain ⟨E, hE, hEcard, hmax⟩ :=
    exists_independentFixedShellEndpointFiber_card_eq_choose_card_complement
      hd (by omega : d ≤ n)
  have hordered : independentFixedShellEndpointFiber (2 * d) d E =
      independentOrderedFiber E d :=
    independentFixedShellEndpointFiber_eq_ordered E (by omega) (by omega)
  have hdata := widthOneParityCompactFamily_orderedFiber_bad_and_endpoint
    (fuel := fuel) E hE (by simpa [hEcard, Nat.two_mul] using hfuel)
  refine ⟨E, hE, hEcard, ?_, ?_⟩
  · rw [← hordered]
    exact hmax
  · simpa [hEcard, Nat.two_mul] using hdata.2

/-! ### The coherent compact-parity assignment as a conditioned code -/

/-- Preserve every value already fixed by the root and set every live coordinate to false.  This
is a coherent extension on the whole restriction space, not just on the independent-root slice. -/
def restrictionFalseExtension {n : ℕ} (sigma : Restriction n) : Fin n → Bool :=
  fun i => (sigma i).getD false

theorem restrictionFalseExtension_extends {n : ℕ} (sigma : Restriction n) :
    Rung4Restriction.Extends sigma (restrictionFalseExtension sigma) := by
  intro i b hi
  simp [restrictionFalseExtension, hi]

/-- The compact selector has exactly one fresh entry per live coordinate. -/
theorem widthOneParityCompactFamily_freshTaggedWitSeq_length_eq_stars
    {n fuel : ℕ} (sigma : Restriction n) (x : Fin n → Bool) :
    (freshTaggedWitSeq (widthOneParityCompactFamily n) (fuel + 1) sigma x).length =
      stars sigma := by
  rw [widthOneParityCompactFamily_freshTaggedWitSeq,
    widthOneParityCompactPositiveEntries_eq, List.length_map, stars]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext i
  simp [freeVars]

/-- The ragged prefix encoder instantiated with the coherent false-on-live extension.  Unlike
`commonShallowBadPrefixCode`, its endpoint does not depend on a classical choice of a deep
residual witness. -/
noncomputable def coherentParityPrefixCode
    {n fuel K d : ℕ} (hdK : d ≤ K) :
    ConditionedFirstRoundCode
      (commonShallowBad (widthOneParityCompactFamily n) (fuel + 1) K d 0) := by
  let bad := commonShallowBad (widthOneParityCompactFamily n) (fuel + 1) K d 0
  let assignment : ↑bad → Fin n → Bool := fun root ↦ restrictionFalseExtension root.1
  let endpoint : ↑bad → Restriction n := fun root ↦
    freshTaggedPrefixEndpoint (widthOneParityCompactFamily n) (fuel + 1)
      root.1 (assignment root) d
  let encode : ↑bad → PrefixActualSymLabel 1 d (widthOneParityCompactFamily n) :=
    fun root ↦ canonicalPrefixActualSymLabel (d := d) (widthOneParityCompactFamily n)
      (widthOneParityCompactFamily_normalized n).1
      (widthOneParityCompactFamily_normalized n).2 (fuel + 1) root.1 (assignment root)
  apply ConditionedFirstRoundCode.ofInjectivePair endpoint encode
  intro root₁ root₂ hpairs
  apply Subtype.ext
  apply freshTaggedPrefixEndpoint_inj_of_vars_eq (widthOneParityCompactFamily n) (fuel + 1)
    (restrictionFalseExtension_extends root₁.1)
    (restrictionFalseExtension_extends root₂.1)
    (congrArg Prod.fst hpairs)
  apply freshTaggedPrefixVars_eq_of_prefixActualSymLabel_eq
    (widthOneParityCompactFamily n) (widthOneParityCompactFamily_normalized n).1
    (widthOneParityCompactFamily_normalized n).2 (fuel + 1)
    root₁.1 root₂.1 (assignment root₁) (assignment root₂)
    (restrictionFalseExtension_extends root₁.1)
    (restrictionFalseExtension_extends root₂.1)
  · rw [← freshTaggedWitSeq_length_eq_trace_readOnce (widthOneParityCompactFamily n)
        (fuel + 1) root₁.1 (assignment root₁)
        (restrictionFalseExtension_extends root₁.1),
      widthOneParityCompactFamily_freshTaggedWitSeq_length_eq_stars,
      (mem_commonShallowBad.mp root₁.property).1]
    exact hdK
  · rw [← freshTaggedWitSeq_length_eq_trace_readOnce (widthOneParityCompactFamily n)
        (fuel + 1) root₂.1 (assignment root₂)
        (restrictionFalseExtension_extends root₂.1),
      widthOneParityCompactFamily_freshTaggedWitSeq_length_eq_stars,
      (mem_commonShallowBad.mp root₂.property).1]
    exact hdK
  · exact congrArg Prod.snd hpairs

/-- Reindex the coherent code independently inside each endpoint fiber. -/
noncomputable def coherentParityMaxFiberPrefixCode
    {n fuel K d : ℕ} (hdK : d ≤ K) :
    ConditionedFirstRoundCode
      (commonShallowBad (widthOneParityCompactFamily n) (fuel + 1) K d 0) :=
  (coherentParityPrefixCode (n := n) (fuel := fuel) hdK).restrictToMaxEndpointFiber

/-- Every coherent endpoint fiber obeys the same fixed-coordinate binomial ceiling. -/
theorem coherentParityPrefixCode_endpointFiberCard_le_choose_fixed
    {n fuel K d : ℕ} (hdK : d ≤ K) (kappa : Restriction n) :
    (coherentParityPrefixCode (n := n) (fuel := fuel) hdK).endpointFiberCard kappa ≤
      Nat.choose (n - stars kappa) d := by
  classical
  let code := coherentParityPrefixCode (n := n) (fuel := fuel) hdK
  let fixed := (Finset.univ : Finset (Fin n)) \ freeVars kappa
  let encodeFiber : {root :
      ↑(commonShallowBad (widthOneParityCompactFamily n) (fuel + 1) K d 0) //
      code.endpoint root = kappa} → ↑(fixed.powersetCard d) := fun root ↦
    ⟨freshTaggedPrefixVars (widthOneParityCompactFamily n) (fuel + 1) root.1.1
        (restrictionFalseExtension root.1.1) d, by
      rw [Finset.mem_powersetCard]
      constructor
      · intro v hv
        simp only [fixed, Finset.mem_sdiff]
        refine ⟨Finset.mem_univ v, ?_⟩
        have hendpoint := root.property
        change freshTaggedPrefixEndpoint (widthOneParityCompactFamily n) (fuel + 1)
          root.1.1 (restrictionFalseExtension root.1.1) d = kappa at hendpoint
        rw [← hendpoint, freeVars_freshTaggedPrefixEndpoint]
        simp [hv]
      · apply freshTaggedPrefixVars_card_eq_of_le_trace
          (widthOneParityCompactFamily n) (fuel + 1) root.1.1
          (restrictionFalseExtension root.1.1) d
          (restrictionFalseExtension_extends root.1.1)
        rw [← freshTaggedWitSeq_length_eq_trace_readOnce
            (widthOneParityCompactFamily n) (fuel + 1) root.1.1
            (restrictionFalseExtension root.1.1)
            (restrictionFalseExtension_extends root.1.1),
          widthOneParityCompactFamily_freshTaggedWitSeq_length_eq_stars,
          (mem_commonShallowBad.mp root.1.property).1]
        exact hdK⟩
  calc
    code.endpointFiberCard kappa ≤ Fintype.card ↑(fixed.powersetCard d) := by
      apply Fintype.card_le_of_injective encodeFiber
      intro root₁ root₂ hvars
      apply Subtype.ext
      apply Subtype.ext
      apply freshTaggedPrefixEndpoint_inj_of_vars_eq (widthOneParityCompactFamily n)
        (fuel + 1) (restrictionFalseExtension_extends root₁.1.1)
        (restrictionFalseExtension_extends root₂.1.1)
      · exact root₁.property.trans root₂.property.symm
      · exact congrArg Subtype.val hvars
    _ = Nat.choose (n - stars kappa) d := by
      rw [Fintype.card_coe, Finset.card_powersetCard]
      congr 2
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin]
      rfl

/-- Every coherent prefix endpoint on the exact `K`-shell has exactly `K-d` live coordinates. -/
theorem coherentParityPrefixCode_endpoint_stars
    {n fuel K d : ℕ} (hdK : d ≤ K)
    (root : ↑(commonShallowBad (widthOneParityCompactFamily n) (fuel + 1) K d 0)) :
    stars ((coherentParityPrefixCode (n := n) (fuel := fuel) hdK).endpoint root) = K - d := by
  have hlong : d ≤ (CommonTree.trace
      (CommonTree.readOnce root.1
        (canonicalFamilyTree (widthOneParityCompactFamily n) (fuel + 1) root.1))
      (restrictionFalseExtension root.1)).length := by
    rw [← freshTaggedWitSeq_length_eq_trace_readOnce (widthOneParityCompactFamily n)
        (fuel + 1) root.1 (restrictionFalseExtension root.1)
        (restrictionFalseExtension_extends root.1),
      widthOneParityCompactFamily_freshTaggedWitSeq_length_eq_stars,
      (mem_commonShallowBad.mp root.property).1]
    exact hdK
  change stars (freshTaggedPrefixEndpoint (widthOneParityCompactFamily n) (fuel + 1)
    root.1 (restrictionFalseExtension root.1) d) = K - d
  rw [stars_freshTaggedPrefixEndpoint (widthOneParityCompactFamily n) (fuel + 1)
      root.1 (restrictionFalseExtension root.1) d
      (restrictionFalseExtension_extends root.1),
    (mem_commonShallowBad.mp root.property).1,
    freshTaggedPrefixVars_card_eq_of_le_trace (widthOneParityCompactFamily n)
      (fuel + 1) root.1 (restrictionFalseExtension root.1) d
      (restrictionFalseExtension_extends root.1) hlong]

/-- On the exact `K`-shell, the coherent code's optimal alphabet retains the familiar uniform
upper bound `choose (n-(K-d)) d`. -/
theorem coherentParityMaxFiberPrefixCode_labelCard_le_choose
    {n fuel K d : ℕ} (hdK : d ≤ K) :
    (coherentParityMaxFiberPrefixCode (n := n) (fuel := fuel) hdK).labelCard ≤
      Nat.choose (n - (K - d)) d := by
  classical
  change
    ((coherentParityPrefixCode (n := n) (fuel := fuel) hdK).restrictToMaxEndpointFiber).labelCard ≤
      Nat.choose (n - (K - d)) d
  rw [ConditionedFirstRoundCode.restrictToMaxEndpointFiber_labelCard,
    ConditionedFirstRoundCode.maxRealizedEndpointFiberCard]
  apply Finset.sup_le
  intro root _
  calc
    (coherentParityPrefixCode (n := n) (fuel := fuel) hdK).endpointFiberCard
        ((coherentParityPrefixCode (n := n) (fuel := fuel) hdK).endpoint root) ≤
        Nat.choose (n - stars
          ((coherentParityPrefixCode (n := n) (fuel := fuel) hdK).endpoint root)) d :=
      coherentParityPrefixCode_endpointFiberCard_le_choose_fixed hdK _
    _ = Nat.choose (n - (K - d)) d := by
      congr 2
      exact coherentParityPrefixCode_endpoint_stars hdK root

/-- In the proportional compact-parity shell the coherent conditioned code has exactly the sharp
ordered binomial alphabet.  This packages the explicit witness into the same decoder-sound
interface consumed by the product-aware recurrence. -/
theorem coherentParityMaxFiberPrefixCode_labelCard_eq_choose
    {n fuel d : ℕ} (hd : 0 < d) (h2dn : 2 * d ≤ n)
    (hfuel : 2 * d ≤ fuel + 1) :
    (coherentParityMaxFiberPrefixCode (n := n) (fuel := fuel)
      (K := 2 * d) (d := d) (by omega)).labelCard = Nat.choose (n - d) d := by
  apply Nat.le_antisymm
  · simpa [Nat.two_mul] using
      (coherentParityMaxFiberPrefixCode_labelCard_le_choose
        (n := n) (fuel := fuel) (K := 2 * d) (d := d) (by omega))
  · obtain ⟨E, hE, hEcard, hfiberCard, hfiber⟩ :=
      exists_widthOneParityCompactFamily_orderedFiber_maximum_bad hd h2dn hfuel
    let code := coherentParityPrefixCode (n := n) (fuel := fuel)
      (K := 2 * d) (d := d) (by omega)
    let embed : ↑(independentOrderedFiber E d) →
        {root : ↑(commonShallowBad (widthOneParityCompactFamily n) (fuel + 1)
          (2 * d) d 0) // code.endpoint root = independentRoot E} := fun rho ↦ by
      have hrho := hfiber rho.1 rho.2
      refine ⟨⟨rho.1, hrho.1⟩, ?_⟩
      change freshTaggedPrefixEndpoint (widthOneParityCompactFamily n) (fuel + 1)
        rho.1 (restrictionFalseExtension rho.1) d = independentRoot E
      rw [widthOneParityCompactFamily_freshTaggedPrefixEndpoint_eq_fixOn]
      rw [widthOneParityCompactFamily_freshTaggedPrefixEndpoint_eq_fixOn] at hrho
      have hassign : ∀ i ∈
          (((List.finRange n).filter fun i => rho.1 i = none).take d).toFinset,
          restrictionFalseExtension rho.1 i = independentAssignment n i := by
        intro i hi
        have hfree : rho.1 i = none := by
          have := List.mem_toFinset.mp hi
          have := List.mem_of_mem_take this
          simpa using (List.mem_filter.mp this).2
        simp [restrictionFalseExtension, independentAssignment, hfree]
      apply Eq.trans ?_ hrho.2
      funext i
      simp only [fixOn]
      split
      · congr 1
        exact hassign i (by assumption)
      · rfl
    have hinj : Function.Injective embed := by
      intro rho₁ rho₂ h
      apply Subtype.ext
      exact congrArg (fun root => root.1.1) h
    have hle : (independentOrderedFiber E d).card ≤
        code.endpointFiberCard (independentRoot E) := by
      rw [← Fintype.card_coe]
      exact Fintype.card_le_of_injective embed hinj
    change Nat.choose (n - d) d ≤ code.restrictToMaxEndpointFiber.labelCard
    rw [ConditionedFirstRoundCode.restrictToMaxEndpointFiber_labelCard]
    calc
      Nat.choose (n - d) d = (independentOrderedFiber E d).card := hfiberCard.symm
      _ ≤ code.endpointFiberCard (independentRoot E) := hle
      _ ≤ code.maxRealizedEndpointFiberCard :=
        code.endpointFiberCard_le_maxRealized_any (independentRoot E)

/-- Exact product-aware slot obligation for the explicit parity representative when its first
round uses the coherent optimal code.  The sharp ordered fiber is now present literally as the
first charged alphabet, while the right side is the representative's exact `n * 2^(n-1)` bottom
slot capacity. -/
theorem widthOneParity_coherentCode_productAware_slot_obligation
    {n fuel d rounds terminal : ℕ} (hd : 0 < d) (h2dn : 2 * d ≤ n)
    (hfuel : 2 * d ≤ fuel + 1) (hrounds : 0 < rounds)
    (actualKeys : ℕ → ℕ)
    (hfirst : actualKeys 1 =
      (coherentParityMaxFiberPrefixCode (n := n) (fuel := fuel)
        (K := 2 * d) (d := d) (by omega)).labelCard)
    (hfit : 20 * leastFiniteProductAwareBudget rounds actualKeys terminal ≤ n) :
    (240 * Nat.choose (n - d) d + 260) *
        (26 ^ (rounds - 1) * terminal) ≤ n * 2 ^ (n - 1) := by
  have hn : 1 ≤ n := by omega
  have hbound := widthTwoParity_firstKey_depth_compression_of_productAwareSchedule_fit
    (widthOneParityLayered n) false (widthOneParityLayered_bottomWidth_two n)
    (fun x ↦ by simpa using widthOneParityLayered_eval n x)
    hrounds actualKeys hfit
  rw [hfirst, coherentParityMaxFiberPrefixCode_labelCard_eq_choose hd h2dn hfuel,
    widthOneParityLayered_bottomSlotCount hn] at hbound
  exact hbound

/-- Every nontrivial interior binomial coefficient dominates its top argument.  This deliberately
uses only Pascal's recurrence: the intended ambient comparison below needs no asymptotic estimate
or factorial approximation. -/
theorem self_le_choose_of_pos_of_lt {N k : ℕ} (hk : 0 < k) (hkN : k < N) :
    N ≤ Nat.choose N k := by
  induction N generalizing k with
  | zero => omega
  | succ N ih =>
      by_cases hkN' : k = N
      · subst k
        simpa using Nat.choose_succ_self_right N
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
        rw [Nat.choose_succ_succ]
        have hlt : j + 1 < N := by omega
        have hmain : N ≤ Nat.choose N (j + 1) := ih (by omega) hlt
        have hside : 0 < Nat.choose N j := Nat.choose_pos (by omega)
        calc
          N + 1 = 1 + N := by omega
          _ ≤ Nat.choose N j + Nat.choose N (j + 1) :=
            Nat.add_le_add (by omega) hmain

/-- In the intended proportional regime, the exact coherent first-round alphabet already makes
the one-step ambient demand too large.  The linear lower bound `choose(N,k) ≥ N` is enough: no
factorial or exponential estimate is needed. -/
theorem intended_coherent_firstRoundDemand_exceeds_ambient
    {A r : ℕ} (hA : 0 < A) (hr : 0 < r) :
    1000 * A * r <
      20 * (24 * Nat.choose (1000 * A * r - 10 * r) (10 * r) + 26) := by
  have hsub : 10 * r ≤ 1000 * A * r := by nlinarith
  have hgap : 10 * r < 1000 * A * r - 10 * r := by
    have heq := Nat.sub_add_cancel hsub
    nlinarith
  have hchoose : 1000 * A * r - 10 * r ≤
      Nat.choose (1000 * A * r - 10 * r) (10 * r) :=
    self_le_choose_of_pos_of_lt (by omega) hgap
  have heq := Nat.sub_add_cancel hsub
  nlinarith

/-- The exact conditioned alphabet therefore cannot enter even the first transition of the
product-aware recurrence at `n = 1000*A*r`, `d = 10*r`, provided the terminal survivor is
positive.  This conclusion is independent of all later alphabets: their only required property is
that the remaining least budget is nonzero. -/
theorem widthOneParity_coherentCode_productAware_not_fit_intended
    {A r fuel rounds terminal : ℕ} (hA : 0 < A) (hr : 0 < r)
    (hfuel : 20 * r ≤ fuel + 1) (hrounds : 0 < rounds) (hterminal : 0 < terminal)
    (actualKeys : ℕ → ℕ)
    (hfirst : actualKeys 1 =
      (coherentParityMaxFiberPrefixCode (n := 1000 * A * r) (fuel := fuel)
        (K := 2 * (10 * r)) (d := 10 * r) (by omega)).labelCard) :
    ¬20 * leastFiniteProductAwareBudget rounds actualKeys terminal ≤ 1000 * A * r := by
  intro hfit
  obtain ⟨remainingRounds, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrounds)
  have htail : 0 < leastFiniteProductAwareBudget remainingRounds
      (fun i => actualKeys (i + 1)) terminal :=
    leastFiniteProductAwareBudget_pos remainingRounds _ hterminal
  have hfirstDemand : 20 * (24 * actualKeys 1 + 26) ≤ 1000 * A * r := by
    calc
      20 * (24 * actualKeys 1 + 26) ≤
          20 * ((24 * actualKeys 1 + 26) *
            leastFiniteProductAwareBudget remainingRounds
              (fun i => actualKeys (i + 1)) terminal) := by
        exact Nat.mul_le_mul_left 20 (Nat.le_mul_of_pos_right _ htail)
      _ = 20 * leastFiniteProductAwareBudget (remainingRounds + 1)
          actualKeys terminal := by
        rw [leastFiniteProductAwareBudget_succ, leastProductAwarePredecessor_eq]
      _ ≤ 1000 * A * r := hfit
  have h2dn : 2 * (10 * r) ≤ 1000 * A * r := by nlinarith
  have hfuel' : 2 * (10 * r) ≤ fuel + 1 := by nlinarith
  rw [hfirst, coherentParityMaxFiberPrefixCode_labelCard_eq_choose
    (by omega) h2dn hfuel'] at hfirstDemand
  have htooLarge := intended_coherent_firstRoundDemand_exceeds_ambient hA hr
  omega

/-- The smallest nonconstant width-two parity representative: the two satisfying parity
assignments, written as a duplicate-free DNF. -/
def xorTwoClauses : List (Clause 2) :=
  [⟨[Rung4Literal.pos 0, Rung4Literal.neg 1]⟩,
   ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1]⟩]

def xorTwoLayered : Layered 2 := Layered.dnf xorTwoClauses

theorem xorTwoLayered_eval (x : Fin 2 → Bool) :
    Layered.eval xorTwoLayered x = DTree.parity x := by
  revert x
  decide

theorem xorTwoLayered_bottomWidth_two : BottomWidth 2 xorTwoLayered := by
  change ∀ cs ∈ [xorTwoClauses], ∀ T ∈ cs, T.lits.length ≤ 2
  simp [xorTwoClauses]

theorem xorTwoLayered_bottomSlotCount : bottomSlotCount xorTwoLayered = 2 := by
  decide

/-- A one-query common trunk cannot make both normalized polarities terminal on the fully live
two-bit parity cube.  Any followed leaf still has a live coordinate, while the positive bottom
gate itself computes parity and hence needs canonical depth at least one there. -/
theorem xorTwoLayered_not_commonShallowAt_one_zero :
    ¬ CommonShallowAt (normalizedLayeredBottomFamily xorTwoLayered) 2
      (fun _ : Fin 2 => none) 1 0 := by
  rintro ⟨trunk, hdepth, hleaf⟩
  let x : Fin 2 → Bool := fun _ => false
  let tau : Restriction 2 := CommonTree.run trunk x
  let path : Finset (Fin 2) := (CommonTree.queryVars trunk x).toFinset
  have hx : Rung4Restriction.Extends (fun _ : Fin 2 => none) x := by
    intro i b hi
    simp at hi
  have hpathCard : path.card ≤ 1 := by
    calc
      path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ 1 := hdepth
  have hagree : ∀ y : Fin 2 → Bool,
      Rung4Restriction.Extends (fun _ : Fin 2 => none) y →
        Rung4Restriction.Extends (CommonTree.run trunk y) y := by
    intro y hy
    exact (hleaf y hy).2.1
  have hfree : Finset.univ \ path ⊆ freeVars tau := by
    intro i hi
    rw [Finset.mem_sdiff] at hi
    rw [mem_freeVars]
    exact CommonTree.run_eq_none_of_root_free_of_not_mem_queryVars
      trunk (fun _ : Fin 2 => none) x hx hagree (by rfl) (by simpa [path] using hi.2)
  have hcomplement : (Finset.univ \ path).card = 2 - path.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ path), Finset.card_univ,
      Fintype.card_fin]
  have hstarsPos : 0 < stars tau := by
    rw [stars]
    have hcard := Finset.card_le_card hfree
    rw [hcomplement] at hcard
    omega
  obtain ⟨_hroot, _hagree, hshallow⟩ := hleaf x hx
  have hmember : xorTwoClauses ∈ bottomGates xorTwoLayered := by
    change xorTwoClauses ∈ [xorTwoClauses]
    simp
  obtain ⟨g, hg⟩ :=
    (normalizedLayeredBottomFamily_covers xorTwoLayered xorTwoClauses hmember).1
  have hzero := hshallow g
  rw [hg 2 tau] at hzero
  have hstarsFuel : stars tau ≤ 2 := by
    calc
      stars tau ≤ stars (fun _ : Fin 2 => none) :=
        stars_le_of_restrictionExtends (hleaf x hx).1
      _ = 2 := by decide
  have hdeep : stars tau ≤ (canonicalDT xorTwoClauses 2 tau).depth := by
    apply canonicalDT_depth_ge_of_parity xorTwoClauses 2 tau hstarsFuel
    intro y hy
    rw [← Layered.eval_dnf]
    exact xorTwoLayered_eval y
  omega

/-- The fully live root is an actual normalized-family bad root at the positive prefix depth used
below, rather than merely a semantic parity example outside the encoder domain. -/
theorem xorTwoAllFree_mem_normalized_commonShallowBad :
    (fun _ : Fin 2 => none) ∈
      commonShallowBad (normalizedLayeredBottomFamily xorTwoLayered) 2 2 1 0 := by
  rw [mem_commonShallowBad]
  exact ⟨by decide, xorTwoLayered_not_commonShallowAt_one_zero⟩

/-- At the canonical endpoint reached from the fully live two-bit parity root, the exact filtered
candidate family has cardinality one.  Positivity comes from that realized root; the fixed-shell
binomial ceiling makes one the only possible value. -/
theorem xorTwo_normalizedCandidateSets_card_eq_one :
    let root : ↑(commonShallowBad (normalizedLayeredBottomFamily xorTwoLayered) 2 2 1 0) :=
      ⟨fun _ => none, xorTwoAllFree_mem_normalized_commonShallowBad⟩
    let code := ConditionedFirstRoundCode.commonShallowBadPrefixCode
      (fuel := 2) (K := 2) (d := 1) (residualDepth := 0)
      (normalizedLayeredBottomFamily xorTwoLayered)
      (normalizedLayeredBottomFamily_nodup xorTwoLayered)
      (normalizedLayeredBottomFamily_width_le xorTwoLayered_bottomWidth_two) (by exact le_rfl)
    (ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets
      (normalizedLayeredBottomFamily xorTwoLayered) 2 2 1 0
      (code.endpoint root)).card = 1 := by
  dsimp only
  let root : ↑(commonShallowBad (normalizedLayeredBottomFamily xorTwoLayered) 2 2 1 0) :=
    ⟨fun _ => none, xorTwoAllFree_mem_normalized_commonShallowBad⟩
  let code := ConditionedFirstRoundCode.commonShallowBadPrefixCode
    (fuel := 2) (K := 2) (d := 1) (residualDepth := 0)
    (normalizedLayeredBottomFamily xorTwoLayered)
    (normalizedLayeredBottomFamily_nodup xorTwoLayered)
    (normalizedLayeredBottomFamily_width_le xorTwoLayered_bottomWidth_two) (by exact le_rfl)
  have heq :=
    ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets_card_eq_endpointFiberCard
      (fuel := 2) (K := 2) (d := 1) (residualDepth := 0)
      (normalizedLayeredBottomFamily xorTwoLayered)
      (normalizedLayeredBottomFamily_nodup xorTwoLayered)
      (normalizedLayeredBottomFamily_width_le xorTwoLayered_bottomWidth_two) (by exact le_rfl)
      (code.endpoint root)
  have hpos : 0 < code.endpointFiberCard (code.endpoint root) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨root, rfl⟩⟩
  have hle : code.endpointFiberCard (code.endpoint root) ≤ 1 := by
    calc
      code.endpointFiberCard (code.endpoint root) ≤ code.maxRealizedEndpointFiberCard :=
        code.endpointFiberCard_le_maxRealized root
      _ ≤ Nat.choose (2 - (2 - 1)) 1 :=
        ConditionedFirstRoundCode.commonShallowBadPrefixCode_maxRealizedEndpointFiberCard_le_choose
          (fuel := 2) (K := 2) (d := 1) (residualDepth := 0)
          (normalizedLayeredBottomFamily xorTwoLayered)
          (normalizedLayeredBottomFamily_nodup xorTwoLayered)
          (normalizedLayeredBottomFamily_width_le xorTwoLayered_bottomWidth_two) (by exact le_rfl)
      _ = 1 := by norm_num
  rw [heq]
  change code.endpointFiberCard (code.endpoint root) = 1
  omega

/-- Concrete invocation of the oversized-endpoint obstruction.  With one round and terminal
survivor one, the realized two-bit XOR endpoint requires `500` slots while the circuit has only
two.  Thus the present product-aware schedule cannot fit even with the optimal endpoint-local
alphabet. -/
theorem xorTwo_productAwareSchedule_not_fit_of_optimal_normalized_firstKey
    (actualKeys : ℕ → ℕ)
    (hfirst : actualKeys 1 =
      (ConditionedFirstRoundCode.commonShallowBadMaxFiberPrefixCode
        (fuel := 2) (K := 2) (d := 1) (residualDepth := 0)
        (normalizedLayeredBottomFamily xorTwoLayered)
        (normalizedLayeredBottomFamily_nodup xorTwoLayered)
        (normalizedLayeredBottomFamily_width_le xorTwoLayered_bottomWidth_two)
        (by exact le_rfl)).labelCard) :
    ¬ 20 * leastFiniteProductAwareBudget 1 actualKeys 1 ≤ 2 := by
  let root : ↑(commonShallowBad (normalizedLayeredBottomFamily xorTwoLayered) 2 2 1 0) :=
    ⟨fun _ => none, xorTwoAllFree_mem_normalized_commonShallowBad⟩
  apply widthTwoParity_normalizedCandidateSets_not_fit_of_oversized
    xorTwoLayered false xorTwoLayered_bottomWidth_two
    (by simpa using xorTwoLayered_eval) (by omega) (by omega) actualKeys hfirst root
  rw [xorTwoLayered_bottomSlotCount, xorTwo_normalizedCandidateSets_card_eq_one]
  norm_num

/-- Concrete two-round calibration of the alphabet-independent obstruction: even an empty first
alphabet and terminal survivor one require at least `6760` actual bottom slots. -/
theorem widthTwoParity_twoRound_productAwareSchedule_not_fit_below_6760
    {n : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (actualKeys : ℕ → ℕ)
    (hsmall : bottomSlotCount C < 6760) :
    ¬20 * leastFiniteProductAwareBudget 2 actualKeys 1 ≤ n := by
  apply widthTwoParity_productAwareSchedule_not_fit_of_depth_baseline
    C phase hw hparity (by omega) actualKeys
  norm_num
  exact hsmall

/-- Contrapositive form of the exact first-key compression threshold.  Any proposed occurrence-
sensitive alphabet that still has too many first-round keys is ruled out before later-round
amortization can matter. -/
theorem widthTwoParity_productAwareSchedule_not_fit_of_firstKey_undercompressed
    {n d terminal : ℕ} (C : Layered n) (phase : Bool)
    (hw : BottomWidth 2 C)
    (hparity : ∀ x : Fin n → Bool,
      Layered.eval C x = xor (DTree.parity x) phase)
    (hd : 0 < d) (hterminal : 0 < terminal)
    (actualKeys : ℕ → ℕ)
    (hkey : bottomSlotCount C < 240 * actualKeys 1 + 260) :
    ¬20 * leastFiniteProductAwareBudget d actualKeys terminal ≤ n := by
  intro hfit
  have hcompression :=
    widthTwoParity_firstKey_compression_of_productAwareSchedule_fit C phase hw hparity
      hd hterminal actualKeys hfit
  omega

/-- Even with one initial gate and terminal survivor one, two product-aware shallow rounds need
`38308` units of initial survivor parameter. -/
theorem leastFiniteProductAwareBudget_two_shallow_rounds_one :
    leastFiniteProductAwareBudget 2 (shallowForwardActualKeys 1) 1 = 38308 := by
  norm_num [leastFiniteProductAwareBudget, shallowForwardActualKeys, shallowSlotBound,
    leastProductAwarePredecessor, ceilDensityBudget, nextRoundProductDemand,
    layeredRoundActualKeyCap]

theorem leastFiniteProductAwareInitialShell_two_shallow_rounds_one :
    20 * leastFiniteProductAwareBudget 2 (shallowForwardActualKeys 1) 1 = 766160 := by
  rw [leastFiniteProductAwareBudget_two_shallow_rounds_one]

/-- A third cheapest shallow round raises the exact initial survivor budget to `34,094,120`, and
therefore the initial shell alone to `681,882,400` live variables. -/
theorem leastFiniteProductAwareBudget_three_shallow_rounds_one :
    leastFiniteProductAwareBudget 3 (shallowForwardActualKeys 1) 1 = 34094120 := by
  rw [leastFiniteProductAwareBudget_shallowForward_eq]
  norm_num [shallowProductBudget]

theorem leastFiniteProductAwareInitialShell_three_shallow_rounds_one :
    20 * leastFiniteProductAwareBudget 3 (shallowForwardActualKeys 1) 1 = 681882400 := by
  rw [leastFiniteProductAwareBudget_three_shallow_rounds_one]

/-- The two arithmetic obligations at every transition of a finite localized iteration: the next
`20 * R` shell fits inside the current exact `10 * R` cube, and that cube also pays the next
actual-margin premise. -/
def FiniteBackwardSurvivorSchedule (d : ℕ) (slots residual survivor : ℕ → ℕ) : Prop :=
  ∀ i < d,
    20 * survivor (i + 1) ≤ 10 * survivor i ∧
    nextRoundActualMargin (residual (i + 1)) (slots (i + 1)) ≤ 10 * survivor i

/-- Initial survivor budget used by the explicit backward construction.  The tail is shifted so
that its zeroth entry represents round one of the original schedule. -/
def initialBackwardSurvivorBudget : ℕ → (ℕ → ℕ) → (ℕ → ℕ) → ℕ
  | 0, _, _ => 0
  | d + 1, slots, residual =>
      2 * initialBackwardSurvivorBudget d (fun i => slots (i + 1))
        (fun i => residual (i + 1)) +
      nextRoundActualMargin (residual 1) (slots 1)

@[simp] theorem initialBackwardSurvivorBudget_zero (slots residual : ℕ → ℕ) :
    initialBackwardSurvivorBudget 0 slots residual = 0 := rfl

@[simp] theorem initialBackwardSurvivorBudget_succ
    (d : ℕ) (slots residual : ℕ → ℕ) :
    initialBackwardSurvivorBudget (d + 1) slots residual =
      2 * initialBackwardSurvivorBudget d (fun i => slots (i + 1))
        (fun i => residual (i + 1)) +
      nextRoundActualMargin (residual 1) (slots 1) := rfl

/-- The existential schedule can be chosen with exactly the displayed recursive initial budget;
this exposes the quantity that must fit the original ambient shell and fuel. -/
theorem exists_finiteBackwardSurvivorSchedule_initial_eq
    (d : ℕ) (slots residual : ℕ → ℕ) :
    ∃ survivor : ℕ → ℕ,
      FiniteBackwardSurvivorSchedule d slots residual survivor ∧
      survivor 0 = initialBackwardSurvivorBudget d slots residual := by
  induction d generalizing slots residual with
  | zero =>
      exact ⟨fun _ => 0, by intro i hi; omega, rfl⟩
  | succ d ih =>
      obtain ⟨tail, htail, htail0⟩ :=
        ih (fun i => slots (i + 1)) (fun i => residual (i + 1))
      let need := nextRoundActualMargin (residual 1) (slots 1)
      let survivor : ℕ → ℕ
        | 0 => 2 * tail 0 + need
        | i + 1 => tail i
      refine ⟨survivor, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
            constructor <;> simp only [survivor, Nat.zero_add]
            · omega
            · dsimp only [need]
              omega
        | succ i =>
            have hi : i < d := by omega
            simpa only [survivor, Nat.add_assoc] using htail i hi
      · simp only [survivor, initialBackwardSurvivorBudget_succ]
        rw [htail0]

/-- If every later-round actual margin is at most `A`, the explicit initial budget is bounded by
the exact geometric multiplier `2^d - 1`. -/
theorem initialBackwardSurvivorBudget_le_geometric
    (d A : ℕ) (slots residual : ℕ → ℕ)
    (hmargin : ∀ i, 1 ≤ i → i ≤ d →
      nextRoundActualMargin (residual i) (slots i) ≤ A) :
    initialBackwardSurvivorBudget d slots residual ≤ (2 ^ d - 1) * A := by
  induction d generalizing slots residual with
  | zero => simp
  | succ d ih =>
      have htail : initialBackwardSurvivorBudget d (fun i => slots (i + 1))
          (fun i => residual (i + 1)) ≤ (2 ^ d - 1) * A := by
        apply ih
        intro i hi hdi
        simpa only [Nat.add_assoc] using hmargin (i + 1) (by omega) (by omega)
      have hone : nextRoundActualMargin (residual 1) (slots 1) ≤ A :=
        hmargin 1 (by omega) (by omega)
      rw [initialBackwardSurvivorBudget_succ]
      calc
        2 * initialBackwardSurvivorBudget d (fun i => slots (i + 1))
              (fun i => residual (i + 1)) +
            nextRoundActualMargin (residual 1) (slots 1) ≤
            2 * ((2 ^ d - 1) * A) + A :=
          Nat.add_le_add (Nat.mul_le_mul_left 2 htail) hone
        _ = (2 ^ (d + 1) - 1) * A := by
          rw [pow_succ]
          have hpow : 0 < 2 ^ d := pow_pos (by omega) d
          have hid : 2 ^ d * 2 - 1 = 2 * (2 ^ d - 1) + 1 := by omega
          rw [hid]
          ring

/-- Exact two-round calibration at the smallest residual-depth choice.  Even when both residual
depths are zero, the slot recurrence turns `M₀` into `3*M₀` and then `9*M₀`, so the explicit
backward initial survivor budget is already linear with coefficient `672`. -/
theorem initialBackwardSurvivorBudget_two_shallow_rounds (M₀ : ℕ) :
    initialBackwardSurvivorBudget 2 (iteratedSlotBound M₀ (fun _ => 0)) (fun _ => 0) =
      672 * M₀ + 24 := by
  simp [initialBackwardSurvivorBudget, iteratedSlotBound, nextRoundActualMargin]
  ring

/-- Consequently the initial `20*R₀` shell and fuel floor for that two-round calibration is
`13440*M₀ + 480`. -/
theorem initialShell_two_shallow_rounds (M₀ : ℕ) :
    20 * initialBackwardSurvivorBudget 2
        (iteratedSlotBound M₀ (fun _ => 0)) (fun _ => 0) =
      13440 * M₀ + 480 := by
  rw [initialBackwardSurvivorBudget_two_shallow_rounds]
  ring

/-- Natural-number ceiling of division by ten, the exact conversion from an ambient margin to
the least survivor parameter that can pay it on a `10 * R` cube. -/
def ceilDivTen (x : ℕ) : ℕ := (x + 9) / 10

theorem le_ten_mul_ceilDivTen (x : ℕ) : x ≤ 10 * ceilDivTen x := by
  have hdiv := Nat.div_add_mod (x + 9) 10
  have hmod := Nat.mod_lt (x + 9) (by omega : 0 < 10)
  simp only [ceilDivTen]
  omega

theorem ceilDivTen_mono {x y : ℕ} (hxy : x ≤ y) : ceilDivTen x ≤ ceilDivTen y := by
  exact Nat.div_le_div_right (c := 10) (Nat.add_le_add_right hxy 9)

/-- Least recursive initial survivor budget: each round pays exactly the larger of the shell
nesting demand and the rounded-up next-round actual margin. -/
def leastBackwardSurvivorBudget : ℕ → (ℕ → ℕ) → (ℕ → ℕ) → ℕ
  | 0, _, _ => 0
  | d + 1, slots, residual =>
      max
        (2 * leastBackwardSurvivorBudget d (fun i => slots (i + 1))
          (fun i => residual (i + 1)))
        (ceilDivTen (nextRoundActualMargin (residual 1) (slots 1)))

@[simp] theorem leastBackwardSurvivorBudget_zero (slots residual : ℕ → ℕ) :
    leastBackwardSurvivorBudget 0 slots residual = 0 := rfl

@[simp] theorem leastBackwardSurvivorBudget_succ
    (d : ℕ) (slots residual : ℕ → ℕ) :
    leastBackwardSurvivorBudget (d + 1) slots residual =
      max
        (2 * leastBackwardSurvivorBudget d (fun i => slots (i + 1))
          (fun i => residual (i + 1)))
        (ceilDivTen (nextRoundActualMargin (residual 1) (slots 1))) := rfl

/-- The least recursive budget is attained by a finite survivor schedule. -/
theorem exists_finiteBackwardSurvivorSchedule_least_initial_eq
    (d : ℕ) (slots residual : ℕ → ℕ) :
    ∃ survivor : ℕ → ℕ,
      FiniteBackwardSurvivorSchedule d slots residual survivor ∧
      survivor 0 = leastBackwardSurvivorBudget d slots residual := by
  induction d generalizing slots residual with
  | zero =>
      exact ⟨fun _ => 0, by intro i hi; omega, rfl⟩
  | succ d ih =>
      obtain ⟨tail, htail, htail0⟩ :=
        ih (fun i => slots (i + 1)) (fun i => residual (i + 1))
      let margin := nextRoundActualMargin (residual 1) (slots 1)
      let need := max (2 * tail 0) (ceilDivTen margin)
      let survivor : ℕ → ℕ
        | 0 => need
        | i + 1 => tail i
      refine ⟨survivor, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
            have hnested : 2 * tail 0 ≤ need := Nat.le_max_left _ _
            have hmarginNeed : ceilDivTen margin ≤ need := Nat.le_max_right _ _
            have hpay : margin ≤ 10 * ceilDivTen margin := le_ten_mul_ceilDivTen margin
            constructor <;> simp only [survivor, Nat.zero_add]
            · dsimp only [need]
              omega
            · dsimp only [margin] at hpay ⊢
              exact hpay.trans (Nat.mul_le_mul_left 10 hmarginNeed)
        | succ i =>
            have hi : i < d := by omega
            simpa only [survivor, Nat.add_assoc] using htail i hi
      · simp only [survivor, leastBackwardSurvivorBudget_succ]
        dsimp only [need, margin]
        rw [htail0]

/-- No finite schedule can start below the least recursive budget.  Together with the attainment
theorem, this justifies comparing this value—not the earlier conservative sum—with ambient `n`
and fuel. -/
theorem leastBackwardSurvivorBudget_le_initial
    (d : ℕ) (slots residual survivor : ℕ → ℕ)
    (hschedule : FiniteBackwardSurvivorSchedule d slots residual survivor) :
    leastBackwardSurvivorBudget d slots residual ≤ survivor 0 := by
  induction d generalizing slots residual survivor with
  | zero => simp
  | succ d ih =>
      have hfirst :
          20 * survivor 1 ≤ 10 * survivor 0 ∧
          nextRoundActualMargin (residual 1) (slots 1) ≤ 10 * survivor 0 := by
        simpa using hschedule 0 (by omega)
      have htail : FiniteBackwardSurvivorSchedule d (fun i => slots (i + 1))
          (fun i => residual (i + 1)) (fun i => survivor (i + 1)) := by
        intro i hi
        simpa only [Nat.add_assoc] using hschedule (i + 1) (by omega)
      have hleastTail :
          leastBackwardSurvivorBudget d (fun i => slots (i + 1))
              (fun i => residual (i + 1)) ≤ survivor 1 :=
        ih _ _ _ htail
      have hnested :
          2 * leastBackwardSurvivorBudget d (fun i => slots (i + 1))
              (fun i => residual (i + 1)) ≤ survivor 0 := by
        omega
      have hmargin :
          ceilDivTen (nextRoundActualMargin (residual 1) (slots 1)) ≤ survivor 0 := by
        rw [ceilDivTen, Nat.div_le_iff_le_mul (by omega : 0 < 10)]
        omega
      simpa only [leastBackwardSurvivorBudget_succ, Nat.max_le] using
        And.intro hnested hmargin

/-- Uniform finite-depth bound for the least schedule.  Compared with the conservative
`(2^(d+1)-1)*A` estimate, the actual-margin scale is first divided by ten and only shell nesting
contributes geometrically. -/
theorem leastBackwardSurvivorBudget_succ_le_geometric
    (d A : ℕ) (slots residual : ℕ → ℕ)
    (hmargin : ∀ i, 1 ≤ i → i ≤ d + 1 →
      nextRoundActualMargin (residual i) (slots i) ≤ A) :
    leastBackwardSurvivorBudget (d + 1) slots residual ≤
      2 ^ d * ceilDivTen A := by
  induction d generalizing slots residual with
  | zero =>
      rw [leastBackwardSurvivorBudget_succ]
      simp only [leastBackwardSurvivorBudget_zero, Nat.mul_zero, max_eq_right (Nat.zero_le _),
        pow_zero, one_mul]
      exact ceilDivTen_mono (hmargin 1 (by omega) (by omega))
  | succ d ih =>
      have htail :
          leastBackwardSurvivorBudget (d + 1) (fun i => slots (i + 1))
              (fun i => residual (i + 1)) ≤ 2 ^ d * ceilDivTen A := by
        apply ih
        intro i hi hid
        simpa only [Nat.add_assoc] using hmargin (i + 1) (by omega) (by omega)
      have hone : ceilDivTen (nextRoundActualMargin (residual 1) (slots 1)) ≤
          ceilDivTen A := ceilDivTen_mono (hmargin 1 (by omega) (by omega))
      rw [leastBackwardSurvivorBudget_succ, Nat.max_le]
      constructor
      · calc
          2 * leastBackwardSurvivorBudget (d + 1) (fun i => slots (i + 1))
                (fun i => residual (i + 1)) ≤
              2 * (2 ^ d * ceilDivTen A) := Nat.mul_le_mul_left 2 htail
          _ = 2 ^ (d + 1) * ceilDivTen A := by rw [pow_succ]; ring
      · exact hone.trans (by
          have hp : 1 ≤ 2 ^ (d + 1) := one_le_pow₀ (by omega)
          nlinarith)

/-- Exact all-depth solution of the least schedule at residual depth zero.  The last round's
actual margin dominates every earlier margin even after the factor-two nesting charge. -/
theorem leastBackwardSurvivorBudget_shallow_exact (d M : ℕ) :
    leastBackwardSurvivorBudget (d + 1) (shallowSlotBound M) (fun _ => 0) =
      2 ^ d * ceilDivTen (nextRoundActualMargin 0 (shallowSlotBound M (d + 1))) := by
  induction d generalizing M with
  | zero => simp [leastBackwardSurvivorBudget_succ]
  | succ d ih =>
      rw [leastBackwardSurvivorBudget_succ]
      rw [show (fun i => shallowSlotBound M (i + 1)) = shallowSlotBound (M * 3) by
        funext i
        exact shallowSlotBound_succ M i]
      change max
          (2 * leastBackwardSurvivorBudget (d + 1) (shallowSlotBound (M * 3)) (fun _ => 0))
          (ceilDivTen (nextRoundActualMargin 0 (shallowSlotBound M 1))) = _
      rw [ih]
      have hslot : shallowSlotBound M 1 ≤ shallowSlotBound M (d + 2) := by
        apply Nat.mul_le_mul_left M
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have hneed : ceilDivTen (nextRoundActualMargin 0 (shallowSlotBound M 1)) ≤
          ceilDivTen (nextRoundActualMargin 0 (shallowSlotBound M (d + 2))) := by
        apply ceilDivTen_mono
        simp only [nextRoundActualMargin]
        omega
      rw [max_eq_left]
      · rw [← shallowSlotBound_succ, pow_succ]
        ring
      · calc
          ceilDivTen (nextRoundActualMargin 0 (shallowSlotBound M 1)) ≤
              ceilDivTen (nextRoundActualMargin 0 (shallowSlotBound M (d + 2))) := hneed
          _ ≤ 2 * (2 ^ d * ceilDivTen
                (nextRoundActualMargin 0 (shallowSlotBound (M * 3) (d + 1)))) := by
            rw [← shallowSlotBound_succ]
            have hpow : 1 ≤ 2 ^ d := one_le_pow₀ (by omega)
            have hp : 1 ≤ 2 * 2 ^ d := by omega
            calc
              ceilDivTen (nextRoundActualMargin 0 (shallowSlotBound M (d + 2))) =
                  1 * ceilDivTen
                    (nextRoundActualMargin 0 (shallowSlotBound M (d + 2))) := by ring
              _ ≤ (2 * 2 ^ d) * ceilDivTen
                    (nextRoundActualMargin 0 (shallowSlotBound M (d + 2))) :=
                Nat.mul_le_mul_right _ hp
              _ = 2 * (2 ^ d * ceilDivTen
                    (nextRoundActualMargin 0 (shallowSlotBound M (d + 2)))) := by ring

/-- The exact least budget specialized back to the verified forward slot recurrence. -/
theorem leastBackwardSurvivorBudget_zero_residual_exact (d M : ℕ) :
    leastBackwardSurvivorBudget (d + 1)
        (iteratedSlotBound M (fun _ => 0)) (fun _ => 0) =
      2 ^ d * ((32 * M * 3 ^ (d + 1) + 17) / 10) := by
  rw [show iteratedSlotBound M (fun _ => 0) = shallowSlotBound M by
    funext i
    exact iteratedSlotBound_zero_residual M i]
  rw [leastBackwardSurvivorBudget_shallow_exact]
  simp only [ceilDivTen, nextRoundActualMargin, shallowSlotBound]
  congr 2
  ring

/-- Consequently `d+1` cheapest rounds have initial shell/fuel demand at most the displayed
linear expression.  For fixed circuit depth this remains linear in the initial slot envelope, but
it cannot repair the separate round-zero density failure when that envelope is at least `n`. -/
theorem leastInitialShell_zero_residual_le (d M : ℕ) :
    20 * leastBackwardSurvivorBudget (d + 1)
        (iteratedSlotBound M (fun _ => 0)) (fun _ => 0) ≤
      32 * 6 ^ (d + 1) * M + 17 * 2 ^ (d + 1) := by
  rw [leastBackwardSurvivorBudget_zero_residual_exact]
  have hdiv : 10 * ((32 * M * 3 ^ (d + 1) + 17) / 10) ≤
      32 * M * 3 ^ (d + 1) + 17 :=
    Nat.mul_div_le _ _
  calc
    20 * (2 ^ d * ((32 * M * 3 ^ (d + 1) + 17) / 10)) =
        2 ^ (d + 1) * (10 * ((32 * M * 3 ^ (d + 1) + 17) / 10)) := by
      rw [pow_succ]
      ring
    _ ≤ 2 ^ (d + 1) * (32 * M * 3 ^ (d + 1) + 17) :=
      Nat.mul_le_mul_left _ hdiv
    _ = 32 * 6 ^ (d + 1) * M + 17 * 2 ^ (d + 1) := by
      rw [show 6 ^ (d + 1) = 2 ^ (d + 1) * 3 ^ (d + 1) by
        rw [← Nat.mul_pow]]
      ring

/-- Exact least-budget two-round calibration at residual depth zero.  The second-round margin
dominates the first-round demand after shell nesting. -/
theorem leastBackwardSurvivorBudget_two_shallow_rounds (M₀ : ℕ) :
    leastBackwardSurvivorBudget 2 (iteratedSlotBound M₀ (fun _ => 0)) (fun _ => 0) =
      2 * ((288 * M₀ + 17) / 10) := by
  simp only [leastBackwardSurvivorBudget_succ, leastBackwardSurvivorBudget_zero,
    iteratedSlotBound_succ, iteratedSlotBound_zero, nextRoundActualMargin, ceilDivTen,
    pow_one, Nat.mul_zero, Nat.zero_add]
  simp only [max_eq_right (Nat.zero_le _)]
  ring_nf
  rw [max_eq_left]
  have hnum : 96 * M₀ + 17 ≤ 288 * M₀ + 17 := by omega
  have hdiv := Nat.div_le_div_right (c := 10) hnum
  omega

/-- The corresponding exact initial shell/fuel demand is about `1152*M₀`, and in particular is
bounded by the displayed integral linear envelope. -/
theorem leastInitialShell_two_shallow_rounds (M₀ : ℕ) :
    20 * leastBackwardSurvivorBudget 2
        (iteratedSlotBound M₀ (fun _ => 0)) (fun _ => 0) =
      40 * ((288 * M₀ + 17) / 10) := by
  rw [leastBackwardSurvivorBudget_two_shallow_rounds]
  ring

theorem leastInitialShell_two_shallow_rounds_le (M₀ : ℕ) :
    20 * leastBackwardSurvivorBudget 2
        (iteratedSlotBound M₀ (fun _ => 0)) (fun _ => 0) ≤
      1160 * M₀ + 80 := by
  rw [leastInitialShell_two_shallow_rounds]
  have hdiv : (288 * M₀ + 17) / 10 ≤ 29 * M₀ + 2 := by
    rw [Nat.div_le_iff_le_mul (by omega : 0 < 10)]
    omega
  omega

/-- Every finite width/slot horizon has a survivor schedule when constructed backwards.  This is
deliberately an existence theorem with no initial upper bound: compatibility of the resulting
`survivor 0` with the original ambient shell and fuel is the remaining quantitative test. -/
theorem exists_finiteBackwardSurvivorSchedule (d : ℕ) (slots residual : ℕ → ℕ) :
    ∃ survivor : ℕ → ℕ, FiniteBackwardSurvivorSchedule d slots residual survivor := by
  induction d generalizing slots residual with
  | zero =>
      exact ⟨fun _ => 0, by intro i hi; omega⟩
  | succ d ih =>
      obtain ⟨tail, htail⟩ := ih (fun i => slots (i + 1)) (fun i => residual (i + 1))
      let need := nextRoundActualMargin (residual 1) (slots 1)
      let survivor : ℕ → ℕ
        | 0 => 2 * tail 0 + need
        | i + 1 => tail i
      refine ⟨survivor, ?_⟩
      intro i hi
      cases i with
      | zero =>
          constructor <;> simp only [survivor, Nat.zero_add]
          · omega
          · dsimp only [need]
            omega
      | succ i =>
          have hi : i < d := by omega
          simpa only [survivor, Nat.add_assoc] using htail i hi

/-- Specialization to the slot recurrence exported by the localized survivor round. -/
theorem exists_iteratedSlot_finiteBackwardSurvivorSchedule
    (d M₀ : ℕ) (residual : ℕ → ℕ) :
    ∃ survivor : ℕ → ℕ,
      FiniteBackwardSurvivorSchedule d (iteratedSlotBound M₀ residual) residual survivor :=
  exists_finiteBackwardSurvivorSchedule d (iteratedSlotBound M₀ residual) residual

/-- Preserve the first small failed parameter choice explicitly: the next-round margin is `104`,
so `R = 1` cannot pay it on a ten-coordinate survivor cube. -/
theorem nextRoundActualMargin_zero_one_fails :
    ¬ nextRoundActualMargin 0 1 ≤ 10 * 1 := by
  norm_num [nextRoundActualMargin]

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

/-- Canonical duplicate-free localization.  Distinct ambient clauses can become equal after fixed
literals are removed, so normalization must occur after localization.  `eraseDups` is used rather
than `dedup`: it retains the first occurrence, which is essential for preserving the canonical
first-active-term walk exactly. -/
noncomputable def localizeLiveGatesNodup {n G : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) : Fin G → List (Clause (stars τ)) :=
  fun g => (localizeLiveGates τ gates g).eraseDups

theorem localizeLiveGatesNodup_nodup {n G : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) :
    ∀ g, (localizeLiveGatesNodup τ gates g).Nodup := by
  intro g
  exact eraseDups_nodup _

theorem localizeLiveGatesNodup_width_le {n G w : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n))
    (hw : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ w) :
    ∀ g, ∀ T ∈ localizeLiveGatesNodup τ gates g, T.lits.length ≤ w := by
  intro g T hT
  apply localizeLiveGates_width_le τ gates hw g T
  exact (mem_eraseDups_iff T _).mp (by simpa [localizeLiveGatesNodup] using hT)

theorem localizeLiveGatesNodup_count_le {n G m : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n))
    (hm : ∀ g, (gates g).length ≤ m) :
    ∀ g, (localizeLiveGatesNodup τ gates g).length ≤ m := by
  intro g
  exact le_trans (eraseDups_length_le _)
    (localizeLiveGates_count_le τ gates hm g)

theorem localizeLiveGatesNodup_eval {n G : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (x : Fin (stars τ) → Bool) :
    ∀ g, DTree.dnfValue (localizeLiveGatesNodup τ gates g) x =
      DTree.dnfValue (gates g) (liftLiveAssignment τ x) := by
  intro g
  rw [← localizeLiveGates_eval τ gates x g]
  apply Bool.eq_iff_iff.mpr
  simp only [DTree.dnfValue, localizeLiveGatesNodup, List.any_eq_true]
  constructor <;> rintro ⟨T, hT, hval⟩
  · exact ⟨T, (mem_eraseDups_iff T _).mp hT, hval⟩
  · exact ⟨T, (mem_eraseDups_iff T _).mpr hT, hval⟩

/-- The normalized local tree is exactly the raw localized tree used by the existing collapse
constructor. -/
theorem canonicalDT_localizeLiveGatesNodup {n G : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (g : Fin G) (F : ℕ)
    (σ : Restriction (stars τ)) :
    canonicalDT (localizeLiveGatesNodup τ gates g) F σ =
      canonicalDT (localizeLiveGates τ gates g) F σ := by
  exact canonicalDT_eraseDups _ F σ

/-- The fixed-star canonical-depth bad event is unchanged by order-preserving normalization. -/
theorem boundedTermBad_eraseDups {n : ℕ} (cs : List (Clause n)) (K threshold : ℕ) :
    boundedTermBad cs.eraseDups K threshold = boundedTermBad cs K threshold := by
  ext ρ
  rw [mem_boundedTermBad_iff, mem_boundedTermBad_iff, canonicalDT_eraseDups]

/-- Hence simultaneous circuit badness is unchanged when every gate is normalized. -/
theorem circuitBad_eraseDups {n G : ℕ} (gates : Fin G → List (Clause n))
    (K threshold : ℕ) :
    circuitBad (fun g => (gates g).eraseDups) K threshold =
      circuitBad gates K threshold := by
  ext ρ
  rw [mem_circuitBad_iff, mem_circuitBad_iff]
  constructor <;> rintro ⟨g, hg⟩
  · exact ⟨g, by simpa [boundedTermBad_eraseDups] using hg⟩
  · exact ⟨g, by simpa [boundedTermBad_eraseDups] using hg⟩

/-- The canonical compact bad event on the current live-coordinate cube. -/
noncomputable def normalizedLocalCircuitBad {n G : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (K threshold : ℕ) :
    Finset (Restriction (stars τ)) :=
  circuitBad (localizeLiveGatesNodup τ gates) K threshold

/-- The normalized event counted by the compact theorem is exactly the raw localized event whose
lift is the genuine ambient bad event. -/
theorem normalizedLocalCircuitBad_eq {n G : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (K threshold : ℕ) :
    normalizedLocalCircuitBad τ gates K threshold =
      circuitBad (localizeLiveGates τ gates) K threshold := by
  exact circuitBad_eraseDups (localizeLiveGates τ gates) K threshold

/-- Outside the normalized local bad event, every produced shallow CNF computes the corresponding
original ambient gate throughout the selected local subcube. -/
theorem normalizedLocal_good_semanticCollapse {n G : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (K threshold : ℕ)
    (σ : Restriction (stars τ)) (hstars : stars σ = K)
    (hgood : σ ∉ normalizedLocalCircuitBad τ gates K threshold) :
    ∀ g,
      (∀ x, DTree.agreeRestriction σ x →
        cnfValue (dtreeToCNF
          (toDTree (canonicalDT (localizeLiveGatesNodup τ gates g) K σ))) x =
          DTree.dnfValue (gates g) (liftLiveAssignment τ x)) ∧
      (∀ C ∈ dtreeToCNF
          (toDTree (canonicalDT (localizeLiveGatesNodup τ gates g) K σ)),
        C.lits.length < threshold) := by
  intro g
  have hcollapse := circuit_good_semanticCollapse
    (localizeLiveGatesNodup τ gates) K threshold σ hstars hgood g
  constructor
  · intro x hx
    rw [← localizeLiveGatesNodup_eval τ gates x g]
    exact hcollapse.1 x hx
  · exact hcollapse.2

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

/-- A child good for the normalized local event lifts to a genuinely good ambient restriction. -/
theorem normalizedLocal_good_lift_not_bad {n G K threshold : ℕ} (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (σ : Restriction (stars τ))
    (hgood : σ ∉ normalizedLocalCircuitBad τ gates K threshold) :
    liftLiveRestriction τ σ ∉ circuitBad gates K threshold := by
  intro hbad
  apply hgood
  rw [normalizedLocalCircuitBad_eq]
  exact (mem_circuitBad_localize_iff τ gates K threshold σ).mp hbad

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

/-- The concrete one-round cover obtained by terminating every good child with the displayed
shallow-solver cost and brute-forcing every genuine bad child. -/
noncomputable def selectedChargedLeafNode {n G K : ℕ} (threshold : ℕ) (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (i : Fin ((stars τ).choose K))
    (residualDepth : ℕ) : ChargedCover n :=
  selectedChargedNode (threshold := threshold) τ gates i (2 ^ K)
    (fun ρ => ChargedCover.leaf ρ.1 (2 ^ residualDepth))

/-- Its recursive tree work is exactly the numerical `goodBadWork` charged by the switching
certificate. -/
theorem selectedChargedLeafNode_work_eq {n G K : ℕ} (threshold : ℕ) (τ : Restriction n)
    (gates : Fin G → List (Clause n)) (i : Fin ((stars τ).choose K))
    (residualDepth : ℕ) (hK : K ≤ stars τ) :
    (selectedChargedLeafNode threshold τ gates i residualDepth).work =
      goodBadWork (stars τ) (stars τ - K)
        (liftedSelectedBucket τ K i \
          selectedBadChildren (threshold := threshold) τ gates i).card
        (concreteBadCount (K := K)
          (circuitBad (localizeLiveGates τ gates) K threshold) i)
        residualDepth := by
  classical
  simp only [selectedChargedLeafNode, selectedChargedNode, ChargedCover.work,
    ChargedCover.root, goodBadWork]
  rw [card_selectedBadChildren]
  have hexp : stars τ - (stars τ - K) = K := by omega
  rw [hexp]
  simp [Nat.mul_comm]
  omega

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

/-- The explicit live scale used by the proportional compact switching certificate. -/
def concreteCompactScale (q : ℕ) : ℕ :=
  compactCircuitScale concreteTerms concreteG q

/-- Width-30 proportional certificate specialized to the actual concrete gate and term bounds. -/
theorem concreteCompact_selectedBucket_activeGap (q : ℕ) (hq : 0 < q)
    (gates : Fin concreteG → List (Clause (4000 * concreteCompactScale q)))
    (hnd : ∀ g, (gates g).Nodup)
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms) :
    ∃ i : Fin ((4000 * concreteCompactScale q).choose (20 * concreteCompactScale q)),
      goodBadWork (4000 * concreteCompactScale q)
        (4000 * concreteCompactScale q - 20 * concreteCompactScale q)
        (2 ^ (4000 * concreteCompactScale q - 20 * concreteCompactScale q))
        (concreteBadCount (K := 20 * concreteCompactScale q)
          (circuitBad gates (20 * concreteCompactScale q) (10 * concreteCompactScale q)) i)
        (10 * concreteCompactScale q - 1) ≤
          2 ^ (4000 * concreteCompactScale q - 8 * concreteCompactScale q) := by
  apply width30_compact_selectedBucket_activeGap concreteTerms concreteG q
    (concreteCompactScale q)
  · norm_num [concreteG, concreteM]
  · exact hq
  · rfl
  · exact hnd
  · simpa [concreteT] using hwidth
  · exact hterms

/-- The compact certificate with its ambient dimension exposed as an equality, for use on a
localized live-coordinate cube. -/
theorem concreteCompact_selectedBucket_activeGap_atSize (N q : ℕ) (hq : 0 < q)
    (hN : N = 4000 * concreteCompactScale q)
    (gates : Fin concreteG → List (Clause N))
    (hnd : ∀ g, (gates g).Nodup)
    (hwidth : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ concreteT)
    (hterms : ∀ g, (gates g).length ≤ concreteTerms) :
    ∃ i : Fin (N.choose (20 * concreteCompactScale q)),
      goodBadWork N (N - 20 * concreteCompactScale q)
        (2 ^ (N - 20 * concreteCompactScale q))
        (concreteBadCount (K := 20 * concreteCompactScale q)
          (circuitBad gates (20 * concreteCompactScale q)
            (10 * concreteCompactScale q)) i)
        (10 * concreteCompactScale q - 1) ≤
          2 ^ (N - 8 * concreteCompactScale q) := by
  subst N
  exact concreteCompact_selectedBucket_activeGap q hq gates hnd hwidth hterms

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

set_option maxRecDepth 10000 in
/-- **Proportional compact round on a real layered circuit.**  The selected bucket's charged work
has an `8r` exponent gap, and every child outside its exact genuine ambient bad set performs the
existing semantic `collapseRound`, drops one alternation, and has the promised bottom width. -/
theorem concreteCompact_padded_selectedBucket_round {n k : ℕ} (q : ℕ) (hq : 0 < q)
    (C : Layered n) (hAlt : AltO (k + 3) C)
    (hcnt : (bottomGates C).length ≤ concreteM)
    (hbw : BottomWidth concreteT C) (hbc : BottomCount concreteTerms C)
    (τ : Restriction n) (hstars : stars τ = 4000 * concreteCompactScale q) :
    ∃ i : Fin ((stars τ).choose (20 * concreteCompactScale q)),
      goodBadWork (stars τ) (stars τ - 20 * concreteCompactScale q)
        (2 ^ (stars τ - 20 * concreteCompactScale q))
        (concreteBadCount (K := 20 * concreteCompactScale q)
          (circuitBad (localizeLiveGates τ (paddedDualBottomGates C))
            (20 * concreteCompactScale q) (10 * concreteCompactScale q)) i)
        (10 * concreteCompactScale q - 1) ≤
          2 ^ (stars τ - 8 * concreteCompactScale q) ∧
      ∀ σ ∈ selectedLocalBucket (stars τ) (20 * concreteCompactScale q) i,
        σ ∉ normalizedLocalCircuitBad τ (paddedDualBottomGates C)
          (20 * concreteCompactScale q) (10 * concreteCompactScale q) →
        let ρ := liftLiveRestriction τ σ
        EquivOn ρ C (collapseRound (20 * concreteCompactScale q) ρ C) ∧
          AltO (k + 2) (collapseRound (20 * concreteCompactScale q) ρ C) ∧
          BottomWidth (10 * concreteCompactScale q)
            (collapseRound (20 * concreteCompactScale q) ρ C) := by
  let gates := localizeLiveGatesNodup τ (paddedDualBottomGates C)
  obtain ⟨i, hwork⟩ := concreteCompact_selectedBucket_activeGap_atSize
    (stars τ) q hq hstars gates
    (localizeLiveGatesNodup_nodup τ (paddedDualBottomGates C))
    (localizeLiveGatesNodup_width_le τ (paddedDualBottomGates C)
      (paddedDualBottomGates_width C hbw))
    (localizeLiveGatesNodup_count_le τ (paddedDualBottomGates C)
      (paddedDualBottomGates_count C hbc))
  refine ⟨i, ?_, ?_⟩
  · change goodBadWork (stars τ) (stars τ - 20 * concreteCompactScale q)
      (2 ^ (stars τ - 20 * concreteCompactScale q))
      (concreteBadCount (K := 20 * concreteCompactScale q)
        (normalizedLocalCircuitBad τ (paddedDualBottomGates C)
          (20 * concreteCompactScale q) (10 * concreteCompactScale q)) i)
      (10 * concreteCompactScale q - 1) ≤
        2 ^ (stars τ - 8 * concreteCompactScale q) at hwork
    rw [normalizedLocalCircuitBad_eq] at hwork
    exact hwork
  · intro σ hσ hgood
    dsimp
    have hσstars : stars σ = 20 * concreteCompactScale q :=
      mem_selectedLocalBucket_stars hσ
    have hamb := normalizedLocal_good_lift_not_bad τ (paddedDualBottomGates C) σ hgood
    apply padded_good_collapseRound C hAlt hcnt
    · simpa [stars_liftLiveRestriction] using hσstars
    · exact hamb

set_option maxRecDepth 10000 in
/-- The proportional round is realized by an actual exhaustive `ChargedCover` node.  Its good
children are explicit shallow-cost leaves and its bad children are exactly the ambient canonical
bad frontier; the real tree work inherits the compact `8r` gap. -/
theorem exists_concreteCompact_padded_chargedNode {n k : ℕ} (q : ℕ) (hq : 0 < q)
    (C : Layered n) (hAlt : AltO (k + 3) C)
    (hcnt : (bottomGates C).length ≤ concreteM)
    (hbw : BottomWidth concreteT C) (hbc : BottomCount concreteTerms C)
    (τ : Restriction n) (hstars : stars τ = 4000 * concreteCompactScale q) :
    ∃ (i : Fin ((stars τ).choose (20 * concreteCompactScale q)))
        (cover : ChargedCover n),
      cover.root = τ ∧
      cover.work ≤ 2 ^ (stars τ - 8 * concreteCompactScale q) ∧
      (∀ σ ∈ selectedLocalBucket (stars τ) (20 * concreteCompactScale q) i,
        σ ∉ normalizedLocalCircuitBad τ (paddedDualBottomGates C)
          (20 * concreteCompactScale q) (10 * concreteCompactScale q) →
        let ρ := liftLiveRestriction τ σ
        EquivOn ρ C (collapseRound (20 * concreteCompactScale q) ρ C) ∧
          AltO (k + 2) (collapseRound (20 * concreteCompactScale q) ρ C) ∧
          BottomWidth (10 * concreteCompactScale q)
            (collapseRound (20 * concreteCompactScale q) ρ C)) := by
  obtain ⟨i, hwork, hgood⟩ := concreteCompact_padded_selectedBucket_round
    q hq C hAlt hcnt hbw hbc τ hstars
  let cover := selectedChargedLeafNode (10 * concreteCompactScale q)
    τ (paddedDualBottomGates C) i
    (10 * concreteCompactScale q - 1)
  refine ⟨i, cover, rfl, ?_, hgood⟩
  rw [show cover.work = goodBadWork (stars τ)
      (stars τ - 20 * concreteCompactScale q)
      (liftedSelectedBucket τ (20 * concreteCompactScale q) i \
        selectedBadChildren (threshold := 10 * concreteCompactScale q)
          τ (paddedDualBottomGates C) i).card
      (concreteBadCount (K := 20 * concreteCompactScale q)
        (circuitBad (localizeLiveGates τ (paddedDualBottomGates C))
          (20 * concreteCompactScale q) (10 * concreteCompactScale q)) i)
      (10 * concreteCompactScale q - 1) by
    apply selectedChargedLeafNode_work_eq
    rw [hstars]
    omega]
  apply le_trans ?_ hwork
  unfold goodBadWork
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_right _
      (card_selectedGoodChildren_le τ (paddedDualBottomGates C) i)
  · exact le_rfl

/-- The currently certified child-width bound is not itself reusable by the width-30 compact
theorem.  This records the remaining depth-composition gap explicitly: another normalization or a
width-parameterized compact budget is required before the proportional round can be iterated. -/
theorem concreteCompact_childThreshold_exceeds_width30 (q : ℕ) (hq : 0 < q) :
    concreteT < 10 * concreteCompactScale q := by
  have hG : 4 ≤ concreteG := by norm_num [concreteG, concreteM]
  have hGq : 4 ≤ concreteG * q := hG.trans (Nat.le_mul_of_pos_right _ hq)
  have hp : 0 < 2 ^ (2 * concreteTerms + 6) := pow_pos (by omega) _
  have hscale : concreteG * q ≤ concreteCompactScale q := by
    simpa [concreteCompactScale, compactCircuitScale] using
      Nat.le_mul_of_pos_left (concreteG * q) hp
  norm_num [concreteT]
  omega

/-- **Width-parameterized single-gate reuse is still sublinear.**  If the next survivor count `K`
is no larger than the current width `w`, and the elementary shell ratio is small enough to absorb
the per-query factor `2w`, then `K²` is at most half the ambient dimension (up to the endpoint
one).  Thus allowing the compact theorem's width parameter to grow with its previous output cannot
restore a constant survivor density. -/
theorem singleGate_widthDensity_forces_squareRoot
    (N K w : ℕ) (hKw : K ≤ w) (hratio : 2 * w * K ≤ N - K + 1) :
    2 * K ^ 2 ≤ N + 1 := by
  have hleft : 2 * K ^ 2 ≤ 2 * w * K := by
    nlinarith
  have hright : N - K + 1 ≤ N + 1 := by omega
  exact hleft.trans (hratio.trans hright)

/-- In particular, any attempted next round that keeps a fixed positive fraction `a/b` of the
ambient variables must satisfy a quadratic ambient upper bound.  This is incompatible with an
unbounded linear-density iteration at fixed `a,b`. -/
theorem singleGate_linearDensity_ambient_bound
    (N K w a b : ℕ) (ha : 0 < a) (hKw : K ≤ w)
    (hratio : 2 * w * K ≤ N - K + 1) (hdensity : a * N ≤ b * K) :
    2 * a ^ 2 * N ^ 2 ≤ b ^ 2 * (N + 1) := by
  have hsqrt := singleGate_widthDensity_forces_squareRoot N K w hKw hratio
  have hsq : a ^ 2 * N ^ 2 ≤ b ^ 2 * K ^ 2 := by
    simpa [mul_pow] using Nat.pow_le_pow_left hdensity 2
  calc
    2 * a ^ 2 * N ^ 2 ≤ 2 * (b ^ 2 * K ^ 2) := by nlinarith
    _ = b ^ 2 * (2 * K ^ 2) := by ring
    _ ≤ b ^ 2 * (N + 1) := Nat.mul_le_mul_left _ hsqrt

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
theorem exists_concreteRetryCover_retryHeightGap {n : ℕ} (j r : ℕ) [NeZero r]
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

private theorem succ_sq_le_four_pow (k : ℕ) : (k + 1) ^ 2 ≤ 4 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        (k + 1 + 1) ^ 2 ≤ 4 * (k + 1) ^ 2 := by
          simp only [pow_two]
          nlinarith [Nat.zero_le k]
        _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (k + 1) := by rw [pow_succ]; ring

/-- **Asymptotic limitation of the retry route.**  Its certified saving `29j` is at most the square
root of the starting live dimension.  Thus increasing retry height through the geometric survivor
schedule cannot provide an `Ω(N)` exponent gap; the preceding theorem is linear in retry height,
not in ambient dimension. -/
theorem concreteRetrySaving_sq_le_ambient (j r : ℕ) [NeZero r] :
    (j * (concreteT - 1)) ^ 2 ≤
      concreteScale * (r * concreteCoverB ^ j) := by
  cases j with
  | zero => simp
  | succ k =>
      have hsq := succ_sq_le_four_pow k
      have hB4 : 4 ≤ concreteCoverB := by
        exact Nat.succ_le_iff.mpr concreteCoverB_gt_three
      have hpow : 4 ^ k ≤ concreteCoverB ^ k := Nat.pow_le_pow_left hB4 k
      have hBlarge : 29 ^ 2 ≤ concreteCoverB := by
        norm_num [concreteCoverB, concreteScale, concreteG, concreteM, concreteT,
          concreteTerms]
      have hcore : ((k + 1) * 29) ^ 2 ≤ concreteCoverB ^ (k + 1) := by
        rw [pow_succ]
        calc
          ((k + 1) * 29) ^ 2 = (k + 1) ^ 2 * 29 ^ 2 := by ring
          _ ≤ 4 ^ k * 29 ^ 2 := Nat.mul_le_mul_right _ hsq
          _ ≤ concreteCoverB ^ k * concreteCoverB :=
            Nat.mul_le_mul hpow hBlarge
      norm_num [concreteT]
      exact le_trans hcore (by
        have hsr : 1 ≤ concreteScale * r :=
          Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
            (by norm_num [concreteScale, concreteG, concreteM, concreteT, concreteTerms])
            (NeZero.ne r))
        simpa [Nat.mul_assoc] using Nat.le_mul_of_pos_left
          (concreteCoverB ^ (k + 1)) hsr)

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
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.commonShallowBadPrefixCode_endpointFiberCard_le_choose_fixed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.commonShallowBadPrefixCandidateSets_card_eq_endpointFiberCard
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.commonShallowBadMaxFiberPrefixCode_labelCard_eq_sup_candidateSets
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.commonShallowBadPrefixCode_maxRealizedEndpointFiberCard_le_choose
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.commonShallowBadMaxFiberPrefixCode_labelCard_le_choose
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
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_concreteRetryCover_retryHeightGap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteRetrySaving_sq_le_ambient
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteDeterministicRoundGap_atSize
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteDeterministicRoundGap_subcube
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteDeterministicRoundCertificate_subcube
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.stars_liftLiveRestriction
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.liveRestrictionEquiv
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.trueCount_liftLiveAssignment
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_liftLiveAssignment
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.DTree.shallow_dtree_not_parity_xor
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveLiteral_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveGates_width_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveDnf_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveCnf_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveLayered_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveLayered_depth
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveLayered_AltO
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveLayered_collapseRound_AltO
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveLayered_collapseRound_NonEmptyGates
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveLayered_BottomWidth
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveLayered_BottomCount
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveLayered_bottomGates_length
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveLayered_bottomClauseCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveLayered_bottomSlotCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.actualMargin_normalizedSurvivorRound_localized
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.supportDensity_normalizedSurvivorRound_localized
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_denseParity_normalizedCollapseSuccessor_of_realized_density
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_normalizedLayered_storedCommonTerminalAt_of_actual_density
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.StoredCommonTerminalAt.exists_localized_collapse_successor_of_realized_density
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastProductAwarePredecessor_pays
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastProductAwarePredecessor_le_of_pays
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_finiteProductAwareSurvivorSchedule_least
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastFiniteProductAwareBudget_le_initial
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastFiniteProductAwareBudget_pos
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastFiniteProductAwareBudget_two_shallow_rounds_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastProductAwarePredecessor_one_shallow_gate
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastProductAwarePredecessor_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastFiniteProductAwareBudget_shallowForward_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.shallowProductBudget_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.shallowProductBudget_upper
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.shallowProductAwareSchedule_not_fit_of_ambient_le_slots
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.shallowProductAwareSchedule_not_fit_of_ambient_le_slots_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.slots_pow_lt_ambient_of_shallowProductAwareSchedule_fit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.shallowProductAwareSchedule_not_fit_of_polynomial_slot_envelope
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_ambient_le_two_mul_bottomSlotCount
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_shallowProductAwareSchedule_not_fit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_firstKey_compression_of_productAwareSchedule_fit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastFiniteProductAwareBudget_baseline_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_firstKey_tail_budget_of_productAwareSchedule_fit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_firstKey_depth_compression_of_productAwareSchedule_fit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_productAwareSchedule_not_fit_of_depth_baseline
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_productAwareSchedule_not_fit_of_positive_firstKey
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.endpoint_encode_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.encode_injective_on_endpoint_fiber
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.endpointFiberCard_le_labelCard
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.bad_card_le_maxRealizedEndpointFiberCard_mul_endpointImage_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.bad_card_le_labelCard_mul_endpointShell_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.labelCard_pos_of_bad_nonempty
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.ofInjectivePair
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.commonShallowBadPrefixCode
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.commonShallowBadPrefixCode_labelCard
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.restrictToRealizedLabels
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.restrictToRealizedLabels_labelCard
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.realizedLabelImage_card_le_labelCard
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.realizedLabelImage_card_le_bad_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.endpointFiberCard_le_maxRealized_any
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.endpoint_maxFiberEncode_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.restrictToMaxEndpointFiber
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.restrictToMaxEndpointFiber_labelCard
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.maxRealizedEndpointFiberCard_le_labelCard
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.commonShallowBadMaxFiberPrefixCode
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.commonShallowBad_card_le_maxFiber_mul_endpointShell_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.commonShallowBadMaxFiberPrefixCode_labelCard
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.commonShallowBadRealizedPrefixCode
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ConditionedFirstRoundCode.commonShallowBadRealizedPrefixCode_labelCard
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_conditionedCodeSchedule_not_fit_of_nonempty_bad
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_commonShallowBadPrefixCode_firstKey_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_commonShallowBadRealizedPrefixCode_firstKey_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_commonShallowBadMaxFiberPrefixCode_firstKey_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_normalizedCandidateSets_firstKey_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_normalizedCandidateSets_not_fit_of_oversized
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.xorTwoLayered_not_commonShallowAt_one_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.xorTwo_normalizedCandidateSets_card_eq_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.xorTwo_productAwareSchedule_not_fit_of_optimal_normalized_firstKey
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_twoRound_productAwareSchedule_not_fit_below_6760
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthTwoParity_productAwareSchedule_not_fit_of_firstKey_undercompressed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastFiniteProductAwareInitialShell_shallow_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.shallowProductAwareSchedule_not_fit_of_ambient_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastFiniteProductAwareBudget_three_shallow_rounds_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.nextRoundActualMargin_not_le_ambient_of_ambient_le_slots
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.finiteBackwardSchedule_obligations_do_not_imply_successor_rectangular_density
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.iteratedSlotBound_zero_residual
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_finiteBackwardSurvivorSchedule_initial_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.initialBackwardSurvivorBudget_le_geometric
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.initialBackwardSurvivorBudget_two_shallow_rounds
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.initialShell_two_shallow_rounds
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.le_ten_mul_ceilDivTen
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_finiteBackwardSurvivorSchedule_least_initial_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastBackwardSurvivorBudget_le_initial
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastBackwardSurvivorBudget_succ_le_geometric
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastBackwardSurvivorBudget_shallow_exact
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastBackwardSurvivorBudget_zero_residual_exact
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastInitialShell_zero_residual_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastBackwardSurvivorBudget_two_shallow_rounds
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastInitialShell_two_shallow_rounds
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.leastInitialShell_two_shallow_rounds_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_finiteBackwardSurvivorSchedule
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_iteratedSlot_finiteBackwardSurvivorSchedule
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.nextRoundActualMargin_zero_one_fails
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveGates_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveGatesNodup_nodup
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.localizeLiveGatesNodup_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.normalizedLocal_good_semanticCollapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.canonicalDT_eraseDups
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.normalizedLocalCircuitBad_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.normalizedLocal_good_lift_not_bad
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteCompact_selectedBucket_activeGap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteCompact_padded_selectedBucket_round
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.selectedChargedLeafNode_work_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_concreteCompact_padded_chargedNode
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.concreteCompact_childThreshold_exceeds_width30
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.singleGate_widthDensity_forces_squareRoot
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.singleGate_linearDensity_ambient_bound
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
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.layeredBottomVariableSupport_localizeLiveLayered_card_le_inter
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.layeredBottomVariableSupport_localizeLiveLayered_collapseRound_card_le_inter
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.freeVars_subset_of_restrictionExtends
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.support_inter_freeVars_card_eq_stars_of_cover
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.sparseSupport16_exact_survivor_overlap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_restrictionExtends_stars_eq_inter_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_assignmentExtending_stars_eq_inter_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.fifteen_mul_stars_le_sixteen_mul_outside_of_overlap_density
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_restrictionExtends_factorSixteen_overlap_density
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.normalizedCanonicalPrefix_zeroOverlapSurvivor_of_not_supportTail
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.supportTail_normalizedSurvivorRound_localized
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.InitialSupportTailSuccessor.toState
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_initialSupportTailSuccessor
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.restriction_eq_of_extends_to_of_freeVars_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_restrictionCoarseningShellFiber_le_choose
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_initialSupportTail_rootFiber_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_initialSupportTailSuccessorFiber_le_product
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_initialSupportTailSuccessorFiber_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_initialGoodRoots_add_bad
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.initialRootShell_card_le_two_mul_good
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_initialGoodRootAssignmentPairs
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_initialGoodRootAssignmentPairDomain
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.initialGoodRoots_mul_assignments_le_successorImage
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.initialRootShell_mul_assignments_le_two_mul_successorImage
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.InitialSupportTailSuccessor.toInitialGeometricState
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.selectedInitialGeometricPath_eval_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.stars_selectedInitialGeometricEndpointRestriction
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.selectedInitialGeometricEndpointRestriction_assignment
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.selectedInitialGeometricEndpointRestriction_root_extends
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.stars_eq_of_mem_initialGeometricEndpointImage
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_initialGeometricEndpointFiber_le_product
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_initialGeometricEndpointFiber_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.initialGoodRoots_mul_assignments_le_geometricEndpointImage
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.initialRootShell_mul_assignments_le_two_mul_geometricEndpointImage
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.terminalShell_card_le_two_mul_choose_mul_of_source_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.terminalRootShell_card_le_two_mul_choose_mul_geometricEndpointImage
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_mem_initialGeometricEndpointImage
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.zeroSupportGeometric_exists_disagrees_parity
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_disagrees_parity_of_bottomSupport_card_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.sparseSupport16_exists_disagrees_parity
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.zeroSupportSurvivorScale_shell_exact
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedState.liveLayeredBottomSupportTail_eq_empty
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedState.normalizedLayered_commonShallowBad_eq_empty
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedStep.toState
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedState.exists_next_agreeing
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedState.selectedNextStep_agreeing
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedState.generatedNextLabels_complete
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedState.card_generatedNextLabels
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedTwoStep.eval_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.LocalizedSemanticPath.eval_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.LocalizedSemanticPath.parity_liftAssignment
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.liftLiveAssignment_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.LocalizedSemanticPath.liftAssignment_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.LocalizedSemanticPath.eq_of_liftAssignment_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.LocalizedSemanticPath.liftAssignment_fiber_card_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.agreeRestriction_liftLiveRestriction_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.LocalizedSemanticPath.stars_rootRestriction
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.LocalizedSemanticPath.exists_liftAssignment_eq_iff_agrees
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.LocalizedSemanticPath.liftAssignment_ranges_overlap_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_liftLiveAssignment_eq_iff_agrees
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.restrictionsCompatible_iff_exists_agrees
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.agreeingRestrictionEquivFreeSet
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_agreeing_restrictions_of_stars_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_distinct_agreeing_restriction_family_le_choose
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.liftLiveAssignment_ranges_overlap_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_distinct_restrictions_with_overlapping_lift_ranges
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportGeometricPath.endpointState
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedState.exists_terminalDnf_depth_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportGeometricPath.exists_endpointDnf_depth_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportGeometricPath.toSemanticPath_endpointN_cons
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportGeometricPath.toSemanticPath_endpointN_scheduled
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportGeometricPath.semantic_endpointN_eq_endpointState_n
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportGeometricPath.exists_semantic_endpointDnf_depth_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportGeometricPath.exists_semantic_endpoint_disagrees_parity_xor
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.liftLiveAssignment_restrict_eq_of_agrees
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedState.exists_geometric_path_lifting_assignment
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedState.selectedGeometricPath_rootRestriction_agrees
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedState.exists_geometric_path
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportGeometricPath.eval_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.selectedInitialGeometricPath_exists_disagrees_parity
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportGeometricPath.semantic_endpointN
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_assignments_agreeing_restriction
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.stars_eq_of_mem_generatedGeometricRootRestrictions
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.generatedGeometricRootFiber_subset_agreeing
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_generatedGeometricRootFiber_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.generatedGeometricRootRestrictions_product_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.stars_eq_of_mem_admissibleGeometricRootRestrictions
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_admissibleGeometricRootRestrictions_agreeing_le_choose
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.dnfValue_eq_of_canonicalDT_depth_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.Layered.eval_eq_of_bottom_canonicalDT_depth_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_mem_normalized_commonShallowBad_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_commonShallowBad_zero_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.card_fixedFreeSetSurvivors
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.fixedFreeSetSurvivors_covers_assignments
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.fixedFreeSetSurvivors_subset_parity_normalized_commonShallowBad_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.fixedFreeSetSurvivors_contraction_compatible
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_fixedFreeSet_survivor_conditioning_gap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_labelCard_mul_endpointShell_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_labelCard_power_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.intended_power_lower_forces_firstRoundDemand
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.intended_variable_power_lower_forces_firstRoundDemand
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_intended_labelCard_demand_exceeds_ambient
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_intended_conditionedCode_productAware_not_fit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_ambiguity_mul_labelCard_mul_endpointShell_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_ambiguity_mul_labelCard_power_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_intended_effectiveAlphabet_demand_exceeds_ambient
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_intended_variable_effectiveAlphabet_demand_exceeds_ambient
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_intended_boundedAmbiguity_productAware_not_fit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_intended_variable_boundedAmbiguity_productAware_not_fit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_maxFiber_mul_endpointShell_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_endpointShell_ratio_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_endpointShell_power_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_intended_endpointShell_power_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_intended_productAware_slot_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_normalized_intended_productAware_not_fit_of_slot_gap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityLayered_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityLayered_bottomSlotCount
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityLayered_bottomWidth_two
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityLayered_bottomClean
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_length
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_normalized
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_total_length
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_covers
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_covered_commonShallowBad_zero_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_commonShallowBad_zero_eq_shell
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_commonShallowBad_zero_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.runWitSeq_positive_singleton
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.runWitSeq_negative_singleton
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_positive_before_negative
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_taggedWitVar
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_taggedRawWitSeq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_freshTaggedWitSeq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_freshTaggedWitSeq_decode
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_freshTaggedPrefixVars_eq_take
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_freshTaggedPrefixEndpoint_eq_fixOn
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_fixedFreeSet_endpoint_freeVars
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_canonicalSelector_concentrates
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_canonicalSelector_sampler_gap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_fixedFreeSet_every_seed_all_bad
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_fixedFreeSet_randomSeed_bad_pairs_eq_product
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.parity_fixedFreeSet_randomSeed_bad_pairs_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_candidateSets_subset_ordered
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_candidateSets_card_le_orderedChoose
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_candidateSets_card_le_choose_min'
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_candidateSets_card_le_choose_of_freeVars_eq_empty
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_candidateSets_card_le_shellChoose
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_independentRoot_prefixEndpoint
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_orderedFiber_bad_and_endpoint
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.exists_widthOneParityCompactFamily_orderedFiber_maximum_bad
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.restrictionFalseExtension_extends
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParityCompactFamily_freshTaggedWitSeq_length_eq_stars
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.coherentParityPrefixCode
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.coherentParityMaxFiberPrefixCode
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.coherentParityMaxFiberPrefixCode_labelCard_le_choose
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.coherentParityPrefixCode_endpointFiberCard_le_choose_fixed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.coherentParityPrefixCode_endpoint_stars
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.coherentParityMaxFiberPrefixCode_labelCard_eq_choose
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParity_coherentCode_productAware_slot_obligation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.self_le_choose_of_pos_of_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.intended_coherent_firstRoundDemand_exceeds_ambient
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.widthOneParity_coherentCode_productAware_not_fit_intended
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedState.exists_next
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.ZeroSupportLocalizedState.exists_two_step
