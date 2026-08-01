import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPRunIndexedFaithfulTPhi
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPTranscriptObserver

/-!
# Branch-spanning dynamic holonomy on actual runs

Additive rank along one local machine trace is bounded by the clock.  The next
honest candidate is therefore a family invariant: count the distinct features
exposed by one observer at one time across a finite family of actual runs.

This file deliberately builds in two audit guardrails.

* an auxiliary label ignored by the dynamics contributes exactly zero image rank;
* every feature that factors through the final Boolean decision has rank at most two,
  even for an exponentially large, highly branching easy family such as full-AND.

Consequently an exponential branch-spanning minor requires an explicit richer
decoder on the actual states.  Merely retaining the input, counting branches, or
using Boolean correctness is not enough.  The final theorem isolates that decoder
as the remaining semantic frontier rather than assuming it inside the rank.
-/

namespace PallLean.Paper93.DeepMath.PathB.BranchSpanningDynamicHolonomy

open PvsNPRunIndexedFaithfulTPhi
open PvsNPRunIndexedFaithfulTPhi.ActualDecisionRun
open PvsNPTranscriptObserver

variable {Input State Feature Base Label : Type*}

/-- Number of distinct values of a feature over a finite run family.  This is an
image cardinality, not the cardinality of a declared ambient state type. -/
noncomputable def familyImageRank [Fintype Input] (feature : Input → Feature) : ℕ := by
  classical
  exact (Finset.univ.image feature).card

/-- Image rank never exceeds the number of available feature values. -/
theorem familyImageRank_le_card [Fintype Input] [Fintype Feature]
    (feature : Input → Feature) :
    familyImageRank feature ≤ Fintype.card Feature := by
  classical
  unfold familyImageRank
  simpa only [Finset.card_univ] using
    Finset.card_le_card (Finset.subset_univ (Finset.univ.image feature))

/-- An injective family feature realizes the whole input-family cardinality. -/
theorem familyImageRank_eq_card_of_injective [Fintype Input]
    (feature : Input → Feature) (hinj : Function.Injective feature) :
    familyImageRank feature = Fintype.card Input := by
  classical
  unfold familyImageRank
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-- Image rank is also bounded by the number of members of the source family,
without requiring the feature codomain itself to be finite. -/
theorem familyImageRank_le_domain_card [Fintype Input]
    (feature : Input → Feature) :
    familyImageRank feature ≤ Fintype.card Input := by
  classical
  unfold familyImageRank
  simpa only [Finset.card_univ] using
    (Finset.card_image_le : (Finset.univ.image feature).card ≤ Finset.univ.card)

/-- Postprocessing cannot increase family image rank. -/
theorem familyImageRank_comp_le [Fintype Input] [Fintype Base]
    (base : Input → Base) (post : Base → Feature) :
    familyImageRank (fun x => post (base x)) ≤ familyImageRank post := by
  classical
  unfold familyImageRank
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy ⊢
  rcases hy with ⟨x, rfl⟩
  exact ⟨base x, rfl⟩

/-- The branch-spanning dynamic holonomy rank at one real execution time. -/
noncomputable def branchHolonomyRankAt [Fintype Input]
    (R : ActualDecisionRun Input State) (project : State → Feature) (time : ℕ) : ℕ :=
  familyImageRank (fun x => project (R.stateAt time x))

/-- Exact hard-family criterion: if the projected actual states distinguish every
branch, branch-spanning rank is the full family size. -/
theorem branchHolonomyRankAt_eq_card_of_injective [Fintype Input]
    (R : ActualDecisionRun Input State) (project : State → Feature) (time : ℕ)
    (hinj : Function.Injective (fun x => project (R.stateAt time x))) :
    branchHolonomyRankAt R project time = Fintype.card Input :=
  familyImageRank_eq_card_of_injective _ hinj

/-! ## Guardrail 1: ignored labels contribute zero -/

/-- Taking a product with a nonempty ignored label type does not change image rank. -/
theorem familyImageRank_prod_ignored [Fintype Base] [Fintype Label] [Nonempty Label]
    (feature : Base → Feature) :
    familyImageRank (fun x : Base × Label => feature x.1) =
      familyImageRank feature := by
  classical
  unfold familyImageRank
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩
  · rintro ⟨x, rfl⟩
    let label : Label := Classical.choice (inferInstance : Nonempty Label)
    exact ⟨(x, label), rfl⟩

/-- On the repository's actual ignored-label lift, no time slice gains branch rank. -/
theorem labelIgnoredRun_branchHolonomyRankAt
    [Fintype Base] [Fintype Label] [Nonempty Label]
    (R : ActualDecisionRun Base State) (project : State → Feature) (time : ℕ) :
    branchHolonomyRankAt (labelIgnoredRun R Label) project time =
      branchHolonomyRankAt R project time := by
  change familyImageRank (fun x : Base × Label => project (R.stateAt time x.1)) =
    familyImageRank (fun x : Base => project (R.stateAt time x))
  simpa using familyImageRank_prod_ignored
    (Base := Base) (Label := Label)
    (feature := fun x : Base => project (R.stateAt time x))

/-! ## Guardrail 2: decision-only observations never look hard -/

/-- A family feature is decision-factored when all information it exposes is a
postprocessing of the run's final Boolean answer. -/
def FactorsThroughDecision (R : ActualDecisionRun Input State)
    (feature : Input → Feature) : Prop :=
  ∃ post : Bool → Feature, ∀ x, feature x = post (R.finalAnswer x)

/-- Every decision-factored feature has branch-spanning image rank at most two. -/
theorem familyImageRank_le_two_of_factorsThroughDecision [Fintype Input]
    (R : ActualDecisionRun Input State) (feature : Input → Feature)
    (hfactor : FactorsThroughDecision R feature) :
    familyImageRank feature ≤ 2 := by
  rcases hfactor with ⟨post, hpost⟩
  have hfun : feature = fun x => post (R.finalAnswer x) := by
    funext x
    exact hpost x
  rw [hfun]
  exact le_trans (familyImageRank_comp_le R.finalAnswer post)
    (by simpa using familyImageRank_le_domain_card post)

/-- In particular, observing only the final answer has rank at most two for every
actual run, independently of how many input branches the family contains. -/
theorem finalAnswer_familyImageRank_le_two [Fintype Input]
    (R : ActualDecisionRun Input State) :
    familyImageRank R.finalAnswer ≤ 2 := by
  apply familyImageRank_le_two_of_factorsThroughDecision R R.finalAnswer
  exact ⟨id, fun _ => rfl⟩

/-- Explicit full-AND guardrail.  Its exponentially large assignment family still
has decision-image rank at most two. -/
theorem fullAnd_decision_rank_le_two (m : ℕ) :
    familyImageRank (fun a : Fin m → Bool => decide (∀ i, a i = true)) ≤ 2 := by
  exact familyImageRank_le_card _

/-- Calibration warning: simply exposing the branch input itself has exponential
image rank for *every* `m`-bit family, including easy ones.  Thus injective raw-trace
rank is not by itself a hardness certificate. -/
theorem rawInput_rank_eq_two_pow (m : ℕ) :
    familyImageRank (fun a : Fin m → Bool => a) = 2 ^ m := by
  classical
  unfold familyImageRank
  simp only [Finset.image_id', Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]

/-! ## Honest exponential criterion -/

/-- Branch-spanning rank of one observer projection over the repository's residual
family, evaluated on actual states of the same real run. -/
noncomputable def residualFamilyHolonomyRankAt
    {m : ℕ} {Feature : Type} (R : ActualDecisionRun ResidualInstance State)
    (fam : FoolingResidualFamily m) (project : State → Feature) (time : ℕ) : ℕ :=
  familyImageRank (fun a => project (R.stateAt time (fam.instanceOf a)))

/-- Existing fooling-family soundness yields full family image rank on the actual
trace projection.  The soundness premise remains visible and is not inferred from
the final Boolean answer. -/
theorem residualFamilyHolonomyRankAt_eq_two_pow_of_sound
    {m : ℕ} {Feature : Type} (R : ActualDecisionRun ResidualInstance State)
    (fam : FoolingResidualFamily m) (project : State → Feature) (time : ℕ)
    (hsound : SoundOnFoolingFamily
      (fun inst => project (R.stateAt time inst)) fam) :
    residualFamilyHolonomyRankAt R fam project time = 2 ^ m := by
  have hinj : Function.Injective
      (fun a => project (R.stateAt time (fam.instanceOf a))) := by
    simpa only [branchTranscriptObserver] using
      branchTranscript_injective_of_sound
        (fun inst => project (R.stateAt time inst)) fam hsound
  rw [residualFamilyHolonomyRankAt,
    familyImageRank_eq_card_of_injective _ hinj]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- An explicit decoder of injective semantic labels from one observer projection
forces the projection itself to distinguish every branch. -/
theorem projectedState_injective_of_label_decoder
    {m : ℕ} (R : ActualDecisionRun (Fin m → Bool) State)
    (project : State → Feature) (time : ℕ)
    (label : (Fin m → Bool) → (Fin m → Bool))
    (hlabel : Function.Injective label)
    (decode : Feature → (Fin m → Bool))
    (hdecode : ∀ a, decode (project (R.stateAt time a)) = label a) :
    Function.Injective (fun a => project (R.stateAt time a)) := by
  intro a b hab
  apply hlabel
  have hdecoded := congrArg decode hab
  simpa only [hdecode] using hdecoded

/-- Branch-spanning exponential rank follows from a visible decoder on actual run
states.  This theorem does not manufacture that decoder from Boolean correctness. -/
theorem branchHolonomyRankAt_eq_two_pow_of_label_decoder
    {m : ℕ} (R : ActualDecisionRun (Fin m → Bool) State)
    (project : State → Feature) (time : ℕ)
    (label : (Fin m → Bool) → (Fin m → Bool))
    (hlabel : Function.Injective label)
    (decode : Feature → (Fin m → Bool))
    (hdecode : ∀ a, decode (project (R.stateAt time a)) = label a) :
    branchHolonomyRankAt R project time = 2 ^ m := by
  rw [branchHolonomyRankAt_eq_card_of_injective R project time
    (projectedState_injective_of_label_decoder R project time label hlabel decode hdecode)]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-!
The object is now operational and calibrated, but this is not a P-vs-NP proof.
The remaining Route G frontier is an independently derived, decision-relevant
decoder for a genuine hard residual family.  The two guardrails above prevent that
frontier from being discharged by ignored labels or by counting Boolean outcomes.
-/

end PallLean.Paper93.DeepMath.PathB.BranchSpanningDynamicHolonomy

#print axioms PallLean.Paper93.DeepMath.PathB.BranchSpanningDynamicHolonomy.labelIgnoredRun_branchHolonomyRankAt
#print axioms PallLean.Paper93.DeepMath.PathB.BranchSpanningDynamicHolonomy.familyImageRank_le_two_of_factorsThroughDecision
#print axioms PallLean.Paper93.DeepMath.PathB.BranchSpanningDynamicHolonomy.residualFamilyHolonomyRankAt_eq_two_pow_of_sound
#print axioms PallLean.Paper93.DeepMath.PathB.BranchSpanningDynamicHolonomy.branchHolonomyRankAt_eq_two_pow_of_label_decoder
