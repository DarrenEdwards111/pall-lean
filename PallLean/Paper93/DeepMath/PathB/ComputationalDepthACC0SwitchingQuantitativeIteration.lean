import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingCircuitLinearGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3IteratedReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundCount2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvRoundREL2

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
