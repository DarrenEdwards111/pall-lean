import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingCircuitLinearGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3IteratedReduction

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

/-- Every consumed round has the width promised by its own varying threshold. -/
theorem collapseSeq_round_width {n d : ℕ} (K threshold : ℕ → ℕ)
    (ρ : ℕ → Restriction n) (C₀ : Layered n)
    (hround : ∀ i < d, GoodRound (K i) (threshold i) (collapseSeq K ρ C₀ i) (ρ i)) :
    ∀ i < d, BottomWidth (threshold i) (collapseSeq K ρ C₀ (i + 1)) := by
  intro i hi
  rw [collapseSeq_succ]
  exact collapseRound_BottomWidth (K i) (ρ i) (hround i hi).shallows

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

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.collapseSeq_terminal_dnf
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.collapseSeq_reduces_final
