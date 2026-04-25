import PallLean.Paper93.Paper283.RouteBKeepFOBTransportAdapter
import Mathlib.RingTheory.MvPolynomial
import Mathlib.Logic.Denumerable

set_option exponentiation.threshold 1000

/-!
# Route B keepFOB finite-rank no-go

The Route B adapter previously isolated the premise that an NFrame
`CandidateGauge` should have the same flat SAT-side projection as the concrete
`keepFOB` map.  This file proves that the premise is impossible: every
`CandidateGauge` has finite-dimensional range, while `keepFOB` fixes all powers
of the first Cook-Levin variable and hence has infinite-dimensional range.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

private abbrev CLSpace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :=
  MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) ℚ

private noncomputable abbrev keepFOBProjection
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    CLSpace M n hn2 htb hns →ₗ[ℚ] CLSpace M n hn2 htb hns :=
  satDeciderGaugeKeepFOBProjection M n hn2 htb hns

private noncomputable def keepFOBRangePower
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (k : Nat) :
    LinearMap.range (keepFOBProjection M n hn2 htb hns) := by
  let i := satDeciderGaugeFirstVar M n hn2 htb hns
  refine ⟨monomial (Finsupp.single i k) (1 : ℚ), ?_⟩
  refine ⟨monomial (Finsupp.single i k) (1 : ℚ), ?_⟩
  unfold keepFOBProjection satDeciderGaugeKeepFOBProjection
  rw [PiStarConcrete.piZero_monomial]
  simp only [PiStarConcrete.keepFOB]
  rw [if_pos]
  intro j hnot
  by_cases hji : j = i
  · subst j
    exact (hnot (by change 3 ∣ (0 : Nat); exact dvd_zero 3)).elim
  · simp [Finsupp.single_eq_of_ne hji]

private theorem keepFOBRangePower_coe
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (k : Nat) :
    (keepFOBRangePower M n hn2 htb hns k : CLSpace M n hn2 htb hns) =
      monomial (Finsupp.single (satDeciderGaugeFirstVar M n hn2 htb hns) k) (1 : ℚ) :=
  rfl

private theorem linearIndependent_keepFOBRangePower
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    LinearIndependent ℚ (keepFOBRangePower M n hn2 htb hns) := by
  let i := satDeciderGaugeFirstVar M n hn2 htb hns
  have hmono :
      LinearIndependent ℚ
        (fun α : Fin (RouteBCookLevinDim M n hn2 htb hns) →₀ Nat =>
          monomial α (1 : ℚ)) := by
    simpa [MvPolynomial.coe_basisMonomials] using
      (MvPolynomial.basisMonomials
        (Fin (RouteBCookLevinDim M n hn2 htb hns)) ℚ).linearIndependent
  have hcoe :
      LinearIndependent ℚ
        (fun k : Nat =>
          (keepFOBRangePower M n hn2 htb hns k : CLSpace M n hn2 htb hns)) := by
    simpa [keepFOBRangePower_coe, i] using
      hmono.comp (fun k : Nat => Finsupp.single i k) (Finsupp.single_injective i)
  exact LinearIndependent.of_comp
    (LinearMap.range (keepFOBProjection M n hn2 htb hns)).subtype hcoe

/-- The concrete `keepFOB` flat projection has infinite-dimensional range. -/
theorem satDeciderGaugeKeepFOBProjection_range_not_finite
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ Module.Finite ℚ
      (LinearMap.range (satDeciderGaugeKeepFOBProjection M n hn2 htb hns)) := by
  intro hfinite
  have hnatFinite : Finite Nat :=
    LinearIndependent.finite
      (R := ℚ)
      (M := LinearMap.range (keepFOBProjection M n hn2 htb hns))
      (linearIndependent_keepFOBRangePower M n hn2 htb hns)
  exact (Infinite.not_finite (α := Nat)) hnatFinite

/-- If an NFrame candidate projection were equal to the concrete `keepFOB`
projection, then `keepFOB` would have finite-dimensional range. -/
theorem keepFOB_range_finite_of_candidate_projection_eq
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hPi :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi =
        satDeciderGaugeKeepFOBProjection M n hn2 htb hns) :
    Module.Finite ℚ
      (LinearMap.range (satDeciderGaugeKeepFOBProjection M n hn2 htb hns)) := by
  rw [← hPi]
  exact Pi.rank_finite

/-- No full-polynomial NFrame `CandidateGauge` can have projection equal to
the concrete `keepFOB` SAT-decider projection. -/
theorem candidate_projection_ne_satDeciderGaugeKeepFOBProjection
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi ≠
      satDeciderGaugeKeepFOBProjection M n hn2 htb hns := by
  intro hPi
  exact satDeciderGaugeKeepFOBProjection_range_not_finite M n hn2 htb hns
    (keepFOB_range_finite_of_candidate_projection_eq M n hn2 htb hns Pi hPi)

/-- Large-dimension named form of the no-go theorem, matching the Route B
paper-scale hypotheses.  The contradiction itself only needs `n ≥ 2`; the
paper-scale assumptions are retained so this theorem can replace the old Route
B adapter premise directly. -/
theorem candidate_projection_ne_satDeciderGaugeKeepFOBProjection_at_paper_scale
    (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi ≠
      satDeciderGaugeKeepFOBProjection M n hn2 htb hns :=
  candidate_projection_ne_satDeciderGaugeKeepFOBProjection M n hn2 htb hns Pi

/-! ## Axiom audit anchors -/

#print axioms satDeciderGaugeKeepFOBProjection_range_not_finite
#print axioms keepFOB_range_finite_of_candidate_projection_eq
#print axioms candidate_projection_ne_satDeciderGaugeKeepFOBProjection
#print axioms candidate_projection_ne_satDeciderGaugeKeepFOBProjection_at_paper_scale

end PallLean.Paper93.Paper283
