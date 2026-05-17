import PallLean.Paper93.DeepMath.PathB.NFrameVariationalAmplituhedronBridge

/-!
# Matrix amplituhedron gauges to Global God-Move gauges

This file isolates the "boss fight" lift:

* the variational/log-det route now produces a **matrix-level**
  `IsAmplituhedronGauge A 𝒥`;
* the final separation needs a **Cook--Levin polynomial-space** gauge,
  i.e. `GlobalGodMoveGauge.IsAmplituhedronGauge` for the exact SAT-decider
  compilation.

The theorem below does not smuggle the final result.  It names the precise
realization interface needed to turn a matrix gauge into the three SPDP-rank
fields, proves the conversion into the existing global frontier, and records
that an over-broad "any matrix gauge lifts" principle is already equivalent to
ruling out bounded SAT deciders.  That is the honest shape of the remaining
mathematics.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- A matrix-level amplituhedron gauge together with the concrete polynomial
linear map it induces on one Cook--Levin SAT-decider compilation.

This is the missing GodMove lift at field level: the matrix gauge itself is the
positive-geometry certificate, while the three remaining fields are exactly the
rank-monotonicity, P-side collapse, and NP identity-minor preservation required
of the induced polynomial-space compressor. -/
structure MatrixGaugeRealizesSATGauge
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n)))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns) : Prop where
  matrix_gauge : IsAmplituhedronGauge A 𝒥
  rank_monotone : SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge
  p_side_bound : SATDeciderGaugePSideBound M n hn2 htb hns gauge
  preserves_identity_minor :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge

/-- A realized matrix gauge gives the explicit three SAT-decider gauge
subgoals. -/
theorem satDeciderGaugeSubgoals_of_matrixGaugeRealizesSATGauge
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n)))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hrealizes : MatrixGaugeRealizesSATGauge M n hn hn2 htb hns A 𝒥 gauge) :
    SATDeciderGaugeSubgoals M n hn2 htb hns gauge :=
  ⟨hrealizes.rank_monotone,
    hrealizes.p_side_bound,
    hrealizes.preserves_identity_minor⟩

/-- A realized matrix gauge gives the bundled `GlobalGodMoveGauge` gauge for the
same Cook--Levin compilation. -/
theorem globalGodMoveGauge_of_matrixGaugeRealizesSATGauge
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n)))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hrealizes : MatrixGaugeRealizesSATGauge M n hn hn2 htb hns A 𝒥 gauge) :
    GlobalGodMoveGauge.IsAmplituhedronGauge M n hn hn2 htb hns gauge :=
  (satDeciderGaugeSubgoals_iff_isAmplituhedronGauge M n hn hn2 htb hns gauge).mp
    (satDeciderGaugeSubgoals_of_matrixGaugeRealizesSATGauge
      M n hn hn2 htb hns A 𝒥 gauge hrealizes)

/-- SAT-decider-level matrix-to-GodMove lift surface.

For every bounded SAT-decider at paper scale, it asks for a matrix-level
amplituhedron certificate and an induced polynomial-space gauge realizing the
three Global God-Move fields. -/
def MatrixToGlobalGodMoveLiftForSatDeciders : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    ∃ (A : Matrix (Fin n) (Fin n) ℝ)
      (𝒥 : Finset (Finset (Fin n)))
      (gauge : SATDeciderGaugeMap M n hn2 htb hns),
      MatrixGaugeRealizesSATGauge M n _hn hn2 htb hns A 𝒥 gauge

/-- The matrix-to-global lift surface is enough to discharge the current global
GodMove frontier. -/
theorem globalAmplituhedronGaugeForSatDeciders_of_matrixToGlobalGodMoveLift
    (hlift : MatrixToGlobalGodMoveLiftForSatDeciders) :
    GlobalAmplituhedronGaugeForSatDeciders := by
  intro M n hn hn2 htb hns hdec
  obtain ⟨A, 𝒥, gauge, hrealizes⟩ := hlift M n hn hn2 htb hns hdec
  exact ⟨gauge,
    globalGodMoveGauge_of_matrixGaugeRealizesSATGauge
      M n hn hn2 htb hns A 𝒥 gauge hrealizes⟩

/-- Therefore the matrix-to-global lift closes the paper-scale no bounded
SAT-decider theorem. -/
theorem no_bounded_sat_decider_of_matrixToGlobalGodMoveLift
    (hlift : MatrixToGlobalGodMoveLiftForSatDeciders) :
    NoBoundedSATDeciderAtPaperScale :=
  globalAmplituhedronGaugeForSatDeciders_iff_no_bounded_sat_decider.mp
    (globalAmplituhedronGaugeForSatDeciders_of_matrixToGlobalGodMoveLift hlift)

/-- Conversely, if no bounded SAT-decider exists, the SAT-decider-indexed lift
surface is vacuous.  This records the logical warning: the fully quantified
SAT-decider lift is exactly final-theorem strength. -/
theorem matrixToGlobalGodMoveLift_of_no_bounded_sat_decider
    (hno : NoBoundedSATDeciderAtPaperScale) :
    MatrixToGlobalGodMoveLiftForSatDeciders := by
  intro M n hn hn2 htb hns hdec
  exact False.elim ((hno M n hn hn2 htb hns) hdec)

/-- The SAT-decider-indexed GodMove lift surface is logically equivalent to the
existing final no-bounded-SAT-decider frontier.  Thus the remaining non-circular
work is not this wrapper, but the concrete realization theorem for the
minimizer-derived matrix gauge before the `DecidesSAT` contradiction fires. -/
theorem matrixToGlobalGodMoveLift_iff_no_bounded_sat_decider :
    MatrixToGlobalGodMoveLiftForSatDeciders ↔
      NoBoundedSATDeciderAtPaperScale := by
  constructor
  · exact no_bounded_sat_decider_of_matrixToGlobalGodMoveLift
  · exact matrixToGlobalGodMoveLift_of_no_bounded_sat_decider

/-- One-step closure from the analytic variational theorem plus a concrete
realization of the resulting matrix gauge.

This is the usable non-circular boss-fight interface: provide a compact
normalized domain and prove that the minimizer's matrix gauge induces the three
SPDP fields, and Lean returns the global GodMove gauge for this SAT-decider
compilation. -/
theorem globalGodMoveGauge_of_compact_normalized_minimizer_realization
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (α β lam : ℝ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ)
    (Φ : Fin n → ℝ)
    (𝒥 : Finset (Finset (Fin n)))
    (Admissible : Matrix (Fin n) (Fin n) ℝ → Prop)
    (hcompact : IsCompact {A : Matrix (Fin n) (Fin n) ℝ | Admissible A})
    (hcont : ContinuousOn
      (fun A : Matrix (Fin n) (Fin n) ℝ =>
        logDetNFrameAction α β lam E χ Φ 𝒥 A)
      {A : Matrix (Fin n) (Fin n) ℝ | Admissible A})
    (hI : Admissible (1 : Matrix (Fin n) (Fin n) ℝ))
    (hlam : 0 < lam)
    (hnorm : ∀ A, Admissible A → NormalizedPositiveCell 𝒥 A)
    (realize : ∀ Astar,
      IsLogDetNFrameMinimizer α β lam E χ Φ 𝒥 Admissible Astar →
      IsAmplituhedronGauge Astar 𝒥 →
      ∃ gauge : SATDeciderGaugeMap M n hn2 htb hns,
        MatrixGaugeRealizesSATGauge M n hn hn2 htb hns Astar 𝒥 gauge) :
    ∃ gauge : SATDeciderGaugeMap M n hn2 htb hns,
      GlobalGodMoveGauge.IsAmplituhedronGauge M n hn hn2 htb hns gauge := by
  obtain ⟨Astar, hmin, hmatrix⟩ :=
    exists_logDet_minimizer_isAmplituhedronGauge_of_compact_normalized_cell
      α β lam E χ Φ 𝒥 Admissible hcompact hcont hI hlam hnorm
  obtain ⟨gauge, hrealizes⟩ := realize Astar hmin hmatrix
  exact ⟨gauge,
    globalGodMoveGauge_of_matrixGaugeRealizesSATGauge
      M n hn hn2 htb hns Astar 𝒥 gauge hrealizes⟩

/-! ## Axiom audit anchors -/
#print axioms satDeciderGaugeSubgoals_of_matrixGaugeRealizesSATGauge
#print axioms globalGodMoveGauge_of_matrixGaugeRealizesSATGauge
#print axioms globalAmplituhedronGaugeForSatDeciders_of_matrixToGlobalGodMoveLift
#print axioms no_bounded_sat_decider_of_matrixToGlobalGodMoveLift
#print axioms matrixToGlobalGodMoveLift_of_no_bounded_sat_decider
#print axioms matrixToGlobalGodMoveLift_iff_no_bounded_sat_decider
#print axioms globalGodMoveGauge_of_compact_normalized_minimizer_realization

end PallLean.Paper93.DeepMath.PathB
