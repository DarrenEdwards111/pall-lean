import PallLean.Paper93.DeepMath.PathB.GodMoveLift

/-!
# Minimizer-derived SPDP fields frontier

This file names the exact theorem requested by the dynamic-CEW/God-Move route:
a log-det N-frame / amplituhedron minimizer must induce the three SPDP fields
on the actual Cook-Levin SAT-decider polynomial space.

No such induction is proved here from matrix positivity alone.  Instead, the
file records the precise logical strength of that theorem.  At the paper scale,
producing those three SPDP fields for a SAT-decider is already equivalent to
the final no-bounded-SAT-decider statement, because the P-side bound and
NP-identity-minor preservation fields are arithmetically incompatible under
`DecidesSAT`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation

/-- The requested minimizer-derived SPDP-field witness for one SAT-decider
compilation.

The witness contains the analytic minimizer data, the matrix-level
amplituhedron certificate, and the induced polynomial-space gauge realizing the
three SPDP fields needed by `GlobalGodMoveGauge.IsAmplituhedronGauge`.
-/
structure MinimizerDerivedSPDPFieldsForSatDecider
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Type where
  alpha : ℝ
  beta : ℝ
  lam : ℝ
  E : Finset (Fin n × Fin n)
  χ : Fin n → ℤ
  Φ : Fin n → ℝ
  J : Finset (Finset (Fin n))
  Admissible : Matrix (Fin n) (Fin n) ℝ → Prop
  Astar : Matrix (Fin n) (Fin n) ℝ
  minimizer :
    IsLogDetNFrameMinimizer alpha beta lam E χ Φ J Admissible Astar
  matrix_gauge : IsAmplituhedronGauge Astar J
  gauge : SATDeciderGaugeMap M n hn2 htb hns
  realizes :
    MatrixGaugeRealizesSATGauge M n hn hn2 htb hns Astar J gauge

/-- SAT-decider-uniform form of the requested theorem.

This is the theorem one would need to prove from the actual N-frame /
amplituhedron construction, without using the no-SAT-decider conclusion as an
input. -/
def MinimizerDerivedSPDPFieldsForSatDeciders : Prop :=
  ∀ (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    Nonempty (MinimizerDerivedSPDPFieldsForSatDecider M n hn hn2 htb hns)

/-- A minimizer-derived SPDP-field theorem would close the paper-scale
no-bounded-SAT-decider statement. -/
theorem no_bounded_sat_decider_of_minimizerDerivedSPDPFields
    (hfields : MinimizerDerivedSPDPFieldsForSatDeciders) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hfields M n hn hn2 htb hns hdec with ⟨w⟩
  have hsubgoals :
      SATDeciderGaugeSubgoals M n hn2 htb hns w.gauge :=
    satDeciderGaugeSubgoals_of_matrixGaugeRealizesSATGauge
      M n hn hn2 htb hns w.Astar w.J w.gauge w.realizes
  exact
    not_satDeciderGaugeSubgoals_at_large_n
      M n hn hn2 htb hns w.gauge hdec hsubgoals

/-- Conversely, if the no-bounded-SAT-decider statement is already known, then
the SAT-decider-indexed minimizer-derived theorem is vacuous.

This direction is not a construction of the minimizer.  It records that the
fully quantified SAT-decider form has exactly final-theorem strength. -/
theorem minimizerDerivedSPDPFields_of_no_bounded_sat_decider
    (hno : NoBoundedSATDeciderAtPaperScale) :
    MinimizerDerivedSPDPFieldsForSatDeciders := by
  intro M n hn hn2 htb hns hdec
  exact False.elim ((hno M n hn hn2 htb hns) hdec)

/-- The requested SAT-decider-uniform minimizer-to-SPDP theorem is logically
equivalent to the paper-scale no-bounded-SAT-decider frontier. -/
theorem minimizerDerivedSPDPFields_iff_no_bounded_sat_decider :
    MinimizerDerivedSPDPFieldsForSatDeciders ↔
      NoBoundedSATDeciderAtPaperScale := by
  constructor
  · exact no_bounded_sat_decider_of_minimizerDerivedSPDPFields
  · exact minimizerDerivedSPDPFields_of_no_bounded_sat_decider

#print axioms no_bounded_sat_decider_of_minimizerDerivedSPDPFields
#print axioms minimizerDerivedSPDPFields_of_no_bounded_sat_decider
#print axioms minimizerDerivedSPDPFields_iff_no_bounded_sat_decider

end PallLean.Paper93.DeepMath.PathB
