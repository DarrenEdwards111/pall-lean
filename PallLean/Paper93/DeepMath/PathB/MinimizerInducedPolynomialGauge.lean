import PallLean.Paper93.DeepMath.PathB.GodMoveLift
import PallLean.Paper93.NFrame.LinearSubstitutionGauge

/-!
# Minimizer-induced polynomial gauges

This file builds the missing *object* between matrix N-frame/amplituhedron data
and the Cook-Levin polynomial space.

The matrix-level minimizer lives over `ℝ`, while the existing SPDP rank
frontier is over `ℚ`.  The concrete construction therefore requires a rational
shadow of the minimizer matrix: if every entry of `Astar` is rational, choose
those rational entries and apply the already-formalized matrix-induced
substitution

`X_i ↦ ∑ j, A_ij X_j`

to the actual Cook-Levin polynomial ring.  This gives a real
`SATDeciderGaugeMap`, not just a socket.

What this file does not prove is that this constructed map satisfies the
P-side bound and NP-identity-minor preservation simultaneously.  In fact, the
existing obstruction theorem shows that under `DecidesSAT` no gauge can satisfy
both fields at paper scale.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.NFrame

/-- A rational shadow of a real matrix, supplied by entrywise rationality. -/
noncomputable def rationalShadowMatrix {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hRat : ∀ i j : Fin n, ∃ q : ℚ, (q : ℝ) = A i j) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => Classical.choose (hRat i j)

/-- The chosen rational shadow really has the requested real entries. -/
theorem rationalShadowMatrix_spec {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hRat : ∀ i j : Fin n, ∃ q : ℚ, (q : ℝ) = A i j)
    (i j : Fin n) :
    ((rationalShadowMatrix A hRat i j : ℚ) : ℝ) = A i j :=
  Classical.choose_spec (hRat i j)

/-- The polynomial-space gauge induced by a rational `n × n` matrix on the
actual Cook-Levin SAT-decider compilation.

The cast is justified by `cook_levin_numVars`: this repository's flat
Cook-Levin compilation uses exactly `n` variables. -/
noncomputable def rationalMatrixSATDeciderGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    SATDeciderGaugeMap M n hn2 htb hns := by
  change
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ
  rw [cook_levin_numVars M n hn2 htb hns]
  exact rationalMatrixSubstGauge A

/-- The identity rational matrix induces the identity SAT-decider gauge. -/
@[simp] theorem rationalMatrixSATDeciderGauge_one
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    rationalMatrixSATDeciderGauge M n hn2 htb hns
        (1 : Matrix (Fin n) (Fin n) ℚ) =
      identitySATDeciderGauge M n hn2 htb hns := by
  unfold rationalMatrixSATDeciderGauge identitySATDeciderGauge
  simp [rationalMatrixSubstGauge_one]

/-- The concrete polynomial gauge induced by a real minimizer matrix with
rational entries. -/
noncomputable def minimizerInducedPolynomialGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Astar : Matrix (Fin n) (Fin n) ℝ)
    (hRat : ∀ i j : Fin n, ∃ q : ℚ, (q : ℝ) = Astar i j) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  rationalMatrixSATDeciderGauge M n hn2 htb hns
    (rationalShadowMatrix Astar hRat)

/-- Field-level packaging for the constructed minimizer-induced gauge. -/
theorem matrixGaugeRealizesSATGauge_of_minimizerInducedPolynomialGauge_fields
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Astar : Matrix (Fin n) (Fin n) ℝ)
    (J : Finset (Finset (Fin n)))
    (hRat : ∀ i j : Fin n, ∃ q : ℚ, (q : ℝ) = Astar i j)
    (hmatrix : IsAmplituhedronGauge Astar J)
    (hrank :
      SATDeciderGaugeRankMonotonicity M n hn2 htb hns
        (minimizerInducedPolynomialGauge M n hn2 htb hns Astar hRat))
    (hp :
      SATDeciderGaugePSideBound M n hn2 htb hns
        (minimizerInducedPolynomialGauge M n hn2 htb hns Astar hRat))
    (hnp :
      SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
        (minimizerInducedPolynomialGauge M n hn2 htb hns Astar hRat)) :
    MatrixGaugeRealizesSATGauge M n hn hn2 htb hns Astar J
      (minimizerInducedPolynomialGauge M n hn2 htb hns Astar hRat) where
  matrix_gauge := hmatrix
  rank_monotone := hrank
  p_side_bound := hp
  preserves_identity_minor := hnp

/-- Fully constructed minimizer-derived data: the gauge field is no longer
arbitrary, but definitionally the rational-shadow substitution induced by
`Astar`. -/
structure ConstructedMinimizerSPDPFieldsForSatDecider
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
  rational_entries :
    ∀ i j : Fin n, ∃ q : ℚ, (q : ℝ) = Astar i j
  rank_monotone :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (minimizerInducedPolynomialGauge
        M n hn2 htb hns Astar rational_entries)
  p_side_bound :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (minimizerInducedPolynomialGauge
        M n hn2 htb hns Astar rational_entries)
  preserves_identity_minor :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (minimizerInducedPolynomialGauge
        M n hn2 htb hns Astar rational_entries)

/-- Under `DecidesSAT`, the constructed minimizer-induced gauge cannot satisfy
all three SPDP fields at paper scale. -/
theorem not_minimizerInducedPolynomialGauge_subgoals_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Astar : Matrix (Fin n) (Fin n) ℝ)
    (hRat : ∀ i j : Fin n, ∃ q : ℚ, (q : ℝ) = Astar i j)
    (hdec : DecidesSAT M) :
    ¬ SATDeciderGaugeSubgoals M n hn2 htb hns
      (minimizerInducedPolynomialGauge M n hn2 htb hns Astar hRat) :=
  not_satDeciderGaugeSubgoals_at_large_n
    M n hn hn2 htb hns
    (minimizerInducedPolynomialGauge M n hn2 htb hns Astar hRat)
    hdec

/-- Therefore constructed minimizer data with all three fields rules out the
SAT-decider hypothesis for that machine at that paper-scale length. -/
theorem not_decidesSAT_of_constructedMinimizerSPDPFields
    {M : DTM} {n : Nat} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (w :
      ConstructedMinimizerSPDPFieldsForSatDecider
        M n hn hn2 htb hns) :
    ¬ DecidesSAT M := by
  intro hdec
  exact
    not_minimizerInducedPolynomialGauge_subgoals_at_large_n
      M n hn hn2 htb hns w.Astar w.rational_entries hdec
      ⟨w.rank_monotone, w.p_side_bound, w.preserves_identity_minor⟩

#print axioms rationalShadowMatrix_spec
#print axioms rationalMatrixSATDeciderGauge_one
#print axioms matrixGaugeRealizesSATGauge_of_minimizerInducedPolynomialGauge_fields
#print axioms not_minimizerInducedPolynomialGauge_subgoals_at_large_n
#print axioms not_decidesSAT_of_constructedMinimizerSPDPFields

end PallLean.Paper93.DeepMath.PathB
