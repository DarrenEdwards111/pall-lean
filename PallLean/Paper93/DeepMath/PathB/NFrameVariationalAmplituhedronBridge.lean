import PallLean.Paper93.DeepMath.PathB.NFrameLagrangianBundle
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRealFrontier

/-!
# N-frame variational route to the amplituhedron/God-Move gauge

This file isolates the exact content of the user's Route B(i)/(ii) observation.
The current proxy N-frame functional is not enough: the real route must use the
actual log-determinantal barrier

  `B(A) = -∑ J∈𝒥, log det A[J,J]`

inside the action, prove existence of a minimizer, and then prove that the
minimizer satisfies the amplituhedron-gauge constraints.  If the log-det term
itself supplies that last implication, this is Route B(i).  If not, the missing
step is a separate positroid bridge, Route B(ii).

No unconditional final theorem is claimed here.  The file gives a kernel-checked
interface showing that a variational minimizer-to-God-Move bridge is exactly a
way to discharge the already-isolated `GlobalAmplituhedronGaugeForSatDeciders`
frontier, hence exactly the final no-bounded-SAT-decider theorem at paper scale.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine PaperFaithfulSeparation MultilinearSPDP
open scoped BigOperators

attribute [local instance] Classical.dec

/-! ## Real log-det N-frame action, not the old rank proxy -/

/-- Real log-det N-frame action obtained by instantiating `SNFAction` with the
actual amplituhedron barrier `amplituhedronBarrier 𝒥`. -/
noncomputable def logDetNFrameAction {n : ℕ}
    (α β lam : ℝ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ)
    (Φ : Fin n → ℝ)
    (𝒥 : Finset (Finset (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  SNFAction α β lam n n E χ Φ (amplituhedronBarrier 𝒥) A

/-- A minimizer of the real log-det N-frame action over a supplied admissible
matrix domain.  The domain is left explicit so later files can choose the exact
paper-faithful compact/coercive admissible set. -/
def IsLogDetNFrameMinimizer {n : ℕ}
    (α β lam : ℝ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ)
    (Φ : Fin n → ℝ)
    (𝒥 : Finset (Finset (Fin n)))
    (Admissible : Matrix (Fin n) (Fin n) ℝ → Prop)
    (Astar : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Admissible Astar ∧
    ∀ A, Admissible A →
      logDetNFrameAction α β lam E χ Φ 𝒥 Astar ≤
        logDetNFrameAction α β lam E χ Φ 𝒥 A

/-- Route B(i): the log-det minimizer itself is rich enough to force the
amplituhedron gauge conditions.  This is the optimistic analytic theorem: no
separate positroid algebra would be needed beyond proving this implication. -/
def LogDetMinimizerForcesAmplituhedronGauge : Prop :=
  ∀ {n : ℕ}
    (α β lam : ℝ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ)
    (Φ : Fin n → ℝ)
    (𝒥 : Finset (Finset (Fin n)))
    (Admissible : Matrix (Fin n) (Fin n) ℝ → Prop)
    (Astar : Matrix (Fin n) (Fin n) ℝ),
    IsLogDetNFrameMinimizer α β lam E χ Φ 𝒥 Admissible Astar →
      IsAmplituhedronGauge Astar 𝒥

/-- Route B(ii): a separate positroid bridge from the chosen minimizer to the
amplituhedron gauge conditions.  This is intentionally the same target as B(i),
but named separately to mark that the proof may require external positroid
algebra rather than following directly from log-det convexity/barrier calculus. -/
def PositroidBridgeFromLogDetMinimizer : Prop :=
  LogDetMinimizerForcesAmplituhedronGauge

/-- The matrix-level bridge target is definitionally the existing
`IsAmplituhedronGauge` predicate: positive definiteness plus unit principal
minors on the selected family. -/
theorem logDet_minimizer_bridge_target_iff_isAmplituhedronGauge
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n))) :
    (A.PosDef ∧ ∀ J ∈ 𝒥, ∀ (e : Fin J.card ≃ {i // i ∈ J}),
      (A.submatrix (fun i => (e i).1) (fun i => (e i).1)).det = 1)
      ↔ IsAmplituhedronGauge A 𝒥 := by
  rfl

/-! ## SAT-decider God-Move compressor surface -/

/-- A variational certificate strong enough to produce the actual
`GlobalGodMoveGauge` object for every bounded SAT-decider at paper scale.

The real analysis/positroid work is deliberately concentrated in the final
field `to_godMoveGauge`: it is the theorem that the minimizer-derived object is
not merely matrix-positive, but satisfies the three SPDP-rank fields bundled in
`GlobalGodMoveGauge.IsAmplituhedronGauge`. -/
structure VariationalGodMoveCompressorForSatDeciders : Prop where
  exists_minimizer :
    ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (_hn2 : n ≥ 2)
      (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
      (_hdec : DecidesSAT M), True
  to_godMoveGauge : GlobalAmplituhedronGaugeForSatDeciders

/-- If the real N-frame variational construction yields a God-Move compressor
for SAT-deciders, then the existing Route-B frontier is discharged. -/
theorem globalAmplituhedronGaugeForSatDeciders_of_variationalGodMoveCompressor
    (h : VariationalGodMoveCompressorForSatDeciders) :
    GlobalAmplituhedronGaugeForSatDeciders :=
  h.to_godMoveGauge

/-- Consequently the variational God-Move compressor is already as strong as the
final no-bounded-SAT-decider theorem at paper scale.  This formally captures the
"same remaining theorem, different lens" point. -/
theorem no_bounded_sat_decider_of_variationalGodMoveCompressor
    (h : VariationalGodMoveCompressorForSatDeciders) :
    NoBoundedSATDeciderAtPaperScale :=
  (globalAmplituhedronGaugeForSatDeciders_iff_no_bounded_sat_decider.mp
    h.to_godMoveGauge)

/-- Conversely, at the current logical level, if no bounded SAT-decider exists,
then the variational compressor surface is vacuously inhabited.  This is not a
construction; it is the same equivalence warning already found for the direct
gauge frontier. -/
theorem variationalGodMoveCompressor_of_no_bounded_sat_decider
    (hno : NoBoundedSATDeciderAtPaperScale) :
    VariationalGodMoveCompressorForSatDeciders := by
  refine ⟨?_, ?_⟩
  · intro M n hn hn2 htb hns hdec
    trivial
  · exact globalAmplituhedronGaugeForSatDeciders_iff_no_bounded_sat_decider.mpr hno

/-- The variational God-Move compressor surface is equivalent to the existing
final frontier.  Thus adding the compressor name alone does not reduce the math;
the missing theorem is precisely the minimizer/positroid bridge encoded in
`to_godMoveGauge`. -/
theorem variationalGodMoveCompressor_iff_no_bounded_sat_decider :
    VariationalGodMoveCompressorForSatDeciders ↔
      NoBoundedSATDeciderAtPaperScale := by
  constructor
  · exact no_bounded_sat_decider_of_variationalGodMoveCompressor
  · exact variationalGodMoveCompressor_of_no_bounded_sat_decider

#print axioms logDet_minimizer_bridge_target_iff_isAmplituhedronGauge
#print axioms globalAmplituhedronGaugeForSatDeciders_of_variationalGodMoveCompressor
#print axioms no_bounded_sat_decider_of_variationalGodMoveCompressor
#print axioms variationalGodMoveCompressor_of_no_bounded_sat_decider
#print axioms variationalGodMoveCompressor_iff_no_bounded_sat_decider

end PallLean.Paper93.DeepMath.PathB
