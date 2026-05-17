import PallLean.Paper93.DeepMath.PathB.NFrameLagrangianBundle
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRealFrontier
import Mathlib.Topology.Order.Compact

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

/-- Normalized positive cell for the log-det/amplituhedron barrier: positive
    definite, with every designated principal minor bounded above by `1`.

This is the analytic domain condition under which the zero-barrier theorem
forces unit principal minors and hence `IsAmplituhedronGauge`. -/
def NormalizedPositiveCell {n : ℕ}
    (𝒥 : Finset (Finset (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.PosDef ∧
    ∀ J ∈ 𝒥,
      PallLean.Paper93.DeepMath.PathB.Positroid.principalMinor A J ≤ 1

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

/-- Direct-method minimizer existence for the real log-det N-frame action.

This is the standard compactness/continuity part of Route B: once a future file
chooses a nonempty compact admissible matrix domain and proves continuity of the
real log-det action on it, Lean gives an actual minimizer.  The theorem is
pure analysis/plumbing; it does **not** prove the minimizer is an amplituhedron
or God-Move gauge. -/
theorem exists_logDetNFrameMinimizer_of_compact_continuous {n : ℕ}
    (α β lam : ℝ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ)
    (Φ : Fin n → ℝ)
    (𝒥 : Finset (Finset (Fin n)))
    (Admissible : Matrix (Fin n) (Fin n) ℝ → Prop)
    (hcompact : IsCompact {A : Matrix (Fin n) (Fin n) ℝ | Admissible A})
    (hne : ({A : Matrix (Fin n) (Fin n) ℝ | Admissible A}).Nonempty)
    (hcont : ContinuousOn
      (fun A : Matrix (Fin n) (Fin n) ℝ =>
        logDetNFrameAction α β lam E χ Φ 𝒥 A)
      {A : Matrix (Fin n) (Fin n) ℝ | Admissible A}) :
    ∃ Astar, IsLogDetNFrameMinimizer α β lam E χ Φ 𝒥 Admissible Astar := by
  obtain ⟨Astar, hAstar, hmin⟩ := hcompact.exists_isMinOn hne hcont
  refine ⟨Astar, hAstar, ?_⟩
  intro A hA
  exact hmin hA

/-! ## Zero-barrier minimizer bridge -/

/-- If the admissible domain contains the identity/reference matrix, then a
log-det N-frame minimizer has nonpositive barrier value.  On a normalized
positive-definite cell the barrier is also nonnegative, hence the minimizer's
barrier is exactly zero.

This is the concrete variational step needed after compact minimizer existence:
identity has barrier `0`, the non-barrier terms are independent of `A`, and
`λ > 0` lets the minimizer inequality isolate the barrier term. -/
theorem minimizer_barrier_eq_zero_of_identity_competitor {n : ℕ}
    (α β lam : ℝ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ)
    (Φ : Fin n → ℝ)
    (𝒥 : Finset (Finset (Fin n)))
    (Admissible : Matrix (Fin n) (Fin n) ℝ → Prop)
    (Astar : Matrix (Fin n) (Fin n) ℝ)
    (hmin : IsLogDetNFrameMinimizer α β lam E χ Φ 𝒥 Admissible Astar)
    (hI : Admissible (1 : Matrix (Fin n) (Fin n) ℝ))
    (hlam : 0 < lam)
    (hAstar : Astar.PosDef)
    (hminor_le : ∀ J ∈ 𝒥,
      PallLean.Paper93.DeepMath.PathB.Positroid.principalMinor Astar J ≤ 1) :
    amplituhedronBarrier 𝒥 Astar = 0 := by
  rcases hmin with ⟨_hAstar_adm, hle_all⟩
  have hle := hle_all (1 : Matrix (Fin n) (Fin n) ℝ) hI
  unfold logDetNFrameAction SNFAction at hle
  rw [amplituhedronBarrier_identity n 𝒥] at hle
  have hbarrier_le : amplituhedronBarrier 𝒥 Astar ≤ 0 := by
    nlinarith [hle, hlam]
  have hbarrier_nonneg : 0 ≤ amplituhedronBarrier 𝒥 Astar :=
    amplituhedronBarrier_nonneg_of_principalMinor_le_one 𝒥 Astar hAstar hminor_le
  exact le_antisymm hbarrier_le hbarrier_nonneg

/-- A log-det N-frame minimizer in a normalized positive-definite admissible
cell is an amplituhedron gauge, provided the identity/reference competitor is
admissible and `λ > 0`.  This composes the variational zero-barrier step with
the log-det barrier bridge to unit principal minors. -/
theorem isAmplituhedronGauge_of_logDet_minimizer_identity_competitor {n : ℕ}
    (α β lam : ℝ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ)
    (Φ : Fin n → ℝ)
    (𝒥 : Finset (Finset (Fin n)))
    (Admissible : Matrix (Fin n) (Fin n) ℝ → Prop)
    (Astar : Matrix (Fin n) (Fin n) ℝ)
    (hmin : IsLogDetNFrameMinimizer α β lam E χ Φ 𝒥 Admissible Astar)
    (hI : Admissible (1 : Matrix (Fin n) (Fin n) ℝ))
    (hlam : 0 < lam)
    (hAstar : Astar.PosDef)
    (hminor_le : ∀ J ∈ 𝒥,
      PallLean.Paper93.DeepMath.PathB.Positroid.principalMinor Astar J ≤ 1) :
    IsAmplituhedronGauge Astar 𝒥 := by
  exact isAmplituhedronGauge_of_barrier_eq_zero 𝒥 Astar hAstar hminor_le
    (minimizer_barrier_eq_zero_of_identity_competitor α β lam E χ Φ 𝒥
      Admissible Astar hmin hI hlam hAstar hminor_le)

/-- Compact/continuous normalized-cell existence theorem for Route B.

Once a future file supplies a concrete paper-faithful admissible domain that is
compact, contains the identity/reference matrix, lies in the normalized positive
cell, and makes the log-det action continuous, Lean now produces an actual
minimizer and immediately upgrades it to `IsAmplituhedronGauge`.

This is the completed analytic plumbing up to the still-open choice/proof of the
concrete admissible domain. -/
theorem exists_logDet_minimizer_isAmplituhedronGauge_of_compact_normalized_cell {n : ℕ}
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
    (hnorm : ∀ A, Admissible A → NormalizedPositiveCell 𝒥 A) :
    ∃ Astar,
      IsLogDetNFrameMinimizer α β lam E χ Φ 𝒥 Admissible Astar ∧
        IsAmplituhedronGauge Astar 𝒥 := by
  have hne : ({A : Matrix (Fin n) (Fin n) ℝ | Admissible A}).Nonempty :=
    ⟨(1 : Matrix (Fin n) (Fin n) ℝ), hI⟩
  obtain ⟨Astar, hmin⟩ :=
    exists_logDetNFrameMinimizer_of_compact_continuous α β lam E χ Φ 𝒥
      Admissible hcompact hne hcont
  have hcell : NormalizedPositiveCell 𝒥 Astar := hnorm Astar hmin.1
  refine ⟨Astar, hmin, ?_⟩
  exact isAmplituhedronGauge_of_logDet_minimizer_identity_competitor
    α β lam E χ Φ 𝒥 Admissible Astar hmin hI hlam hcell.1 hcell.2

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

#print axioms exists_logDetNFrameMinimizer_of_compact_continuous
#print axioms minimizer_barrier_eq_zero_of_identity_competitor
#print axioms isAmplituhedronGauge_of_logDet_minimizer_identity_competitor
#print axioms exists_logDet_minimizer_isAmplituhedronGauge_of_compact_normalized_cell
#print axioms logDet_minimizer_bridge_target_iff_isAmplituhedronGauge
#print axioms globalAmplituhedronGaugeForSatDeciders_of_variationalGodMoveCompressor
#print axioms no_bounded_sat_decider_of_variationalGodMoveCompressor
#print axioms variationalGodMoveCompressor_of_no_bounded_sat_decider
#print axioms variationalGodMoveCompressor_iff_no_bounded_sat_decider

end PallLean.Paper93.DeepMath.PathB
