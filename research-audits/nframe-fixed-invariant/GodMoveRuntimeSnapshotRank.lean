import GodMoveComputedWireRank
import GodMoveFiniteStateInterpolation

/-!
# Rank of the actual machine's snapshot coordinates

At each time, the faithful simulator exposes tape bits, one-hot head bits,
and one-hot control bits through `ComposableStepCircuit.snapV`. Interpolating
these actual coordinate functions over all inputs of length L gives a finite
polynomial span. Over times 0 through t its dimension is at most
`(t+1)*(2*(L+t+1)+QM M)`, directly from the number of snapshot coordinates.

This span concerns symbolic functions over the whole input slice. It is not
the span of scalar values in one run, not the span of every circuit wire,
and not the derivative/SPDP space. Defining the interpolants supplies no
efficient algorithm for constructing their expanded coefficients.
-/

namespace GodMoveRuntimeSnapshotRank

open GodMoveBooleanInterpolation
open PallLean.Paper93.DeepMath.PathB
open ComposableMachine ComposableStepCircuit SATCircuitSeparationBridge
open scoped BigOperators

/-- The actual value of one snapshot coordinate, as a polynomial in the
original length-L input bits. -/
noncomputable def snapshotPolynomial (M : Machine) (L S time : ℕ)
    (pt : CPort M S) : Poly L :=
  interpolate (fun x => snapV M S (wordOfFin x) time pt)

/-- All physical snapshot coordinates at all times through the clock. -/
abbrev SnapshotIndex (M : Machine) (L t : ℕ) :=
  Fin (t + 1) × CPort M (L + t + 1)

instance snapshotIndex_fintype (M : Machine) (L t : ℕ) : Fintype (SnapshotIndex M L t) := by
  unfold SnapshotIndex CPort
  infer_instance

noncomputable def snapshotFamily (M : Machine) (L t : ℕ)
    (i : SnapshotIndex M L t) : Poly L :=
  snapshotPolynomial M L (L + t + 1) i.1.val i.2

noncomputable def snapshotSpace (M : Machine) (L t : ℕ) : Submodule ℚ (Poly L) :=
  Submodule.span ℚ (Set.range (snapshotFamily M L t))

instance snapshotSpace_finite (M : Machine) (L t : ℕ) :
    FiniteDimensional ℚ (snapshotSpace M L t) :=
  Module.Finite.span_of_finite ℚ (Set.finite_range _)

theorem snapshotIndex_card (M : Machine) (L t : ℕ) :
    Fintype.card (SnapshotIndex M L t) = (t + 1) * (2 * (L + t + 1) + QM M) := by
  simp [SnapshotIndex, CPort]
  ring

/-- A quadratic bound in input length and clock, counting real snapshot
coordinates rather than all intermediate gates of the unrolling. -/
theorem snapshotRank_le_clock (M : Machine) (L t : ℕ) :
    Module.finrank ℚ (snapshotSpace M L t) ≤
      (t + 1) * (2 * (L + t + 1) + QM M) := by
  classical
  rw [← snapshotIndex_card M L t]
  calc
    _ ≤ Fintype.card (Set.range (snapshotFamily M L t)) := by
      simpa only [snapshotSpace, Set.toFinset_card] using
        (finrank_span_le_card (R := ℚ) (Set.range (snapshotFamily M L t)))
    _ ≤ Fintype.card (SnapshotIndex M L t) := Fintype.card_range_le _

/-- Every actual snapshot-coordinate polynomial is captured through the
specified clock. -/
theorem snapshotPolynomial_mem_snapshotSpace (M : Machine) (L t time : ℕ)
    (htime : time ≤ t) (pt : CPort M (L + t + 1)) :
    snapshotPolynomial M L (L + t + 1) time pt ∈ snapshotSpace M L t := by
  apply Submodule.subset_span
  exact ⟨(⟨time, by omega⟩, pt), rfl⟩

/-- The chosen snapshot window includes the actual head and complete tape
throughout the run; no outlying memory cells are discarded. -/
theorem snapshot_covers_configuration (M : Machine) (L t time : ℕ)
    (htime : time ≤ t) (x : Assignment L) :
    (run M time (init M (wordOfFin x))).hd < L + t + 1 ∧
      (run M time (init M (wordOfFin x))).tp.length ≤ L + t + 1 := by
  obtain ⟨hhead, htape⟩ := run_bounds M (wordOfFin x) time
  rw [wordOfFin_length] at hhead htape
  constructor <;> omega

/-- The ordinary decision polynomial over all length-L inputs at the clock. -/
noncomputable def decisionPolynomial (M : Machine) (L t : ℕ) : Poly L :=
  interpolate (fun x => decideOut M (wordOfFin x) t)

/-- Acceptance is a linear combination of the actual final control bits.
This uses the machine's finite state partition, not a derivative-closure
or output-capture assumption. -/
theorem decisionPolynomial_eq_sum_controls (M : Machine) (L S t : ℕ) :
    decisionPolynomial M L t =
      ∑ q : Fin (QM M), bit (M.accept (stN M q)) •
        snapshotPolynomial M L S t (ctrlP M S q) := by
  have h := GodMoveFiniteStateInterpolation.interpolate_comp_eq_sum_fibers
    (fun x : Assignment L => Fintype.equivFin M.State
      (run M t (init M (wordOfFin x))).st)
    (fun q => M.accept (stN M q))
  simpa [decisionPolynomial, decideOut, snapshotPolynomial, snapV, ctrlP, stN] using h

/-- The state indicators partition the actual configurations on the entire
input slice, at every clock time. -/
theorem sum_control_polynomials_eq_one (M : Machine) (L S t : ℕ) :
    (∑ q : Fin (QM M), snapshotPolynomial M L S t (ctrlP M S q)) = 1 := by
  simpa [snapshotPolynomial, snapV, ctrlP] using
    GodMoveFiniteStateInterpolation.sum_fibers_eq_one
      (fun x : Assignment L => Fintype.equivFin M.State
        (run M t (init M (wordOfFin x))).st)

/-- The decision polynomial is captured by the clock-bounded snapshot span. -/
theorem decisionPolynomial_mem_snapshotSpace (M : Machine) (L t : ℕ) :
    decisionPolynomial M L t ∈ snapshotSpace M L t := by
  rw [decisionPolynomial_eq_sum_controls M L (L + t + 1) t]
  apply Submodule.sum_mem
  intro q _
  exact Submodule.smul_mem _ _
    (snapshotPolynomial_mem_snapshotSpace M L t t (le_refl _) (ctrlP M _ q))

/-- The same actual snapshot span contains the constant polynomial one. -/
theorem one_mem_snapshotSpace (M : Machine) (L t : ℕ) :
    (1 : Poly L) ∈ snapshotSpace M L t := by
  rw [← sum_control_polynomials_eq_one M L (L + t + 1) t]
  apply Submodule.sum_mem
  intro q _
  exact snapshotPolynomial_mem_snapshotSpace M L t t (le_refl _) (ctrlP M _ q)

end GodMoveRuntimeSnapshotRank

#print axioms GodMoveRuntimeSnapshotRank.snapshotIndex_card
#print axioms GodMoveRuntimeSnapshotRank.snapshotRank_le_clock
#print axioms GodMoveRuntimeSnapshotRank.snapshotPolynomial_mem_snapshotSpace
#print axioms GodMoveRuntimeSnapshotRank.snapshot_covers_configuration
#print axioms GodMoveRuntimeSnapshotRank.decisionPolynomial_eq_sum_controls
#print axioms GodMoveRuntimeSnapshotRank.sum_control_polynomials_eq_one
#print axioms GodMoveRuntimeSnapshotRank.decisionPolynomial_mem_snapshotSpace
#print axioms GodMoveRuntimeSnapshotRank.one_mem_snapshotSpace
