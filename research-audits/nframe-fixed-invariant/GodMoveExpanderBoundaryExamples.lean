import GodMoveExpanderPositiveProjection
import GodMoveRamanujanCalibration
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompleteGraphExpansion

/-!
# Concrete expander and positive-boundary instances at the actual SAT window

The K4 example uses the same endpoint graph for the derived Ramanujan spectral
bound, expansion, erased parity screen, and positive coefficient boundary.
The complete graph gives an actual all-size family, with its existing proved
expansion constant one. Its degree grows, so it is not a fixed-degree family.

At the paper scale m = n/3 and k = log₂ n, the screen window 4k ≤ m is proved
from the existing logarithmic estimates. Faithful SAT correctness supplies the
selected derivative rows. Their positive boundary has choose(m,k) coordinates,
and that superpolynomial dimension cost is retained explicitly.
-/

namespace GodMoveExpanderBoundaryExamples

open MvPolynomial SPDP MultilinearSPDP
open GodMoveMonomialMinor GodMoveSATUnitExtraction GodMoveUnitCharacteristic
open GodMoveMachineFaceExtraction GodMoveExpanderPositiveProjection
open PallLean.Paper93.DeepMath.PathB ComposableMachine SeparationTarget
open scoped BigOperators

/-- K4 preserves all four singleton derivative rows after up to three erasures. -/
theorem K4_boundary_rows_linearIndependent (erased : Finset (Fin 6))
    (herased : erased.card < 4) :
    LinearIndependent ℚ (fun S : KSubset 4 1 =>
      coefficientBoundary (k := 1) K4 erased 4 (derivativeRow S.val)) := by
  exact boundary_derivativeRows_linearIndependent K4 K4_hasExpansion
    (by decide) erased herased (by decide)

/-- The actual spectral bound and positive SAT-minor map concern the same K4. -/
theorem K4_spectral_and_sat_boundary
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (erased : Finset (Fin 6)) (herased : erased.card < 4) :
    (∀ x : Fin 4 → ℝ, (∑ i, x i) = 0 →
      GodMoveRamanujanCalibration.normSquared
          (GodMoveRamanujanCalibration.adjacency.mulVec x) ≤
        8 * GodMoveRamanujanCalibration.normSquared x) ∧
    LinearIndependent ℚ (fun S : KSubset 4 1 =>
      coefficientBoundary (k := 1) K4 erased 4
        (iterDerivList S.val.toList
          (unitExtraction 4 (machineSource M T (unitFormula 4) 4)))) := by
  refine ⟨GodMoveRamanujanCalibration.K4_spectral_and_expansion.2, ?_⟩
  exact sat_boundary_rows_linearIndependent M T hD K4 K4_hasExpansion
    (by decide) erased herased (by decide)

/-- The production complete graph uses two-element vertex sets as actual edges. -/
abbrev CompleteEdge (m : ℕ) := {s : Finset (Fin m) // s.card = 2}

/-- Actual simple adjacency of the production complete graph. -/
def completeAdjacency (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i = j then 0 else 1

theorem completeGraph_endpoints_iff {m : ℕ} (i j : Fin m) :
    (∃ e : CompleteEdge m, (completeGraph m).endpoints e = {i, j}) ↔ i ≠ j := by
  constructor
  · rintro ⟨e, he⟩ h
    have hc : ({i, j} : Finset (Fin m)).card = 2 :=
      he ▸ (completeGraph m).card_endpoints e
    subst j
    simp at hc
  · intro h
    exact ⟨⟨{i, j}, Finset.card_pair h⟩, rfl⟩

/-- The matrix entries are tied to the actual edge endpoint sets. -/
theorem completeAdjacency_eq_endpoint_indicator {m : ℕ} (i j : Fin m) :
    completeAdjacency m i j =
      if ∃ e : CompleteEdge m, (completeGraph m).endpoints e = {i, j} then 1 else 0 := by
  by_cases h : i = j
  · have hn : ¬ ∃ e : CompleteEdge m, (completeGraph m).endpoints e = {i, j} :=
      fun he => (completeGraph_endpoints_iff i j).mp he h
    simp only [completeAdjacency, if_pos h, if_neg hn]
  · have he := (completeGraph_endpoints_iff i j).mpr h
    simp only [completeAdjacency, if_neg h, if_pos he]

/-- Every vertex has exactly m−1 neighbors in that same endpoint graph. -/
theorem completeGraph_neighbor_degree {m : ℕ} (i : Fin m) :
    (Finset.univ.filter (fun j : Fin m =>
      ∃ e : CompleteEdge m, (completeGraph m).endpoints e = {i, j})).card = m - 1 := by
  simp only [completeGraph_endpoints_iff]
  have hfilter : (Finset.univ.filter (fun j : Fin m => i ≠ j)) =
      Finset.univ.erase i := by
    ext j
    simp [eq_comm]
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp

/-- Complete-graph adjacency is J−I on every vector, at every size. -/
theorem completeAdjacency_mulVec (m : ℕ) (x : Fin m → ℝ) :
    (completeAdjacency m).mulVec x = fun i => (∑ j, x j) - x i := by
  have hA : completeAdjacency m =
      Matrix.of (fun (_ _ : Fin m) => (1 : ℝ)) -
        (1 : Matrix (Fin m) (Fin m) ℝ) := by
    ext i j
    by_cases h : i = j <;>
      simp [completeAdjacency, Matrix.sub_apply, Matrix.of_apply, h]
  rw [hA, Matrix.sub_mulVec, Matrix.one_mulVec]
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- The nonconstant adjacency action is exactly −1, not a supplied scalar. -/
theorem completeAdjacency_mulVec_of_sum_zero {m : ℕ} (x : Fin m → ℝ)
    (hx : ∑ i, x i = 0) : (completeAdjacency m).mulVec x = -x := by
  rw [completeAdjacency_mulVec]
  ext i
  simp [hx]

def completeNormSquared {m : ℕ} (x : Fin m → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- An actual growing Ramanujan family, with explicitly growing degree m−1. -/
theorem completeGraph_ramanujan_squared (m : ℕ) (hm : 3 ≤ m)
    (x : Fin m → ℝ) (hx : ∑ i, x i = 0) :
    completeNormSquared ((completeAdjacency m).mulVec x) ≤
      4 * (((m - 1 : ℕ) : ℝ) - 1) * completeNormSquared x := by
  have hd : (2 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 ≤ m - 1)
  have hnorm : 0 ≤ completeNormSquared x :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [completeAdjacency_mulVec_of_sum_zero x hx]
  have hneg : completeNormSquared (-x) = completeNormSquared x := by
    simp [completeNormSquared]
  rw [hneg]
  nlinarith

/-- A growing, fully instantiated family, at its explicit binomial dimension. -/
theorem completeGraph_boundary_rows_linearIndependent (m k : ℕ)
    (hwindow : 4 * k ≤ m) (erased : Finset (CompleteEdge m))
    (herased : erased.card < 2) :
    LinearIndependent ℚ (fun S : KSubset m k =>
      coefficientBoundary (k := k) (completeGraph m) erased (Nat.choose m k)
        (derivativeRow S.val)) := by
  exact boundary_derivativeRows_linearIndependent (completeGraph m)
    (completeGraph_hasExpansion m) hwindow erased herased (le_refl _)

/-- The graph-screen window holds at the unchanged paper logarithmic order. -/
theorem paper_window (n : ℕ) (hn : 2 ^ 20 ≤ n) :
    4 * Nat.log 2 n ≤ n / 3 := by
  have hk20 : 20 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) hn
  have h30 : 30 * Nat.log 2 n ≤ n :=
    (BinomialBound.thirty_k_le_pow_half _ hk20).trans
      ((Nat.pow_le_pow_right (by decide : 1 ≤ 2)
        (Nat.div_le_self (Nat.log 2 n) 2)).trans
        (Nat.pow_log_le_self 2 (by omega : n ≠ 0)))
  omega

/-- Actual SAT derivative rows have a positive boundary on a proved growing
graph family, with no graph-existence or label-preservation premise remaining. -/
theorem completeGraph_sat_paper_boundary_rows_linearIndependent
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (n : ℕ) (hn : 2 ^ 20 ≤ n)
    (erased : Finset (CompleteEdge (n / 3))) (herased : erased.card < 2) :
    LinearIndependent ℚ (fun S : KSubset (n / 3) (Nat.log 2 n) =>
      coefficientBoundary (k := Nat.log 2 n) (completeGraph (n / 3)) erased
        (Nat.choose (n / 3) (Nat.log 2 n))
        (iterDerivList S.val.toList
          (unitExtraction (n / 3)
            (machineSource M T (unitFormula (n / 3)) (n / 3))))) := by
  exact sat_boundary_rows_linearIndependent M T hD (completeGraph (n / 3))
    (completeGraph_hasExpansion (n / 3)) (paper_window n hn)
    erased herased (le_refl _)

/-- Any linear boundary preserving this minor pays its superpolynomial
dimension at the very same paper scale and derivative order. -/
theorem paper_window_boundary_dimension (n q : ℕ) (hn : 2 ^ 20 ≤ n)
    (B : GodMoveMonomialMinor.Poly (n / 3) →ₗ[ℚ] (Fin q → ℚ))
    (hB : LinearIndependent ℚ (fun S : KSubset (n / 3) (Nat.log 2 n) =>
      B (derivativeRow S.val))) :
    n ^ (Nat.log 2 n / 4) ≤ q := by
  exact (BinomialBound.binomial_lower_bound_concrete n hn).trans
    ((Nat.choose_mono (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)).trans
      (faithful_boundary_dimension B hB))

end GodMoveExpanderBoundaryExamples

#print axioms GodMoveExpanderBoundaryExamples.K4_boundary_rows_linearIndependent
#print axioms GodMoveExpanderBoundaryExamples.K4_spectral_and_sat_boundary
#print axioms GodMoveExpanderBoundaryExamples.completeGraph_endpoints_iff
#print axioms GodMoveExpanderBoundaryExamples.completeAdjacency_eq_endpoint_indicator
#print axioms GodMoveExpanderBoundaryExamples.completeGraph_neighbor_degree
#print axioms GodMoveExpanderBoundaryExamples.completeAdjacency_mulVec_of_sum_zero
#print axioms GodMoveExpanderBoundaryExamples.completeGraph_ramanujan_squared
#print axioms GodMoveExpanderBoundaryExamples.completeGraph_boundary_rows_linearIndependent
#print axioms GodMoveExpanderBoundaryExamples.paper_window
#print axioms GodMoveExpanderBoundaryExamples.completeGraph_sat_paper_boundary_rows_linearIndependent
#print axioms GodMoveExpanderBoundaryExamples.paper_window_boundary_dimension
