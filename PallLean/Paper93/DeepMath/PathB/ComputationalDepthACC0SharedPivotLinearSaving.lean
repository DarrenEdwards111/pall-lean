import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DisjointFragmentSpeedup

/-!
# Linear SAT saving for a genuinely overlapping depth-two MOD fragment

Disjoint supports are sufficient for independent gate-output control, but they are not necessary.
This file gives a concrete high-overlap counterpoint.  Every bottom gate is a parity gate on a
shared variable `0` and its own private pivot `j+1`.  Thus all supports meet at the shared variable,
while setting that variable to false and the pivots to a requested output vector realizes every
gate-output pattern.

Consequently an arbitrary top control over `k` such gates on `k+1` designated variables reduces
exactly to search over its `k` output bits.  More generally, embedding this layer into `n` inputs
with `k ≤ n-s` gives `2^(n-s)` work; a proportional gap gives `2^(n-Ω(n))`.

The load-bearing property is therefore not disjointness but a system of private pivots after a
small shared separator has been fixed.  This is the first proved overlapping separator fragment.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SharedPivotLinearSaving

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0OracleControl

variable {k : ℕ}

/-- Gate `j` reads the common separator coordinate `0` and private pivot `j+1`. -/
def sharedPivotGate (j : Fin k) : ModGate (k + 1) :=
  ⟨2, {0, j.succ}, 1⟩

/-- Realize a requested output vector by fixing the common coordinate to false and pivot `j+1`
to the requested bit `y j`. -/
def pivotAssignment (y : Fin k → Bool) : Fin (k + 1) → Bool :=
  Fin.cases false y

/-- Every shared-pivot gate returns its requested output under `pivotAssignment`. -/
theorem sharedPivotGate_eval (y : Fin k → Bool) (j : Fin k) :
    (sharedPivotGate j).eval (pivotAssignment y) = y j := by
  have hw : weightOn {0, j.succ} (pivotAssignment y) = if y j then 1 else 0 := by
    unfold weightOn
    have hne : (0 : Fin (k + 1)) ≠ j.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
    simp [pivotAssignment]
  cases h : y j <;>
    simp [sharedPivotGate, ModGate.eval, modQStatOn, hw, h]

/-- Despite the common intersection of all supports, the full gate-output map is surjective. -/
theorem gate_vector_surjective (y : Fin k → Bool) :
    ∃ x : Fin (k + 1) → Bool, ∀ j, (sharedPivotGate j).eval x = y j :=
  ⟨pivotAssignment y, sharedPivotGate_eval y⟩

/-- Exact SAT reduction for the overlapping shared-pivot fragment. -/
theorem shared_pivot_sat_iff (C : OracleControl k) :
    Satisfiable (fun x => controlEval C (fun j => (sharedPivotGate j).eval x)) ↔
      Satisfiable (controlEval C) := by
  unfold Satisfiable
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨fun j => (sharedPivotGate j).eval x, hx⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := gate_vector_surjective y
    refine ⟨x, ?_⟩
    change controlEval C (fun j => (sharedPivotGate j).eval x) = true
    rw [funext hx]
    exact hy

/-- Quantitative search bound: if the overlapping layer has `k ≤ n-s` outputs, exhaustive
control search costs at most `2^(n-s)`. -/
theorem shared_pivot_linear_speedup (C : OracleControl k) (n saving : ℕ)
    (hs : saving ≤ n) (hgap : k ≤ n - saving) :
    (Satisfiable (fun x => controlEval C (fun j => (sharedPivotGate j).eval x)) ↔
        ∃ y ∈ (Finset.univ : Finset (Fin k → Bool)), controlEval C y = true)
      ∧ (Finset.univ : Finset (Fin k → Bool)).card ≤ 2 ^ (n - saving)
      ∧ saving ≤ n := by
  refine ⟨?_, ?_, hs⟩
  · rw [shared_pivot_sat_iff C]
    unfold Satisfiable
    simp only [Finset.mem_univ, true_and]
  · simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    exact Nat.pow_le_pow_right (by norm_num) hgap

end PallLean.Paper93.DeepMath.PathB.ACC0SharedPivotLinearSaving

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SharedPivotLinearSaving.sharedPivotGate_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SharedPivotLinearSaving.gate_vector_surjective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SharedPivotLinearSaving.shared_pivot_sat_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SharedPivotLinearSaving.shared_pivot_linear_speedup
