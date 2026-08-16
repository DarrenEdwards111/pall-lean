import PallLean.Paper93.DeepMath.PathB.ComputationalDepth2CNFSCCBridge

/-!
# Executable implication-graph interface and linear SCC budget

Mathlib contains a meta-level Tarjan routine used by a tactic, but currently exposes no theorem connecting its output
to graph reachability or certifying its running time.  This file therefore proves the algorithm-independent finite
graph facts needed by any certified traversal: the explicit implication-edge list represents exactly `Edge`, has two
directed edges per clause, and lives on exactly two literal vertices per variable.

It also proves the precise exponent condition for plugging any SCC implementation with the resulting linear budget
into a width-three cover branch.  Correctness of an executable Tarjan/Kosaraju traversal remains the next obligation.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoSATSCCLinearBudget

open PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT

variable {n : ℕ}

/-- The two directed implication edges contributed by every pair clause. -/
def implicationEdges (cls : List (Clause n)) : List (Lit n × Lit n) :=
  cls.flatMap fun c => [(neg c.1, c.2), (neg c.2, c.1)]

/-- The executable edge list represents exactly the semantic edge relation used by `twosat_iff`. -/
theorem mem_implicationEdges_iff (cls : List (Clause n)) (a b : Lit n) :
    (a, b) ∈ implicationEdges cls ↔ Edge cls a b := by
  simp [implicationEdges, Edge]

/-- Exact directed-edge count: two entries per pair clause. -/
theorem length_implicationEdges (cls : List (Clause n)) :
    (implicationEdges cls).length = 2 * cls.length := by
  simp [implicationEdges, Nat.mul_comm]

/-- Exact literal-vertex count: positive and negative literal for every variable. -/
theorem card_literals : Fintype.card (Lit n) = 2 * n := by
  simp [Lit, Nat.mul_comm]

/-- Abstract linear traversal budget: one unit per literal vertex and implication edge. -/
def sccLinearBudget (n clauseCount : ℕ) : ℕ := 2 * n + 2 * clauseCount

theorem sccLinearBudget_eq (n clauseCount : ℕ) :
    sccLinearBudget n clauseCount = 2 * (n + clauseCount) := by
  unfold sccLinearBudget
  omega

/-- Work after branching on `c` cover bits and running one linear-budget SCC pass at each leaf. -/
def coverSCCWork (c n clauseCount : ℕ) : ℕ := 2 ^ c * sccLinearBudget n clauseCount

/-- If the linear budget fits in `p` bits, cover branching consumes exactly `c+p` exponent bits. -/
theorem coverSCCWork_le_pow
    (c n clauseCount p : ℕ) (hbudget : sccLinearBudget n clauseCount ≤ 2 ^ p) :
    coverSCCWork c n clauseCount ≤ 2 ^ (c + p) := by
  unfold coverSCCWork
  calc
    2 ^ c * sccLinearBudget n clauseCount ≤ 2 ^ c * 2 ^ p := Nat.mul_le_mul_left _ hbudget
    _ = 2 ^ (c + p) := by rw [Nat.pow_add]

/-- A strict subcube result follows exactly when cover bits plus budget bits leave one bit of slack. -/
theorem coverSCCWork_le_half_cube
    (totalVars c residualVars clauseCount p : ℕ)
    (hbudget : sccLinearBudget residualVars clauseCount ≤ 2 ^ p)
    (hslack : c + p ≤ totalVars - 1) :
    coverSCCWork c residualVars clauseCount ≤ 2 ^ (totalVars - 1) := by
  exact (coverSCCWork_le_pow c residualVars clauseCount p hbudget).trans
    (Nat.pow_le_pow_right (by norm_num) hslack)

end PallLean.Paper93.DeepMath.PathB.TwoSATSCCLinearBudget

#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATSCCLinearBudget.mem_implicationEdges_iff
#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATSCCLinearBudget.length_implicationEdges
#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATSCCLinearBudget.coverSCCWork_le_half_cube
