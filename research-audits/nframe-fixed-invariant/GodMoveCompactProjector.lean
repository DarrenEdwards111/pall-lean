import GodMoveProjectorKernel
import GodMoveOperatorSubsetDAG
import GodMoveCompactGaugeCost

/-!
# Executable compact syntax for the exact production projector kernel

The input factors are stored arithmetic expressions, not expensive opaque
operators supplied for free. Together with the shared coefficient DAG they
describe exactly the existing production projection through coefficient
contraction. Syntax generation does not enumerate subsets or Boolean screens.
The contraction is a semantic operation; no polynomial bit-cost evaluator for
contraction against arbitrary succinct input polynomials is claimed.
-/

namespace GodMoveCompactProjector

open GodMoveProjectorKernel GodMoveOperatorSubsetDAG
open GodMoveBoundaryNFrameGauge GodMoveCompactGaugeCost

/-- Small arithmetic syntax with separate output and dual-coordinate leaves. -/
inductive FactorExpr (m : ℕ) where
  | integer : ℤ → FactorExpr m
  | output : Fin m → FactorExpr m
  | dual : Fin m → FactorExpr m
  | neg : FactorExpr m → FactorExpr m
  | add : FactorExpr m → FactorExpr m → FactorExpr m
  | mul : FactorExpr m → FactorExpr m → FactorExpr m
deriving Repr, DecidableEq

def FactorExpr.nodes {m : ℕ} : FactorExpr m → ℕ
  | .integer _ | .output _ | .dual _ => 1
  | .neg e => 1 + e.nodes
  | .add e f | .mul e f => 1 + e.nodes + f.nodes

noncomputable def FactorExpr.denote {m : ℕ} : FactorExpr m → Kernel m
  | .integer z => z
  | .output i => MvPolynomial.C (MvPolynomial.X i)
  | .dual i => MvPolynomial.X i
  | .neg e => -e.denote
  | .add e f => e.denote + f.denote
  | .mul e f => e.denote * f.denote

def inputA {m : ℕ} (i : Fin m) : FactorExpr m :=
  .mul (.add (.integer 1) (.neg (.output i))) (.dual i)

def inputB {m : ℕ} (i : Fin m) : FactorExpr m :=
  .add (.mul (.integer 2) (.output i)) (.integer (-1))

theorem input_nodes {m : ℕ} (i : Fin m) :
    (inputA i).nodes = 6 ∧ (inputB i).nodes = 5 := by
  constructor <;> rfl

theorem input_denote {m : ℕ} (i : Fin m) :
    (inputA i).denote = branchA i ∧ (inputB i).denote = branchB i := by
  simp [inputA, inputB, FactorExpr.denote, branchA, branchB, sub_eq_add_neg]
  exact (map_ofNat MvPolynomial.C 2).symm

/-- All supplied factors and every layer reference are stored explicitly. -/
structure Descriptor (m k : ℕ) where
  factorsA : Vector (FactorExpr m) m
  factorsB : Vector (FactorExpr m) m
  layers : List (Layer m k)

/-- An executable constructor with no subset or screen enumeration. -/
def descriptor (m k : ℕ) : Descriptor m k :=
  ⟨Vector.ofFn inputA, Vector.ofFn inputB, program m k⟩

def Descriptor.nodes {m k : ℕ} (D : Descriptor m k) : ℕ :=
  nodeCount D.layers +
    (D.factorsA.toList.map FactorExpr.nodes).sum +
    (D.factorsB.toList.map FactorExpr.nodes).sum

theorem descriptor_nodes (m k : ℕ) :
    (descriptor m k).nodes = 2 + 3 * m * (k + 1) + 11 * m := by
  simp [Descriptor.nodes, descriptor, program_nodeCount, Vector.toList_ofFn,
    List.map_ofFn, Function.comp_def, inputA, inputB, FactorExpr.nodes,
    List.ofFn_const, Nat.mul_comm]
  omega

/-- Semantic evaluation may expand polynomials; its cost is not node count. -/
noncomputable def Descriptor.kernel {m k : ℕ} (D : Descriptor m k) : Kernel m :=
  (evalProgram (fun i => (D.factorsA.get i).denote)
    (fun i => (D.factorsB.get i).denote) D.layers).get ⟨k, by omega⟩

/-- The compact descriptor produces exactly the coefficient kernel. -/
theorem descriptor_kernel (m k : ℕ) :
    (descriptor m k).kernel = rowKernel m k := by
  have hA : (fun i : Fin m => ((descriptor m k).factorsA.get i).denote) = branchA := by
    funext i
    simpa [descriptor, Vector.get] using (input_denote i).1
  have hB : (fun i : Fin m => ((descriptor m k).factorsB.get i).denote) = branchB := by
    funext i
    simpa [descriptor, Vector.get] using (input_denote i).2
  unfold Descriptor.kernel
  rw [hA, hB]
  change evalDAG branchA branchB k = _
  rw [evalDAG_eq_coefficient]
  exact generatingKernel_coeff m k

/-- Exact agreement with the unchanged production N-Frame projection, for
every polynomial input. This is an identity, not a contraction time bound. -/
theorem descriptor_contract (m k : ℕ) (p : GodMoveProjectorKernel.Poly m) :
    contract p (descriptor m k).kernel = (boundaryGauge m k).projection p := by
  rw [descriptor_kernel, contract_rowKernel]
  rfl

theorem descriptor_log_nodes (m : ℕ) :
    (descriptor m (Nat.log 2 m)).nodes = descriptionBudget 11 m := by
  rw [descriptor_nodes, descriptionBudget_exact]

theorem descriptor_log_quadratic (m : ℕ) :
    (descriptor m (Nat.log 2 m)).nodes ≤ 16 * (m + 1) ^ 2 := by
  rw [descriptor_log_nodes]
  exact descriptionBudget_quadratic 11 m

/-- Even exact compact syntax for this projection cannot make its actual
production rank polynomial in the number of stored arithmetic nodes. -/
theorem no_eventual_polynomial_rank_in_descriptor :
    ¬ ∃ C d m0 : ℕ, ∀ m ≥ m0,
      Module.finrank ℚ (LinearMap.range (boundaryGauge m (Nat.log 2 m)).projection) ≤
        C * ((descriptor m (Nat.log 2 m)).nodes) ^ d := by
  simpa only [descriptor_log_nodes] using
    no_eventual_polynomial_production_rank_in_description 11

end GodMoveCompactProjector

#print axioms GodMoveCompactProjector.input_nodes
#print axioms GodMoveCompactProjector.input_denote
#print axioms GodMoveCompactProjector.descriptor_nodes
#print axioms GodMoveCompactProjector.descriptor_kernel
#print axioms GodMoveCompactProjector.descriptor_contract
#print axioms GodMoveCompactProjector.descriptor_log_quadratic
#print axioms GodMoveCompactProjector.no_eventual_polynomial_rank_in_descriptor
