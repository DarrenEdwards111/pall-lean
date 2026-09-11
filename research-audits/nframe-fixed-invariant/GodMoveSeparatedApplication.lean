import GodMoveCompactProjector
import GodMoveSubsetCoefficient
import PallLean.CoeffDisjoint

/-!
# Exact compact projector application to separated factors

For products whose factors use distinct single variables, complemented
coefficients factor into local coefficients. In particular, the affine
product `prod_i (a_i + b_i X_i)` needs only the local values `a_i+b_i`
and `-b_i`. The shared coefficient DAG then constructs its projected output
without enumerating subsets or requesting a general coefficient oracle.
The actual quadratic designated sheet has the same selected coefficients as
the full monomial, so the construction also applies exactly to that sheet.

This is a restricted application theorem. Multiplication of factors sharing
variables does not satisfy the disjoint-support coefficient identity used
here. Arithmetic syntax size does not bound rational bit cost or expanded
output size, and no SAT separation is asserted.
-/

namespace GodMoveSeparatedApplication

open MvPolynomial SymmetricPower
open GodMoveMonomialMinor (KSubset complementaryColumn)
open GodMoveQuadraticSheetLift (affineComplement affineComplement_X)
open GodMoveBoundaryNFrameGauge (rowProjection rowCoordinates rowSynthesis boundaryGauge)
open GodMoveDesignatedPositiveBoundary (qRow)
open GodMoveGaugeLocalOperators (qRow_factorization)
open GodMoveOperatorSubsetDAG
open GodMoveSubsetCoefficient
open scoped BigOperators

abbrev Poly (m : ℕ) := MvPolynomial (Fin m) ℚ

/-- Disjoint coordinate factors turn a squarefree coefficient into a product
of their actual local coefficients. No rank or independence premise occurs. -/
theorem coeff_complement_prod {m : ℕ} (f : Fin m → Poly m)
    (hf : ∀ i, CoeffDisjoint.usesOnly (f i) ({i} : Set (Fin m)))
    (S : Finset (Fin m)) :
    coeff (complementaryColumn S) (∏ i, f i) =
      (∏ i ∈ S, coeff 0 (f i)) *
        ∏ i ∈ Finset.univ \ S, coeff (Finsupp.single i 1) (f i) := by
  classical
  let d : Fin m → Fin m →₀ ℕ := fun i => if i ∈ S then 0 else Finsupp.single i 1
  have hsum : (∑ i, d i) = complementaryColumn S := by
    ext j
    simp [d, complementaryColumn, tagMonomial, Finsupp.finset_sum_apply,
      Finsupp.single_apply, Finset.sum_ite, eq_comm]
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      CoeffDisjoint.monomSupportedIn (d i) ({i} : Set (Fin m)) := by
    intro i _
    dsimp [d]
    split_ifs
    · exact monomSupportedIn_zero _
    · exact monomSupportedIn_single i
  rw [← hsum, CoeffDisjoint.coeff_finset_prod_disjoint
    (fun i _ => hf i) (singleton_pairwiseDisjoint Finset.univ) hd]
  have hc (i : Fin m) : coeff (d i) (f i) =
      if i ∈ S then coeff 0 (f i) else coeff (Finsupp.single i 1) (f i) := by
    dsimp [d]
    split_ifs <;> rfl
  simp only [hc]
  rw [Finset.prod_ite]
  congr 1
  · congr 1
    ext i
    simp
  · congr 1
    ext i
    simp

noncomputable def affineFactor {m : ℕ} (a b : ℚ) (i : Fin m) : Poly m :=
  C a + C b * X i

noncomputable def affineProduct {m : ℕ} (a b : Fin m → ℚ) : Poly m :=
  ∏ i, affineFactor (a i) (b i) i

theorem affineFactor_usesOnly {m : ℕ} (a b : ℚ) (i : Fin m) :
    CoeffDisjoint.usesOnly (affineFactor a b i) ({i} : Set (Fin m)) := by
  intro d hd j hj
  have hv : j ∈ (affineFactor a b i).vars := (mem_vars j).mpr ⟨d, hd, hj⟩
  have hs : (affineFactor a b i).vars ⊆ {i} := by
    apply (vars_add_subset _ _).trans
    simpa only [vars_C, Finset.empty_union, vars_X] using vars_mul (C b : Poly m) (X i)
  exact Finset.mem_singleton.mp (hs hv)

theorem complement_affineFactor {m : ℕ} (a b : ℚ) (i : Fin m) :
    affineComplement m (affineFactor a b i) = affineFactor (a + b) (-b) i := by
  simp [affineFactor, affineComplement]
  ring

theorem affineFactor_coeff_zero {m : ℕ} (a b : ℚ) (i : Fin m) :
    coeff 0 (affineFactor a b i) = a := by
  simp [affineFactor]

theorem affineFactor_coeff_single {m : ℕ} (a b : ℚ) (i : Fin m) :
    coeff (Finsupp.single i 1) (affineFactor a b i) = b := by
  have hn : (0 : Fin m →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro h
    have hi := DFunLike.congr_fun h i
    simp at hi
  simp [affineFactor, coeff_C, hn]

theorem complemented_affineProduct_coefficient {m : ℕ}
    (a b : Fin m → ℚ) (S : Finset (Fin m)) :
    coeff (complementaryColumn S) (affineComplement m (affineProduct a b)) =
      (∏ i ∈ S, (a i + b i)) * ∏ i ∈ Finset.univ \ S, -b i := by
  rw [affineProduct, map_prod]
  simp only [complement_affineFactor]
  rw [coeff_complement_prod _ (fun i => affineFactor_usesOnly _ _ i)]
  simp only [affineFactor_coeff_zero, affineFactor_coeff_single]

noncomputable def outputA {m : ℕ} (b : Fin m → ℚ) (i : Fin m) : Poly m :=
  C (-b i) * (1 - X i)

noncomputable def outputB {m : ℕ} (a b : Fin m → ℚ) (i : Fin m) : Poly m :=
  C (a i + b i) * (2 * X i - 1)

theorem output_branch_product {m : ℕ} (a b : Fin m → ℚ) (S : Finset (Fin m)) :
    (∏ i ∈ S, outputB a b i) * (∏ i ∈ Finset.univ \ S, outputA b i) =
      ((∏ i ∈ S, (a i + b i)) * ∏ i ∈ Finset.univ \ S, -b i) • qRow S := by
  simp only [outputA, outputB, Finset.prod_mul_distrib, ← map_prod,
    qRow_factorization, Algebra.smul_def, map_mul, MvPolynomial.algebraMap_eq]
  ring

/-- The shared arithmetic recurrence applies the projector to this separated
input directly. No evaluation of the general kernel contraction is used. -/
theorem evalDAG_affineProduct {m : ℕ} (a b : Fin m → ℚ) (k : ℕ) :
    evalDAG (outputA b) (outputB a b) k =
      (boundaryGauge m k).projection (affineProduct a b) := by
  rw [evalDAG_eq_subset_sum]
  change (∑ S : KSubset m k,
      (∏ i ∈ S.val, outputB a b i) * (∏ i ∈ Finset.univ \ S.val, outputA b i)) =
    ∑ S : KSubset m k,
      coeff (complementaryColumn S.val) (affineComplement m (affineProduct a b)) • qRow S.val
  apply Finset.sum_congr rfl
  intro S _
  rw [output_branch_product, complemented_affineProduct_coefficient]

/-- Rational arithmetic syntax for an actual output factor, not an opaque
coefficient oracle or polynomial operator. -/
inductive OutputExpr (m : ℕ) where
  | scalar : ℚ → OutputExpr m
  | variable : Fin m → OutputExpr m
  | neg : OutputExpr m → OutputExpr m
  | add : OutputExpr m → OutputExpr m → OutputExpr m
  | mul : OutputExpr m → OutputExpr m → OutputExpr m
deriving Repr, DecidableEq

def OutputExpr.nodes {m : ℕ} : OutputExpr m → ℕ
  | .scalar _ | .variable _ => 1
  | .neg e => 1 + e.nodes
  | .add e f | .mul e f => 1 + e.nodes + f.nodes

noncomputable def OutputExpr.denote {m : ℕ} : OutputExpr m → Poly m
  | .scalar a => C a
  | .variable i => X i
  | .neg e => -e.denote
  | .add e f => e.denote + f.denote
  | .mul e f => e.denote * f.denote

def OutputExpr.eval {m : ℕ} (x : Fin m → ℚ) : OutputExpr m → ℚ
  | .scalar a => a
  | .variable i => x i
  | .neg e => -e.eval x
  | .add e f => e.eval x + f.eval x
  | .mul e f => e.eval x * f.eval x

theorem OutputExpr.eval_denote {m : ℕ} (x : Fin m → ℚ) (e : OutputExpr m) :
    MvPolynomial.eval x e.denote = e.eval x := by
  induction e <;> simp [OutputExpr.denote, OutputExpr.eval, *]

def outputExprA {m : ℕ} (b : ℚ) (i : Fin m) : OutputExpr m :=
  .mul (.neg (.scalar b)) (.add (.scalar 1) (.neg (.variable i)))

def outputExprB {m : ℕ} (a b : ℚ) (i : Fin m) : OutputExpr m :=
  .mul (.add (.scalar a) (.scalar b))
    (.add (.mul (.scalar 2) (.variable i)) (.scalar (-1)))

theorem outputExpr_nodes {m : ℕ} (a b : ℚ) (i : Fin m) :
    (outputExprA b i).nodes = 7 ∧ (outputExprB a b i).nodes = 9 := by
  constructor <;> rfl

theorem outputExpr_denote {m : ℕ} (a b : Fin m → ℚ) (i : Fin m) :
    (outputExprA (b i) i).denote = outputA b i ∧
      (outputExprB (a i) (b i) i).denote = outputB a b i := by
  simp [outputExprA, outputExprB, OutputExpr.denote, outputA, outputB,
    sub_eq_add_neg, map_ofNat]

/-- All local arithmetic factors and all shared recurrence references are
stored. The input scalars are supplied in arrays, preserving finite access. -/
structure ApplicationDescriptor (m k : ℕ) where
  factorsA : Vector (OutputExpr m) m
  factorsB : Vector (OutputExpr m) m
  layers : List (Layer m k)

def applicationDescriptor {m : ℕ} (a b : Vector ℚ m) (k : ℕ) :
    ApplicationDescriptor m k :=
  ⟨Vector.ofFn (fun i => outputExprA (b.get i) i),
    Vector.ofFn (fun i => outputExprB (a.get i) (b.get i) i), program m k⟩

def ApplicationDescriptor.nodes {m k : ℕ} (D : ApplicationDescriptor m k) : ℕ :=
  nodeCount D.layers + (D.factorsA.toList.map OutputExpr.nodes).sum +
    (D.factorsB.toList.map OutputExpr.nodes).sum

theorem applicationDescriptor_nodes {m : ℕ} (a b : Vector ℚ m) (k : ℕ) :
    (applicationDescriptor a b k).nodes = 2 + 3 * m * (k + 1) + 16 * m := by
  simp [ApplicationDescriptor.nodes, applicationDescriptor, program_nodeCount,
    Vector.toList_ofFn, List.map_ofFn, Function.comp_def, outputExprA, outputExprB,
    OutputExpr.nodes, List.ofFn_const, Nat.mul_comm]
  omega

/-- The compact output polynomial's denotation. This definition does not
materialize that polynomial during descriptor construction. -/
noncomputable def ApplicationDescriptor.denote {m k : ℕ}
    (D : ApplicationDescriptor m k) : Poly m :=
  (evalProgram (fun i => (D.factorsA.get i).denote)
    (fun i => (D.factorsB.get i).denote) D.layers).get ⟨k, by omega⟩

theorem applicationDescriptor_denote_eq_DAG {m : ℕ} (a b : Vector ℚ m) (k : ℕ) :
    (applicationDescriptor a b k).denote = evalDAG (outputA b.get) (outputB a.get b.get) k := by
  have hA : (fun i : Fin m => ((applicationDescriptor a b k).factorsA.get i).denote) =
      outputA b.get := by
    funext i
    simpa [applicationDescriptor, Vector.get] using (outputExpr_denote a.get b.get i).1
  have hB : (fun i : Fin m => ((applicationDescriptor a b k).factorsB.get i).denote) =
      outputB a.get b.get := by
    funext i
    simpa [applicationDescriptor, Vector.get] using (outputExpr_denote a.get b.get i).2
  unfold ApplicationDescriptor.denote
  rw [hA, hB]
  rfl

/-- The executable constructor returns compact output arithmetic syntax
denoting the exact production projection of the supplied affine product. -/
theorem applicationDescriptor_correct {m : ℕ} (a b : Vector ℚ m) (k : ℕ) :
    (applicationDescriptor a b k).denote =
      (boundaryGauge m k).projection (affineProduct a.get b.get) := by
  rw [applicationDescriptor_denote_eq_DAG, evalDAG_affineProduct]

/-- Booleanity factors are unchanged by coordinate complementation. -/
theorem complement_boolFactorFullProd (m : ℕ) :
    affineComplement m (boolFactorFullProd m) = boolFactorFullProd m := by
  simp only [boolFactorFullProd, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [boolFactor, map_sub, map_one, map_mul, affineComplement_X]
  ring

/-- The actual quadratic sheet and the full monomial have the same selected
complemented coefficients, although they are different polynomials. -/
theorem complemented_Q_coefficient {m : ℕ} (S : Finset (Fin m)) :
    coeff (complementaryColumn S) (affineComplement m (boolFactorFullProd m)) =
      coeff (complementaryColumn S)
        (affineComplement m (affineProduct (fun _ : Fin m => 0) (fun _ => 1))) := by
  rw [complemented_affineProduct_coefficient, complement_boolFactorFullProd,
    boolFactorFullProd, coeff_complement_prod _ (fun i => usesOnly_boolFactor i)]
  simp only [coeff_zero_boolFactor, coeff_single_boolFactor, zero_add]

theorem affineProduct_zero_one (m : ℕ) :
    affineProduct (fun _ : Fin m => 0) (fun _ => 1) = GodMoveMonomialMinor.fullMonomial m := by
  simp [affineProduct, affineFactor, GodMoveMonomialMinor.fullMonomial]

theorem projector_Q_eq_fullMonomial (m k : ℕ) :
    (boundaryGauge m k).projection (boolFactorFullProd m) =
      (boundaryGauge m k).projection (GodMoveMonomialMinor.fullMonomial m) := by
  change (∑ S : KSubset m k,
      coeff (complementaryColumn S.val) (affineComplement m (boolFactorFullProd m)) • qRow S.val) =
    ∑ S : KSubset m k,
      coeff (complementaryColumn S.val)
        (affineComplement m (GodMoveMonomialMinor.fullMonomial m)) • qRow S.val
  apply Finset.sum_congr rfl
  intro S _
  rw [complemented_Q_coefficient, affineProduct_zero_one]

/-- A fully specified compact output descriptor for the actual quadratic
sheet. Its input scalars are zero and one, not unknown local coefficients. -/
def QDescriptor (m k : ℕ) : ApplicationDescriptor m k :=
  applicationDescriptor (Vector.ofFn (fun _ : Fin m => 0))
    (Vector.ofFn (fun _ : Fin m => 1)) k

/-- Exact application to the actual booleanity-factor sheet, with all square
terms present in the input. The returned output is ordinary arithmetic syntax. -/
theorem descriptor_Q (m k : ℕ) :
    (QDescriptor m k).denote = (boundaryGauge m k).projection (boolFactorFullProd m) := by
  rw [QDescriptor, applicationDescriptor_correct]
  have hzero : (Vector.ofFn (fun _ : Fin m => (0 : ℚ))).get = fun _ => 0 := by
    funext i
    simp [Vector.get]
  have hone : (Vector.ofFn (fun _ : Fin m => (1 : ℚ))).get = fun _ => 1 := by
    funext i
    simp [Vector.get]
  rw [hzero, hone, affineProduct_zero_one]
  exact (projector_Q_eq_fullMonomial m k).symm

theorem QDescriptor_nodes (m k : ℕ) :
    (QDescriptor m k).nodes = 2 + 3 * m * (k + 1) + 16 * m :=
  applicationDescriptor_nodes _ _ k

/-- The same compact output theorem for the exact production designated
target, using its previously proved polynomial identity. -/
theorem descriptor_actual_designated_sheet
    (D : TuringMachine.DTM) (n : ℕ) (hn2 : 2 ≤ n)
    (htb : D.timeBound ≤ 4) (hns : D.numStates ≤ n)
    (B : SPDP.BlockPartition (PaperFaithfulCompilation.cookLevinUVSplit D n).total)
    (k : ℕ) :
    (QDescriptor (n / 3) k).denote =
      (boundaryGauge (n / 3) k).projection
        (Step4Compiler.Step252.cookLevinStrictFOBTarget D n hn2 htb hns B).coupledPoly := by
  rw [GodMoveQuadraticSheetLift.designated_sheet_eq_boolFactorFullProd]
  exact descriptor_Q _ _

end GodMoveSeparatedApplication

#print axioms GodMoveSeparatedApplication.coeff_complement_prod
#print axioms GodMoveSeparatedApplication.complemented_affineProduct_coefficient
#print axioms GodMoveSeparatedApplication.output_branch_product
#print axioms GodMoveSeparatedApplication.evalDAG_affineProduct
#print axioms GodMoveSeparatedApplication.OutputExpr.eval_denote
#print axioms GodMoveSeparatedApplication.applicationDescriptor_nodes
#print axioms GodMoveSeparatedApplication.applicationDescriptor_denote_eq_DAG
#print axioms GodMoveSeparatedApplication.applicationDescriptor_correct
#print axioms GodMoveSeparatedApplication.projector_Q_eq_fullMonomial
#print axioms GodMoveSeparatedApplication.descriptor_Q
#print axioms GodMoveSeparatedApplication.QDescriptor_nodes
#print axioms GodMoveSeparatedApplication.descriptor_actual_designated_sheet
