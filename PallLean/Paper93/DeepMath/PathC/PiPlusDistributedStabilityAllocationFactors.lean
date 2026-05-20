import PallLean.Paper93.DeepMath.PathC.PiPlusDistributedStabilityAllocation

/-!
# Factor/product reduction for allocation-level Boolean stability

The previous allocation split replaced the opaque `q ∈ distribDerivProds` surface
by a concrete derivative-allocation product.  This file makes the next seam
smaller: allocation-level Boolean stability follows if Boolean-normalizing any
allocated product lands on another concrete distributed Leibniz generator.

This isolates the remaining algebraic content from the span bookkeeping.  The
hard part is now the product/factor theorem that constructs the normalized
allocation; the span closeout is immediate from `Submodule.subset_span`.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open LeibnizProduct

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Concrete allocated Leibniz product for transformed local factors. -/
noncomputable def piPlusBooleanProjectedAllocatedDerivativeProduct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ :=
  let L := piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D
  Finset.univ.prod (fun i : Fin L.length => iterDerivList (alloc i) L[i.val])

/-! ## Pure product-span assembly

The next algebraic move after the Leibniz split is not another socket: if each
local allocated factor has already been expressed in its own local span, then
the product of those local expressions lies in the span of all pointwise choices
of local generators.  This is the finite-product multilinearity bookkeeping
needed before specializing the local generator sets to Booleanity-residue and
signed-row certificates.
-/

/-- Pointwise products obtained by choosing one generator from each local factor
set over the finite index set `s`. -/
noncomputable def finiteProductChoiceSet
    {n : Nat} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → Set (MvPolynomial (Fin n) ℚ)) :
    Set (MvPolynomial (Fin n) ℚ) :=
  { q | ∃ a : ι → MvPolynomial (Fin n) ℚ,
      (∀ i ∈ s, a i ∈ A i) ∧ q = s.prod a }

/-- Finite-product span assembly: local span membership for every factor implies
membership of the whole product in the span of pointwise products of local
generators. -/
theorem finset_prod_mem_span_finiteProductChoiceSet
    {n : Nat} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → Set (MvPolynomial (Fin n) ℚ))
    (p : ι → MvPolynomial (Fin n) ℚ)
    (hp : ∀ i ∈ s, p i ∈ Submodule.span ℚ (A i)) :
    s.prod p ∈ Submodule.span ℚ (finiteProductChoiceSet s A) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      apply Submodule.subset_span
      refine ⟨fun _ => 1, ?_, ?_⟩
      · intro i hi
        simp at hi
      · simp
  | insert k s hks ih =>
      rw [Finset.prod_insert hks]
      let W : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
        Submodule.span ℚ (finiteProductChoiceSet (insert k s) A)
      let T : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
        { carrier := {x | x * s.prod p ∈ W}
          zero_mem' := by simp [W]
          add_mem' := by
            intro x y hx hy
            change (x + y) * s.prod p ∈ W
            rw [add_mul]
            exact Submodule.add_mem W hx hy
          smul_mem' := by
            intro c x hx
            change (c • x) * s.prod p ∈ W
            simpa [Algebra.smul_def, mul_assoc] using
              (Submodule.smul_mem W c hx) }
      have hk : p k ∈ T := by
        refine Submodule.span_induction
          (s := A k) (p := fun x _hx => x ∈ T) ?base ?zero ?add ?smul
          (hp k (Finset.mem_insert_self k s))
        · intro x hx
          change x * s.prod p ∈ W
          have hsprod :
              s.prod p ∈ Submodule.span ℚ (finiteProductChoiceSet s A) := by
            apply ih
            intro i hi
            exact hp i (Finset.mem_insert_of_mem hi)
          let mulx : MvPolynomial (Fin n) ℚ →ₗ[ℚ]
              MvPolynomial (Fin n) ℚ :=
            { toFun := fun q => x * q
              map_add' := fun a b => mul_add x a b
              map_smul' := by
                intro c q
                change x * (c • q) = c • (x * q)
                rw [Algebra.mul_smul_comm] }
          have hmap : mulx (s.prod p) ∈
              Submodule.map mulx
                (Submodule.span ℚ (finiteProductChoiceSet s A)) :=
            Submodule.mem_map_of_mem hsprod
          rw [Submodule.map_span] at hmap
          apply Submodule.span_mono ?_ hmap
          intro y hy
          rcases hy with ⟨z, hz, rfl⟩
          rcases hz with ⟨a, ha, rfl⟩
          refine ⟨Function.update a k x, ?_, ?_⟩
          · intro i hi
            by_cases hik : i = k
            · subst i
              simpa using hx
            · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hik
              simpa [Function.update_of_ne hik] using ha i his
          · rw [Finset.prod_insert hks]
            simp only [Function.update_self]
            change x * s.prod a =
              x * ∏ i ∈ s, Function.update a k x i
            congr 1
            apply Finset.prod_congr rfl
            intro i hi
            have hne : i ≠ k := by
              intro hik
              subst i
              exact hks hi
            simp [Function.update_of_ne hne]
        · change (0 : MvPolynomial (Fin n) ℚ) ∈ T
          exact T.zero_mem
        · intro x y _ _ hx hy
          exact T.add_mem hx hy
        · intro c x _ hx
          exact T.smul_mem c hx
      exact hk

/-- Specialization of finite-product span assembly to transformed Cook--Levin
allocated derivative products.  Once each local derivative factor is in its
chosen local span, the whole allocated Leibniz product is in the span of all
pointwise products of local choices. -/
theorem allocatedDerivativeProduct_mem_span_finiteProductChoiceSet
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (A : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      Set (MvPolynomial
        (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))
    (hlocal : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length,
      iterDerivList (alloc i)
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D)[i.val] ∈ Submodule.span ℚ (A i)) :
    piPlusBooleanProjectedAllocatedDerivativeProduct
      M n hn2 htb hns D alloc ∈
      Submodule.span ℚ (finiteProductChoiceSet Finset.univ A) := by
  classical
  simpa [piPlusBooleanProjectedAllocatedDerivativeProduct] using
    (finset_prod_mem_span_finiteProductChoiceSet
      (s := Finset.univ) (A := A)
      (p := fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).length =>
        iterDerivList (alloc i)
          (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D)[i.val])
      (by
        intro i _hi
        exact hlocal i))

/-- Product/factor normalization target for one concrete allocation.

It says that Boolean-normalizing the allocated product is itself another
allocated product whose derivative sublists are still drawn from the ambient
Leibniz derivative list `S`. -/
def PiPlusBooleanProjectedAllocatedProductNormalizesToDistributedGenerator
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) : Prop :=
  ∃ alloc' : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars),
    (∀ i, ∀ v ∈ alloc' i, v ∈ S) ∧
      zeroProfileBooleanNormalize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) =
        piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc'

/-- The remaining product/factor reduction for allocation-level stability: every
admissible concrete allocation normalizes to another distributed generator. -/
def PiPlusBooleanProjectedAllocationProductNormalizationReduction
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
    S.length = Nat.log 2 n →
    isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      ∀ (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).length →
        List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
        (∀ i, ∀ v ∈ alloc i, v ∈ S) →
          PiPlusBooleanProjectedAllocatedProductNormalizesToDistributedGenerator
            M n hn2 htb hns D S alloc

/-- If an allocated product normalizes to another distributed generator, its
Boolean normalization lies in the span of `distribDerivProds`. -/
theorem allocatedProduct_mem_span_of_normalizesToDistributedGenerator
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (hnorm : PiPlusBooleanProjectedAllocatedProductNormalizesToDistributedGenerator
      M n hn2 htb hns D S alloc) :
    zeroProfileBooleanNormalize
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈
      Submodule.span ℚ
        (distribDerivProds Finset.univ
          (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length =>
            (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D)[i.val]) S) := by
  rcases hnorm with ⟨alloc', halloc', hnorm_eq⟩
  rw [hnorm_eq]
  apply Submodule.subset_span
  refine ⟨alloc', halloc', ?_⟩
  rfl

/-- Product-normalization reduction implies allocation-level Boolean stability. -/
theorem allocationStability_of_productNormalizationReduction
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedAllocationProductNormalizationReduction
      M n hn2 htb hns D) :
    PiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M n hn2 htb hns D := by
  intro S hSlen hadm
  change ∀ (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).length →
        List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
      (∀ i, ∀ v ∈ alloc i, v ∈ S) →
        zeroProfileBooleanNormalize
          (Finset.univ.prod (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length =>
            iterDerivList (alloc i)
              (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D)[i.val])) ∈
          Submodule.span ℚ
            (distribDerivProds Finset.univ
              (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
                  M n hn2 htb hns D).length =>
                (piPlusBooleanProjectedTransformedConstraintFactors
                  M n hn2 htb hns D)[i.val]) S)
  intro alloc halloc
  exact allocatedProduct_mem_span_of_normalizesToDistributedGenerator
    M n hn2 htb hns D S alloc (hred S hSlen hadm alloc halloc)

/-- Paper-scale product/factor normalization reduction. -/
abbrev PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedAllocationProductNormalizationReduction
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale allocation-level stability from the product/factor normalization
reduction. -/
theorem paperScale_allocationStability_of_productNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M htb hns :=
  allocationStability_of_productNormalizationReduction
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hred

/-- Commutation plus product/factor normalization reduction reassemble into the
normalized derivative criterion. -/
theorem paperScale_normalizedDerivativeCriterion_of_commutation_and_productNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns :=
  paperScale_normalizedDerivativeCriterion_of_commutation_and_allocationStability
    M htb hns hcomm
    (paperScale_allocationStability_of_productNormalizationReduction
      M htb hns hred)

/-- Final envelope closeout using the product/factor normalization reduction as
the Boolean-stability input. -/
theorem no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_localFactorReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hprod : PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns)
    (hlocal : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_allocationStability_localFactorReduction_routeBEnvelope_npInclusion
    M htb hns hcomm
    (paperScale_allocationStability_of_productNormalizationReduction
      M htb hns hprod)
    hlocal henv hnp

/-- Compact closeout package with product/factor normalization as the remaining
Boolean-stability target. -/
structure PaperScalePiPlusBooleanProjectedOneOneProductNormalizationCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  commutation : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
    M htb hns
  product_normalization :
    PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns
  local_factor_to_allocation :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns
  routeB_envelope : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns
  np_subspace_inclusion : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    M htb hns

/-- The product-normalization closeout package rules out a SAT decider. -/
theorem no_decidesSAT_at_paperScale_of_oneOneProductNormalizationCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOneProductNormalizationCloseoutInputs
      M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_localFactorReduction_routeBEnvelope_npInclusion
    M htb hns hinputs.commutation hinputs.product_normalization
    hinputs.local_factor_to_allocation hinputs.routeB_envelope
    hinputs.np_subspace_inclusion

/-! ## Axiom audit anchors -/

#print axioms finset_prod_mem_span_finiteProductChoiceSet
#print axioms allocatedDerivativeProduct_mem_span_finiteProductChoiceSet
#print axioms allocatedProduct_mem_span_of_normalizesToDistributedGenerator
#print axioms allocationStability_of_productNormalizationReduction
#print axioms paperScale_allocationStability_of_productNormalizationReduction
#print axioms paperScale_normalizedDerivativeCriterion_of_commutation_and_productNormalizationReduction
#print axioms no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_localFactorReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_oneOneProductNormalizationCloseoutInputs

end PallLean.Paper93.DeepMath.PathC
