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

/-- Raw-pullback assembly for an allocated transformed Leibniz product from
local factor spans.  If each local derivative factor is in its local span, and
if every pointwise product-choice generator has its projected row pullback in
the enlarged source SPDP window, then the allocated product row itself pulls
back into that window. -/
theorem allocatedProduct_rawPullback_mem_of_localSpans
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (m : SATDeciderGaugeSpace M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (A : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      Set (SATDeciderGaugeSpace M n hn2 htb hns))
    (hlocal : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length,
      iterDerivList (alloc i)
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D)[i.val] ∈ Submodule.span ℚ (A i))
    (hchoice : ∀ q ∈ finiteProductChoiceSet Finset.univ A,
      (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
        (mlProj (m * q)) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
            (cookLevinFactoredPoly M n)) :
    (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
      (mlProj (m * piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc)) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
            (cookLevinFactoredPoly M n) := by
  classical
  let G : Set (SATDeciderGaugeSpace M n hn2 htb hns) :=
    (fun q => mlProj (m * q)) '' finiteProductChoiceSet Finset.univ A
  let W : Submodule ℚ (SATDeciderGaugeSpace M n hn2 htb hns) :=
    mlBlockedSpdpSubspaceInc
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
      (cookLevinFactoredPoly M n)
  have hprod : piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc ∈
      Submodule.span ℚ (finiteProductChoiceSet Finset.univ A) :=
    allocatedDerivativeProduct_mem_span_finiteProductChoiceSet
      M n hn2 htb hns D alloc A hlocal
  have hspan : mlProj (m * piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈ Submodule.span ℚ G := by
    simpa [G] using
      SymmetricPower.mlProj_mul_mem_span_image m
        (finiteProductChoiceSet Finset.univ A)
        (piPlusBooleanProjectedAllocatedDerivativeProduct M n hn2 htb hns D alloc)
        hprod
  refine piPlusRawPullback_mem_of_mem_span M n hn2 htb hns
    (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) G W
    (mlProj (m * piPlusBooleanProjectedAllocatedDerivativeProduct
      M n hn2 htb hns D alloc)) hspan ?_
  intro q hq
  rcases hq with ⟨r, hr, rfl⟩
  exact hchoice r hr

/-- Paper-scale specialization of `allocatedProduct_rawPullback_mem_of_localSpans`
for the widened `(1,1)` source window. -/
theorem paperScale_allocatedProduct_rawPullback_mem_of_localSpans_oneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (m : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (A : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      Set (SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns))
    (hlocal : ∀ i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length,
      iterDerivList (alloc i)
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns)[i.val] ∈ Submodule.span ℚ (A i))
    (hchoice : ∀ q ∈ finiteProductChoiceSet Finset.univ A,
      (cookLevinPiPlusSATTransform_paperScale M htb hns).equiv.symm
        (mlProj (m * q)) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
            (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 1)
            (cookLevinFactoredPoly M (2 ^ 804))) :
    (cookLevinPiPlusSATTransform_paperScale M htb hns).equiv.symm
      (mlProj (m * piPlusBooleanProjectedAllocatedDerivativeProduct
        M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc)) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
            (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 1)
            (cookLevinFactoredPoly M (2 ^ 804)) :=
  allocatedProduct_rawPullback_mem_of_localSpans 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    m alloc A hlocal hchoice

/-! ## From allocation-local spans to transformed-generator pullback

The previous theorem handles one concrete allocation once its local factors have
been classified into local spans and every product-choice generator has a source
pullback.  The next useful seam is the uniform version consumed by the existing
P-side classifier: every distributed Leibniz generator has such a local-span
classification.
-/

/-- Uniform local-span/product-choice reduction for transformed Leibniz
generator pullback.  For each derivative allocation, it supplies local generator
sets `A i`, proves every local allocated derivative lies in its local span, and
proves every pointwise product choice pulls back into the widened source SPDP
window. -/
def PiPlusBooleanProjectedAllocationLocalSpansPullbackReduction
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      ∀ (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length →
          List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
        (∀ i, ∀ v ∈ alloc i, v ∈ S) →
        ∃ A : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length →
          Set (SATDeciderGaugeSpace M n hn2 htb hns),
          (∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length,
            iterDerivList (alloc i)
              (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D)[i.val] ∈ Submodule.span ℚ (A i)) ∧
          (∀ q ∈ finiteProductChoiceSet Finset.univ A,
            (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
              (mlProj (m * q)) ∈
                mlBlockedSpdpSubspaceInc
                  (cook_levin_compilation M n hn2 htb hns).partition
                  (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
                  (cookLevinFactoredPoly M n))

/-- The allocation-local span/product-choice reduction closes the standard
transformed Leibniz generator pullback payload. -/
theorem transformedLeibnizGeneratorPullback_of_allocationLocalSpansPullbackReduction
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedAllocationLocalSpansPullbackReduction
      extraK extraL M n hn2 htb hns D) :
    PiPlusBooleanProjectedTransformedLeibnizGeneratorPullback
      extraK extraL M n hn2 htb hns D := by
  intro S m hSlen hmdeg hmvars hadm q hq
  rcases hq with ⟨alloc, halloc, rfl⟩
  rcases hred S m hSlen hmdeg hmvars hadm alloc halloc with
    ⟨A, hlocal, hchoice⟩
  exact allocatedProduct_rawPullback_mem_of_localSpans
    extraK extraL M n hn2 htb hns D m alloc A hlocal hchoice

/-- Paper-scale `(1,1)` local-span/product-choice reduction. -/
abbrev PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedAllocationLocalSpansPullbackReduction 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale `(1,1)` transformed-generator pullback from the local-span /
product-choice reduction. -/
theorem paperScale_transformedLeibnizGeneratorPullbackOneOne_of_allocationLocalSpansPullbackReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorPullbackOneOne
      M htb hns :=
  transformedLeibnizGeneratorPullback_of_allocationLocalSpansPullbackReduction
    1 1 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hred

/-- Normalized polynomial span plus the allocation-local span/product-choice
reduction closes the `(1,1)` factored row-span classifier directly, bypassing the
older exact row/allocation-certificate socket. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_allocationLocalSpansPullbackReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_generatorPullback
    M htb hns hpoly
    (paperScale_transformedLeibnizGeneratorPullbackOneOne_of_allocationLocalSpansPullbackReduction
      M htb hns hred)

/-- Compact P-side closeout package whose remaining product work is exactly the
allocation-local span/product-choice reduction. -/
structure PaperScalePiPlusBooleanProjectedOneOneAllocationLocalSpansCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  polynomial_span : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
    M htb hns
  allocation_local_spans_pullback :
    PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
      M htb hns

/-- The allocation-local span closeout package yields the `(1,1)` factored
row-span classifier. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_allocationLocalSpansCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOneAllocationLocalSpansCloseoutInputs
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_allocationLocalSpansPullbackReduction
    M htb hns hinputs.polynomial_span hinputs.allocation_local_spans_pullback

/-- Allocation-local span closeout inputs plus explicit Route-B `(1,1)` and
NP-side inputs rule out a SAT decider at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_allocationLocalSpansCloseoutInputs_routeB_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOneAllocationLocalSpansCloseoutInputs
      M htb hns)
    (hpside : PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_oneOneFinalFrontierData
    M htb hns
    { compiled_p_subspace_inclusion :=
        paperScale_compiledPSubspaceInclusionOneOne_of_rowSpanClassifier
          M htb hns
          (paperScale_factoredRowSpanClassifierOneOne_of_allocationLocalSpansCloseoutInputs
            M htb hns hinputs)
      routeB_windowed_p_side_bound := hpside
      np_subspace_inclusion := hnp }

/-- Allocation-local span closeout inputs plus a Route-B `(1,1)` envelope and
NP-side input rule out a SAT decider at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_allocationLocalSpansCloseoutInputs_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOneAllocationLocalSpansCloseoutInputs
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_allocationLocalSpansCloseoutInputs_routeB_npInclusion
    M htb hns hinputs
    (paperScale_routeBSATWindowedIncPSideRankBoundOneOne_of_envelope
      M htb hns henv)
    hnp

/-- Polynomial span plus allocation-local span/product-choice reduction plus a
Route-B `(1,1)` envelope and NP-side input rule out a SAT decider at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_polynomialSpan_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_allocationLocalSpansCloseoutInputs_routeBEnvelope_npInclusion
    M htb hns
    { polynomial_span := hpoly, allocation_local_spans_pullback := hred }
    henv hnp

/-! ## From local-factor payloads to allocation-local pullback reductions

The rest/Booleanity local payloads are now unconditional.  This names the next
honest mathematical target: use those local certificates to provide, for every
Leibniz allocation, local spans for all allocated factors and pullback membership
for every pointwise product-choice generator.
-/

/-- The remaining local-to-product-choice seam for the allocation-local pullback
route.  It consumes the unconditional `(1,1)` local-factor payload and produces
the allocation-local span/product-choice pullback reduction. -/
structure PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationLocalSpansPullbackReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  allocation_local_spans_of_local :
    ∀ (_payload : BoolPoly.PaperScalePiPlusBooleanProjectedOneOneLocalFactorPayload
        M htb hns),
      PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
        M htb hns

/-- Since the local-factor payload is unconditional, the local-to-product-choice
reduction yields the paper-scale allocation-local span/product-choice pullback
reduction. -/
theorem paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorToAllocationLocalSpansReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred :
      PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationLocalSpansPullbackReduction
        M htb hns) :
    PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
      M htb hns :=
  hred.allocation_local_spans_of_local
    (BoolPoly.paperScalePiPlusBooleanProjectedOneOneLocalFactorPayload_unconditional
      M htb hns)

/-- Normalized polynomial span plus the local-to-product-choice reduction closes
the `(1,1)` factored row-span classifier through the allocation-local route. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_localFactorToAllocationLocalSpansReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred :
      PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationLocalSpansPullbackReduction
        M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_allocationLocalSpansPullbackReduction
    M htb hns hpoly
    (paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorToAllocationLocalSpansReduction
      M htb hns hred)

/-- Polynomial span plus the local-to-product-choice reduction plus a Route-B
`(1,1)` envelope and NP-side input rule out a SAT decider at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred :
      PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationLocalSpansPullbackReduction
        M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_polynomialSpan_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    M htb hns hpoly
    (paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorToAllocationLocalSpansReduction
      M htb hns hred)
    henv hnp

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

/-- The remaining local-to-product-normalization seam.  It consumes the
unconditional `(1,1)` local-factor payload and produces the product/factor
normalization reduction needed for Boolean stability. -/
structure PaperScalePiPlusBooleanProjectedOneOneLocalFactorToProductNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  product_normalization_of_local :
    ∀ (_payload : BoolPoly.PaperScalePiPlusBooleanProjectedOneOneLocalFactorPayload
        M htb hns),
      PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
        M htb hns

/-- Since the local-factor payload is unconditional, the local-to-product-
normalization reduction yields the paper-scale product/factor normalization
reduction. -/
theorem paperScale_productNormalizationReduction_of_localFactorToProductNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred :
      PaperScalePiPlusBooleanProjectedOneOneLocalFactorToProductNormalizationReduction
        M htb hns) :
    PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns :=
  hred.product_normalization_of_local
    (BoolPoly.paperScalePiPlusBooleanProjectedOneOneLocalFactorPayload_unconditional
      M htb hns)

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

/-- Commutation plus product/factor normalization reduction give the normalized
polynomial span used by the allocation-local pullback closeout. -/
theorem paperScale_normalizedDerivativePolynomialSpan_of_commutation_and_productNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hprod : PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan M htb hns :=
  paperScale_normalizedDerivativePolynomialSpan_of_criterion
    M htb hns
    (paperScale_normalizedDerivativeCriterion_of_commutation_and_productNormalizationReduction
      M htb hns hcomm hprod)

/-- Final closeout using product/factor normalization for the normalized
polynomial span, allocation-local span/product-choice reduction for the
transformed-generator pullback, and an explicit Route-B `(1,1)` P-side bound. -/
theorem no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_allocationLocalSpansPullbackReduction_routeB_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hprod : PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns)
    (hpull : PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
      M htb hns)
    (hpside : PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_allocationLocalSpansCloseoutInputs_routeB_npInclusion
    M htb hns
    { polynomial_span :=
        paperScale_normalizedDerivativePolynomialSpan_of_commutation_and_productNormalizationReduction
          M htb hns hcomm hprod
      allocation_local_spans_pullback := hpull }
    hpside hnp

/-- Final envelope closeout using product/factor normalization for the normalized
polynomial span and allocation-local span/product-choice reduction for the
transformed-generator pullback. -/
theorem no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hprod : PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns)
    (hpull : PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_polynomialSpan_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    M htb hns
    (paperScale_normalizedDerivativePolynomialSpan_of_commutation_and_productNormalizationReduction
      M htb hns hcomm hprod)
    hpull henv hnp

/-- Local-factor-to-product-normalization supplies the normalized-polynomial-span
side, while the local-factor-to-product-choice reduction supplies the allocation-
local pullback side. -/
theorem no_decidesSAT_at_paperScale_of_commutation_localFactorToProductNormalization_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hprodLocal :
      PaperScalePiPlusBooleanProjectedOneOneLocalFactorToProductNormalizationReduction
        M htb hns)
    (hlocal :
      PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationLocalSpansPullbackReduction
        M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    M htb hns hcomm
    (paperScale_productNormalizationReduction_of_localFactorToProductNormalizationReduction
      M htb hns hprodLocal)
    (paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorToAllocationLocalSpansReduction
      M htb hns hlocal)
    henv hnp

/-- Product normalization supplies the normalized-polynomial-span side, while the
local-factor-to-product-choice reduction supplies the allocation-local pullback
side. -/
theorem no_decidesSAT_at_paperScale_of_commutation_productNormalization_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hprod : PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns)
    (hlocal :
      PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationLocalSpansPullbackReduction
        M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    M htb hns hcomm hprod
    (paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorToAllocationLocalSpansReduction
      M htb hns hlocal)
    henv hnp

/-- Compact closeout package for the current Route-C frontier: product/factor
normalization supplies the normalized-polynomial-span side, and allocation-local
span/product-choice pullback supplies the transformed-generator side. -/
structure PaperScalePiPlusBooleanProjectedOneOneProductNormalizationAllocationLocalSpansCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  commutation : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
    M htb hns
  product_normalization :
    PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns
  allocation_local_spans_pullback :
    PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
      M htb hns
  routeB_envelope : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns
  np_subspace_inclusion : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    M htb hns

/-- The product-normalization/allocation-local-spans closeout package rules out a
SAT decider. -/
theorem no_decidesSAT_at_paperScale_of_oneOneProductNormalizationAllocationLocalSpansCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs :
      PaperScalePiPlusBooleanProjectedOneOneProductNormalizationAllocationLocalSpansCloseoutInputs
        M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    M htb hns hinputs.commutation hinputs.product_normalization
    hinputs.allocation_local_spans_pullback hinputs.routeB_envelope
    hinputs.np_subspace_inclusion

/-- Unified local-factor product-assembly seam.  It consumes the unconditional
`(1,1)` local-factor payload once and produces both pieces needed downstream:
product/factor normalization for Boolean stability and allocation-local
span/product-choice pullback for the transformed-generator side. -/
structure PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  product_assembly_of_local :
    ∀ (_payload : BoolPoly.PaperScalePiPlusBooleanProjectedOneOneLocalFactorPayload
        M htb hns),
      PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
          M htb hns ∧
        PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
          M htb hns

/-- The unified local-factor product-assembly seam yields product/factor
normalization. -/
theorem paperScale_productNormalizationReduction_of_localFactorProductAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns :=
  (hred.product_assembly_of_local
    (BoolPoly.paperScalePiPlusBooleanProjectedOneOneLocalFactorPayload_unconditional
      M htb hns)).1

/-- The unified local-factor product-assembly seam yields the allocation-local
span/product-choice pullback reduction. -/
theorem paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorProductAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
      M htb hns :=
  (hred.product_assembly_of_local
    (BoolPoly.paperScalePiPlusBooleanProjectedOneOneLocalFactorPayload_unconditional
      M htb hns)).2

/-- Normalized polynomial span plus the unified local-factor product-assembly
reduction, explicit Route-B `(1,1)` P-side bound, and NP-side input rule out a
SAT decider at paper scale.  This is the commutation-free closeout surface: the
normalized span is supplied directly, while the unified product-assembly seam
supplies the transformed-generator pullback side. -/
theorem no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorProductAssemblyReduction_routeB_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns)
    (hpside : PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_allocationLocalSpansCloseoutInputs_routeB_npInclusion
    M htb hns
    { polynomial_span := hpoly
      allocation_local_spans_pullback :=
        paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorProductAssemblyReduction
          M htb hns hred }
    hpside hnp

/-- Normalized polynomial span plus the unified local-factor product-assembly
reduction, Route-B `(1,1)` envelope, and NP-side input rule out a SAT decider at
paper scale. -/
theorem no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorProductAssemblyReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorProductAssemblyReduction_routeB_npInclusion
    M htb hns hpoly hred
    (paperScale_routeBSATWindowedIncPSideRankBoundOneOne_of_envelope
      M htb hns henv)
    hnp

/-- Commutation plus the unified local-factor product-assembly reduction,
explicit Route-B `(1,1)` P-side bound, and NP-side input rule out a SAT decider
at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_commutation_localFactorProductAssemblyReduction_routeB_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns)
    (hpside : PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_allocationLocalSpansPullbackReduction_routeB_npInclusion
    M htb hns hcomm
    (paperScale_productNormalizationReduction_of_localFactorProductAssemblyReduction
      M htb hns hred)
    (paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorProductAssemblyReduction
      M htb hns hred)
    hpside hnp

/-- Commutation plus the unified local-factor product-assembly reduction, Route-B
`(1,1)` envelope, and NP-side input rule out a SAT decider at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_commutation_localFactorProductAssemblyReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    M htb hns hcomm
    (paperScale_productNormalizationReduction_of_localFactorProductAssemblyReduction
      M htb hns hred)
    (paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorProductAssemblyReduction
      M htb hns hred)
    henv hnp

/-- Compact closeout package whose remaining product work is the single unified
local-factor product-assembly reduction. -/
structure PaperScalePiPlusBooleanProjectedOneOneUnifiedLocalFactorProductAssemblyCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  commutation : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
    M htb hns
  local_factor_product_assembly :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns
  routeB_envelope : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns
  np_subspace_inclusion : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    M htb hns

/-- Commutation-free closeout package with direct normalized-polynomial-span
input and a Route-B `(1,1)` envelope. -/
structure PaperScalePiPlusBooleanProjectedOneOnePolynomialSpanUnifiedLocalFactorProductAssemblyCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  polynomial_span : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
    M htb hns
  local_factor_product_assembly :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns
  routeB_envelope : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns
  np_subspace_inclusion : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    M htb hns

/-- Commutation-free closeout package with direct normalized-polynomial-span
input and an explicit Route-B `(1,1)` P-side bound. -/
structure PaperScalePiPlusBooleanProjectedOneOnePolynomialSpanUnifiedLocalFactorProductAssemblyRankBoundCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  polynomial_span : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
    M htb hns
  local_factor_product_assembly :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns
  routeB_windowed_p_side_bound :
    PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns
  np_subspace_inclusion : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    M htb hns

/-- The direct-polynomial-span, explicit-rank-bound unified closeout package rules
out a SAT decider. -/
theorem no_decidesSAT_at_paperScale_of_oneOnePolynomialSpanUnifiedLocalFactorProductAssemblyRankBoundCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs :
      PaperScalePiPlusBooleanProjectedOneOnePolynomialSpanUnifiedLocalFactorProductAssemblyRankBoundCloseoutInputs
        M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorProductAssemblyReduction_routeB_npInclusion
    M htb hns hinputs.polynomial_span hinputs.local_factor_product_assembly
    hinputs.routeB_windowed_p_side_bound hinputs.np_subspace_inclusion

/-- The direct-polynomial-span unified closeout package rules out a SAT decider. -/
theorem no_decidesSAT_at_paperScale_of_oneOnePolynomialSpanUnifiedLocalFactorProductAssemblyCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs :
      PaperScalePiPlusBooleanProjectedOneOnePolynomialSpanUnifiedLocalFactorProductAssemblyCloseoutInputs
        M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorProductAssemblyReduction_routeBEnvelope_npInclusion
    M htb hns hinputs.polynomial_span hinputs.local_factor_product_assembly
    hinputs.routeB_envelope hinputs.np_subspace_inclusion

/-- Compact closeout package with an explicit Route-B `(1,1)` P-side bound rather
than a max-window envelope. -/
structure PaperScalePiPlusBooleanProjectedOneOneUnifiedLocalFactorProductAssemblyRankBoundCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  commutation : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
    M htb hns
  local_factor_product_assembly :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns
  routeB_windowed_p_side_bound :
    PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns
  np_subspace_inclusion : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    M htb hns

/-- The explicit-rank-bound unified closeout package rules out a SAT decider. -/
theorem no_decidesSAT_at_paperScale_of_oneOneUnifiedLocalFactorProductAssemblyRankBoundCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs :
      PaperScalePiPlusBooleanProjectedOneOneUnifiedLocalFactorProductAssemblyRankBoundCloseoutInputs
        M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_localFactorProductAssemblyReduction_routeB_npInclusion
    M htb hns hinputs.commutation hinputs.local_factor_product_assembly
    hinputs.routeB_windowed_p_side_bound hinputs.np_subspace_inclusion

/-- The unified local-factor product-assembly closeout package rules out a SAT
decider. -/
theorem no_decidesSAT_at_paperScale_of_oneOneUnifiedLocalFactorProductAssemblyCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs :
      PaperScalePiPlusBooleanProjectedOneOneUnifiedLocalFactorProductAssemblyCloseoutInputs
        M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_localFactorProductAssemblyReduction_routeBEnvelope_npInclusion
    M htb hns hinputs.commutation hinputs.local_factor_product_assembly
    hinputs.routeB_envelope hinputs.np_subspace_inclusion

/-- Compact closeout package whose two product-assembly inputs are both phrased
as consumers of the unconditional local-factor payload. -/
structure PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  commutation : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
    M htb hns
  local_factor_to_product_normalization :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorToProductNormalizationReduction
      M htb hns
  local_factor_to_allocation_local_spans :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationLocalSpansPullbackReduction
      M htb hns
  routeB_envelope : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns
  np_subspace_inclusion : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    M htb hns

/-- The local-factor product-assembly closeout package rules out a SAT decider. -/
theorem no_decidesSAT_at_paperScale_of_oneOneLocalFactorProductAssemblyCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs :
      PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyCloseoutInputs
        M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_localFactorToProductNormalization_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
    M htb hns hinputs.commutation
    hinputs.local_factor_to_product_normalization
    hinputs.local_factor_to_allocation_local_spans hinputs.routeB_envelope
    hinputs.np_subspace_inclusion

/-- Compact closeout package with only the local-factor-to-product-choice seam as
the transformed-generator-side input.  The local payload itself is unconditional,
so this exposes the next real product assembly target. -/
structure PaperScalePiPlusBooleanProjectedOneOneProductNormalizationLocalFactorToAllocationLocalSpansCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  commutation : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
    M htb hns
  product_normalization :
    PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns
  local_factor_to_allocation_local_spans :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationLocalSpansPullbackReduction
      M htb hns
  routeB_envelope : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns
  np_subspace_inclusion : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    M htb hns

/-- The product-normalization/local-factor-to-product-choice closeout package
rules out a SAT decider. -/
theorem no_decidesSAT_at_paperScale_of_oneOneProductNormalizationLocalFactorToAllocationLocalSpansCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs :
      PaperScalePiPlusBooleanProjectedOneOneProductNormalizationLocalFactorToAllocationLocalSpansCloseoutInputs
        M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_productNormalization_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
    M htb hns hinputs.commutation hinputs.product_normalization
    hinputs.local_factor_to_allocation_local_spans hinputs.routeB_envelope
    hinputs.np_subspace_inclusion

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
#print axioms allocatedProduct_rawPullback_mem_of_localSpans
#print axioms paperScale_allocatedProduct_rawPullback_mem_of_localSpans_oneOne
#print axioms transformedLeibnizGeneratorPullback_of_allocationLocalSpansPullbackReduction
#print axioms paperScale_transformedLeibnizGeneratorPullbackOneOne_of_allocationLocalSpansPullbackReduction
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_allocationLocalSpansPullbackReduction
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_allocationLocalSpansCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_allocationLocalSpansCloseoutInputs_routeB_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_allocationLocalSpansCloseoutInputs_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_polynomialSpan_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
#print axioms paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorToAllocationLocalSpansReduction
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_localFactorToAllocationLocalSpansReduction
#print axioms no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
#print axioms allocatedProduct_mem_span_of_normalizesToDistributedGenerator
#print axioms paperScale_productNormalizationReduction_of_localFactorToProductNormalizationReduction
#print axioms allocationStability_of_productNormalizationReduction
#print axioms paperScale_allocationStability_of_productNormalizationReduction
#print axioms paperScale_normalizedDerivativeCriterion_of_commutation_and_productNormalizationReduction
#print axioms paperScale_normalizedDerivativePolynomialSpan_of_commutation_and_productNormalizationReduction
#print axioms no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_allocationLocalSpansPullbackReduction_routeB_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
#print axioms paperScale_productNormalizationReduction_of_localFactorProductAssemblyReduction
#print axioms paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorProductAssemblyReduction
#print axioms no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorProductAssemblyReduction_routeB_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorProductAssemblyReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_oneOnePolynomialSpanUnifiedLocalFactorProductAssemblyRankBoundCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_oneOnePolynomialSpanUnifiedLocalFactorProductAssemblyCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_commutation_localFactorProductAssemblyReduction_routeB_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_commutation_localFactorProductAssemblyReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_oneOneUnifiedLocalFactorProductAssemblyRankBoundCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_oneOneUnifiedLocalFactorProductAssemblyCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_commutation_localFactorToProductNormalization_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_commutation_productNormalization_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_oneOneProductNormalizationAllocationLocalSpansCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_oneOneLocalFactorProductAssemblyCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_oneOneProductNormalizationLocalFactorToAllocationLocalSpansCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_localFactorReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_oneOneProductNormalizationCloseoutInputs

end PallLean.Paper93.DeepMath.PathC
