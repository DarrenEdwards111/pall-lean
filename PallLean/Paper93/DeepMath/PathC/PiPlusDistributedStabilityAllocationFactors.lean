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

/-- Allocated derivative product form of the finite quotient-product law:
Boolean-normalizing the whole allocated product is the same final normal form as
first Boolean-normalizing every allocated local derivative factor and then
multiplying.  This is the first product-level algebraic step after the generic
finite normalization law. -/
theorem zeroProfileBooleanNormalize_allocatedDerivativeProduct_eq_normalizedFactorProduct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    zeroProfileBooleanNormalize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) =
      zeroProfileBooleanNormalize
        (Finset.univ.prod (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length =>
          zeroProfileBooleanNormalize
            (iterDerivList (alloc i)
              (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D)[i.val]))) := by
  rw [piPlusBooleanProjectedAllocatedDerivativeProduct]
  symm
  exact zeroProfileBooleanNormalize_finset_prod_normalized
    (s := (Finset.univ : Finset (Fin (piPlusBooleanProjectedTransformedConstraintFactors
      M n hn2 htb hns D).length)))
    (p := fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
      M n hn2 htb hns D).length =>
      iterDerivList (alloc i)
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D)[i.val])

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

/-- Pointwise products are monotone in the local generator sets.  This is the
basic enlargement lemma needed when Booleanity/signed-row local certificates are
first proved in small hand-built spans and then absorbed into a larger product
choice space. -/
theorem finiteProductChoiceSet_mono
    {n : Nat} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {A B : ι → Set (MvPolynomial (Fin n) ℚ)}
    (hAB : ∀ i ∈ s, A i ⊆ B i) :
    finiteProductChoiceSet s A ⊆ finiteProductChoiceSet s B := by
  intro q hq
  rcases hq with ⟨a, ha, rfl⟩
  refine ⟨a, ?_, rfl⟩
  intro i hi
  exact hAB i hi (ha i hi)

/-- Span form of `finiteProductChoiceSet_mono`. -/
theorem span_finiteProductChoiceSet_mono
    {n : Nat} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {A B : ι → Set (MvPolynomial (Fin n) ℚ)}
    (hAB : ∀ i ∈ s, A i ⊆ B i) :
    Submodule.span ℚ (finiteProductChoiceSet s A) ≤
      Submodule.span ℚ (finiteProductChoiceSet s B) :=
  Submodule.span_mono (finiteProductChoiceSet_mono s hAB)

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

/-- Finite-product span assembly with local generator enlargement.  This is the
raw, pre-normalization version of the monotone assembly bridge: local witnesses
proved in compact sets `A i` may be consumed by a larger common product-choice
family `B i`. -/
theorem finset_prod_mem_span_finiteProductChoiceSet_of_mono
    {n : Nat} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A B : ι → Set (MvPolynomial (Fin n) ℚ))
    (p : ι → MvPolynomial (Fin n) ℚ)
    (hp : ∀ i ∈ s, p i ∈ Submodule.span ℚ (A i))
    (hAB : ∀ i ∈ s, A i ⊆ B i) :
    s.prod p ∈ Submodule.span ℚ (finiteProductChoiceSet s B) := by
  exact (span_finiteProductChoiceSet_mono s hAB)
    (finset_prod_mem_span_finiteProductChoiceSet s A p hp)

/-- Allocated Cook--Levin product assembly with local generator enlargement.
This bridges concrete local row/Booleanity certificates into a larger product
classifier before any Boolean quotient normalization is applied. -/
theorem allocatedDerivativeProduct_mem_span_finiteProductChoiceSet_of_mono
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (A B : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      Set (MvPolynomial
        (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))
    (hlocal : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length,
      iterDerivList (alloc i)
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D)[i.val] ∈ Submodule.span ℚ (A i))
    (hAB : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length, A i ⊆ B i) :
    piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc ∈
      Submodule.span ℚ (finiteProductChoiceSet Finset.univ B) := by
  classical
  rw [piPlusBooleanProjectedAllocatedDerivativeProduct]
  let ι := Fin (piPlusBooleanProjectedTransformedConstraintFactors
    M n hn2 htb hns D).length
  let N := (cook_levin_compilation M n hn2 htb hns).numVars
  let p : ι → MvPolynomial (Fin N) ℚ := fun i =>
    iterDerivList (alloc i)
      (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D)[i.val]
  change (Finset.univ : Finset ι).prod p ∈
    Submodule.span ℚ (finiteProductChoiceSet (Finset.univ : Finset ι) B)
  refine finset_prod_mem_span_finiteProductChoiceSet_of_mono
    (n := N) (ι := ι) (s := (Finset.univ : Finset ι))
    (A := A) (B := B) (p := p) ?_ ?_
  · intro i _
    exact hlocal i
  · intro i _
    exact hAB i

/-- Generator-level Boolean stability of a product-choice set lifts to stability
of its whole linear span.  This separates the genuinely algebraic normalization
condition from the linear-span bookkeeping used by the product assembly. -/
theorem zeroProfileBooleanNormalize_mem_span_finiteProductChoiceSet_of_generatorStable
    {n : Nat} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → Set (MvPolynomial (Fin n) ℚ))
    (hstable : ∀ q ∈ finiteProductChoiceSet s A,
      zeroProfileBooleanNormalize q ∈ Submodule.span ℚ (finiteProductChoiceSet s A))
    {p : MvPolynomial (Fin n) ℚ}
    (hp : p ∈ Submodule.span ℚ (finiteProductChoiceSet s A)) :
    zeroProfileBooleanNormalize p ∈
      Submodule.span ℚ (finiteProductChoiceSet s A) := by
  classical
  have hmap_le :
      Submodule.map (zeroProfileBooleanNormalizeLinearMap (n := n))
        (Submodule.span ℚ (finiteProductChoiceSet s A)) ≤
      Submodule.span ℚ (finiteProductChoiceSet s A) := by
    rw [Submodule.map_span_le]
    intro q hq
    exact hstable q hq
  change zeroProfileBooleanNormalizeLinearMap p ∈
    Submodule.span ℚ (finiteProductChoiceSet s A)
  exact hmap_le (Submodule.mem_map_of_mem hp)

/-- Normalized finite-product span assembly.  If every locally normalized factor
lies in its local span, and the pointwise product-choice span is closed under
Boolean normalization, then the Boolean normal form of the whole product lies in
that same product-choice span.  This is the span-level replacement for the too
strong demand that a normalized product literally be one distributed generator. -/
theorem zeroProfileBooleanNormalize_finset_prod_mem_span_finiteProductChoiceSet
    {n : Nat} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → Set (MvPolynomial (Fin n) ℚ))
    (p : ι → MvPolynomial (Fin n) ℚ)
    (hp : ∀ i ∈ s, zeroProfileBooleanNormalize (p i) ∈ Submodule.span ℚ (A i))
    (hstable : ∀ q ∈ finiteProductChoiceSet s A,
      zeroProfileBooleanNormalize q ∈ Submodule.span ℚ (finiteProductChoiceSet s A)) :
    zeroProfileBooleanNormalize (s.prod p) ∈
      Submodule.span ℚ (finiteProductChoiceSet s A) := by
  classical
  have hprod : s.prod (fun i => zeroProfileBooleanNormalize (p i)) ∈
      Submodule.span ℚ (finiteProductChoiceSet s A) :=
    finset_prod_mem_span_finiteProductChoiceSet s A
      (fun i => zeroProfileBooleanNormalize (p i)) hp
  have hnorm : zeroProfileBooleanNormalize
      (s.prod (fun i => zeroProfileBooleanNormalize (p i))) ∈
      Submodule.span ℚ (finiteProductChoiceSet s A) :=
    zeroProfileBooleanNormalize_mem_span_finiteProductChoiceSet_of_generatorStable
      s A hstable hprod
  rw [zeroProfileBooleanNormalize_finset_prod_normalized] at hnorm
  exact hnorm

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

/-- Normalized allocated-product span assembly.  This is the actual allocation
version of the normalized finite-product theorem: local normalized derivative
factor spans plus stability of product-choice generators imply that the Boolean
normal form of the whole allocated derivative product lies in the product-choice
span. -/
theorem zeroProfileBooleanNormalize_allocatedDerivativeProduct_mem_span_finiteProductChoiceSet
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
      zeroProfileBooleanNormalize
        (iterDerivList (alloc i)
          (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D)[i.val]) ∈ Submodule.span ℚ (A i))
    (hstable : ∀ q ∈ finiteProductChoiceSet Finset.univ A,
      zeroProfileBooleanNormalize q ∈
        Submodule.span ℚ (finiteProductChoiceSet Finset.univ A)) :
    zeroProfileBooleanNormalize
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈
      Submodule.span ℚ (finiteProductChoiceSet Finset.univ A) := by
  classical
  rw [zeroProfileBooleanNormalize_allocatedDerivativeProduct_eq_normalizedFactorProduct]
  let ι := Fin (piPlusBooleanProjectedTransformedConstraintFactors
    M n hn2 htb hns D).length
  let N := (cook_levin_compilation M n hn2 htb hns).numVars
  let p : ι → MvPolynomial (Fin N) ℚ := fun i =>
    zeroProfileBooleanNormalize
      (iterDerivList (alloc i)
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D)[i.val])
  change zeroProfileBooleanNormalize ((Finset.univ : Finset ι).prod p) ∈
    Submodule.span ℚ (finiteProductChoiceSet (Finset.univ : Finset ι) A)
  refine zeroProfileBooleanNormalize_finset_prod_mem_span_finiteProductChoiceSet
    (n := N) (ι := ι) (s := (Finset.univ : Finset ι)) (A := A) (p := p) ?_ ?_
  · intro i _
    dsimp [p]
    change zeroProfileBooleanNormalizeLinearMap
        (zeroProfileBooleanNormalizeLinearMap
          (iterDerivList (alloc i)
            (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D)[i.val])) ∈ Submodule.span ℚ (A i)
    rw [← LinearMap.comp_apply, zeroProfileBooleanNormalizeLinearMap_idempotent]
    exact hlocal i
  · exact hstable

/-- Normalized finite-product assembly with local generator enlargement.  Local
factors may first be certified in smaller sets `A i`; if those sets embed into
larger classifier sets `B i`, and the `B` product-choice span is stable under
Boolean normalization, then the whole normalized product lands in the larger
`B` product-choice span. -/
theorem zeroProfileBooleanNormalize_finset_prod_mem_span_finiteProductChoiceSet_of_mono
    {n : Nat} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A B : ι → Set (MvPolynomial (Fin n) ℚ))
    (p : ι → MvPolynomial (Fin n) ℚ)
    (hp : ∀ i ∈ s, zeroProfileBooleanNormalize (p i) ∈ Submodule.span ℚ (A i))
    (hAB : ∀ i ∈ s, A i ⊆ B i)
    (hstable : ∀ q ∈ finiteProductChoiceSet s B,
      zeroProfileBooleanNormalize q ∈ Submodule.span ℚ (finiteProductChoiceSet s B)) :
    zeroProfileBooleanNormalize (s.prod p) ∈
      Submodule.span ℚ (finiteProductChoiceSet s B) := by
  classical
  refine zeroProfileBooleanNormalize_finset_prod_mem_span_finiteProductChoiceSet
    (n := n) (ι := ι) (s := s) (A := B) (p := p) ?_ hstable
  intro i hi
  exact (Submodule.span_mono (hAB i hi)) (hp i hi)

/-- Allocated-product version of the monotone normalized finite-product
assembly.  This is useful when local Booleanity/signed-row derivative residues
are proved in compact local spans but the product assembly wants a larger common
classification family. -/
theorem zeroProfileBooleanNormalize_allocatedDerivativeProduct_mem_span_finiteProductChoiceSet_of_mono
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (A B : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      Set (MvPolynomial
        (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))
    (hlocal : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length,
      zeroProfileBooleanNormalize
        (iterDerivList (alloc i)
          (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D)[i.val]) ∈ Submodule.span ℚ (A i))
    (hAB : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length, A i ⊆ B i)
    (hstable : ∀ q ∈ finiteProductChoiceSet Finset.univ B,
      zeroProfileBooleanNormalize q ∈
        Submodule.span ℚ (finiteProductChoiceSet Finset.univ B)) :
    zeroProfileBooleanNormalize
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈
      Submodule.span ℚ (finiteProductChoiceSet Finset.univ B) := by
  classical
  rw [zeroProfileBooleanNormalize_allocatedDerivativeProduct_eq_normalizedFactorProduct]
  let ι := Fin (piPlusBooleanProjectedTransformedConstraintFactors
    M n hn2 htb hns D).length
  let N := (cook_levin_compilation M n hn2 htb hns).numVars
  let p : ι → MvPolynomial (Fin N) ℚ := fun i =>
    zeroProfileBooleanNormalize
      (iterDerivList (alloc i)
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D)[i.val])
  change zeroProfileBooleanNormalize ((Finset.univ : Finset ι).prod p) ∈
    Submodule.span ℚ (finiteProductChoiceSet (Finset.univ : Finset ι) B)
  refine zeroProfileBooleanNormalize_finset_prod_mem_span_finiteProductChoiceSet_of_mono
    (n := N) (ι := ι) (s := (Finset.univ : Finset ι))
    (A := A) (B := B) (p := p) ?_ ?_ hstable
  · intro i _
    dsimp [p]
    change zeroProfileBooleanNormalizeLinearMap
        (zeroProfileBooleanNormalizeLinearMap
          (iterDerivList (alloc i)
            (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D)[i.val])) ∈ Submodule.span ℚ (A i)
    rw [← LinearMap.comp_apply, zeroProfileBooleanNormalizeLinearMap_idempotent]
    exact hlocal i
  · intro i _
    exact hAB i

/-- Target-submodule form of normalized allocated-product assembly.  Instead of
requiring the product-choice set to be closed under Boolean normalization inside
itself, it is enough to know that the Boolean normal form of every pointwise
product choice already lands in a target submodule `W`.  This is the form needed
for the real Cook--Levin product synthesis, where product-choice representatives
may reduce into a larger classified row space rather than literally back to the
same generator set. -/
theorem zeroProfileBooleanNormalize_allocatedDerivativeProduct_mem_of_localNormalizedSpans_and_choiceNormalizes
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
    (W : Submodule ℚ (MvPolynomial
        (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))
    (hlocal : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length,
      zeroProfileBooleanNormalize
        (iterDerivList (alloc i)
          (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D)[i.val]) ∈ Submodule.span ℚ (A i))
    (hchoice : ∀ q ∈ finiteProductChoiceSet Finset.univ A,
      zeroProfileBooleanNormalize q ∈ W) :
    zeroProfileBooleanNormalize
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈ W := by
  classical
  rw [zeroProfileBooleanNormalize_allocatedDerivativeProduct_eq_normalizedFactorProduct]
  let ι := Fin (piPlusBooleanProjectedTransformedConstraintFactors
    M n hn2 htb hns D).length
  let N := (cook_levin_compilation M n hn2 htb hns).numVars
  let p : ι → MvPolynomial (Fin N) ℚ := fun i =>
    zeroProfileBooleanNormalize
      (iterDerivList (alloc i)
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D)[i.val])
  have hprod : (Finset.univ : Finset ι).prod p ∈
      Submodule.span ℚ (finiteProductChoiceSet (Finset.univ : Finset ι) A) := by
    refine finset_prod_mem_span_finiteProductChoiceSet
      (n := N) (ι := ι) (s := (Finset.univ : Finset ι)) (A := A) (p := p) ?_
    intro i _
    dsimp [p]
    exact hlocal i
  have hmap_le :
      Submodule.map (zeroProfileBooleanNormalizeLinearMap (n := N))
        (Submodule.span ℚ (finiteProductChoiceSet (Finset.univ : Finset ι) A)) ≤ W := by
    rw [Submodule.map_span_le]
    intro q hq
    exact hchoice q hq
  change zeroProfileBooleanNormalizeLinearMap ((Finset.univ : Finset ι).prod p) ∈ W
  exact hmap_le (Submodule.mem_map_of_mem hprod)

/-- Target-submodule normalized allocated-product assembly with local generator
enlargement.  Local normalized factors may be certified in compact spans `A i`,
then enlarged to a product-choice family `B i`; it is enough to normalize every
`B`-choice into the target submodule. -/
theorem zeroProfileBooleanNormalize_allocatedDerivativeProduct_mem_of_localNormalizedSpans_mono_and_choiceNormalizes
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (A B : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      Set (MvPolynomial
        (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))
    (W : Submodule ℚ (MvPolynomial
        (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))
    (hlocal : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length,
      zeroProfileBooleanNormalize
        (iterDerivList (alloc i)
          (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D)[i.val]) ∈ Submodule.span ℚ (A i))
    (hAB : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length, A i ⊆ B i)
    (hchoice : ∀ q ∈ finiteProductChoiceSet Finset.univ B,
      zeroProfileBooleanNormalize q ∈ W) :
    zeroProfileBooleanNormalize
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈ W := by
  refine zeroProfileBooleanNormalize_allocatedDerivativeProduct_mem_of_localNormalizedSpans_and_choiceNormalizes
    M n hn2 htb hns D alloc B W ?_ hchoice
  intro i
  exact (Submodule.span_mono (hAB i)) (hlocal i)

/-- Allocation-level Boolean stability from local normalized spans, local-set
enlargement, and normalization of every enlarged pointwise product choice into
the distributed Leibniz span.  This is the concrete consumer for local
Booleanity/row certificates that are smaller than the final classifier family. -/
theorem allocationStability_of_localNormalizedSpans_mono_and_choiceNormalizesToDistribSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
      S.length = Nat.log 2 n →
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      ∀ (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).length →
        List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
        (∀ i, ∀ v ∈ alloc i, v ∈ S) →
        ∃ A B : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length →
          Set (SATDeciderGaugeSpace M n hn2 htb hns),
          (∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length,
            zeroProfileBooleanNormalize
              (iterDerivList (alloc i)
                (piPlusBooleanProjectedTransformedConstraintFactors
                  M n hn2 htb hns D)[i.val]) ∈ Submodule.span ℚ (A i)) ∧
          (∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length, A i ⊆ B i) ∧
          (∀ q ∈ finiteProductChoiceSet Finset.univ B,
            zeroProfileBooleanNormalize q ∈
              Submodule.span ℚ
                (distribDerivProds Finset.univ
                  (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
                      M n hn2 htb hns D).length =>
                    (piPlusBooleanProjectedTransformedConstraintFactors
                      M n hn2 htb hns D)[i.val]) S))) :
    PiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M n hn2 htb hns D := by
  change ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
    S.length = Nat.log 2 n →
    isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      ∀ (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
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
  intro S hSlen hadm alloc halloc
  rcases hred S hSlen hadm alloc halloc with ⟨A, B, hlocal, hAB, hchoice⟩
  exact zeroProfileBooleanNormalize_allocatedDerivativeProduct_mem_of_localNormalizedSpans_mono_and_choiceNormalizes
    M n hn2 htb hns D alloc A B
    (Submodule.span ℚ
      (distribDerivProds Finset.univ
        (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length =>
          (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D)[i.val]) S))
    hlocal hAB hchoice

/-- Allocation-level Boolean stability from local normalized spans and
normalization of every pointwise product choice into the distributed Leibniz
span.  This avoids the too-strong exact-generator normalization requirement and
is the quotient-aware product-synthesis surface for Property 2. -/
theorem allocationStability_of_localNormalizedSpans_and_choiceNormalizesToDistribSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
      S.length = Nat.log 2 n →
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
            zeroProfileBooleanNormalize
              (iterDerivList (alloc i)
                (piPlusBooleanProjectedTransformedConstraintFactors
                  M n hn2 htb hns D)[i.val]) ∈ Submodule.span ℚ (A i)) ∧
          (∀ q ∈ finiteProductChoiceSet Finset.univ A,
            zeroProfileBooleanNormalize q ∈
              Submodule.span ℚ
                (distribDerivProds Finset.univ
                  (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
                      M n hn2 htb hns D).length =>
                    (piPlusBooleanProjectedTransformedConstraintFactors
                      M n hn2 htb hns D)[i.val]) S))) :
    PiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M n hn2 htb hns D := by
  change ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
    S.length = Nat.log 2 n →
    isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      ∀ (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
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
  intro S hSlen hadm alloc halloc
  rcases hred S hSlen hadm alloc halloc with ⟨A, hlocal, hchoice⟩
  exact zeroProfileBooleanNormalize_allocatedDerivativeProduct_mem_of_localNormalizedSpans_and_choiceNormalizes
    M n hn2 htb hns D alloc A
    (Submodule.span ℚ
      (distribDerivProds Finset.univ
        (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length =>
          (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D)[i.val]) S))
    hlocal hchoice

/-- Named monotone quotient-aware local product-normalization reduction: local
certificates may live in compact spans `A i`, then be enlarged into classifier
sets `B i` whose pointwise choices Boolean-reduce into the distributed Leibniz
span. -/
def PiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
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
      ∃ A B : Fin (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).length →
        Set (SATDeciderGaugeSpace M n hn2 htb hns),
        (∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length,
          zeroProfileBooleanNormalize
            (iterDerivList (alloc i)
              (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D)[i.val]) ∈ Submodule.span ℚ (A i)) ∧
        (∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length, A i ⊆ B i) ∧
        (∀ q ∈ finiteProductChoiceSet Finset.univ B,
          zeroProfileBooleanNormalize q ∈
            Submodule.span ℚ
              (distribDerivProds Finset.univ
                (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
                    M n hn2 htb hns D).length =>
                  (piPlusBooleanProjectedTransformedConstraintFactors
                    M n hn2 htb hns D)[i.val]) S))

/-- The monotone local product-choice reduction implies allocation-level Boolean
stability. -/
theorem allocationStability_of_localNormalizedChoiceProductMonotoneReduction
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
      M n hn2 htb hns D) :
    PiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M n hn2 htb hns D :=
  allocationStability_of_localNormalizedSpans_mono_and_choiceNormalizesToDistribSpan
    M n hn2 htb hns D hred

/-- Named quotient-aware local product-normalization reduction: every allocated
product has local normalized factor spans whose pointwise choices Boolean-reduce
into the distributed Leibniz span. -/
def PiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
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
      ∃ A : Fin (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).length →
        Set (SATDeciderGaugeSpace M n hn2 htb hns),
        (∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length,
          zeroProfileBooleanNormalize
            (iterDerivList (alloc i)
              (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D)[i.val]) ∈ Submodule.span ℚ (A i)) ∧
        (∀ q ∈ finiteProductChoiceSet Finset.univ A,
          zeroProfileBooleanNormalize q ∈
            Submodule.span ℚ
              (distribDerivProds Finset.univ
                (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
                    M n hn2 htb hns D).length =>
                  (piPlusBooleanProjectedTransformedConstraintFactors
                    M n hn2 htb hns D)[i.val]) S))

/-- The non-monotone quotient-aware reduction is a special case of the monotone
one, by taking the enlarged classifier family equal to the compact local family. -/
theorem localNormalizedChoiceProductMonotoneReduction_of_localNormalizedChoiceProductReduction
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
      M n hn2 htb hns D) :
    PiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
      M n hn2 htb hns D := by
  intro S hSlen hadm alloc halloc
  rcases hred S hSlen hadm alloc halloc with ⟨A, hlocal, hchoice⟩
  refine ⟨A, A, hlocal, ?_, hchoice⟩
  intro i x hx
  exact hx

/-- Named reduction implies allocation-level Boolean stability. -/
theorem allocationStability_of_localNormalizedChoiceProductReduction
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
      M n hn2 htb hns D) :
    PiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M n hn2 htb hns D :=
  allocationStability_of_localNormalizedSpans_and_choiceNormalizesToDistribSpan
    M n hn2 htb hns D hred

/-- Paper-scale monotone quotient-aware local product-normalization reduction. -/
abbrev PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale allocation-level stability from the monotone quotient-aware local
product normalization reduction. -/
theorem paperScale_allocationStability_of_localNormalizedChoiceProductMonotoneReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M htb hns :=
  allocationStability_of_localNormalizedChoiceProductMonotoneReduction
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hred

/-- Paper-scale quotient-aware local product-normalization reduction. -/
abbrev PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale allocation-level stability from the quotient-aware local product
normalization reduction. -/
theorem paperScale_allocationStability_of_localNormalizedChoiceProductReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M htb hns :=
  allocationStability_of_localNormalizedChoiceProductReduction
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hred

/-- Commutation plus the monotone quotient-aware local product-normalization
reduction reassemble into the normalized derivative criterion.  This is the
paper-scale consumer for local certificates proved in smaller spans and then
enlarged before product synthesis. -/
theorem paperScale_normalizedDerivativeCriterion_of_commutation_and_localNormalizedChoiceProductMonotoneReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns :=
  paperScale_normalizedDerivativeCriterion_of_commutation_and_allocationStability
    M htb hns hcomm
    (paperScale_allocationStability_of_localNormalizedChoiceProductMonotoneReduction
      M htb hns hred)

/-- Commutation plus the monotone quotient-aware local product-normalization
reduction produce the normalized polynomial span required by the P-side
classifier. -/
theorem paperScale_normalizedDerivativePolynomialSpan_of_commutation_and_localNormalizedChoiceProductMonotoneReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan M htb hns :=
  paperScale_normalizedDerivativePolynomialSpan_of_criterion
    M htb hns
    (paperScale_normalizedDerivativeCriterion_of_commutation_and_localNormalizedChoiceProductMonotoneReduction
      M htb hns hcomm hred)

/-- Commutation plus the quotient-aware local product-normalization reduction
reassemble into the normalized derivative criterion. -/
theorem paperScale_normalizedDerivativeCriterion_of_commutation_and_localNormalizedChoiceProductReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns :=
  paperScale_normalizedDerivativeCriterion_of_commutation_and_allocationStability
    M htb hns hcomm
    (paperScale_allocationStability_of_localNormalizedChoiceProductReduction
      M htb hns hred)

/-- Commutation plus the quotient-aware local product-normalization reduction
produce the normalized polynomial span required by the P-side classifier. -/
theorem paperScale_normalizedDerivativePolynomialSpan_of_commutation_and_localNormalizedChoiceProductReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan M htb hns :=
  paperScale_normalizedDerivativePolynomialSpan_of_criterion
    M htb hns
    (paperScale_normalizedDerivativeCriterion_of_commutation_and_localNormalizedChoiceProductReduction
      M htb hns hcomm hred)

/-- Normalized raw-pullback assembly for an allocated transformed Leibniz
product.  This is the pullback version of the normalized finite-product theorem:
local normalized derivative-factor spans, closure of product-choice generators
under Boolean normalization, and product-choice pullback of rows imply that the
Boolean-normalized allocated product row pulls back into the enlarged source
SPDP window. -/
theorem normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans
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
      zeroProfileBooleanNormalize
        (iterDerivList (alloc i)
          (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D)[i.val]) ∈ Submodule.span ℚ (A i))
    (hstable : ∀ q ∈ finiteProductChoiceSet Finset.univ A,
      zeroProfileBooleanNormalize q ∈
        Submodule.span ℚ (finiteProductChoiceSet Finset.univ A))
    (hchoice : ∀ q ∈ finiteProductChoiceSet Finset.univ A,
      (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
        (mlProj (m * q)) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
            (cookLevinFactoredPoly M n)) :
    (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
      (mlProj (m * zeroProfileBooleanNormalize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc))) ∈
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
  have hprod : zeroProfileBooleanNormalize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ∈
      Submodule.span ℚ (finiteProductChoiceSet Finset.univ A) :=
    zeroProfileBooleanNormalize_allocatedDerivativeProduct_mem_span_finiteProductChoiceSet
      M n hn2 htb hns D alloc A hlocal hstable
  have hspan : mlProj (m * zeroProfileBooleanNormalize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc)) ∈ Submodule.span ℚ G := by
    simpa [G] using
      SymmetricPower.mlProj_mul_mem_span_image m
        (finiteProductChoiceSet Finset.univ A)
        (zeroProfileBooleanNormalize
          (piPlusBooleanProjectedAllocatedDerivativeProduct M n hn2 htb hns D alloc))
        hprod
  refine piPlusRawPullback_mem_of_mem_span M n hn2 htb hns
    (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) G W
    (mlProj (m * zeroProfileBooleanNormalize
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc))) hspan ?_
  intro q hq
  rcases hq with ⟨r, hr, rfl⟩
  exact hchoice r hr

/-- Monotone normalized raw-pullback assembly for an allocated transformed
Leibniz product.  Local normalized factors can be proved in compact spans `A i`,
then enlarged to classifier spans `B i`; Boolean stability and product-choice
pullback are required only for the enlarged `B` family. -/
theorem normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans_mono
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (m : SATDeciderGaugeSpace M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (A B : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      Set (SATDeciderGaugeSpace M n hn2 htb hns))
    (hlocal : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length,
      zeroProfileBooleanNormalize
        (iterDerivList (alloc i)
          (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D)[i.val]) ∈ Submodule.span ℚ (A i))
    (hAB : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length, A i ⊆ B i)
    (hstable : ∀ q ∈ finiteProductChoiceSet Finset.univ B,
      zeroProfileBooleanNormalize q ∈
        Submodule.span ℚ (finiteProductChoiceSet Finset.univ B))
    (hchoice : ∀ q ∈ finiteProductChoiceSet Finset.univ B,
      (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
        (mlProj (m * q)) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
            (cookLevinFactoredPoly M n)) :
    (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
      (mlProj (m * zeroProfileBooleanNormalize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc))) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
            (cookLevinFactoredPoly M n) := by
  refine normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans
    extraK extraL M n hn2 htb hns D m alloc B ?_ hstable hchoice
  intro i
  exact (Submodule.span_mono (hAB i)) (hlocal i)

/-- Paper-scale specialization of the normalized allocated-product raw-pullback
assembly for the widened `(1,1)` source window. -/
theorem paperScale_normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans_oneOne
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
      zeroProfileBooleanNormalize
        (iterDerivList (alloc i)
          (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
            M htb hns)[i.val]) ∈ Submodule.span ℚ (A i))
    (hstable : ∀ q ∈ finiteProductChoiceSet Finset.univ A,
      zeroProfileBooleanNormalize q ∈
        Submodule.span ℚ (finiteProductChoiceSet Finset.univ A))
    (hchoice : ∀ q ∈ finiteProductChoiceSet Finset.univ A,
      (cookLevinPiPlusSATTransform_paperScale M htb hns).equiv.symm
        (mlProj (m * q)) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
            (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 1)
            (cookLevinFactoredPoly M (2 ^ 804))) :
    (cookLevinPiPlusSATTransform_paperScale M htb hns).equiv.symm
      (mlProj (m * zeroProfileBooleanNormalize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc))) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
            (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 1)
            (cookLevinFactoredPoly M (2 ^ 804)) :=
  normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    m alloc A hlocal hstable hchoice

/-- Paper-scale specialization of the monotone normalized allocated-product
raw-pullback assembly for the widened `(1,1)` source window. -/
theorem paperScale_normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans_mono_oneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (m : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (A B : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      Set (SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns))
    (hlocal : ∀ i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length,
      zeroProfileBooleanNormalize
        (iterDerivList (alloc i)
          (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
            M htb hns)[i.val]) ∈ Submodule.span ℚ (A i))
    (hAB : ∀ i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length, A i ⊆ B i)
    (hstable : ∀ q ∈ finiteProductChoiceSet Finset.univ B,
      zeroProfileBooleanNormalize q ∈
        Submodule.span ℚ (finiteProductChoiceSet Finset.univ B))
    (hchoice : ∀ q ∈ finiteProductChoiceSet Finset.univ B,
      (cookLevinPiPlusSATTransform_paperScale M htb hns).equiv.symm
        (mlProj (m * q)) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
            (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 1)
            (cookLevinFactoredPoly M (2 ^ 804))) :
    (cookLevinPiPlusSATTransform_paperScale M htb hns).equiv.symm
      (mlProj (m * zeroProfileBooleanNormalize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc))) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
            (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 1)
            (cookLevinFactoredPoly M (2 ^ 804)) :=
  normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans_mono 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    m alloc A B hlocal hAB hstable hchoice

/-- Uniform normalized local-span/product-choice reduction for allocated
transformed products.  For each derivative allocation, it supplies local
generator sets for the Boolean-normalized local derivatives, proves the finite
product-choice span is stable under Boolean normalization, and proves every
pointwise product-choice row pulls back into the source SPDP window. -/
def PiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackReduction
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
            zeroProfileBooleanNormalize
              (iterDerivList (alloc i)
                (piPlusBooleanProjectedTransformedConstraintFactors
                  M n hn2 htb hns D)[i.val]) ∈ Submodule.span ℚ (A i)) ∧
          (∀ q ∈ finiteProductChoiceSet Finset.univ A,
            zeroProfileBooleanNormalize q ∈
              Submodule.span ℚ (finiteProductChoiceSet Finset.univ A)) ∧
          (∀ q ∈ finiteProductChoiceSet Finset.univ A,
            (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
              (mlProj (m * q)) ∈
                mlBlockedSpdpSubspaceInc
                  (cook_levin_compilation M n hn2 htb hns).partition
                  (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
                  (cookLevinFactoredPoly M n))

/-- Monotone uniform normalized local-span/product-choice reduction for
allocated transformed products.  It separates compact local certificate spans
`A i` from the enlarged classifier/product-choice spans `B i` used for Boolean
stability and raw pullback. -/
def PiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackMonotoneReduction
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
        ∃ A B : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length →
          Set (SATDeciderGaugeSpace M n hn2 htb hns),
          (∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length,
            zeroProfileBooleanNormalize
              (iterDerivList (alloc i)
                (piPlusBooleanProjectedTransformedConstraintFactors
                  M n hn2 htb hns D)[i.val]) ∈ Submodule.span ℚ (A i)) ∧
          (∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length, A i ⊆ B i) ∧
          (∀ q ∈ finiteProductChoiceSet Finset.univ B,
            zeroProfileBooleanNormalize q ∈
              Submodule.span ℚ (finiteProductChoiceSet Finset.univ B)) ∧
          (∀ q ∈ finiteProductChoiceSet Finset.univ B,
            (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
              (mlProj (m * q)) ∈
                mlBlockedSpdpSubspaceInc
                  (cook_levin_compilation M n hn2 htb hns).partition
                  (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
                  (cookLevinFactoredPoly M n))

/-- The monotone normalized local-span/product-choice reduction closes the
normalized allocated-product pullback for every concrete derivative allocation. -/
theorem normalizedAllocatedProduct_rawPullback_of_normalizedAllocationLocalSpansPullbackMonotoneReduction
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackMonotoneReduction
      extraK extraL M n hn2 htb hns D) :
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
          (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
            (mlProj (m * zeroProfileBooleanNormalize
              (piPlusBooleanProjectedAllocatedDerivativeProduct
                M n hn2 htb hns D alloc))) ∈
              mlBlockedSpdpSubspaceInc
                (cook_levin_compilation M n hn2 htb hns).partition
                (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
                (cookLevinFactoredPoly M n) := by
  intro S m hSlen hmdeg hmvars hadm alloc halloc
  rcases hred S m hSlen hmdeg hmvars hadm alloc halloc with
    ⟨A, B, hlocal, hAB, hstable, hchoice⟩
  exact normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans_mono
    extraK extraL M n hn2 htb hns D m alloc A B hlocal hAB hstable hchoice

/-- The non-monotone normalized local-span/product-choice reduction is a special
case of the monotone reduction. -/
theorem normalizedAllocationLocalSpansPullbackMonotoneReduction_of_normalizedAllocationLocalSpansPullbackReduction
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackReduction
      extraK extraL M n hn2 htb hns D) :
    PiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackMonotoneReduction
      extraK extraL M n hn2 htb hns D := by
  intro S m hSlen hmdeg hmvars hadm alloc halloc
  rcases hred S m hSlen hmdeg hmvars hadm alloc halloc with
    ⟨A, hlocal, hstable, hchoice⟩
  refine ⟨A, A, hlocal, ?_, hstable, hchoice⟩
  intro i x hx
  exact hx

/-- The normalized local-span/product-choice reduction closes the normalized
allocated-product pullback for every concrete derivative allocation. -/
theorem normalizedAllocatedProduct_rawPullback_of_normalizedAllocationLocalSpansPullbackReduction
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackReduction
      extraK extraL M n hn2 htb hns D) :
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
          (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
            (mlProj (m * zeroProfileBooleanNormalize
              (piPlusBooleanProjectedAllocatedDerivativeProduct
                M n hn2 htb hns D alloc))) ∈
              mlBlockedSpdpSubspaceInc
                (cook_levin_compilation M n hn2 htb hns).partition
                (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
                (cookLevinFactoredPoly M n) := by
  intro S m hSlen hmdeg hmvars hadm alloc halloc
  rcases hred S m hSlen hmdeg hmvars hadm alloc halloc with
    ⟨A, hlocal, hstable, hchoice⟩
  exact normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans
    extraK extraL M n hn2 htb hns D m alloc A hlocal hstable hchoice

/-- Paper-scale `(1,1)` monotone normalized local-span/product-choice reduction. -/
abbrev PaperScalePiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackMonotoneReductionOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackMonotoneReduction 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale closeout of normalized allocated-product pullback from the
monotone normalized local-span/product-choice reduction. -/
theorem paperScale_normalizedAllocatedProduct_rawPullback_of_normalizedAllocationLocalSpansPullbackMonotoneReduction_oneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackMonotoneReductionOneOne
      M htb hns) :
    ∀ (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
      (m : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns),
        S.length = Nat.log 2 (2 ^ 804) →
        m.totalDegree ≤ Nat.log 2 (2 ^ 804) →
        m.vars ⊆ S.toFinset →
        isBlockAdmissible (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition S →
        ∀ (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns).length →
            List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars)),
          (∀ i, ∀ v ∈ alloc i, v ∈ S) →
          (cookLevinPiPlusSATTransform_paperScale M htb hns).equiv.symm
            (mlProj (m * zeroProfileBooleanNormalize
              (piPlusBooleanProjectedAllocatedDerivativeProduct
                M (2 ^ 804) paperScale_ge_two htb hns
                (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc))) ∈
              mlBlockedSpdpSubspaceInc
                (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
                (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 1)
                (cookLevinFactoredPoly M (2 ^ 804)) :=
  normalizedAllocatedProduct_rawPullback_of_normalizedAllocationLocalSpansPullbackMonotoneReduction
    1 1 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hred

/-- Paper-scale `(1,1)` normalized local-span/product-choice reduction. -/
abbrev PaperScalePiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackReductionOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackReduction 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale closeout of normalized allocated-product pullback from the
normalized local-span/product-choice reduction. -/
theorem paperScale_normalizedAllocatedProduct_rawPullback_of_normalizedAllocationLocalSpansPullbackReduction_oneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackReductionOneOne
      M htb hns) :
    ∀ (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
      (m : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns),
        S.length = Nat.log 2 (2 ^ 804) →
        m.totalDegree ≤ Nat.log 2 (2 ^ 804) →
        m.vars ⊆ S.toFinset →
        isBlockAdmissible (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition S →
        ∀ (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns).length →
            List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars)),
          (∀ i, ∀ v ∈ alloc i, v ∈ S) →
          (cookLevinPiPlusSATTransform_paperScale M htb hns).equiv.symm
            (mlProj (m * zeroProfileBooleanNormalize
              (piPlusBooleanProjectedAllocatedDerivativeProduct
                M (2 ^ 804) paperScale_ge_two htb hns
                (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc))) ∈
              mlBlockedSpdpSubspaceInc
                (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
                (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 1)
                (cookLevinFactoredPoly M (2 ^ 804)) :=
  normalizedAllocatedProduct_rawPullback_of_normalizedAllocationLocalSpansPullbackReduction
    1 1 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hred

/-- Paper-scale non-monotone normalized pullback reduction as a monotone one. -/
theorem paperScale_normalizedAllocationLocalSpansPullbackMonotoneReductionOneOne_of_normalizedAllocationLocalSpansPullbackReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackReductionOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedNormalizedAllocationLocalSpansPullbackMonotoneReductionOneOne
      M htb hns :=
  normalizedAllocationLocalSpansPullbackMonotoneReduction_of_normalizedAllocationLocalSpansPullbackReduction
    1 1 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hred

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

/-- Monotone raw-pullback assembly for an allocated transformed Leibniz product.
Local factor certificates may be proved in smaller spans `A i` and then enlarged
to product-classifier spans `B i`; only `B` product choices need pullback
certificates. -/
theorem allocatedProduct_rawPullback_mem_of_localSpans_mono
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (m : SATDeciderGaugeSpace M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (A B : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      Set (SATDeciderGaugeSpace M n hn2 htb hns))
    (hlocal : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length,
      iterDerivList (alloc i)
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D)[i.val] ∈ Submodule.span ℚ (A i))
    (hAB : ∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length, A i ⊆ B i)
    (hchoice : ∀ q ∈ finiteProductChoiceSet Finset.univ B,
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
  refine allocatedProduct_rawPullback_mem_of_localSpans
    extraK extraL M n hn2 htb hns D m alloc B ?_ hchoice
  intro i
  exact (Submodule.span_mono (hAB i)) (hlocal i)

/-- Paper-scale specialization of the monotone raw-pullback assembly for the
widened `(1,1)` source window. -/
theorem paperScale_allocatedProduct_rawPullback_mem_of_localSpans_mono_oneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (m : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (A B : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      Set (SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns))
    (hlocal : ∀ i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length,
      iterDerivList (alloc i)
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns)[i.val] ∈ Submodule.span ℚ (A i))
    (hAB : ∀ i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length, A i ⊆ B i)
    (hchoice : ∀ q ∈ finiteProductChoiceSet Finset.univ B,
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
  allocatedProduct_rawPullback_mem_of_localSpans_mono 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    m alloc A B hlocal hAB hchoice

/-! ## From allocation-local spans to transformed-generator pullback

The previous theorem handles one concrete allocation once its local factors have
been classified into local spans and every product-choice generator has a source
pullback.  The next useful seam is the uniform version consumed by the existing
P-side classifier: every distributed Leibniz generator has such a local-span
classification.
-/

/-- Monotone uniform local-span/product-choice reduction for transformed
Leibniz generator pullback.  It allows compact local factor certificates `A i`
to be enlarged to product-classifier spans `B i` before proving the product
choice pullback. -/
def PiPlusBooleanProjectedAllocationLocalSpansPullbackMonotoneReduction
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
        ∃ A B : Fin (piPlusBooleanProjectedTransformedConstraintFactors
            M n hn2 htb hns D).length →
          Set (SATDeciderGaugeSpace M n hn2 htb hns),
          (∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length,
            iterDerivList (alloc i)
              (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D)[i.val] ∈ Submodule.span ℚ (A i)) ∧
          (∀ i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length, A i ⊆ B i) ∧
          (∀ q ∈ finiteProductChoiceSet Finset.univ B,
            (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm
              (mlProj (m * q)) ∈
                mlBlockedSpdpSubspaceInc
                  (cook_levin_compilation M n hn2 htb hns).partition
                  (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
                  (cookLevinFactoredPoly M n))

/-- The monotone allocation-local span/product-choice reduction closes the
standard transformed Leibniz generator pullback payload. -/
theorem transformedLeibnizGeneratorPullback_of_allocationLocalSpansPullbackMonotoneReduction
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedAllocationLocalSpansPullbackMonotoneReduction
      extraK extraL M n hn2 htb hns D) :
    PiPlusBooleanProjectedTransformedLeibnizGeneratorPullback
      extraK extraL M n hn2 htb hns D := by
  intro S m hSlen hmdeg hmvars hadm q hq
  rcases hq with ⟨alloc, halloc, rfl⟩
  rcases hred S m hSlen hmdeg hmvars hadm alloc halloc with
    ⟨A, B, hlocal, hAB, hchoice⟩
  exact allocatedProduct_rawPullback_mem_of_localSpans_mono
    extraK extraL M n hn2 htb hns D m alloc A B hlocal hAB hchoice

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

/-- The non-monotone allocation-local pullback reduction is a special case of the
monotone reduction. -/
theorem allocationLocalSpansPullbackMonotoneReduction_of_allocationLocalSpansPullbackReduction
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedAllocationLocalSpansPullbackReduction
      extraK extraL M n hn2 htb hns D) :
    PiPlusBooleanProjectedAllocationLocalSpansPullbackMonotoneReduction
      extraK extraL M n hn2 htb hns D := by
  intro S m hSlen hmdeg hmvars hadm alloc halloc
  rcases hred S m hSlen hmdeg hmvars hadm alloc halloc with
    ⟨A, hlocal, hchoice⟩
  refine ⟨A, A, hlocal, ?_, hchoice⟩
  intro i x hx
  exact hx

/-- Paper-scale `(1,1)` monotone local-span/product-choice reduction. -/
abbrev PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackMonotoneReductionOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedAllocationLocalSpansPullbackMonotoneReduction 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale `(1,1)` transformed-generator pullback from the monotone local-
span/product-choice reduction. -/
theorem paperScale_transformedLeibnizGeneratorPullbackOneOne_of_allocationLocalSpansPullbackMonotoneReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackMonotoneReductionOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorPullbackOneOne
      M htb hns :=
  transformedLeibnizGeneratorPullback_of_allocationLocalSpansPullbackMonotoneReduction
    1 1 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hred

/-- Paper-scale `(1,1)` local-span/product-choice reduction. -/
abbrev PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedAllocationLocalSpansPullbackReduction 1 1
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale non-monotone allocation-local pullback reduction as a monotone one. -/
theorem paperScale_allocationLocalSpansPullbackMonotoneReductionOneOne_of_allocationLocalSpansPullbackReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackMonotoneReductionOneOne
      M htb hns :=
  allocationLocalSpansPullbackMonotoneReduction_of_allocationLocalSpansPullbackReduction
    1 1 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hred

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

/-- Normalized polynomial span plus the monotone allocation-local span/product-
choice reduction closes the `(1,1)` factored row-span classifier directly.  This
is the classifier-level consumer of the `Aᵢ ⊆ Bᵢ` pullback seam. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_allocationLocalSpansPullbackMonotoneReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackMonotoneReductionOneOne
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_generatorPullback
    M htb hns hpoly
    (paperScale_transformedLeibnizGeneratorPullbackOneOne_of_allocationLocalSpansPullbackMonotoneReduction
      M htb hns hred)

/-- Compact P-side closeout package whose remaining product work is exactly the
monotone allocation-local span/product-choice reduction. -/
structure PaperScalePiPlusBooleanProjectedOneOneAllocationLocalSpansMonotoneCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  polynomial_span : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
    M htb hns
  allocation_local_spans_pullback :
    PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackMonotoneReductionOneOne
      M htb hns

/-- The monotone allocation-local span closeout package yields the `(1,1)`
factored row-span classifier. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_allocationLocalSpansMonotoneCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOneAllocationLocalSpansMonotoneCloseoutInputs
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_allocationLocalSpansPullbackMonotoneReduction
    M htb hns hinputs.polynomial_span hinputs.allocation_local_spans_pullback

/-- Monotone allocation-local span closeout inputs plus explicit Route-B `(1,1)`
and NP-side inputs rule out a SAT decider at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_allocationLocalSpansMonotoneCloseoutInputs_routeB_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOneAllocationLocalSpansMonotoneCloseoutInputs
      M htb hns)
    (hpside : PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_oneOneFinalFrontierData
    M htb hns
    { compiled_p_subspace_inclusion :=
        paperScale_compiledPSubspaceInclusionOneOne_of_rowSpanClassifier
          M htb hns
          (paperScale_factoredRowSpanClassifierOneOne_of_allocationLocalSpansMonotoneCloseoutInputs
            M htb hns hinputs)
      routeB_windowed_p_side_bound := hpside
      np_subspace_inclusion := hnp }

/-- Monotone allocation-local span closeout inputs plus a Route-B `(1,1)`
envelope and NP-side input rule out a SAT decider at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_allocationLocalSpansMonotoneCloseoutInputs_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOneAllocationLocalSpansMonotoneCloseoutInputs
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_allocationLocalSpansMonotoneCloseoutInputs_routeB_npInclusion
    M htb hns hinputs
    (paperScale_routeBSATWindowedIncPSideRankBoundOneOne_of_envelope
      M htb hns henv)
    hnp

/-- Polynomial span plus monotone allocation-local span/product-choice reduction
plus a Route-B `(1,1)` envelope and NP-side input rule out a SAT decider at paper
scale. -/
theorem no_decidesSAT_at_paperScale_of_polynomialSpan_allocationLocalSpansPullbackMonotoneReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackMonotoneReductionOneOne
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_allocationLocalSpansMonotoneCloseoutInputs_routeBEnvelope_npInclusion
    M htb hns
    { polynomial_span := hpoly, allocation_local_spans_pullback := hred }
    henv hnp

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

/-! ## Product-normalization obstruction

The attempted unconditional discharge of
`PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction` runs
into a real quotient/product issue, not a missing wrapper.  Boolean
normalization can collapse a repeated untouched variable (`X * X ↦ X`).  If the
Leibniz derivative window `S` does not contain that variable, the collapsed
representative cannot be justified by reallocating a derivative from `S`; the
normalization-aware product proof must account for this erasure explicitly. -/

/-- Concrete one-variable obstruction for the product-normalization half of the
local-factor product assembly: Boolean normalization collapses a repeated factor.
This is the algebraic reason the unconditional Leibniz/product assembly cannot
be discharged by merely reusing the same allocated derivative product shape. -/
theorem productNormalization_repeatedUntouchedVariable_obstruction :
    zeroProfileBooleanNormalize
        ((X (0 : Fin 1) * X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ)) ≠
      ((X (0 : Fin 1) * X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ)) := by
  rw [zeroProfileBooleanNormalize_X_mul_X]
  intro h
  have hcoeff1 := congrArg
    (fun p : MvPolynomial (Fin 1) ℚ => coeff (Finsupp.single (0 : Fin 1) 1) p) h
  simp [MvPolynomial.X, MvPolynomial.monomial_mul] at hcoeff1

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

/-- Absorption form of `allocatedProduct_mem_span_of_normalizesToDistributedGenerator`:
if every distributed generator row already lands in a target submodule `W`, then
the Boolean-normalized allocated product lands in `W`.  This removes one more
explicit span-elimination step from the local-factor assembly proof. -/
theorem allocatedProduct_mem_of_normalizesToDistributedGenerator_and_distribRows
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (W : Submodule ℚ (SATDeciderGaugeSpace M n hn2 htb hns))
    (hnorm : PiPlusBooleanProjectedAllocatedProductNormalizesToDistributedGenerator
      M n hn2 htb hns D S alloc)
    (hgen : ∀ q ∈ distribDerivProds Finset.univ
          (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length =>
            (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D)[i.val]) S,
        q ∈ W) :
    zeroProfileBooleanNormalize
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈ W := by
  have hspan := allocatedProduct_mem_span_of_normalizesToDistributedGenerator
    M n hn2 htb hns D S alloc hnorm
  exact (Submodule.span_le.mpr hgen) hspan

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

/-- Exact allocated-product normalization implies the quotient-aware local
normalized-choice reduction.  The proof chooses, for each local factor, the
singleton span generated by its Boolean-normalized allocated derivative.  A
pointwise product choice is therefore exactly the product of normalized local
factors; Boolean-normalizing that product agrees with Boolean-normalizing the
raw allocated product, and the exact normalization witness turns it into a
true distributed Leibniz generator. -/
theorem localNormalizedChoiceProductReduction_of_productNormalizationReduction
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedAllocationProductNormalizationReduction
      M n hn2 htb hns D) :
    PiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
      M n hn2 htb hns D := by
  classical
  intro S hSlen hadm alloc halloc
  let L := piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D
  let A : Fin L.length → Set (SATDeciderGaugeSpace M n hn2 htb hns) := fun i =>
    {zeroProfileBooleanNormalize (iterDerivList (alloc i) L[i.val])}
  refine ⟨A, ?_, ?_⟩
  · intro i
    change zeroProfileBooleanNormalize (iterDerivList (alloc i) L[i.val]) ∈
      Submodule.span ℚ (A i)
    apply Submodule.subset_span
    simp [A]
  · intro q hq
    rcases hq with ⟨a, ha, rfl⟩
    rcases hred S hSlen hadm alloc halloc with ⟨alloc', halloc', hnorm_eq⟩
    have haeq : ∀ i : Fin L.length,
        a i = zeroProfileBooleanNormalize (iterDerivList (alloc i) L[i.val]) := by
      intro i
      have hi := ha i (Finset.mem_univ i)
      simpa [A] using hi
    have hprod_eq :
        Finset.univ.prod a =
          Finset.univ.prod (fun i : Fin L.length =>
            zeroProfileBooleanNormalize (iterDerivList (alloc i) L[i.val])) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact haeq i
    rw [hprod_eq]
    have hnorm_factor :=
      zeroProfileBooleanNormalize_allocatedDerivativeProduct_eq_normalizedFactorProduct
        M n hn2 htb hns D alloc
    have htarget :
        zeroProfileBooleanNormalize
            (Finset.univ.prod (fun i : Fin L.length =>
              zeroProfileBooleanNormalize (iterDerivList (alloc i) L[i.val]))) =
          piPlusBooleanProjectedAllocatedDerivativeProduct
            M n hn2 htb hns D alloc' := by
      rw [← hnorm_factor, hnorm_eq]
    rw [htarget]
    apply Submodule.subset_span
    refine ⟨alloc', halloc', ?_⟩
    rfl

/-- Exact allocated-product normalization implies the monotone quotient-aware
local normalized-choice product reduction.  This packages the singleton-span
exact-normalization proof behind the more flexible `Aᵢ ⊆ Bᵢ` interface. -/
theorem localNormalizedChoiceProductMonotoneReduction_of_productNormalizationReduction
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedAllocationProductNormalizationReduction
      M n hn2 htb hns D) :
    PiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
      M n hn2 htb hns D :=
  localNormalizedChoiceProductMonotoneReduction_of_localNormalizedChoiceProductReduction
    M n hn2 htb hns D
    (localNormalizedChoiceProductReduction_of_productNormalizationReduction
      M n hn2 htb hns D hred)

/-- Paper-scale exact product/factor normalization implies the quotient-aware
local normalized-choice product reduction. -/
theorem paperScale_localNormalizedChoiceProductReduction_of_productNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
      M htb hns :=
  localNormalizedChoiceProductReduction_of_productNormalizationReduction
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hred

/-- Paper-scale exact product/factor normalization implies the monotone
quotient-aware local normalized-choice product reduction. -/
theorem paperScale_localNormalizedChoiceProductMonotoneReduction_of_productNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
      M htb hns :=
  localNormalizedChoiceProductMonotoneReduction_of_productNormalizationReduction
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hred

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

/-- The local-factor-to-product-normalization seam also yields the weaker,
quotient-aware local normalized-choice product reduction.  This lets downstream
Route-C closeouts depend on the semantically correct quotient-aware target even
when an exact distributed-generator normalization proof is available. -/
theorem paperScale_localNormalizedChoiceProductReduction_of_localFactorToProductNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred :
      PaperScalePiPlusBooleanProjectedOneOneLocalFactorToProductNormalizationReduction
        M htb hns) :
    PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
      M htb hns :=
  paperScale_localNormalizedChoiceProductReduction_of_productNormalizationReduction
    M htb hns
    (paperScale_productNormalizationReduction_of_localFactorToProductNormalizationReduction
      M htb hns hred)

/-- The local-factor-to-product-normalization seam also yields the monotone,
quotient-aware local normalized-choice product reduction. -/
theorem paperScale_localNormalizedChoiceProductMonotoneReduction_of_localFactorToProductNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred :
      PaperScalePiPlusBooleanProjectedOneOneLocalFactorToProductNormalizationReduction
        M htb hns) :
    PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
      M htb hns :=
  paperScale_localNormalizedChoiceProductMonotoneReduction_of_productNormalizationReduction
    M htb hns
    (paperScale_productNormalizationReduction_of_localFactorToProductNormalizationReduction
      M htb hns hred)

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

/-- Final no-SAT closeout using the quotient-aware product-normalization seam for
the normalized-polynomial side and allocation-local spans for the transformed
Leibniz generator pullback side. -/
theorem no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hprod : PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
      M htb hns)
    (hpull : PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_polynomialSpan_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    M htb hns
    (paperScale_normalizedDerivativePolynomialSpan_of_commutation_and_localNormalizedChoiceProductReduction
      M htb hns hcomm hprod)
    hpull henv hnp

/-- Final no-SAT closeout using the monotone quotient-aware product-normalization
seam for the normalized-polynomial side and allocation-local spans for the
transformed Leibniz generator pullback side. -/
theorem no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductMonotoneReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hprod : PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
      M htb hns)
    (hpull : PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_polynomialSpan_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    M htb hns
    (paperScale_normalizedDerivativePolynomialSpan_of_commutation_and_localNormalizedChoiceProductMonotoneReduction
      M htb hns hcomm hprod)
    hpull henv hnp

/-- Final no-SAT closeout when both monotone quotient-aware product normalization
and allocation-local pullback are provided by local-factor reductions. -/
theorem no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductMonotoneReduction_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hprod : PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductMonotoneReduction
      M htb hns)
    (hlocal :
      PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationLocalSpansPullbackReduction
        M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductMonotoneReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    M htb hns hcomm hprod
    (paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorToAllocationLocalSpansReduction
      M htb hns hlocal)
    henv hnp

/-- Final no-SAT closeout when both quotient-aware product normalization and
allocation-local pullback are provided by local-factor reductions. -/
theorem no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductReduction_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hprod : PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
      M htb hns)
    (hlocal :
      PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationLocalSpansPullbackReduction
        M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    M htb hns hcomm hprod
    (paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorToAllocationLocalSpansReduction
      M htb hns hlocal)
    henv hnp

/-- Local-factor exact product normalization can be weakened to the quotient-aware
choice-normalization route, while a separate local-factor allocation reduction
supplies the transformed-generator pullback side. -/
theorem no_decidesSAT_at_paperScale_of_commutation_localFactorToProductNormalization_asChoice_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
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
  no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductReduction_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
    M htb hns hcomm
    (paperScale_localNormalizedChoiceProductReduction_of_localFactorToProductNormalizationReduction
      M htb hns hprodLocal)
    hlocal henv hnp

/-- Local-factor exact product normalization can also be weakened to the monotone
quotient-aware route, exposing the product-classifier enlargement seam in the
final no-SAT closeout. -/
theorem no_decidesSAT_at_paperScale_of_commutation_localFactorToProductNormalization_asMonotoneChoice_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
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
  no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductMonotoneReduction_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
    M htb hns hcomm
    (paperScale_localNormalizedChoiceProductMonotoneReduction_of_localFactorToProductNormalizationReduction
      M htb hns hprodLocal)
    hlocal henv hnp

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

/-- The unified local-factor product-assembly seam also provides the
quotient-aware local normalized-choice product reduction, by weakening its exact
product-normalization component. -/
theorem paperScale_localNormalizedChoiceProductReduction_of_localFactorProductAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductReduction
      M htb hns :=
  paperScale_localNormalizedChoiceProductReduction_of_productNormalizationReduction
    M htb hns
    (paperScale_productNormalizationReduction_of_localFactorProductAssemblyReduction
      M htb hns hred)

/-- The unified local-factor product-assembly seam yields both quotient-aware
choice normalization and allocation-local pullback. -/
theorem paperScale_localNormalizedChoice_and_allocationPullback_of_localFactorProductAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedLocalNormalizedChoiceProductReduction M htb hns ∧
      PaperScalePiPlusBooleanProjectedAllocationLocalSpansPullbackReductionOneOne
        M htb hns := by
  exact ⟨paperScale_localNormalizedChoiceProductReduction_of_localFactorProductAssemblyReduction
      M htb hns hred,
    paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorProductAssemblyReduction
      M htb hns hred⟩

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

/-- Same unified local-factor product-assembly closeout, but routed through the
quotient-aware choice-normalization surface rather than the stronger exact
product-normalization surface. -/
theorem no_decidesSAT_at_paperScale_of_commutation_localFactorProductAssembly_asChoice_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorProductAssemblyReduction
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
    M htb hns hcomm
    (paperScale_localNormalizedChoiceProductReduction_of_localFactorProductAssemblyReduction
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

#print axioms zeroProfileBooleanNormalize_allocatedDerivativeProduct_eq_normalizedFactorProduct
#print axioms finiteProductChoiceSet_mono
#print axioms span_finiteProductChoiceSet_mono
#print axioms finset_prod_mem_span_finiteProductChoiceSet
#print axioms finset_prod_mem_span_finiteProductChoiceSet_of_mono
#print axioms allocatedDerivativeProduct_mem_span_finiteProductChoiceSet_of_mono
#print axioms zeroProfileBooleanNormalize_mem_span_finiteProductChoiceSet_of_generatorStable
#print axioms zeroProfileBooleanNormalize_finset_prod_mem_span_finiteProductChoiceSet
#print axioms zeroProfileBooleanNormalize_finset_prod_mem_span_finiteProductChoiceSet_of_mono
#print axioms allocatedDerivativeProduct_mem_span_finiteProductChoiceSet
#print axioms zeroProfileBooleanNormalize_allocatedDerivativeProduct_mem_span_finiteProductChoiceSet
#print axioms zeroProfileBooleanNormalize_allocatedDerivativeProduct_mem_span_finiteProductChoiceSet_of_mono
#print axioms zeroProfileBooleanNormalize_allocatedDerivativeProduct_mem_of_localNormalizedSpans_and_choiceNormalizes
#print axioms zeroProfileBooleanNormalize_allocatedDerivativeProduct_mem_of_localNormalizedSpans_mono_and_choiceNormalizes
#print axioms allocationStability_of_localNormalizedSpans_mono_and_choiceNormalizesToDistribSpan
#print axioms allocationStability_of_localNormalizedSpans_and_choiceNormalizesToDistribSpan
#print axioms allocationStability_of_localNormalizedChoiceProductMonotoneReduction
#print axioms localNormalizedChoiceProductMonotoneReduction_of_localNormalizedChoiceProductReduction
#print axioms allocationStability_of_localNormalizedChoiceProductReduction
#print axioms paperScale_allocationStability_of_localNormalizedChoiceProductMonotoneReduction
#print axioms paperScale_allocationStability_of_localNormalizedChoiceProductReduction
#print axioms paperScale_normalizedDerivativeCriterion_of_commutation_and_localNormalizedChoiceProductMonotoneReduction
#print axioms paperScale_normalizedDerivativePolynomialSpan_of_commutation_and_localNormalizedChoiceProductMonotoneReduction
#print axioms paperScale_normalizedDerivativeCriterion_of_commutation_and_localNormalizedChoiceProductReduction
#print axioms paperScale_normalizedDerivativePolynomialSpan_of_commutation_and_localNormalizedChoiceProductReduction
#print axioms normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans
#print axioms normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans_mono
#print axioms paperScale_normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans_oneOne
#print axioms paperScale_normalizedAllocatedProduct_rawPullback_mem_of_localNormalizedSpans_mono_oneOne
#print axioms normalizedAllocatedProduct_rawPullback_of_normalizedAllocationLocalSpansPullbackMonotoneReduction
#print axioms normalizedAllocationLocalSpansPullbackMonotoneReduction_of_normalizedAllocationLocalSpansPullbackReduction
#print axioms normalizedAllocatedProduct_rawPullback_of_normalizedAllocationLocalSpansPullbackReduction
#print axioms paperScale_normalizedAllocatedProduct_rawPullback_of_normalizedAllocationLocalSpansPullbackMonotoneReduction_oneOne
#print axioms paperScale_normalizedAllocationLocalSpansPullbackMonotoneReductionOneOne_of_normalizedAllocationLocalSpansPullbackReduction
#print axioms paperScale_normalizedAllocatedProduct_rawPullback_of_normalizedAllocationLocalSpansPullbackReduction_oneOne
#print axioms allocatedProduct_rawPullback_mem_of_localSpans
#print axioms allocatedProduct_rawPullback_mem_of_localSpans_mono
#print axioms paperScale_allocatedProduct_rawPullback_mem_of_localSpans_oneOne
#print axioms paperScale_allocatedProduct_rawPullback_mem_of_localSpans_mono_oneOne
#print axioms transformedLeibnizGeneratorPullback_of_allocationLocalSpansPullbackMonotoneReduction
#print axioms allocationLocalSpansPullbackMonotoneReduction_of_allocationLocalSpansPullbackReduction
#print axioms transformedLeibnizGeneratorPullback_of_allocationLocalSpansPullbackReduction
#print axioms paperScale_transformedLeibnizGeneratorPullbackOneOne_of_allocationLocalSpansPullbackMonotoneReduction
#print axioms paperScale_allocationLocalSpansPullbackMonotoneReductionOneOne_of_allocationLocalSpansPullbackReduction
#print axioms paperScale_transformedLeibnizGeneratorPullbackOneOne_of_allocationLocalSpansPullbackReduction
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_allocationLocalSpansPullbackMonotoneReduction
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_allocationLocalSpansMonotoneCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_allocationLocalSpansMonotoneCloseoutInputs_routeB_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_allocationLocalSpansMonotoneCloseoutInputs_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_polynomialSpan_allocationLocalSpansPullbackMonotoneReduction_routeBEnvelope_npInclusion
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_allocationLocalSpansPullbackReduction
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_allocationLocalSpansCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_allocationLocalSpansCloseoutInputs_routeB_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_allocationLocalSpansCloseoutInputs_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_polynomialSpan_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
#print axioms paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorToAllocationLocalSpansReduction
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_localFactorToAllocationLocalSpansReduction
#print axioms no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
#print axioms productNormalization_repeatedUntouchedVariable_obstruction
#print axioms allocatedProduct_mem_span_of_normalizesToDistributedGenerator
#print axioms allocatedProduct_mem_of_normalizesToDistributedGenerator_and_distribRows
#print axioms localNormalizedChoiceProductReduction_of_productNormalizationReduction
#print axioms localNormalizedChoiceProductMonotoneReduction_of_productNormalizationReduction
#print axioms paperScale_localNormalizedChoiceProductReduction_of_productNormalizationReduction
#print axioms paperScale_localNormalizedChoiceProductMonotoneReduction_of_productNormalizationReduction
#print axioms paperScale_productNormalizationReduction_of_localFactorToProductNormalizationReduction
#print axioms paperScale_localNormalizedChoiceProductReduction_of_localFactorToProductNormalizationReduction
#print axioms paperScale_localNormalizedChoiceProductMonotoneReduction_of_localFactorToProductNormalizationReduction
#print axioms allocationStability_of_productNormalizationReduction
#print axioms paperScale_allocationStability_of_productNormalizationReduction
#print axioms paperScale_normalizedDerivativeCriterion_of_commutation_and_productNormalizationReduction
#print axioms paperScale_normalizedDerivativePolynomialSpan_of_commutation_and_productNormalizationReduction
#print axioms no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_allocationLocalSpansPullbackReduction_routeB_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductMonotoneReduction_allocationLocalSpansPullbackReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductReduction_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_commutation_localNormalizedChoiceProductMonotoneReduction_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_commutation_localFactorToProductNormalization_asChoice_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_commutation_localFactorToProductNormalization_asMonotoneChoice_localFactorToAllocationLocalSpansReduction_routeBEnvelope_npInclusion
#print axioms paperScale_productNormalizationReduction_of_localFactorProductAssemblyReduction
#print axioms paperScale_allocationLocalSpansPullbackReductionOneOne_of_localFactorProductAssemblyReduction
#print axioms paperScale_localNormalizedChoiceProductReduction_of_localFactorProductAssemblyReduction
#print axioms paperScale_localNormalizedChoice_and_allocationPullback_of_localFactorProductAssemblyReduction
#print axioms no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorProductAssemblyReduction_routeB_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorProductAssemblyReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_oneOnePolynomialSpanUnifiedLocalFactorProductAssemblyRankBoundCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_oneOnePolynomialSpanUnifiedLocalFactorProductAssemblyCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_commutation_localFactorProductAssemblyReduction_routeB_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_commutation_localFactorProductAssemblyReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_commutation_localFactorProductAssembly_asChoice_routeBEnvelope_npInclusion
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
