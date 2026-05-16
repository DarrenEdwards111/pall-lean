import PallLean.Paper93.DeepMath.PathB.RouteBTouchedKRProductComposition
import PallLean.Paper93.DeepMath.PathB.ZeroProfileConcreteNormalFormProgress

/-!
# Route B untouched-background normal-form bridge

The touched split row has already been factored as

`mlProj ((touched local row) * untouchedBackgroundProduct)`.

This file connects the untouched background factor to the existing zero-profile
normal-form machinery.  We do **not** introduce an ambient monomial span or drop
background factors.  Instead, we require the paper §9.3 normal-form row map for
an exact factorization of the untouched background and extract its global basis
at the zero-shift/zero-derivative row.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open SymmetricPowerBound
open scoped BigOperators

/-- The exact list of untouched Cook--Levin constraint factors for a touched
row `S`.  This is just the filtered untouched constraint set, converted to a
list for the existing `Fin L → polynomial` normal-form APIs. -/
noncomputable def untouchedBackgroundFactorList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    List (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) :=
  (((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
    (fun i => i ∉ cookLevinTouchedConstraints M n hn2 htb hns S)).toList.map
      (fun i => cookLevinConstraintFactor M n hn2 htb hns i))

/-- The untouched background list product is definitionally the filtered
untouched background product. -/
theorem untouchedBackgroundFactorList_prod_eq
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    (untouchedBackgroundFactorList M n hn2 htb hns S).prod =
      untouchedBackgroundProduct M n hn2 htb hns S := by
  classical
  unfold untouchedBackgroundFactorList untouchedBackgroundProduct
  rw [Finset.prod_map_toList]

/-- The `Fin L` family extracted from the exact untouched factor list has
product equal to the untouched background product. -/
theorem untouchedBackgroundFactorFamily_prod_eq
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    Finset.univ.prod
        (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
          (untouchedBackgroundFactorList M n hn2 htb hns S).get i) =
      untouchedBackgroundProduct M n hn2 htb hns S := by
  classical
  let factors := untouchedBackgroundFactorList M n hn2 htb hns S
  have hfin :
      factors.prod =
        Finset.univ.prod (fun i : Fin factors.length => factors.get i) := by
    rw [← Fin.prod_univ_getElem]
    simp [List.get_eq_getElem]
  have hlist : factors.prod = untouchedBackgroundProduct M n hn2 htb hns S := by
    simpa [factors] using untouchedBackgroundFactorList_prod_eq M n hn2 htb hns S
  simpa [factors] using hfin.symm.trans hlist

/-- The zero-profile normal-form row map with identity projection spans the
multilinear projection of the raw product row.  This is the `S=[]`, `shift=1`
row of the existing normal-form interface. -/
theorem mlProj_product_mem_normalFormGlobalBasis_of_idRowMap
    {N L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (F : ZeroProfileProjectedNormalFormFamily N κ typeBudget)
    (hmap : ZeroProfileProjectedNormalFormRowMap factors
      (LinearMap.id : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ) F) :
    MultilinearSPDP.mlProj (Finset.univ.prod factors) ∈
      Submodule.span ℚ
        (↑(zeroProfileProjectedNormalFormGlobalBasis F) :
          Set (MvPolynomial (Fin N) ℚ)) := by
  classical
  have hrow := zeroProfileProjectedNormalFormRowMap_row_mem_compressedSpan
    factors
    (LinearMap.id : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    F hmap [] (by simp) (1 : MvPolynomial (Fin N) ℚ) (by simp)
  simpa [zeroProfileProjectedNormalFormCompressedSpan, LinearMap.id_apply] using hrow

/-- If a normal-form factor family has product exactly equal to the untouched
background, its global normal-form basis spans `mlProj` of that background. -/
theorem mlProj_untouchedBackground_mem_normalFormGlobalBasis_of_idRowMap
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {L typeBudget : ℕ}
    (factors : Fin L →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (F : ZeroProfileProjectedNormalFormFamily
      (cookLevinTableau M n hn2 htb hns).numVars (Nat.log 2 n) typeBudget)
    (hmap : ZeroProfileProjectedNormalFormRowMap factors
      (LinearMap.id :
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
          MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) F)
    (hprod : Finset.univ.prod factors =
      untouchedBackgroundProduct M n hn2 htb hns S) :
    MultilinearSPDP.mlProj
        (untouchedBackgroundProduct M n hn2 htb hns S) ∈
      Submodule.span ℚ
        (↑(zeroProfileProjectedNormalFormGlobalBasis F) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  rw [← hprod]
  exact mlProj_product_mem_normalFormGlobalBasis_of_idRowMap factors F hmap

/-- The global basis supplied by a projected normal-form family obeys its
explicit type budget. -/
theorem untouchedBackgroundNormalFormGlobalBasis_card_le
    {N κ typeBudget : ℕ}
    (F : ZeroProfileProjectedNormalFormFamily N κ typeBudget) :
    (zeroProfileProjectedNormalFormGlobalBasis F).card ≤ typeBudget :=
  zeroProfileProjectedNormalFormGlobalBasis_card_le_typeBudget F


/-- List-indexed version of the touched local monomial span theorem.

The final monomial-interface datum carries the row as a list `S`, not as an
arbitrary `Finset` coerced back through `toList`.  This theorem keeps that exact
list visible in the row-window and touched-product definitions. -/
theorem mlProj_touchedMonomialLocalPart_mem_rowWindowMonomialSpan_list
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S.toFinset) :
    MultilinearSPDP.mlProj
      (touchedShiftMonomial T *
        touchedAllocatedProductOnly M n hn2 htb hns S alloc) ∈
      Submodule.span ℚ
        (↑(MlProjFar.mlMonomialBasis
          (cookLevinRowLocalWindow M n hn2 htb hns S)) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  classical
  apply MlProjFar.mlProj_in_span_of_vars_subset
  · intro α hα
    exact WithinProfileBound.isMultilinear_of_mem_mlProj_support
      (touchedShiftMonomial T *
        touchedAllocatedProductOnly M n hn2 htb hns S alloc) α hα
  · intro v hv
    have hvars :
        (touchedShiftMonomial T *
          touchedAllocatedProductOnly M n hn2 htb hns S alloc).vars ⊆
          cookLevinRowLocalWindow M n hn2 htb hns S := by
      intro w hw
      have hmul := MvPolynomial.vars_mul
        (touchedShiftMonomial T)
        (touchedAllocatedProductOnly M n hn2 htb hns S alloc) hw
      simp only [Finset.mem_union] at hmul
      rcases hmul with hleft | hright
      · unfold touchedShiftMonomial at hleft
        have hsubset := MvPolynomial.vars_prod
          (s := T) (fun v => MvPolynomial.X v :
            Fin (cookLevinTableau M n hn2 htb hns).numVars →
              MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
        have hprod := hsubset hleft
        rw [Finset.mem_biUnion] at hprod
        rcases hprod with ⟨x, hxT, hwx⟩
        simp only [MvPolynomial.vars_X, Finset.mem_singleton] at hwx
        subst w
        unfold cookLevinRowLocalWindow
        rw [Finset.mem_biUnion]
        exact ⟨x, hT hxT, mem_cookLevinVarLocalWindow_self _ x⟩
      · exact touchedAllocatedProductOnly_vars_subset_rowLocalWindow
          M n hn2 htb hns S alloc hright
    exact hvars (WithinProfileBound.vars_mlProj_subset
      (touchedShiftMonomial T *
        touchedAllocatedProductOnly M n hn2 htb hns S alloc) hv)

/-- List-indexed projected-background span bridge.

This is the exact shape needed by `TouchedMonomialInterfaceDatum`: the split row,
row window, touched constraints, and untouched background all use the original
list `S`, avoiding any `Finset.toList` normalization shortcut. -/
theorem touchedMonomialSplitRow_mem_rowWindowProductBasis_of_projectedBackgroundSpan_list
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S.toFinset)
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S → alloc i = [])
    (B : Finset (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))
    (hB : MultilinearSPDP.mlProj
        (untouchedBackgroundProduct M n hn2 htb hns S) ∈
      Submodule.span ℚ (↑B : Set (MvPolynomial
        (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))) :
    touchedMonomialSplitRow M n hn2 htb hns S T alloc ∈
      Submodule.span ℚ
        (↑(mlProjProductBasis
          (MlProjFar.mlMonomialBasis
            (cookLevinRowLocalWindow M n hn2 htb hns S)) B) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  rw [touchedMonomialSplitRow_eq_mlProj_local_mul_background
    M n hn2 htb hns S T alloc hout]
  exact mlProj_mul_mem_span_productBasis_of_bothProjected
    (MlProjFar.mlMonomialBasis
      (cookLevinRowLocalWindow M n hn2 htb hns S)) B
    (mlProj_touchedMonomialLocalPart_mem_rowWindowMonomialSpan_list
      M n hn2 htb hns S T alloc hT)
    hB

/-- Main bridge: an identity-projected zero-profile normal-form row map for an
exact untouched-background factorization supplies the background span consumed
by the touched/background Khatri--Rao composition theorem. -/
theorem touchedMonomialSplitRow_mem_rowWindowProductBasis_of_backgroundNormalForm
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S)
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S.toList → alloc i = [])
    {L typeBudget : ℕ}
    (factors : Fin L →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (F : ZeroProfileProjectedNormalFormFamily
      (cookLevinTableau M n hn2 htb hns).numVars (Nat.log 2 n) typeBudget)
    (hmap : ZeroProfileProjectedNormalFormRowMap factors
      (LinearMap.id :
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
          MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) F)
    (hprod : Finset.univ.prod factors =
      untouchedBackgroundProduct M n hn2 htb hns S.toList) :
    touchedMonomialSplitRow M n hn2 htb hns S.toList T alloc ∈
      Submodule.span ℚ
        (↑(mlProjProductBasis
          (MlProjFar.mlMonomialBasis
            (cookLevinRowLocalWindow M n hn2 htb hns S.toList))
          (zeroProfileProjectedNormalFormGlobalBasis F)) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  exact touchedMonomialSplitRow_mem_rowWindowProductBasis_of_projectedBackgroundSpan
    M n hn2 htb hns S T alloc hT hout
    (zeroProfileProjectedNormalFormGlobalBasis F)
    (mlProj_untouchedBackground_mem_normalFormGlobalBasis_of_idRowMap
      M n hn2 htb hns S.toList factors F hmap hprod)

/-- Same as `touchedMonomialSplitRow_mem_rowWindowProductBasis_of_backgroundNormalForm`,
but with the untouched factor family fixed to the concrete filtered
Cook--Levin factor list.  The only remaining input is the actual §9.3
normal-form row map for that concrete family. -/
theorem touchedMonomialSplitRow_mem_rowWindowProductBasis_of_concreteBackgroundNormalForm
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S)
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S.toList → alloc i = [])
    {typeBudget : ℕ}
    (F : ZeroProfileProjectedNormalFormFamily
      (cookLevinTableau M n hn2 htb hns).numVars (Nat.log 2 n) typeBudget)
    (hmap : ZeroProfileProjectedNormalFormRowMap
      (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length =>
        (untouchedBackgroundFactorList M n hn2 htb hns S.toList).get i)
      (LinearMap.id :
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
          MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) F) :
    touchedMonomialSplitRow M n hn2 htb hns S.toList T alloc ∈
      Submodule.span ℚ
        (↑(mlProjProductBasis
          (MlProjFar.mlMonomialBasis
            (cookLevinRowLocalWindow M n hn2 htb hns S.toList))
          (zeroProfileProjectedNormalFormGlobalBasis F)) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  exact touchedMonomialSplitRow_mem_rowWindowProductBasis_of_backgroundNormalForm
    M n hn2 htb hns S T alloc hT hout
    (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length =>
      (untouchedBackgroundFactorList M n hn2 htb hns S.toList).get i)
    F hmap
    (untouchedBackgroundFactorFamily_prod_eq M n hn2 htb hns S.toList)


/-! ## Concrete §9.3 row classifier for the filtered untouched background

The preceding theorem consumes an abstract projected normal-form row map for
the exact filtered untouched factor list.  The next definitions pin that row map
to the concrete §9.3 symmetric-power/profile classifier surface: a finite
normal-form alphabet with concrete local charts, together with the proof that
every shifted zero-profile row of the filtered background lands in its selected
chart.  This is deliberately not weakened to an ambient span; it keeps the
exact factor family

`fun i => (untouchedBackgroundFactorList ... S.toList).get i`

all the way through the finite classifier and then forgets it only via the
already-proved `ZeroProfileConcreteNormalFormRowMap` →
`ZeroProfileProjectedNormalFormRowMap` bridge.
-/

/-- Concrete §9.3 normal-form classifier data for the exact untouched
background factor list associated to a touched row `S`.

This is the paper-faithful row map/classifier obligation for the filtered
background: finite concrete normal forms, concrete local profile charts, and a
row classifier for all zero-profile shifted rows of that exact factor family at
identity projection. -/
structure UntouchedBackgroundConcreteNormalFormClassifier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  data : ZeroProfileConcreteNormalFormData
    (cookLevinTableau M n hn2 htb hns).numVars (Nat.log 2 n) typeBudget
  rowMap : ZeroProfileConcreteNormalFormRowMap
    (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length =>
      (untouchedBackgroundFactorList M n hn2 htb hns S.toList).get i)
    (LinearMap.id :
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    data


/-- The exact constraint-index list underlying `untouchedBackgroundFactorList`.
Keeping the indices (not just the polynomials) lets the background classifier
use the real Cook--Levin three-segment type map on the filtered family. -/
noncomputable def untouchedBackgroundConstraintIdxList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    List (cookLevinConstraintIdx M n hn2 htb hns) :=
  ((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
    (fun i => i ∉ cookLevinTouchedConstraints M n hn2 htb hns S)).toList

/-- The indexed untouched-background factor family is definitionally the same
filtered Cook--Levin factor list as `untouchedBackgroundFactorList`, but it
retains a path back to the original constraint index. -/
theorem untouchedBackgroundConstraintIdxList_map_factor_eq
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    (untouchedBackgroundConstraintIdxList M n hn2 htb hns S).map
        (fun i => cookLevinConstraintFactor M n hn2 htb hns i) =
      untouchedBackgroundFactorList M n hn2 htb hns S := by
  rfl

/-- The real Cook--Levin type map restricted to the exact filtered untouched
background list. -/
noncomputable def untouchedBackgroundConstraintTypeFamily
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length →
      SymmetricPowerBound.ConstraintType :=
  fun i =>
    cookLevinConstraintIdxType M n hn2 htb hns
      ((untouchedBackgroundConstraintIdxList M n hn2 htb hns S.toList).get
        (by
          simpa [untouchedBackgroundFactorList,
            untouchedBackgroundConstraintIdxList] using i))



/-- The real Cook--Levin type map restricted to the exact filtered untouched
background list, preserving the original touched-row list `S`. -/
noncomputable def untouchedBackgroundConstraintTypeFamilyForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length →
      SymmetricPowerBound.ConstraintType :=
  fun i =>
    cookLevinConstraintIdxType M n hn2 htb hns
      ((untouchedBackgroundConstraintIdxList M n hn2 htb hns S).get
        (by
          simpa [untouchedBackgroundFactorList,
            untouchedBackgroundConstraintIdxList] using i))

/-- List-indexed exact zero-profile per-generator row containment for the
filtered untouched background family.

This is the final-assembly-facing version of
`UntouchedBackgroundZeroProfilePerTypeSpanning_concreteW`: the exact filtered
factor family and its restricted Cook--Levin type map are both indexed by the
original row list `S`, not by `S.toFinset.toList`. -/
def UntouchedBackgroundZeroProfilePerTypeSpanning_concreteW_forList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) : Prop :=
  let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
    fun i => (untouchedBackgroundFactorList M n hn2 htb hns S).get i
  let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
  ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (_hR : R.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (_hshift : shift.vars ⊆ R.toFinset)
    (g : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
    g ∈ WithinProfileBound.boundedProfileClassifiedSet factors ctype R zeroProfileHistogram →
      MultilinearSPDP.mlProj (shift * g) ∈
        profileSubspace zeroProfileHistogram
          (zeroProfileConcreteLocalChart_concreteW
            (n := (cookLevinTableau M n hn2 htb hns).numVars)
            hn4 zeroProfileHistogram).W

/-- List-indexed shifted-base-product form of the exact filtered untouched
background zero-profile obligation. -/
def UntouchedBackgroundZeroProfileShiftRows_concreteW_forList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) : Prop :=
  let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
    fun i => (untouchedBackgroundFactorList M n hn2 htb hns S).get i
  ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (_hR : R.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (_hshift : shift.vars ⊆ R.toFinset),
      MultilinearSPDP.mlProj (shift * Finset.univ.prod factors) ∈
        profileSubspace zeroProfileHistogram
          (zeroProfileConcreteLocalChart_concreteW
            (n := (cookLevinTableau M n hn2 htb hns).numVars)
            hn4 zeroProfileHistogram).W

/-- List-indexed zero-profile per-generator containment implies list-indexed
shifted-base-product control. -/
theorem untouchedBackgroundZeroProfileShiftRows_of_perTypeSpanning_concreteW_forList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hspan : UntouchedBackgroundZeroProfilePerTypeSpanning_concreteW_forList
      M n hn2 htb hns hn4 S) :
    UntouchedBackgroundZeroProfileShiftRows_concreteW_forList
      M n hn2 htb hns hn4 S := by
  classical
  intro R hR shift hshift
  let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
    fun i => (untouchedBackgroundFactorList M n hn2 htb hns S).get i
  let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
  have hg : Finset.univ.prod factors ∈
      WithinProfileBound.boundedProfileClassifiedSet factors ctype R zeroProfileHistogram := by
    rw [boundedProfileClassifiedSet_zeroProfile_eq_singleton factors ctype R]
    simp
  exact hspan R hR shift hshift (Finset.univ.prod factors) hg

/-- List-indexed shifted-base-product control implies list-indexed per-generator
zero-profile containment. -/
theorem untouchedBackgroundZeroProfilePerTypeSpanning_of_shiftRows_concreteW_forList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hshiftRows : UntouchedBackgroundZeroProfileShiftRows_concreteW_forList
      M n hn2 htb hns hn4 S) :
    UntouchedBackgroundZeroProfilePerTypeSpanning_concreteW_forList
      M n hn2 htb hns hn4 S := by
  classical
  intro R hR shift hshift g hg
  let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
    fun i => (untouchedBackgroundFactorList M n hn2 htb hns S).get i
  let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
  have hg_single : g ∈ ({Finset.univ.prod factors} : Set
      (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
    rwa [boundedProfileClassifiedSet_zeroProfile_eq_singleton factors ctype R] at hg
  have hg_eq : g = Finset.univ.prod factors := by
    simpa using hg_single
  rw [hg_eq]
  exact hshiftRows R hR shift hshift


/-- List-indexed zero-profile per-generator containment gives the post-span
containment consumed by the list-indexed concrete classifier constructor. -/
theorem untouchedBackgroundZeroProfilePostSpan_le_of_perTypeSpanning_concreteW_forList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hspan : UntouchedBackgroundZeroProfilePerTypeSpanning_concreteW_forList
      M n hn2 htb hns hn4 S) :
    WithinProfileBound.allBoundedProfilePostSpan
        (cookLevinTableau M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
          (untouchedBackgroundFactorList M n hn2 htb hns S).get i)
        (untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S)
        zeroProfileHistogram
      ≤ profileSubspace zeroProfileHistogram
          (zeroProfileConcreteLocalChart_concreteW
            (n := (cookLevinTableau M n hn2 htb hns).numVars)
            hn4 zeroProfileHistogram).W := by
  classical
  let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
    fun i => (untouchedBackgroundFactorList M n hn2 htb hns S).get i
  let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
  refine Submodule.span_le.mpr ?_
  intro q hq
  simp only [Set.mem_iUnion, Set.mem_image] at hq
  obtain ⟨R, hR, shift, hshift, g, hg, rfl⟩ := hq
  exact hspan R hR shift hshift g hg

/-- Exact zero-profile per-generator row containment for the filtered untouched
background family.

This is the local/profile normal-form content needed for the untouched side:
for the exact filtered factor family, every zero-profile shifted product row is
already in the concrete zero-profile chart.  It is deliberately stated on the
filtered family itself, with its real restricted Cook--Levin type map; it does
not appeal to a full-product span or an ambient monomial space. -/
def UntouchedBackgroundZeroProfilePerTypeSpanning_concreteW
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars)) : Prop :=
  let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
    fun i => (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).get i
  let ctype := untouchedBackgroundConstraintTypeFamily M n hn2 htb hns Srow
  ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (_hR : R.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (_hshift : shift.vars ⊆ R.toFinset)
    (g : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
    g ∈ WithinProfileBound.boundedProfileClassifiedSet factors ctype R zeroProfileHistogram →
      MultilinearSPDP.mlProj (shift * g) ∈
        profileSubspace zeroProfileHistogram
          (zeroProfileConcreteLocalChart_concreteW
            (n := (cookLevinTableau M n hn2 htb hns).numVars)
            hn4 zeroProfileHistogram).W


/-- Shifted-base-product form of the exact filtered untouched-background
zero-profile normal-form obligation.

By the zero-profile classification theorem, no factor receives derivatives;
the whole untouched side is the shifted product of the exact filtered
background factors.  This is the concrete §9.3 local-monoid/profile target for
the untouched background. -/
def UntouchedBackgroundZeroProfileShiftRows_concreteW
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars)) : Prop :=
  let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
    fun i => (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).get i
  ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (_hR : R.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (_hshift : shift.vars ⊆ R.toFinset),
      MultilinearSPDP.mlProj (shift * Finset.univ.prod factors) ∈
        profileSubspace zeroProfileHistogram
          (zeroProfileConcreteLocalChart_concreteW
            (n := (cookLevinTableau M n hn2 htb hns).numVars)
            hn4 zeroProfileHistogram).W


/-- Exact zero-profile per-generator containment implies shifted-base-product
control for the filtered untouched background.

This is the converse of the zero-profile singleton reduction below: the all-zero
profile classified set contains exactly the untouched base product, so the
per-type/profile theorem applies to that product without changing the filtered
factor family. -/
theorem untouchedBackgroundZeroProfileShiftRows_of_perTypeSpanning_concreteW
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hspan : UntouchedBackgroundZeroProfilePerTypeSpanning_concreteW
      M n hn2 htb hns hn4 Srow) :
    UntouchedBackgroundZeroProfileShiftRows_concreteW
      M n hn2 htb hns hn4 Srow := by
  classical
  intro R hR shift hshift
  let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
    fun i => (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).get i
  let ctype := untouchedBackgroundConstraintTypeFamily M n hn2 htb hns Srow
  have hg : Finset.univ.prod factors ∈
      WithinProfileBound.boundedProfileClassifiedSet factors ctype R zeroProfileHistogram := by
    rw [boundedProfileClassifiedSet_zeroProfile_eq_singleton factors ctype R]
    simp
  exact hspan R hR shift hshift (Finset.univ.prod factors) hg

/-- Shifted-base-product control implies the per-generator zero-profile
containment for the exact filtered untouched factor family. -/
theorem untouchedBackgroundZeroProfilePerTypeSpanning_of_shiftRows_concreteW
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hshiftRows : UntouchedBackgroundZeroProfileShiftRows_concreteW
      M n hn2 htb hns hn4 Srow) :
    UntouchedBackgroundZeroProfilePerTypeSpanning_concreteW
      M n hn2 htb hns hn4 Srow := by
  classical
  intro R hR shift hshift g hg
  let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
    fun i => (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).get i
  let ctype := untouchedBackgroundConstraintTypeFamily M n hn2 htb hns Srow
  have hg_single : g ∈ ({Finset.univ.prod factors} : Set
      (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
    rwa [boundedProfileClassifiedSet_zeroProfile_eq_singleton factors ctype R] at hg
  have hg_eq : g = Finset.univ.prod factors := by
    simpa using hg_single
  rw [hg_eq]
  exact hshiftRows R hR shift hshift

/-- The exact zero-profile per-generator containment for the filtered untouched
background family gives the post-span containment consumed by the concrete
classifier constructor.

This is the same `Submodule.span_le` composition as the global Route C→A
bridge, but specialized to the exact filtered background list and the all-zero
profile. -/
theorem untouchedBackgroundZeroProfilePostSpan_le_of_perTypeSpanning_concreteW
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hspan : UntouchedBackgroundZeroProfilePerTypeSpanning_concreteW
      M n hn2 htb hns hn4 Srow) :
    WithinProfileBound.allBoundedProfilePostSpan
        (cookLevinTableau M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
          (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).get i)
        (untouchedBackgroundConstraintTypeFamily M n hn2 htb hns Srow)
        zeroProfileHistogram
      ≤ profileSubspace zeroProfileHistogram
          (zeroProfileConcreteLocalChart_concreteW
            (n := (cookLevinTableau M n hn2 htb hns).numVars)
            hn4 zeroProfileHistogram).W := by
  classical
  let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
    fun i => (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).get i
  let ctype := untouchedBackgroundConstraintTypeFamily M n hn2 htb hns Srow
  refine Submodule.span_le.mpr ?_
  intro q hq
  simp only [Set.mem_iUnion, Set.mem_image] at hq
  obtain ⟨R, hR, shift, hshift, g, hg, rfl⟩ := hq
  exact hspan R hR shift hshift g hg

/-- A zero-profile post-span containment at the concrete `concreteW` chart
constructs the actual concrete row classifier for the exact filtered untouched
background family.

This is the paper §9.3 row-map construction specialized to the all-zero
profile: rows are first shown to lie in the zero-profile post-span of the exact
factor/type family, then the supplied normal-form/profile containment places
that post-span inside the concrete symmetric-power chart. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifier_of_zeroProfilePostSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hpost :
      WithinProfileBound.allBoundedProfilePostSpan
          (cookLevinTableau M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length =>
            (untouchedBackgroundFactorList M n hn2 htb hns S.toList).get i)
          (untouchedBackgroundConstraintTypeFamily M n hn2 htb hns S)
          zeroProfileHistogram
        ≤ profileSubspace zeroProfileHistogram
            (zeroProfileConcreteLocalChart_concreteW
              (n := (cookLevinTableau M n hn2 htb hns).numVars)
              hn4 zeroProfileHistogram).W) :
    UntouchedBackgroundConcreteNormalFormClassifier M n hn2 htb hns S
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) where
  data := zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
    (n := (cookLevinTableau M n hn2 htb hns).numVars)
    (κ := Nat.log 2 n) hn4
  rowMap := by
    classical
    refine
      { rowNormalForm := fun _ _ _ _ => PUnit.unit
        projected_row_mem_profileSubspace := ?_ }
    intro R hR shift hshift
    let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length →
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
      fun i => (untouchedBackgroundFactorList M n hn2 htb hns S.toList).get i
    let ctype := untouchedBackgroundConstraintTypeFamily M n hn2 htb hns S
    have hrowSet :
        MultilinearSPDP.mlProj (shift * Finset.univ.prod factors) ∈
          zeroProfileShiftImageSet (Nat.log 2 n) factors := by
      simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
        Set.mem_singleton_iff]
      exact ⟨R, hR, shift, hshift, rfl⟩
    have hrowPost :
        MultilinearSPDP.mlProj (shift * Finset.univ.prod factors) ∈
          WithinProfileBound.allBoundedProfilePostSpan
            (cookLevinTableau M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            factors ctype zeroProfileHistogram := by
      rw [allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan
        (cookLevinTableau M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) factors ctype]
      exact Submodule.subset_span hrowSet
    have hmem :
        MultilinearSPDP.mlProj (shift * Finset.univ.prod factors) ∈
          profileSubspace zeroProfileHistogram
            (zeroProfileConcreteLocalChart_concreteW
              (n := (cookLevinTableau M n hn2 htb hns).numVars)
              hn4 zeroProfileHistogram).W := by
      exact hpost hrowPost
    simpa [LinearMap.id_apply, factors, ctype,
      zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW,
      zeroProfileConcreteNormalFormData_singletonZeroProfile] using hmem



/-- The paper §9.3 zero-profile per-generator normal form for the exact
filtered untouched family constructs the concrete untouched-background
classifier directly. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifier_of_zeroProfilePerTypeSpanning
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hspan : UntouchedBackgroundZeroProfilePerTypeSpanning_concreteW
      M n hn2 htb hns hn4 S) :
    UntouchedBackgroundConcreteNormalFormClassifier M n hn2 htb hns S
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  untouchedBackgroundConcreteNormalFormClassifier_of_zeroProfilePostSpan
    M n hn2 htb hns hn4 S
    (untouchedBackgroundZeroProfilePostSpan_le_of_perTypeSpanning_concreteW
      M n hn2 htb hns hn4 S hspan)


/-- Concrete zero-profile normal-form data induced by a finite local monoid for
the exact filtered untouched background.

Every monoid normal form is interpreted at the all-zero derivative profile, and
its concrete chart is the same `concreteW` zero-profile chart.  The only budget
requirement is the actual finite monoid cardinality bound. -/
noncomputable def untouchedBackgroundZeroProfileConcreteDataOfLocalMonoid
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (A : ZeroProfileFiniteLocalMonoid) (typeBudget : ℕ)
    (hbudget : Fintype.card A.localMonoid ≤ typeBudget) :
    ZeroProfileConcreteNormalFormData
      (cookLevinTableau M n hn2 htb hns).numVars (Nat.log 2 n) typeBudget where
  normalForm := A.localMonoid
  normalFormFintype := inferInstance
  profile := fun _ => zeroProfileHistogram
  profile_admissible := fun _ => zeroProfileHistogram_admissible (Nat.log 2 n)
  chart := fun _ =>
    zeroProfileConcreteLocalChart_concreteW
      (n := (cookLevinTableau M n hn2 htb hns).numVars)
      hn4 zeroProfileHistogram
  totalProfileBudget_le := by
    classical
    simpa [zeroProfileSymmetricProfileDim, zeroProfileHistogram]
      using hbudget


/-- Finite local-monoid action data for the exact filtered untouched background.

This is one level more concrete than an arbitrary row map.  Each exact
untouched Cook--Levin factor is assigned a local-monoid element, every allowed
shift row is assigned its shift element, and the row normal form is their
monoid product.  The only remaining mathematical field is the paper §9.3
semantic theorem saying that the shifted product row lies in the concrete chart
for that product normal form. -/
structure UntouchedBackgroundZeroProfileLocalMonoidActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  monoid : ZeroProfileFiniteLocalMonoid
  monoid_card_le_typeBudget : Fintype.card monoid.localMonoid ≤ typeBudget
  factorElement :
    Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length →
      monoid.localMonoid
  shiftElement :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      R.length ≤ Nat.log 2 n →
      ∀ shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
        shift.vars ⊆ R.toFinset → monoid.localMonoid
  row_mem_productNormalForm :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let rowNF := shiftElement R hR shift hshift *
        (List.ofFn factorElement).prod
      MultilinearSPDP.mlProj (shift *
          Finset.univ.prod
            (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
              (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).get i)) ∈
        profileSubspace zeroProfileHistogram
          ((untouchedBackgroundZeroProfileConcreteDataOfLocalMonoid
            M n hn2 htb hns hn4 monoid typeBudget monoid_card_le_typeBudget).chart
              rowNF).W

/-- A finite-local-monoid concrete row classifier for the exact filtered
untouched-background shifted rows.

This is the literal §9.3 source of the shifted-row theorem: rows are classified
by elements of a finite local monoid (with shortlex normal forms available from
`ZeroProfileFiniteLocalMonoid.normalFormWord`), and the row-map proof places
each shifted product row in the concrete zero-profile chart selected by that
monoid normal form. -/
structure UntouchedBackgroundZeroProfileLocalMonoidConcreteClassifier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  monoid : ZeroProfileFiniteLocalMonoid
  monoid_card_le_typeBudget : Fintype.card monoid.localMonoid ≤ typeBudget
  rowMap : ZeroProfileConcreteNormalFormRowMap
    (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
      (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).get i)
    (LinearMap.id :
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (untouchedBackgroundZeroProfileConcreteDataOfLocalMonoid
      M n hn2 htb hns hn4 monoid typeBudget monoid_card_le_typeBudget)



/-- Generator-word data for the exact filtered untouched local-monoid action.

This is the next paper-faithful refinement of the action seam: factor and shift
normal forms are not arbitrary monoid elements, but products of words over the
finite local generator list from §9.3.  Coefficients and gadget semantics remain
in the row-membership theorem; the finite alphabet only records generator-word
normal forms. -/
structure UntouchedBackgroundZeroProfileLocalGeneratorActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  monoid : ZeroProfileFiniteLocalMonoid
  monoid_card_le_typeBudget : Fintype.card monoid.localMonoid ≤ typeBudget
  factorWord :
    Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length →
      List monoid.localMonoid
  factorWord_letters :
    ∀ i, ∀ a ∈ factorWord i, a ∈ monoid.generators
  shiftWord :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      R.length ≤ Nat.log 2 n →
      ∀ shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
        shift.vars ⊆ R.toFinset → List monoid.localMonoid
  shiftWord_letters :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      ∀ a ∈ shiftWord R hR shift hshift, a ∈ monoid.generators
  row_mem_generatorWordNormalForm :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let rowNF := (shiftWord R hR shift hshift).prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
            (factorWord i).prod)).prod
      MultilinearSPDP.mlProj (shift *
          Finset.univ.prod
            (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
              (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).get i)) ∈
        profileSubspace zeroProfileHistogram
          ((untouchedBackgroundZeroProfileConcreteDataOfLocalMonoid
            M n hn2 htb hns hn4 monoid typeBudget monoid_card_le_typeBudget).chart
              rowNF).W


/-- Shortlex-normalized generator-word data for the exact filtered untouched
local-monoid action.

This is the paper §9.3 `NFOfWord` form: raw factor/shift traces are witnessed
as words over the finite generator list, then normalized by shortlex before
being used as the row normal form.  The semantic row theorem is stated at the
normalized products, so no arbitrary/noncanonical words leak into the final
classifier. -/
structure UntouchedBackgroundZeroProfileLocalNFGeneratorActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  monoid : ZeroProfileFiniteLocalMonoid
  monoid_card_le_typeBudget : Fintype.card monoid.localMonoid ≤ typeBudget
  rawFactorWord :
    Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length →
      List monoid.localMonoid
  rawFactorWord_letters :
    ∀ i, ∀ a ∈ rawFactorWord i, a ∈ monoid.generators
  rawShiftWord :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      R.length ≤ Nat.log 2 n →
      ∀ shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
        shift.vars ⊆ R.toFinset → List monoid.localMonoid
  rawShiftWord_letters :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      ∀ a ∈ rawShiftWord R hR shift hshift, a ∈ monoid.generators
  row_mem_NFOfWordNormalForm :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let rowNF := (PallLean.Paper93.NFOfWord monoid.generators
          (rawShiftWord R hR shift hshift)).prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
            (PallLean.Paper93.NFOfWord monoid.generators
              (rawFactorWord i)).prod)).prod
      MultilinearSPDP.mlProj (shift *
          Finset.univ.prod
            (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
              (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).get i)) ∈
        profileSubspace zeroProfileHistogram
          ((untouchedBackgroundZeroProfileConcreteDataOfLocalMonoid
            M n hn2 htb hns hn4 monoid typeBudget monoid_card_le_typeBudget).chart
              rowNF).W


/-- Raw generator-trace action data for the exact filtered untouched background.

This is the form closest to the Cook--Levin gadget calculation: the row theorem
is proved for the unnormalized product of witnessed generator traces.  The
bridge below transports it to the shortlex `NFOfWord` normal forms using the
representation theorem for `NFOfWord`, keeping the semantic proof separate from
normal-form canonicalization. -/
structure UntouchedBackgroundZeroProfileRawGeneratorTraceActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  monoid : ZeroProfileFiniteLocalMonoid
  monoid_card_le_typeBudget : Fintype.card monoid.localMonoid ≤ typeBudget
  rawFactorWord :
    Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length →
      List monoid.localMonoid
  rawFactorWord_letters :
    ∀ i, ∀ a ∈ rawFactorWord i, a ∈ monoid.generators
  rawShiftWord :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      R.length ≤ Nat.log 2 n →
      ∀ shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
        shift.vars ⊆ R.toFinset → List monoid.localMonoid
  rawShiftWord_letters :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      ∀ a ∈ rawShiftWord R hR shift hshift, a ∈ monoid.generators
  row_mem_rawWordNormalForm :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let rowNF := (rawShiftWord R hR shift hshift).prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
            (rawFactorWord i).prod)).prod
      MultilinearSPDP.mlProj (shift *
          Finset.univ.prod
            (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
              (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).get i)) ∈
        profileSubspace zeroProfileHistogram
          ((untouchedBackgroundZeroProfileConcreteDataOfLocalMonoid
            M n hn2 htb hns hn4 monoid typeBudget monoid_card_le_typeBudget).chart
              rowNF).W


/-- Shifted-row control plus explicit generator traces gives raw generator-trace
action data.

This is the faithful bridge from the concrete shifted-base-product theorem to
raw §9.3 trace data: callers still provide the actual finite local monoid and
the raw factor/shift generator words, with letter-membership proofs.  The row
semantics are supplied by the exact filtered shifted-row theorem, and the chart
is the all-zero concrete chart attached to every local-monoid normal form. -/
noncomputable def untouchedBackgroundRawTraceActionData_of_shiftRows_and_words
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (A : ZeroProfileFiniteLocalMonoid)
    (hbudget : Fintype.card A.localMonoid ≤ typeBudget)
    (rawFactorWord :
      Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length →
        List A.localMonoid)
    (rawFactorWord_letters :
      ∀ i, ∀ a ∈ rawFactorWord i, a ∈ A.generators)
    (rawShiftWord :
      ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
        R.length ≤ Nat.log 2 n →
        ∀ shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
          shift.vars ⊆ R.toFinset → List A.localMonoid)
    (rawShiftWord_letters :
      ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
        (hR : R.length ≤ Nat.log 2 n)
        (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
        (hshift : shift.vars ⊆ R.toFinset),
        ∀ a ∈ rawShiftWord R hR shift hshift, a ∈ A.generators)
    (hshiftRows : UntouchedBackgroundZeroProfileShiftRows_concreteW
      M n hn2 htb hns hn4 Srow) :
    UntouchedBackgroundZeroProfileRawGeneratorTraceActionData
      M n hn2 htb hns hn4 Srow typeBudget where
  monoid := A
  monoid_card_le_typeBudget := hbudget
  rawFactorWord := rawFactorWord
  rawFactorWord_letters := rawFactorWord_letters
  rawShiftWord := rawShiftWord
  rawShiftWord_letters := rawShiftWord_letters
  row_mem_rawWordNormalForm := by
    intro R hR shift hshift
    simpa [untouchedBackgroundZeroProfileConcreteDataOfLocalMonoid]
      using hshiftRows R hR shift hshift

/-- Raw witnessed generator traces transport to shortlex-normalized
`NFOfWord` traces.  This is only normal-form rewriting: the Cook--Levin semantic
row theorem remains the `row_mem_rawWordNormalForm` field. -/
noncomputable def untouchedBackgroundLocalNFGeneratorActionData_of_rawTraceActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (T : UntouchedBackgroundZeroProfileRawGeneratorTraceActionData
      M n hn2 htb hns hn4 Srow typeBudget) :
    UntouchedBackgroundZeroProfileLocalNFGeneratorActionData
      M n hn2 htb hns hn4 Srow typeBudget where
  monoid := T.monoid
  monoid_card_le_typeBudget := T.monoid_card_le_typeBudget
  rawFactorWord := T.rawFactorWord
  rawFactorWord_letters := T.rawFactorWord_letters
  rawShiftWord := T.rawShiftWord
  rawShiftWord_letters := T.rawShiftWord_letters
  row_mem_NFOfWordNormalForm := by
    intro R hR shift hshift
    have hshiftProd :
        (PallLean.Paper93.NFOfWord T.monoid.generators
          (T.rawShiftWord R hR shift hshift)).prod =
            (T.rawShiftWord R hR shift hshift).prod :=
      PallLean.Paper93.NFOfWord_represents T.monoid.generators
        (T.rawShiftWord R hR shift hshift)
    have hfactorFun :
        (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
          (PallLean.Paper93.NFOfWord T.monoid.generators
            (T.rawFactorWord i)).prod) =
        (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
          (T.rawFactorWord i).prod) := by
      funext i
      exact PallLean.Paper93.NFOfWord_represents T.monoid.generators
        (T.rawFactorWord i)
    have hfactorProd :
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
            (PallLean.Paper93.NFOfWord T.monoid.generators
              (T.rawFactorWord i)).prod)).prod =
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns Srow.toList).length =>
            (T.rawFactorWord i).prod)).prod := by
      simp [hfactorFun]
    simpa [hshiftProd, hfactorProd] using
      T.row_mem_rawWordNormalForm R hR shift hshift

/-- Shortlex-normalized generator traces induce generator-word action data by
replacing every raw trace by its `NFOfWord` representative. -/
noncomputable def untouchedBackgroundLocalGeneratorActionData_of_NFGeneratorActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (NFD : UntouchedBackgroundZeroProfileLocalNFGeneratorActionData
      M n hn2 htb hns hn4 Srow typeBudget) :
    UntouchedBackgroundZeroProfileLocalGeneratorActionData
      M n hn2 htb hns hn4 Srow typeBudget where
  monoid := NFD.monoid
  monoid_card_le_typeBudget := NFD.monoid_card_le_typeBudget
  factorWord := fun i => PallLean.Paper93.NFOfWord NFD.monoid.generators
    (NFD.rawFactorWord i)
  factorWord_letters := by
    intro i a ha
    exact PallLean.Paper93.NFOfWord_letters_mem
      (NFD.rawFactorWord_letters i) a ha
  shiftWord := fun R hR shift hshift =>
    PallLean.Paper93.NFOfWord NFD.monoid.generators
      (NFD.rawShiftWord R hR shift hshift)
  shiftWord_letters := by
    intro R hR shift hshift a ha
    exact PallLean.Paper93.NFOfWord_letters_mem
      (NFD.rawShiftWord_letters R hR shift hshift) a ha
  row_mem_generatorWordNormalForm := by
    intro R hR shift hshift
    exact NFD.row_mem_NFOfWordNormalForm R hR shift hshift

/-- Generator-word local data induces local-monoid action data by evaluating
factor and shift words in the finite local monoid. -/
noncomputable def untouchedBackgroundLocalMonoidActionData_of_generatorActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (G : UntouchedBackgroundZeroProfileLocalGeneratorActionData
      M n hn2 htb hns hn4 Srow typeBudget) :
    UntouchedBackgroundZeroProfileLocalMonoidActionData
      M n hn2 htb hns hn4 Srow typeBudget where
  monoid := G.monoid
  monoid_card_le_typeBudget := G.monoid_card_le_typeBudget
  factorElement := fun i => (G.factorWord i).prod
  shiftElement := fun R hR shift hshift => (G.shiftWord R hR shift hshift).prod
  row_mem_productNormalForm := by
    intro R hR shift hshift
    exact G.row_mem_generatorWordNormalForm R hR shift hshift

/-- The local-monoid action data gives the concrete row-map classifier by using
`shiftElement * product factorElement` as the row normal form.  The product is a
list product, so the order of the exact filtered factor list is preserved and
no commutativity of the finite local monoid is assumed. -/
noncomputable def untouchedBackgroundLocalMonoidConcreteClassifier_of_actionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (A : UntouchedBackgroundZeroProfileLocalMonoidActionData
      M n hn2 htb hns hn4 Srow typeBudget) :
    UntouchedBackgroundZeroProfileLocalMonoidConcreteClassifier
      M n hn2 htb hns hn4 Srow typeBudget where
  monoid := A.monoid
  monoid_card_le_typeBudget := A.monoid_card_le_typeBudget
  rowMap :=
    { rowNormalForm := fun R hR shift hshift =>
        A.shiftElement R hR shift hshift * (List.ofFn A.factorElement).prod
      projected_row_mem_profileSubspace := by
        intro R hR shift hshift
        simpa [untouchedBackgroundZeroProfileConcreteDataOfLocalMonoid,
          LinearMap.id_apply] using
          A.row_mem_productNormalForm R hR shift hshift }

/-- The finite-local-monoid concrete classifier supplies the exact shifted-row
normal-form theorem for the filtered untouched background. -/
theorem untouchedBackgroundZeroProfileShiftRows_of_localMonoidConcreteClassifier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (Srow : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (C : UntouchedBackgroundZeroProfileLocalMonoidConcreteClassifier
      M n hn2 htb hns hn4 Srow typeBudget) :
    UntouchedBackgroundZeroProfileShiftRows_concreteW
      M n hn2 htb hns hn4 Srow := by
  classical
  intro R hR shift hshift
  let D := untouchedBackgroundZeroProfileConcreteDataOfLocalMonoid
    M n hn2 htb hns hn4 C.monoid typeBudget C.monoid_card_le_typeBudget
  have hrow := C.rowMap.projected_row_mem_profileSubspace R hR shift hshift
  simpa [D, untouchedBackgroundZeroProfileConcreteDataOfLocalMonoid,
    LinearMap.id_apply] using hrow

/-- A finite-local-monoid concrete classifier constructs the concrete
untouched-background normal-form classifier used by the touched/background
Khatri--Rao composition. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifier_of_localMonoidConcreteClassifier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (C : UntouchedBackgroundZeroProfileLocalMonoidConcreteClassifier
      M n hn2 htb hns hn4 S typeBudget) :
    UntouchedBackgroundConcreteNormalFormClassifier M n hn2 htb hns S
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  untouchedBackgroundConcreteNormalFormClassifier_of_zeroProfilePerTypeSpanning
    M n hn2 htb hns hn4 S
    (untouchedBackgroundZeroProfilePerTypeSpanning_of_shiftRows_concreteW
      M n hn2 htb hns hn4 S
      (untouchedBackgroundZeroProfileShiftRows_of_localMonoidConcreteClassifier
        M n hn2 htb hns hn4 S C))


/-- Finite local-monoid action data constructs the concrete untouched-background
normal-form classifier. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifier_of_localMonoidActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (A : UntouchedBackgroundZeroProfileLocalMonoidActionData
      M n hn2 htb hns hn4 S typeBudget) :
    UntouchedBackgroundConcreteNormalFormClassifier M n hn2 htb hns S
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  untouchedBackgroundConcreteNormalFormClassifier_of_localMonoidConcreteClassifier
    M n hn2 htb hns hn4 S
    (untouchedBackgroundLocalMonoidConcreteClassifier_of_actionData
      M n hn2 htb hns hn4 S A)

/-- Generator-word finite local-monoid data constructs the concrete
untouched-background normal-form classifier. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifier_of_localGeneratorActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (G : UntouchedBackgroundZeroProfileLocalGeneratorActionData
      M n hn2 htb hns hn4 S typeBudget) :
    UntouchedBackgroundConcreteNormalFormClassifier M n hn2 htb hns S
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  untouchedBackgroundConcreteNormalFormClassifier_of_localMonoidActionData
    M n hn2 htb hns hn4 S
    (untouchedBackgroundLocalMonoidActionData_of_generatorActionData
      M n hn2 htb hns hn4 S G)


/-- Shortlex-normalized generator-word data constructs the concrete
untouched-background normal-form classifier. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifier_of_localNFGeneratorActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (NFD : UntouchedBackgroundZeroProfileLocalNFGeneratorActionData
      M n hn2 htb hns hn4 S typeBudget) :
    UntouchedBackgroundConcreteNormalFormClassifier M n hn2 htb hns S
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  untouchedBackgroundConcreteNormalFormClassifier_of_localGeneratorActionData
    M n hn2 htb hns hn4 S
    (untouchedBackgroundLocalGeneratorActionData_of_NFGeneratorActionData
      M n hn2 htb hns hn4 S NFD)


/-- Raw generator-trace data constructs the concrete untouched-background
normal-form classifier via shortlex `NFOfWord` normalization. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifier_of_rawTraceActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (T : UntouchedBackgroundZeroProfileRawGeneratorTraceActionData
      M n hn2 htb hns hn4 S typeBudget) :
    UntouchedBackgroundConcreteNormalFormClassifier M n hn2 htb hns S
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  untouchedBackgroundConcreteNormalFormClassifier_of_localNFGeneratorActionData
    M n hn2 htb hns hn4 S
    (untouchedBackgroundLocalNFGeneratorActionData_of_rawTraceActionData
      M n hn2 htb hns hn4 S T)


/-- Shifted-row control plus explicit generator traces directly constructs the
concrete untouched-background classifier. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifier_of_shiftRows_and_words
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (A : ZeroProfileFiniteLocalMonoid)
    (hbudget : Fintype.card A.localMonoid ≤ typeBudget)
    (rawFactorWord :
      Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length →
        List A.localMonoid)
    (rawFactorWord_letters :
      ∀ i, ∀ a ∈ rawFactorWord i, a ∈ A.generators)
    (rawShiftWord :
      ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
        R.length ≤ Nat.log 2 n →
        ∀ shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
          shift.vars ⊆ R.toFinset → List A.localMonoid)
    (rawShiftWord_letters :
      ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
        (hR : R.length ≤ Nat.log 2 n)
        (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
        (hshift : shift.vars ⊆ R.toFinset),
        ∀ a ∈ rawShiftWord R hR shift hshift, a ∈ A.generators)
    (hshiftRows : UntouchedBackgroundZeroProfileShiftRows_concreteW
      M n hn2 htb hns hn4 S) :
    UntouchedBackgroundConcreteNormalFormClassifier M n hn2 htb hns S
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  untouchedBackgroundConcreteNormalFormClassifier_of_rawTraceActionData
    M n hn2 htb hns hn4 S
    (untouchedBackgroundRawTraceActionData_of_shiftRows_and_words
      M n hn2 htb hns hn4 S A hbudget rawFactorWord rawFactorWord_letters
      rawShiftWord rawShiftWord_letters hshiftRows)

/-- The shifted-row form of the exact filtered untouched-background normal form
constructs the concrete untouched-background classifier. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifier_of_zeroProfileShiftRows
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hshiftRows : UntouchedBackgroundZeroProfileShiftRows_concreteW
      M n hn2 htb hns hn4 S) :
    UntouchedBackgroundConcreteNormalFormClassifier M n hn2 htb hns S
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  untouchedBackgroundConcreteNormalFormClassifier_of_zeroProfilePerTypeSpanning
    M n hn2 htb hns hn4 S
    (untouchedBackgroundZeroProfilePerTypeSpanning_of_shiftRows_concreteW
      M n hn2 htb hns hn4 S hshiftRows)

/-- The concrete untouched-background classifier induces the existing finite
normal-form row classifier.  This exposes the actual finite alphabet selected
by §9.3 rather than hiding it behind the projected common-span interface. -/
noncomputable def UntouchedBackgroundConcreteNormalFormClassifier.toFiniteClassifier
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars)}
    {typeBudget : ℕ}
    (C : UntouchedBackgroundConcreteNormalFormClassifier
      M n hn2 htb hns S typeBudget) :
    ZeroProfileFiniteNormalFormRowClassifier
      (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length =>
        (untouchedBackgroundFactorList M n hn2 htb hns S.toList).get i)
      (LinearMap.id :
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
          MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (zeroProfileFiniteNormalFormFamilyData_of_concreteData C.data) :=
  zeroProfileFiniteNormalFormRowClassifier_of_concreteRowMap
    (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length =>
      (untouchedBackgroundFactorList M n hn2 htb hns S.toList).get i)
    (LinearMap.id :
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    C.data C.rowMap


/-- List-indexed concrete §9.3 normal-form classifier data for the exact
untouched background associated to a touched-row list `S`.

This is the final-assembly-facing version of
`UntouchedBackgroundConcreteNormalFormClassifier`: the factor family is
`untouchedBackgroundFactorList ... S` for the original list, not a `Finset`
converted back to an arbitrary list. -/
structure UntouchedBackgroundConcreteNormalFormClassifierForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  data : ZeroProfileConcreteNormalFormData
    (cookLevinTableau M n hn2 htb hns).numVars (Nat.log 2 n) typeBudget
  rowMap : ZeroProfileConcreteNormalFormRowMap
    (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
      (untouchedBackgroundFactorList M n hn2 htb hns S).get i)
    (LinearMap.id :
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    data


/-! ## List-indexed §9.3 local-monoid/profile classifier

The zero-profile constructors below are still useful for the current Route B
gate, but the paper-faithful source object is more structured: a finite local
monoid supplies canonical shortlex normal forms (§9.3, Lemmas 24--25), and a
profile map sends each canonical local action to its interface-anonymous
histogram (§9.3, Definition 21 / Lemma 29).  The concrete chart attached to a
monoid element is the symmetric-power/profile chart `V_h` for that histogram,
not an ambient or singleton span.
-/

/-- Concrete normal-form data induced by a finite local monoid together with
the paper §9.3 profile interpretation of its canonical elements.

This is the non-singleton/profile-aware variant of
`untouchedBackgroundZeroProfileConcreteDataOfLocalMonoid`: normal forms are
local-monoid elements, each element carries its own admissible histogram, and
the budget is the sum of the corresponding symmetric-profile dimensions. -/
noncomputable def untouchedBackgroundConcreteDataOfLocalMonoidProfiles
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : ZeroProfileFiniteLocalMonoid)
    (profile : A.localMonoid → ProfileHistogram)
    (profile_admissible : ∀ g, ProfileAdmissible (Nat.log 2 n) (profile g))
    (chart : ∀ g, ZeroProfileConcreteLocalChart
      (cookLevinTableau M n hn2 htb hns).numVars (profile g))
    (typeBudget : ℕ)
    (hbudget :
      (∑ g : A.localMonoid, zeroProfileSymmetricProfileDim (profile g)) ≤
        typeBudget) :
    ZeroProfileConcreteNormalFormData
      (cookLevinTableau M n hn2 htb hns).numVars (Nat.log 2 n) typeBudget where
  normalForm := A.localMonoid
  normalFormFintype := inferInstance
  profile := profile
  profile_admissible := profile_admissible
  chart := chart
  totalProfileBudget_le := hbudget

/-- List-indexed paper §9.3 local-monoid/profile classifier for the exact
untouched background.

This is the faithful object wanted before collapsing to the downstream
`UntouchedBackgroundConcreteNormalFormClassifierForList`: it keeps the exact
filtered factor list `untouchedBackgroundFactorList ... S`, classifies rows by
finite local-monoid normal forms, and attaches each normal form to its genuine
interface-anonymous profile chart. -/
structure UntouchedBackgroundProfileLocalMonoidConcreteClassifierForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  monoid : ZeroProfileFiniteLocalMonoid
  profile : monoid.localMonoid → ProfileHistogram
  profile_admissible :
    ∀ g, ProfileAdmissible (Nat.log 2 n) (profile g)
  chart : ∀ g, ZeroProfileConcreteLocalChart
    (cookLevinTableau M n hn2 htb hns).numVars (profile g)
  totalProfileBudget_le :
    (∑ g : monoid.localMonoid,
        zeroProfileSymmetricProfileDim (profile g)) ≤ typeBudget
  rowMap : ZeroProfileConcreteNormalFormRowMap
    (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
      (untouchedBackgroundFactorList M n hn2 htb hns S).get i)
    (LinearMap.id :
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (untouchedBackgroundConcreteDataOfLocalMonoidProfiles
      M n hn2 htb hns monoid profile profile_admissible chart
      typeBudget totalProfileBudget_le)

/-- A profile-aware finite-local-monoid classifier is already the concrete
list-indexed untouched-background normal-form classifier after forgetting the
reason why its normal forms are canonical §9.3 monoid/profile types. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifierForList_of_profileLocalMonoidClassifier
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (C : UntouchedBackgroundProfileLocalMonoidConcreteClassifierForList
      M n hn2 htb hns S typeBudget) :
    UntouchedBackgroundConcreteNormalFormClassifierForList
      M n hn2 htb hns S typeBudget where
  data := untouchedBackgroundConcreteDataOfLocalMonoidProfiles
    M n hn2 htb hns C.monoid C.profile C.profile_admissible C.chart
    typeBudget C.totalProfileBudget_le
  rowMap := C.rowMap

/-- Ordered local-monoid action data for the list-indexed profile-aware
classifier.

The row normal form is the shift action followed by the ordered product of the
exact filtered untouched factor actions.  We deliberately use `List.prod`, not
`Finset.prod`, because §9.3 only supplies a finite local monoid, not a
commutative one. -/
structure UntouchedBackgroundProfileLocalMonoidActionDataForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  monoid : ZeroProfileFiniteLocalMonoid
  profile : monoid.localMonoid → ProfileHistogram
  profile_admissible :
    ∀ g, ProfileAdmissible (Nat.log 2 n) (profile g)
  chart : ∀ g, ZeroProfileConcreteLocalChart
    (cookLevinTableau M n hn2 htb hns).numVars (profile g)
  totalProfileBudget_le :
    (∑ g : monoid.localMonoid,
        zeroProfileSymmetricProfileDim (profile g)) ≤ typeBudget
  factorElement :
    Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length →
      monoid.localMonoid
  shiftElement :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      R.length ≤ Nat.log 2 n →
      ∀ shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
        shift.vars ⊆ R.toFinset → monoid.localMonoid
  row_mem_productProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let rowNF := shiftElement R hR shift hshift *
        (List.ofFn factorElement).prod
      MultilinearSPDP.mlProj (shift *
          Finset.univ.prod
            (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
              (untouchedBackgroundFactorList M n hn2 htb hns S).get i)) ∈
        profileSubspace (profile rowNF) (chart rowNF).W

/-- Shortlex-normalized generator trace data for the list-indexed
profile-aware classifier.

This is the paper §9.3 canonical-window surface: each exact untouched factor
and each shift row is witnessed by a raw word over the fixed finite generator
list, but the row normal form used for classification is the shortlex
`NFOfWord` product.  The profile/chart is evaluated at that canonical product,
so the downstream row map is genuinely profile-aware rather than the singleton
zero-profile collapse. -/
structure UntouchedBackgroundProfileLocalNFGeneratorActionDataForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  monoid : ZeroProfileFiniteLocalMonoid
  profile : monoid.localMonoid → ProfileHistogram
  profile_admissible :
    ∀ g, ProfileAdmissible (Nat.log 2 n) (profile g)
  chart : ∀ g, ZeroProfileConcreteLocalChart
    (cookLevinTableau M n hn2 htb hns).numVars (profile g)
  totalProfileBudget_le :
    (∑ g : monoid.localMonoid,
        zeroProfileSymmetricProfileDim (profile g)) ≤ typeBudget
  rawFactorWord :
    Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length →
      List monoid.localMonoid
  rawFactorWord_letters :
    ∀ i, ∀ a ∈ rawFactorWord i, a ∈ monoid.generators
  rawShiftWord :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      R.length ≤ Nat.log 2 n →
      ∀ shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
        shift.vars ⊆ R.toFinset → List monoid.localMonoid
  rawShiftWord_letters :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      ∀ a ∈ rawShiftWord R hR shift hshift, a ∈ monoid.generators
  row_mem_NFOfWordProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let rowNF := (PallLean.Paper93.NFOfWord monoid.generators
          (rawShiftWord R hR shift hshift)).prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            (PallLean.Paper93.NFOfWord monoid.generators
              (rawFactorWord i)).prod)).prod
      MultilinearSPDP.mlProj (shift *
          Finset.univ.prod
            (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
              (untouchedBackgroundFactorList M n hn2 htb hns S).get i)) ∈
        profileSubspace (profile rowNF) (chart rowNF).W

/-- Raw generator trace data for the list-indexed profile-aware classifier.

This is the form the eventual Cook--Levin gadget calculation should prove:
rows are first described by raw local generator traces.  The bridge below
canonicalizes those traces with `NFOfWord`, keeping semantic row membership
separate from shortlex normalization. -/
structure UntouchedBackgroundProfileRawGeneratorTraceActionDataForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  monoid : ZeroProfileFiniteLocalMonoid
  profile : monoid.localMonoid → ProfileHistogram
  profile_admissible :
    ∀ g, ProfileAdmissible (Nat.log 2 n) (profile g)
  chart : ∀ g, ZeroProfileConcreteLocalChart
    (cookLevinTableau M n hn2 htb hns).numVars (profile g)
  totalProfileBudget_le :
    (∑ g : monoid.localMonoid,
        zeroProfileSymmetricProfileDim (profile g)) ≤ typeBudget
  rawFactorWord :
    Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length →
      List monoid.localMonoid
  rawFactorWord_letters :
    ∀ i, ∀ a ∈ rawFactorWord i, a ∈ monoid.generators
  rawShiftWord :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      R.length ≤ Nat.log 2 n →
      ∀ shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
        shift.vars ⊆ R.toFinset → List monoid.localMonoid
  rawShiftWord_letters :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      ∀ a ∈ rawShiftWord R hR shift hshift, a ∈ monoid.generators
  row_mem_rawWordProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let rowNF := (rawShiftWord R hR shift hshift).prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            (rawFactorWord i).prod)).prod
      MultilinearSPDP.mlProj (shift *
          Finset.univ.prod
            (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
              (untouchedBackgroundFactorList M n hn2 htb hns S).get i)) ∈
        profileSubspace (profile rowNF) (chart rowNF).W

/-- Finite endomorphism monoid used for the concrete type-trace action. -/
structure UntouchedBackgroundFiniteEnd (α : Type) where
  toFun : α → α

instance (α : Type) : CoeFun (UntouchedBackgroundFiniteEnd α) (fun _ => α → α) where
  coe f := f.toFun

instance (α : Type) : One (UntouchedBackgroundFiniteEnd α) where
  one := ⟨id⟩

instance (α : Type) : Mul (UntouchedBackgroundFiniteEnd α) where
  mul f g := ⟨fun x => f (g x)⟩

instance (α : Type) : Monoid (UntouchedBackgroundFiniteEnd α) where
  one_mul := by
    intro f
    cases f
    rfl
  mul_one := by
    intro f
    cases f
    rfl
  mul_assoc := by
    intro f g h
    cases f
    cases g
    cases h
    rfl

noncomputable instance (α : Type) [Fintype α] [DecidableEq α] :
    Fintype (UntouchedBackgroundFiniteEnd α) :=
  Fintype.ofEquiv (α → α)
    { toFun := fun f => ⟨f⟩
      invFun := fun f => f.toFun
      left_inv := by intro f; rfl
      right_inv := by intro f; cases f; rfl }

noncomputable instance (α : Type) [Fintype α] [DecidableEq α] :
    DecidableEq (UntouchedBackgroundFiniteEnd α) := by
  intro f g
  let e : UntouchedBackgroundFiniteEnd α ≃ (α → α) :=
    { toFun := fun f => f.toFun
      invFun := fun f => ⟨f⟩
      left_inv := by intro f; cases f; rfl
      right_inv := by intro f; rfl }
  exact e.decidableEq f g

/-- Bounded ordered trace state for the untouched-background local type word.
It stores the exact ordered list of filtered Cook--Levin constraint types up to
the Route B window bound. -/
structure UntouchedBackgroundConstraintTypeTraceState (κ : ℕ) where
  len : Fin (κ + 1)
  slot : Fin κ → Option ConstraintType

noncomputable instance untouchedBackgroundConstraintTypeTraceStateDecidableEq
    (κ : ℕ) : DecidableEq (UntouchedBackgroundConstraintTypeTraceState κ) := by
  intro s t
  let e : UntouchedBackgroundConstraintTypeTraceState κ ≃
      (Fin (κ + 1) × (Fin κ → Option ConstraintType)) :=
    { toFun := fun s => (s.len, s.slot)
      invFun := fun p => { len := p.1, slot := p.2 }
      left_inv := by intro s; cases s; rfl
      right_inv := by intro p; cases p; rfl }
  exact e.decidableEq s t

noncomputable instance untouchedBackgroundConstraintTypeTraceStateFintype
    (κ : ℕ) : Fintype (UntouchedBackgroundConstraintTypeTraceState κ) :=
  Fintype.ofEquiv (Fin (κ + 1) × (Fin κ → Option ConstraintType))
    { toFun := fun p => { len := p.1, slot := p.2 }
      invFun := fun s => (s.len, s.slot)
      left_inv := by intro p; cases p; rfl
      right_inv := by intro s; cases s; rfl }

/-- Append one concrete Cook--Levin constraint type to the bounded ordered type
trace, saturating outside the window so the action is total. -/
noncomputable def untouchedBackgroundConstraintTypeTraceAppend {κ : ℕ}
    (τ : ConstraintType) :
    UntouchedBackgroundFiniteEnd (UntouchedBackgroundConstraintTypeTraceState κ) :=
  ⟨fun s =>
    if h : s.len.val < κ then
      { len := ⟨s.len.val + 1, by omega⟩
        slot := fun j => if j.val = s.len.val then some τ else s.slot j }
    else
      s⟩

/-- Empty ordered type trace. -/
noncomputable def untouchedBackgroundConstraintTypeTraceEmpty (κ : ℕ) :
    UntouchedBackgroundConstraintTypeTraceState κ where
  len := ⟨0, by omega⟩
  slot := fun _ => none

/-- The interface-anonymous histogram read from a concrete ordered type-trace
state: count how many occupied slots carry each filtered Cook--Levin
`ConstraintType`. -/
noncomputable def untouchedBackgroundConstraintTypeTraceProfile {κ : ℕ}
    (s : UntouchedBackgroundConstraintTypeTraceState κ) : ProfileHistogram :=
  fun τ => Fintype.card { j : Fin κ // s.slot j = some τ }

/-- The concrete type-trace profile has mass bounded by the trace window. -/
theorem untouchedBackgroundConstraintTypeTraceProfile_admissible {κ : ℕ}
    (s : UntouchedBackgroundConstraintTypeTraceState κ) :
    ProfileAdmissible κ (untouchedBackgroundConstraintTypeTraceProfile s) := by
  classical
  unfold ProfileAdmissible profileMass untouchedBackgroundConstraintTypeTraceProfile
  rw [← Fintype.card_sigma]
  simpa [Fintype.card_fin] using
    (Fintype.card_le_of_injective
      (fun x : Sigma (fun τ : ConstraintType => { j : Fin κ // s.slot j = some τ }) =>
        x.2.1) (by
    intro x y hxy
    cases x with
    | mk τx jx =>
      cases y with
      | mk τy jy =>
        cases jx with
        | mk jx hjx =>
          cases jy with
          | mk jy hjy =>
            simp only at hxy
            subst jy
            have hτ : τx = τy := by
              simpa [hjx] using hjy
            subst hτ
            rfl))

/-- The histogram of a concrete type-trace monoid element is obtained by
applying the endomorphism to the empty trace and reading the occupied type
slots. -/
noncomputable def untouchedBackgroundConstraintTypeTraceActionProfile (κ : ℕ)
    (g : UntouchedBackgroundFiniteEnd (UntouchedBackgroundConstraintTypeTraceState κ)) :
    ProfileHistogram :=
  untouchedBackgroundConstraintTypeTraceProfile
    (g (untouchedBackgroundConstraintTypeTraceEmpty κ))

/-- The action-profile of every concrete type-trace monoid element is
admissible at the trace window. -/
theorem untouchedBackgroundConstraintTypeTraceActionProfile_admissible (κ : ℕ)
    (g : UntouchedBackgroundFiniteEnd (UntouchedBackgroundConstraintTypeTraceState κ)) :
    ProfileAdmissible κ (untouchedBackgroundConstraintTypeTraceActionProfile κ g) :=
  untouchedBackgroundConstraintTypeTraceProfile_admissible _

/-- The concrete finite local monoid generated by the four filtered
Cook--Levin constraint-type append actions.  This is the finite local action
package underlying the list-indexed untouched-background raw traces. -/
noncomputable def untouchedBackgroundConstraintTypeTraceLocalMonoid (κ : ℕ) :
    ZeroProfileFiniteLocalMonoid where
  localMonoid := UntouchedBackgroundFiniteEnd
    (UntouchedBackgroundConstraintTypeTraceState κ)
  generators :=
    (Finset.univ : Finset ConstraintType).toList.map
      (fun τ => untouchedBackgroundConstraintTypeTraceAppend (κ := κ) τ)

/-- The generator attached to a concrete filtered Cook--Levin constraint type. -/
noncomputable def untouchedBackgroundConstraintTypeTraceGenerator (κ : ℕ)
    (τ : ConstraintType) :
    (untouchedBackgroundConstraintTypeTraceLocalMonoid κ).localMonoid :=
  untouchedBackgroundConstraintTypeTraceAppend (κ := κ) τ

/-- Each concrete type generator is one of the displayed local generators. -/
theorem untouchedBackgroundConstraintTypeTraceGenerator_mem (κ : ℕ)
    (τ : ConstraintType) :
    untouchedBackgroundConstraintTypeTraceGenerator κ τ ∈
      (untouchedBackgroundConstraintTypeTraceLocalMonoid κ).generators := by
  classical
  unfold untouchedBackgroundConstraintTypeTraceGenerator
    untouchedBackgroundConstraintTypeTraceLocalMonoid
  simp

/-- Concrete local atoms for the untouched-background row word.  Factor atoms
record the filtered Cook--Levin constraint type; `shift` records the presence of
a row-local shift/monomial operation without putting machine-dependent
coefficients into the finite alphabet. -/
inductive UntouchedBackgroundTraceAtom where
  | factor : ConstraintType → UntouchedBackgroundTraceAtom
  | shift : UntouchedBackgroundTraceAtom
  deriving DecidableEq, Fintype

/-- Bounded ordered trace state for the full untouched-background row word,
including both factor-type atoms and shift atoms. -/
structure UntouchedBackgroundAtomTraceState (κ : ℕ) where
  len : Fin (κ + 1)
  slot : Fin κ → Option UntouchedBackgroundTraceAtom

noncomputable instance untouchedBackgroundAtomTraceStateDecidableEq
    (κ : ℕ) : DecidableEq (UntouchedBackgroundAtomTraceState κ) := by
  intro s t
  let e : UntouchedBackgroundAtomTraceState κ ≃
      (Fin (κ + 1) × (Fin κ → Option UntouchedBackgroundTraceAtom)) :=
    { toFun := fun s => (s.len, s.slot)
      invFun := fun p => { len := p.1, slot := p.2 }
      left_inv := by intro s; cases s; rfl
      right_inv := by intro p; cases p; rfl }
  exact e.decidableEq s t

noncomputable instance untouchedBackgroundAtomTraceStateFintype
    (κ : ℕ) : Fintype (UntouchedBackgroundAtomTraceState κ) :=
  Fintype.ofEquiv (Fin (κ + 1) × (Fin κ → Option UntouchedBackgroundTraceAtom))
    { toFun := fun p => { len := p.1, slot := p.2 }
      invFun := fun s => (s.len, s.slot)
      left_inv := by intro p; cases p; rfl
      right_inv := by intro s; cases s; rfl }

/-- Empty full row-atom trace. -/
noncomputable def untouchedBackgroundAtomTraceEmpty (κ : ℕ) :
    UntouchedBackgroundAtomTraceState κ where
  len := ⟨0, by omega⟩
  slot := fun _ => none

/-- Append one full row atom, saturating at the Route B window bound so the
action is total on a finite state space. -/
noncomputable def untouchedBackgroundAtomTraceAppend {κ : ℕ}
    (a : UntouchedBackgroundTraceAtom) :
    UntouchedBackgroundFiniteEnd (UntouchedBackgroundAtomTraceState κ) :=
  ⟨fun s =>
    if h : s.len.val < κ then
      { len := ⟨s.len.val + 1, by omega⟩
        slot := fun j => if j.val = s.len.val then some a else s.slot j }
    else
      s⟩

/-- The profile of a full row-atom trace counts only factor-type atoms; shift
atoms affect the local monoid normal form but not the `ConstraintType`
histogram. -/
noncomputable def untouchedBackgroundAtomTraceProfile {κ : ℕ}
    (s : UntouchedBackgroundAtomTraceState κ) : ProfileHistogram :=
  fun τ => Fintype.card
    { j : Fin κ // s.slot j = some (UntouchedBackgroundTraceAtom.factor τ) }

/-- The factor-only profile read from a full atom trace is admissible because
occupied factor slots inject into the bounded trace slots. -/
theorem untouchedBackgroundAtomTraceProfile_admissible {κ : ℕ}
    (s : UntouchedBackgroundAtomTraceState κ) :
    ProfileAdmissible κ (untouchedBackgroundAtomTraceProfile s) := by
  classical
  unfold ProfileAdmissible profileMass untouchedBackgroundAtomTraceProfile
  rw [← Fintype.card_sigma]
  simpa [Fintype.card_fin] using
    (Fintype.card_le_of_injective
      (fun x : Sigma (fun τ : ConstraintType =>
          { j : Fin κ // s.slot j = some (UntouchedBackgroundTraceAtom.factor τ) }) =>
        x.2.1) (by
    intro x y hxy
    cases x with
    | mk τx jx =>
      cases y with
      | mk τy jy =>
        cases jx with
        | mk jx hjx =>
          cases jy with
          | mk jy hjy =>
            simp only at hxy
            subst jy
            have hτ : τx = τy := by
              have hsome :
                  some (UntouchedBackgroundTraceAtom.factor τx) =
                    some (UntouchedBackgroundTraceAtom.factor τy) := by
                rw [← hjx, hjy]
              injection hsome with hatom
              injection hatom
            subst hτ
            rfl))

/-- Profile of a full atom-trace monoid element, read by applying it to the
empty trace. -/
noncomputable def untouchedBackgroundAtomTraceActionProfile (κ : ℕ)
    (g : UntouchedBackgroundFiniteEnd (UntouchedBackgroundAtomTraceState κ)) :
    ProfileHistogram :=
  untouchedBackgroundAtomTraceProfile (g (untouchedBackgroundAtomTraceEmpty κ))

/-- Every full atom-trace action profile is admissible. -/
theorem untouchedBackgroundAtomTraceActionProfile_admissible (κ : ℕ)
    (g : UntouchedBackgroundFiniteEnd (UntouchedBackgroundAtomTraceState κ)) :
    ProfileAdmissible κ (untouchedBackgroundAtomTraceActionProfile κ g) :=
  untouchedBackgroundAtomTraceProfile_admissible _

/-- Concrete finite local monoid for full untouched-background raw traces: one
generator for each factor type and one generator for a shift atom. -/
noncomputable def untouchedBackgroundAtomTraceLocalMonoid (κ : ℕ) :
    ZeroProfileFiniteLocalMonoid where
  localMonoid := UntouchedBackgroundFiniteEnd (UntouchedBackgroundAtomTraceState κ)
  generators :=
    (Finset.univ : Finset UntouchedBackgroundTraceAtom).toList.map
      (fun a => untouchedBackgroundAtomTraceAppend (κ := κ) a)

/-- Generator for one filtered Cook--Levin factor type in the full atom trace. -/
noncomputable def untouchedBackgroundAtomTraceFactorGenerator (κ : ℕ)
    (τ : ConstraintType) :
    (untouchedBackgroundAtomTraceLocalMonoid κ).localMonoid :=
  untouchedBackgroundAtomTraceAppend (κ := κ)
    (UntouchedBackgroundTraceAtom.factor τ)

/-- Generator for a row-local shift atom. -/
noncomputable def untouchedBackgroundAtomTraceShiftGenerator (κ : ℕ) :
    (untouchedBackgroundAtomTraceLocalMonoid κ).localMonoid :=
  untouchedBackgroundAtomTraceAppend (κ := κ) UntouchedBackgroundTraceAtom.shift

/-- Factor-type generators belong to the displayed full atom alphabet. -/
theorem untouchedBackgroundAtomTraceFactorGenerator_mem (κ : ℕ)
    (τ : ConstraintType) :
    untouchedBackgroundAtomTraceFactorGenerator κ τ ∈
      (untouchedBackgroundAtomTraceLocalMonoid κ).generators := by
  classical
  unfold untouchedBackgroundAtomTraceFactorGenerator untouchedBackgroundAtomTraceLocalMonoid
  simp

/-- The shift generator belongs to the displayed full atom alphabet. -/
theorem untouchedBackgroundAtomTraceShiftGenerator_mem (κ : ℕ) :
    untouchedBackgroundAtomTraceShiftGenerator κ ∈
      (untouchedBackgroundAtomTraceLocalMonoid κ).generators := by
  classical
  unfold untouchedBackgroundAtomTraceShiftGenerator untouchedBackgroundAtomTraceLocalMonoid
  simp

/-- Fully concrete atom-trace compiled-chart row theorem.  The shift word is no
longer arbitrary: it is the list of `R.length` copies of the single shift
atom.  Coefficients of `shift` remain in the polynomial scalar side, not in the
finite local alphabet. -/
structure UntouchedBackgroundConcreteAtomTraceCompiledChartRowsForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ typeBudget : ℕ) where
  totalProfileBudget_le :
    (∑ g : (untouchedBackgroundAtomTraceLocalMonoid
        (Nat.log 2 n)).localMonoid,
        zeroProfileSymmetricProfileDim
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) g)) ≤
      typeBudget
  row_mem_atomTraceProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      MultilinearSPDP.mlProj (shift *
          Finset.univ.prod
            (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
              (untouchedBackgroundFactorList M n hn2 htb hns S).get i)) ∈
        profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W

/-- The exact atom-trace profile budget for the full finite local action monoid.

Keeping this as a definition lets downstream instantiations avoid carrying a
separate arbitrary `typeBudget`: the budget is literally the paper §9.3 sum of
symmetric-profile dimensions over the concrete finite local action monoid. -/
noncomputable def untouchedBackgroundAtomTraceExactTypeBudget (n : ℕ) : ℕ :=
  ∑ g : (untouchedBackgroundAtomTraceLocalMonoid (Nat.log 2 n)).localMonoid,
    zeroProfileSymmetricProfileDim
      (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) g)

/-- Fully concrete atom-trace row theorem with the canonical exact budget.

This is the leanest remaining local-chart obligation: prove the actual
Cook--Levin row membership in the compiled coefficient-basis chart for the
profile read from the concrete atom trace.  The finite-budget field is then
forced by `untouchedBackgroundAtomTraceExactTypeBudget`; no arbitrary/global
budget is introduced. -/
structure UntouchedBackgroundConcreteAtomTraceExactCompiledChartRowsForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ) where
  row_mem_atomTraceProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      MultilinearSPDP.mlProj (shift *
          Finset.univ.prod
            (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
              (untouchedBackgroundFactorList M n hn2 htb hns S).get i)) ∈
        profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W

/-- Local-algebra split of the exact atom-trace row theorem.

This is the paper-faithful algebraic decomposition of `row_mem_atomTraceProfile`:
first put the exact untouched Cook--Levin background product in the selected
compiled-basis profile subspace, then prove that multiplying by the row-local
shift and applying `mlProj` preserves that same selected subspace.  The selected
profile is still the one read from the concrete atom-trace normal form; no
ambient/global span and no dropped background factors are introduced. -/
structure UntouchedBackgroundConcreteAtomTraceExactLocalAlgebraRowsForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ) where
  unshifted_background_mem_atomTraceProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      Finset.univ.prod
          (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            (untouchedBackgroundFactorList M n hn2 htb hns S).get i) ∈
        profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W
  shift_mlProj_closure_atomTraceProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset)
      (p : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      p ∈ profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W →
      MultilinearSPDP.mlProj (shift * p) ∈
        profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W

/-- Slot-product version of the exact atom-trace local-algebra row theorem.

This lowers the unshifted-background half of
`UntouchedBackgroundConcreteAtomTraceExactLocalAlgebraRowsForList` to the
literal Lemma-31 constructor: provide, for the profile read from the concrete
atom trace, an ordered slot family whose slots lie in the corresponding
compiled-basis interface spaces and whose typed product is exactly the
unshifted untouched Cook--Levin background product.  The shift/`mlProj` closure
field is left explicit because it is the other independent local-algebra
obligation. -/
structure UntouchedBackgroundConcreteAtomTraceExactSlotProductLocalAlgebraRowsForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ) where
  slot :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      (τ : SymmetricPowerBound.ConstraintType) →
        Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ) →
          MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ
  slot_mem :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      ∀ (τ : SymmetricPowerBound.ConstraintType)
        (j : Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ)),
        slot R hR shift hshift τ j ∈
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W τ
  product_eq :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      Finset.univ.prod
          (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            (untouchedBackgroundFactorList M n hn2 htb hns S).get i) =
        ∏ τ : SymmetricPowerBound.ConstraintType,
          ∏ j : Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ),
            slot R hR shift hshift τ j
  shift_mlProj_closure_atomTraceProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset)
      (p : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      p ∈ profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W →
      MultilinearSPDP.mlProj (shift * p) ∈
        profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W

/-- Pure finite-set product factorization for a two-level slot fibre cover.

If the slot fibres are pairwise disjoint and cover all factor indices, then the
flat product over all factors is the product over slot-fibre products.  This is
just `Finset.prod_biUnion` plus `Fintype.prod_sigma`, isolated here so the next
Route-B seam is visibly finite/combinatorial rather than geometric. -/
theorem untouchedBackground_prod_eq_twoLevelFiberProduct
    {ι β σ : Type} [Fintype ι] [DecidableEq ι] [CommMonoid β]
    [Fintype σ]
    (m : σ → ℕ) (fiber : ∀ s, Fin (m s) → Finset ι) (f : ι → β)
    (hdisj :
      (↑(Finset.univ.sigma
        (fun s : σ => (Finset.univ : Finset (Fin (m s))))) :
          Set ((s : σ) × Fin (m s))).PairwiseDisjoint
        (fun p => fiber p.1 p.2))
    (hunion :
      (Finset.univ.sigma
        (fun s : σ => (Finset.univ : Finset (Fin (m s))))).biUnion
          (fun p => fiber p.1 p.2) = Finset.univ) :
    Finset.univ.prod f = ∏ s : σ, ∏ j : Fin (m s), (fiber s j).prod f := by
  classical
  have hflat :
      Finset.univ.prod f =
        ∏ p ∈ (Finset.univ.sigma
          (fun s : σ => (Finset.univ : Finset (Fin (m s))))),
          (fiber p.1 p.2).prod f := by
    rw [← hunion]
    exact Finset.prod_biUnion hdisj
  rw [hflat]
  rw [Finset.univ_sigma_univ]
  exact Fintype.prod_sigma
    (fun p : Sigma (fun s => Fin (m s)) => (fiber p.1 p.2).prod f)

/-- Fibre-product version of the exact atom-trace local-algebra row theorem.

This lowers the slot-product seam one more step: instead of providing a slot
polynomial directly, provide a finite partition of the untouched Cook--Levin
factor indices into profile slots.  Each slot contributes the product over its
assigned factor fibre, and pure finite-set algebra proves the global product
identity. -/
structure UntouchedBackgroundConcreteAtomTraceExactFiberProductLocalAlgebraRowsForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ) where
  fiber :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      (τ : SymmetricPowerBound.ConstraintType) →
        Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ) →
          Finset (Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length)
  fiber_pairwiseDisjoint :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      (↑(Finset.univ.sigma
        (fun τ : SymmetricPowerBound.ConstraintType =>
          (Finset.univ : Finset
            (Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ))))) :
          Set ((τ : SymmetricPowerBound.ConstraintType) ×
            Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ))).PairwiseDisjoint
        (fun p => fiber R hR shift hshift p.1 p.2)
  fiber_cover :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      (Finset.univ.sigma
        (fun τ : SymmetricPowerBound.ConstraintType =>
          (Finset.univ : Finset
            (Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ))))).biUnion
          (fun p => fiber R hR shift hshift p.1 p.2) = Finset.univ
  fiber_product_mem :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      ∀ (τ : SymmetricPowerBound.ConstraintType)
        (j : Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ)),
        (fiber R hR shift hshift τ j).prod
            (fun i => (untouchedBackgroundFactorList M n hn2 htb hns S).get i) ∈
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W τ
  shift_mlProj_closure_atomTraceProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset)
      (p : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      p ∈ profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W →
      MultilinearSPDP.mlProj (shift * p) ∈
        profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W

/-- Per-constraint-type fibre version of the exact atom-trace local-algebra row
seam.

This is one step more concrete than the global fibre-product data: for each
real `ConstraintType`, provide a partition of exactly the factor indices with
that filtered Cook--Levin type among the profile slots of the same type.  The
constructor below proves the global cross-type disjointness and cover fields by
pure finite-set/type-filter algebra. -/
structure UntouchedBackgroundConcreteAtomTraceExactTypeFiberProductLocalAlgebraRowsForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ) where
  typeFiber :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      (τ : SymmetricPowerBound.ConstraintType) →
        Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ) →
          Finset (Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length)
  typeFiber_subset_type :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      ∀ (τ : SymmetricPowerBound.ConstraintType)
        (j : Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ)),
        typeFiber R hR shift hshift τ j ⊆
          (Finset.univ.filter (fun i => ctype i = τ))
  typeFiber_pairwiseDisjoint :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      ∀ τ : SymmetricPowerBound.ConstraintType,
        ((Finset.univ : Finset
          (Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ))) :
            Set (Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ))).PairwiseDisjoint
          (fun j => typeFiber R hR shift hshift τ j)
  typeFiber_cover_type :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      ∀ τ : SymmetricPowerBound.ConstraintType,
        (Finset.univ : Finset
          (Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ))).biUnion
            (fun j => typeFiber R hR shift hshift τ j) =
          Finset.univ.filter (fun i => ctype i = τ)
  typeFiber_product_mem :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      ∀ (τ : SymmetricPowerBound.ConstraintType)
        (j : Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ)),
        (typeFiber R hR shift hshift τ j).prod
            (fun i => (untouchedBackgroundFactorList M n hn2 htb hns S).get i) ∈
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W τ
  shift_mlProj_closure_atomTraceProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset)
      (p : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      p ∈ profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W →
      MultilinearSPDP.mlProj (shift * p) ∈
        profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W


/-- Concrete Cook--Levin factor/type trace data for the exact atom-trace
row seam.

This is lower than an explicit slot equivalence.  It records the numerical fact
that, for each `ConstraintType`, the atom-trace profile has exactly as many
slots as the filtered Cook--Levin factor list has factors of that type, plus
singleton factor membership in the selected compiled-basis chart and the
independent shift/`mlProj` closure.  The constructor below turns the cardinal
equality into an arbitrary finite equivalence; the algebra above then turns
that equivalence into singleton fibres. -/
structure UntouchedBackgroundConcreteAtomTraceExactFactorTypeTraceLocalAlgebraRowsForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ) where
  typeSlot_count_eq :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      ∀ τ : SymmetricPowerBound.ConstraintType,
        Fintype.card { i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length //
            ctype i = τ } =
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ
  typeFactor_mem :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      ∀ (τ : SymmetricPowerBound.ConstraintType)
        (i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length),
        ctype i = τ →
        (untouchedBackgroundFactorList M n hn2 htb hns S).get i ∈
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W τ
  shift_mlProj_closure_atomTraceProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset)
      (p : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      p ∈ profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W →
      MultilinearSPDP.mlProj (shift * p) ∈
        profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W

/-- Slot-indexed Cook--Levin factor/type trace data for the exact atom-trace
row seam.

This is lower than the per-type fibre-product seam: instead of asking for
arbitrary fibres, it asks for an explicit bijection between the atom-trace
slots of each `ConstraintType` and the concrete filtered Cook--Levin factors of
that type.  The constructor below turns this bijection into singleton fibres;
disjointness and cover are then pure finite-set/equivalence algebra. -/
structure UntouchedBackgroundConcreteAtomTraceExactTypeSlotFactorLocalAlgebraRowsForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ) where
  typeSlotEquiv :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      (τ : SymmetricPowerBound.ConstraintType) →
        Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ) ≃
          { i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length //
            ctype i = τ }
  typeSlotFactor_mem :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      ∀ (τ : SymmetricPowerBound.ConstraintType)
        (j : Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF) τ)),
        (untouchedBackgroundFactorList M n hn2 htb hns S).get
            ((typeSlotEquiv R hR shift hshift τ j).1) ∈
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W τ
  shift_mlProj_closure_atomTraceProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset)
      (p : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let shiftWord := List.replicate R.length
        (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
      let rowNF := shiftWord.prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      p ∈ profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W →
      MultilinearSPDP.mlProj (shift * p) ∈
        profileSubspace
          (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) rowNF)).W

/-- Concrete factor/type trace data supplies explicit slot-factor data by
choosing the finite equivalence given by the per-type cardinal equality. -/
noncomputable def untouchedBackgroundConcreteAtomTraceExactTypeSlotFactorLocalAlgebraRowsForList_of_factorTypeTrace
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ)
    (A : UntouchedBackgroundConcreteAtomTraceExactFactorTypeTraceLocalAlgebraRowsForList
      M n hn2 htb hns S B ℓ) :
    UntouchedBackgroundConcreteAtomTraceExactTypeSlotFactorLocalAlgebraRowsForList
      M n hn2 htb hns S B ℓ where
  typeSlotEquiv := by
    intro R hR shift hshift
    dsimp
    intro τ
    exact (Fintype.equivFinOfCardEq
      (A.typeSlot_count_eq R hR shift hshift τ)).symm
  typeSlotFactor_mem := by
    intro R hR shift hshift
    dsimp
    intro τ j
    exact A.typeFactor_mem R hR shift hshift τ
      (((Fintype.equivFinOfCardEq
        (A.typeSlot_count_eq R hR shift hshift τ)).symm j).1)
      (((Fintype.equivFinOfCardEq
        (A.typeSlot_count_eq R hR shift hshift τ)).symm j).2)
  shift_mlProj_closure_atomTraceProfile := A.shift_mlProj_closure_atomTraceProfile

/-- Slot-factor data supplies per-type singleton fibre-product data. -/
noncomputable def untouchedBackgroundConcreteAtomTraceExactTypeFiberProductLocalAlgebraRowsForList_of_typeSlotFactor
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ)
    (A : UntouchedBackgroundConcreteAtomTraceExactTypeSlotFactorLocalAlgebraRowsForList
      M n hn2 htb hns S B ℓ) :
    UntouchedBackgroundConcreteAtomTraceExactTypeFiberProductLocalAlgebraRowsForList
      M n hn2 htb hns S B ℓ where
  typeFiber := by
    intro R hR shift hshift
    dsimp
    intro τ j
    exact {((A.typeSlotEquiv R hR shift hshift τ) j).1}
  typeFiber_subset_type := by
    intro R hR shift hshift
    dsimp
    intro τ j i hi
    simp only [Finset.mem_singleton] at hi
    subst hi
    simpa [Finset.mem_filter] using ((A.typeSlotEquiv R hR shift hshift τ) j).2
  typeFiber_pairwiseDisjoint := by
    intro R hR shift hshift
    dsimp
    intro τ
    intro j _hj k _hk hjk
    show Disjoint ({((A.typeSlotEquiv R hR shift hshift τ) j).1} :
        Finset (Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length))
        {((A.typeSlotEquiv R hR shift hshift τ) k).1}
    rw [Finset.disjoint_left]
    intro i hi hk
    simp only [Finset.mem_singleton] at hi hk
    have hval : ((A.typeSlotEquiv R hR shift hshift τ) j) =
        ((A.typeSlotEquiv R hR shift hshift τ) k) := by
      apply Subtype.ext
      simpa using hi.symm.trans hk
    exact hjk ((A.typeSlotEquiv R hR shift hshift τ).injective hval)
  typeFiber_cover_type := by
    intro R hR shift hshift
    dsimp
    intro τ
    apply Finset.ext
    intro i
    constructor
    · intro hi
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hi
      rcases hi with ⟨j, hij⟩
      subst hij
      simpa [Finset.mem_filter] using ((A.typeSlotEquiv R hR shift hshift τ) j).2
    · intro hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      refine ⟨(A.typeSlotEquiv R hR shift hshift τ).symm ⟨i, hi⟩, ?_⟩
      simp
  typeFiber_product_mem := by
    intro R hR shift hshift
    dsimp
    intro τ j
    simpa using A.typeSlotFactor_mem R hR shift hshift τ j
  shift_mlProj_closure_atomTraceProfile := A.shift_mlProj_closure_atomTraceProfile

/-- Per-type fibre-product data supplies the global fibre-product seam. -/
noncomputable def untouchedBackgroundConcreteAtomTraceExactFiberProductLocalAlgebraRowsForList_of_typeFiberProduct
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ)
    (A : UntouchedBackgroundConcreteAtomTraceExactTypeFiberProductLocalAlgebraRowsForList
      M n hn2 htb hns S B ℓ) :
    UntouchedBackgroundConcreteAtomTraceExactFiberProductLocalAlgebraRowsForList
      M n hn2 htb hns S B ℓ where
  fiber := A.typeFiber
  fiber_pairwiseDisjoint := by
    classical
    intro R hR shift hshift
    dsimp
    intro p hp q hq hpq
    rcases p with ⟨τp, jp⟩
    rcases q with ⟨τq, jq⟩
    dsimp at hp hq hpq ⊢
    by_cases hτ : τp = τq
    · subst τq
      have hj_ne : jp ≠ jq := by
        intro hj
        apply hpq
        subst jq
        rfl
      exact (A.typeFiber_pairwiseDisjoint R hR shift hshift τp)
        (x := jp) (by simp) (y := jq) (by simp) hj_ne
    · show Disjoint (A.typeFiber R hR shift hshift τp jp)
        (A.typeFiber R hR shift hshift τq jq)
      rw [Finset.disjoint_left]
      intro x hx hy
      have hx_type := A.typeFiber_subset_type R hR shift hshift τp jp hx
      have hy_type := A.typeFiber_subset_type R hR shift hshift τq jq hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx_type hy_type
      exact hτ (hx_type.symm.trans hy_type)
  fiber_cover := by
    classical
    intro R hR shift hshift
    apply Finset.ext
    intro i
    constructor
    · intro _; exact Finset.mem_univ _
    · intro _hi
      let τ := (untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S) i
      have hiτ : i ∈ Finset.univ.filter
          (fun k => (untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S) k = τ) := by
        simp [τ]
      have hcover := A.typeFiber_cover_type R hR shift hshift τ
      have hiUnion : i ∈ (Finset.univ : Finset
          (Fin ((untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n)
            ((List.replicate R.length
              (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))).prod *
            (List.ofFn (fun k : Fin
              (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
                ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
                  ((untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S) k)] :
                    List (untouchedBackgroundAtomTraceLocalMonoid
                      (Nat.log 2 n)).localMonoid).prod)).prod)) τ))).biUnion
            (fun j => A.typeFiber R hR shift hshift τ j) := by
        rw [hcover]
        exact hiτ
      simp only [Finset.mem_biUnion] at hiUnion ⊢
      rcases hiUnion with ⟨j, hjmem, hij⟩
      refine ⟨⟨τ, j⟩, ?_, hij⟩
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hjmem⟩
  fiber_product_mem := A.typeFiber_product_mem
  shift_mlProj_closure_atomTraceProfile := A.shift_mlProj_closure_atomTraceProfile

/-- Fibre-product data supplies the slot-product seam. -/
noncomputable def untouchedBackgroundConcreteAtomTraceExactSlotProductLocalAlgebraRowsForList_of_fiberProduct
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ)
    (A : UntouchedBackgroundConcreteAtomTraceExactFiberProductLocalAlgebraRowsForList
      M n hn2 htb hns S B ℓ) :
    UntouchedBackgroundConcreteAtomTraceExactSlotProductLocalAlgebraRowsForList
      M n hn2 htb hns S B ℓ where
  slot := by
    intro R hR shift hshift
    dsimp
    intro τ j
    exact (A.fiber R hR shift hshift τ j).prod
      (fun i => (untouchedBackgroundFactorList M n hn2 htb hns S).get i)
  slot_mem := by
    intro R hR shift hshift
    dsimp
    intro τ j
    exact A.fiber_product_mem R hR shift hshift τ j
  product_eq := by
    intro R hR shift hshift
    exact untouchedBackground_prod_eq_twoLevelFiberProduct
      (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n)
        ((List.replicate R.length
          (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))).prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              ((untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S) i)] :
                List (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod))
      (A.fiber R hR shift hshift)
      (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
        (untouchedBackgroundFactorList M n hn2 htb hns S).get i)
      (A.fiber_pairwiseDisjoint R hR shift hshift)
      (A.fiber_cover R hR shift hshift)
  shift_mlProj_closure_atomTraceProfile := A.shift_mlProj_closure_atomTraceProfile

/-- Slot-product data proves the unshifted half of the local-algebra seam by
the existing Lemma-31 slot-product constructor, and carries over the independent
shift/`mlProj` closure field. -/
noncomputable def untouchedBackgroundConcreteAtomTraceExactLocalAlgebraRowsForList_of_slotProduct
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ)
    (A : UntouchedBackgroundConcreteAtomTraceExactSlotProductLocalAlgebraRowsForList
      M n hn2 htb hns S B ℓ) :
    UntouchedBackgroundConcreteAtomTraceExactLocalAlgebraRowsForList
      M n hn2 htb hns S B ℓ where
  unshifted_background_mem_atomTraceProfile := by
    intro R hR shift hshift
    rw [A.product_eq R hR shift hshift]
    exact profileProduct_mem_profileSubspace
      (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n)
        ((List.replicate R.length
          (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))).prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
              ((untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S) i)] :
                List (untouchedBackgroundAtomTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod))
      (zeroProfileConcreteLocalChart_compiledCoefficientBasis
        B (Nat.log 2 n) ℓ
        (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n)
          ((List.replicate R.length
            (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))).prod *
          (List.ofFn (fun i : Fin
            (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
              ([untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
                ((untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S) i)] :
                  List (untouchedBackgroundAtomTraceLocalMonoid
                    (Nat.log 2 n)).localMonoid).prod)).prod))).W
      (A.slot R hR shift hshift)
      (A.slot_mem R hR shift hshift)
  shift_mlProj_closure_atomTraceProfile := A.shift_mlProj_closure_atomTraceProfile

/-- The local-algebra split supplies the exact atom-trace compiled-chart row
theorem. -/
noncomputable def untouchedBackgroundConcreteAtomTraceExactCompiledChartRowsForList_of_localAlgebra
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ)
    (A : UntouchedBackgroundConcreteAtomTraceExactLocalAlgebraRowsForList
      M n hn2 htb hns S B ℓ) :
    UntouchedBackgroundConcreteAtomTraceExactCompiledChartRowsForList
      M n hn2 htb hns S B ℓ where
  row_mem_atomTraceProfile := by
    intro R hR shift hshift
    exact A.shift_mlProj_closure_atomTraceProfile R hR shift hshift
      (Finset.univ.prod
        (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
          (untouchedBackgroundFactorList M n hn2 htb hns S).get i))
      (A.unshifted_background_mem_atomTraceProfile R hR shift hshift)

/-- Exact-budget atom-trace row data instantiates the previous budgeted
compiled-chart row package. -/
noncomputable def untouchedBackgroundConcreteAtomTraceCompiledChartRowsForList_of_exact
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ)
    (A : UntouchedBackgroundConcreteAtomTraceExactCompiledChartRowsForList
      M n hn2 htb hns S B ℓ) :
    UntouchedBackgroundConcreteAtomTraceCompiledChartRowsForList
      M n hn2 htb hns S B ℓ
        (untouchedBackgroundAtomTraceExactTypeBudget n) where
  totalProfileBudget_le := by
    rfl
  row_mem_atomTraceProfile := by
    intro R hR shift hshift
    simpa using A.row_mem_atomTraceProfile R hR shift hshift

/-- The fully concrete atom trace theorem feeds directly into the raw-trace
normal-form classifier pipeline. -/
noncomputable def untouchedBackgroundProfileRawGeneratorTraceActionDataForList_of_atomTraceCompiledChartRows
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ) {typeBudget : ℕ}
    (A : UntouchedBackgroundConcreteAtomTraceCompiledChartRowsForList
      M n hn2 htb hns S B ℓ typeBudget) :
    UntouchedBackgroundProfileRawGeneratorTraceActionDataForList
      M n hn2 htb hns S typeBudget where
  monoid := untouchedBackgroundAtomTraceLocalMonoid (Nat.log 2 n)
  profile := untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n)
  profile_admissible := untouchedBackgroundAtomTraceActionProfile_admissible (Nat.log 2 n)
  chart := fun g => zeroProfileConcreteLocalChart_compiledCoefficientBasis
    B (Nat.log 2 n) ℓ (untouchedBackgroundAtomTraceActionProfile (Nat.log 2 n) g)
  totalProfileBudget_le := A.totalProfileBudget_le
  rawFactorWord := fun i =>
    [untouchedBackgroundAtomTraceFactorGenerator (Nat.log 2 n)
      (untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S i)]
  rawFactorWord_letters := by
    intro i a ha
    simp only [List.mem_singleton] at ha
    subst a
    exact untouchedBackgroundAtomTraceFactorGenerator_mem (Nat.log 2 n)
      (untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S i)
  rawShiftWord := fun R _hR _shift _hshift =>
    List.replicate R.length (untouchedBackgroundAtomTraceShiftGenerator (Nat.log 2 n))
  rawShiftWord_letters := by
    intro R hR shift hshift a ha
    simp only [List.mem_replicate] at ha
    rcases ha with ⟨_, haeq⟩
    subst a
    exact untouchedBackgroundAtomTraceShiftGenerator_mem (Nat.log 2 n)
  row_mem_rawWordProfile := by
    intro R hR shift hshift
    simpa using A.row_mem_atomTraceProfile R hR shift hshift

/-- Type-generator local alphabet data for the exact list-indexed untouched
background.

This is one step closer to the actual Cook--Levin gadget calculation than
arbitrary raw factor words: every untouched factor contributes the generator
attached to its real filtered Cook--Levin `ConstraintType`.  The only remaining
raw word freedom is the shift word, since shifts are column-side monomial data
rather than Cook--Levin constraint factors. -/
structure UntouchedBackgroundProfileTypeGeneratorActionDataForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  monoid : ZeroProfileFiniteLocalMonoid
  profile : monoid.localMonoid → ProfileHistogram
  profile_admissible :
    ∀ g, ProfileAdmissible (Nat.log 2 n) (profile g)
  chart : ∀ g, ZeroProfileConcreteLocalChart
    (cookLevinTableau M n hn2 htb hns).numVars (profile g)
  totalProfileBudget_le :
    (∑ g : monoid.localMonoid,
        zeroProfileSymmetricProfileDim (profile g)) ≤ typeBudget
  generatorOfType : ConstraintType → monoid.localMonoid
  generatorOfType_mem : ∀ τ, generatorOfType τ ∈ monoid.generators
  rawShiftWord :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      R.length ≤ Nat.log 2 n →
      ∀ shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
        shift.vars ⊆ R.toFinset → List monoid.localMonoid
  rawShiftWord_letters :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      ∀ a ∈ rawShiftWord R hR shift hshift, a ∈ monoid.generators
  row_mem_typeGeneratorProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let rowNF := (rawShiftWord R hR shift hshift).prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([generatorOfType (ctype i)] : List monoid.localMonoid).prod)).prod
      MultilinearSPDP.mlProj (shift *
          Finset.univ.prod
            (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
              (untouchedBackgroundFactorList M n hn2 htb hns S).get i)) ∈
        profileSubspace (profile rowNF) (chart rowNF).W

/-- Concrete constraint-type trace action data for the exact list-indexed
untouched background.

Unlike `UntouchedBackgroundProfileTypeGeneratorActionDataForList`, this fixes
the local monoid to the actual finite transformation monoid generated by the
four Cook--Levin `ConstraintType` append actions.  The open theorem is now only
the paper's local row-membership theorem for this concrete trace monoid. -/
structure UntouchedBackgroundConcreteConstraintTypeTraceActionDataForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (typeBudget : ℕ) where
  profile : (untouchedBackgroundConstraintTypeTraceLocalMonoid
      (Nat.log 2 n)).localMonoid → ProfileHistogram
  profile_admissible :
    ∀ g, ProfileAdmissible (Nat.log 2 n) (profile g)
  chart : ∀ g, ZeroProfileConcreteLocalChart
    (cookLevinTableau M n hn2 htb hns).numVars (profile g)
  totalProfileBudget_le :
    (∑ g : (untouchedBackgroundConstraintTypeTraceLocalMonoid
        (Nat.log 2 n)).localMonoid,
        zeroProfileSymmetricProfileDim (profile g)) ≤ typeBudget
  rawShiftWord :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      R.length ≤ Nat.log 2 n →
      ∀ shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
        shift.vars ⊆ R.toFinset →
          List (untouchedBackgroundConstraintTypeTraceLocalMonoid
            (Nat.log 2 n)).localMonoid
  rawShiftWord_letters :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      ∀ a ∈ rawShiftWord R hR shift hshift,
        a ∈ (untouchedBackgroundConstraintTypeTraceLocalMonoid
          (Nat.log 2 n)).generators
  row_mem_concreteTypeTraceProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let rowNF := (rawShiftWord R hR shift hshift).prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundConstraintTypeTraceGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundConstraintTypeTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      MultilinearSPDP.mlProj (shift *
          Finset.univ.prod
            (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
              (untouchedBackgroundFactorList M n hn2 htb hns S).get i)) ∈
        profileSubspace (profile rowNF) (chart rowNF).W

/-- Fully concrete compiled-chart row theorem for the exact list-indexed
untouched background.

This fixes both ingredients that were previously parameters: the profile is the
histogram read from the concrete type-trace action on the empty trace, and the
chart is the in-repo compiled coefficient-basis chart of paper §9.  The only
remaining field is the genuine local row-membership theorem for the exact
filtered untouched Cook--Levin product. -/
structure UntouchedBackgroundConcreteConstraintTypeTraceCompiledChartRowsForList
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ typeBudget : ℕ) where
  totalProfileBudget_le :
    (∑ g : (untouchedBackgroundConstraintTypeTraceLocalMonoid
        (Nat.log 2 n)).localMonoid,
        zeroProfileSymmetricProfileDim
          (untouchedBackgroundConstraintTypeTraceActionProfile (Nat.log 2 n) g)) ≤
      typeBudget
  rawShiftWord :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      R.length ≤ Nat.log 2 n →
      ∀ shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ,
        shift.vars ⊆ R.toFinset →
          List (untouchedBackgroundConstraintTypeTraceLocalMonoid
            (Nat.log 2 n)).localMonoid
  rawShiftWord_letters :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      ∀ a ∈ rawShiftWord R hR shift hshift,
        a ∈ (untouchedBackgroundConstraintTypeTraceLocalMonoid
          (Nat.log 2 n)).generators
  row_mem_compiledTypeTraceProfile :
    ∀ (R : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (hR : R.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (hshift : shift.vars ⊆ R.toFinset),
      let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
      let rowNF := (rawShiftWord R hR shift hshift).prod *
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            ([untouchedBackgroundConstraintTypeTraceGenerator (Nat.log 2 n)
              (ctype i)] : List
                (untouchedBackgroundConstraintTypeTraceLocalMonoid
                  (Nat.log 2 n)).localMonoid).prod)).prod
      MultilinearSPDP.mlProj (shift *
          Finset.univ.prod
            (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
              (untouchedBackgroundFactorList M n hn2 htb hns S).get i)) ∈
        profileSubspace
          (untouchedBackgroundConstraintTypeTraceActionProfile (Nat.log 2 n) rowNF)
          (zeroProfileConcreteLocalChart_compiledCoefficientBasis
            B (Nat.log 2 n) ℓ
            (untouchedBackgroundConstraintTypeTraceActionProfile
              (Nat.log 2 n) rowNF)).W

/-- Package the fully concrete compiled-chart row theorem as the existing
concrete type-trace action data. -/
noncomputable def untouchedBackgroundConcreteConstraintTypeTraceActionDataForList_of_compiledChartRows
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ) {typeBudget : ℕ}
    (A : UntouchedBackgroundConcreteConstraintTypeTraceCompiledChartRowsForList
      M n hn2 htb hns S B ℓ typeBudget) :
    UntouchedBackgroundConcreteConstraintTypeTraceActionDataForList
      M n hn2 htb hns S typeBudget where
  profile := untouchedBackgroundConstraintTypeTraceActionProfile (Nat.log 2 n)
  profile_admissible :=
    untouchedBackgroundConstraintTypeTraceActionProfile_admissible (Nat.log 2 n)
  chart := fun g => zeroProfileConcreteLocalChart_compiledCoefficientBasis
    B (Nat.log 2 n) ℓ
    (untouchedBackgroundConstraintTypeTraceActionProfile (Nat.log 2 n) g)
  totalProfileBudget_le := A.totalProfileBudget_le
  rawShiftWord := A.rawShiftWord
  rawShiftWord_letters := A.rawShiftWord_letters
  row_mem_concreteTypeTraceProfile := by
    intro R hR shift hshift
    simpa using A.row_mem_compiledTypeTraceProfile R hR shift hshift

/-- Forget the fixed concrete type-trace monoid into the general type-generator
surface. -/
noncomputable def untouchedBackgroundProfileTypeGeneratorActionDataForList_of_concreteTypeTraceActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (A : UntouchedBackgroundConcreteConstraintTypeTraceActionDataForList
      M n hn2 htb hns S typeBudget) :
    UntouchedBackgroundProfileTypeGeneratorActionDataForList
      M n hn2 htb hns S typeBudget where
  monoid := untouchedBackgroundConstraintTypeTraceLocalMonoid (Nat.log 2 n)
  profile := A.profile
  profile_admissible := A.profile_admissible
  chart := A.chart
  totalProfileBudget_le := A.totalProfileBudget_le
  generatorOfType := untouchedBackgroundConstraintTypeTraceGenerator (Nat.log 2 n)
  generatorOfType_mem :=
    untouchedBackgroundConstraintTypeTraceGenerator_mem (Nat.log 2 n)
  rawShiftWord := A.rawShiftWord
  rawShiftWord_letters := A.rawShiftWord_letters
  row_mem_typeGeneratorProfile := by
    intro R hR shift hshift
    simpa using A.row_mem_concreteTypeTraceProfile R hR shift hshift

/-- The type-generator alphabet data induces raw generator traces by assigning
each exact untouched factor the singleton word consisting of its real filtered
Cook--Levin type generator. -/
noncomputable def untouchedBackgroundProfileRawGeneratorTraceActionDataForList_of_typeGeneratorActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (A : UntouchedBackgroundProfileTypeGeneratorActionDataForList
      M n hn2 htb hns S typeBudget) :
    UntouchedBackgroundProfileRawGeneratorTraceActionDataForList
      M n hn2 htb hns S typeBudget where
  monoid := A.monoid
  profile := A.profile
  profile_admissible := A.profile_admissible
  chart := A.chart
  totalProfileBudget_le := A.totalProfileBudget_le
  rawFactorWord := fun i =>
    [A.generatorOfType
      (untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S i)]
  rawFactorWord_letters := by
    intro i a ha
    simp only [List.mem_singleton] at ha
    subst a
    exact A.generatorOfType_mem
      (untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S i)
  rawShiftWord := A.rawShiftWord
  rawShiftWord_letters := A.rawShiftWord_letters
  row_mem_rawWordProfile := by
    intro R hR shift hshift
    simpa using A.row_mem_typeGeneratorProfile R hR shift hshift

/-- Raw witnessed generator traces transport to shortlex-normalized traces by
`NFOfWord_represents`.  This is the exact §9.3 separation between local gadget
semantics and canonical normal-form selection. -/
noncomputable def untouchedBackgroundProfileLocalNFGeneratorActionDataForList_of_rawTraceActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (T : UntouchedBackgroundProfileRawGeneratorTraceActionDataForList
      M n hn2 htb hns S typeBudget) :
    UntouchedBackgroundProfileLocalNFGeneratorActionDataForList
      M n hn2 htb hns S typeBudget where
  monoid := T.monoid
  profile := T.profile
  profile_admissible := T.profile_admissible
  chart := T.chart
  totalProfileBudget_le := T.totalProfileBudget_le
  rawFactorWord := T.rawFactorWord
  rawFactorWord_letters := T.rawFactorWord_letters
  rawShiftWord := T.rawShiftWord
  rawShiftWord_letters := T.rawShiftWord_letters
  row_mem_NFOfWordProfile := by
    intro R hR shift hshift
    have hshiftProd :
        (PallLean.Paper93.NFOfWord T.monoid.generators
          (T.rawShiftWord R hR shift hshift)).prod =
          (T.rawShiftWord R hR shift hshift).prod :=
      PallLean.Paper93.NFOfWord_represents T.monoid.generators
        (T.rawShiftWord R hR shift hshift)
    have hfactorFun :
        (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            (PallLean.Paper93.NFOfWord T.monoid.generators
              (T.rawFactorWord i)).prod) =
          (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            (T.rawFactorWord i).prod) := by
      funext i
      exact PallLean.Paper93.NFOfWord_represents T.monoid.generators
        (T.rawFactorWord i)
    have hfactorProd :
        (List.ofFn (fun i : Fin
          (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            (PallLean.Paper93.NFOfWord T.monoid.generators
              (T.rawFactorWord i)).prod)).prod =
          (List.ofFn (fun i : Fin
            (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            (T.rawFactorWord i).prod)).prod := by
      simp [hfactorFun]
    have hrowNF :
        (PallLean.Paper93.NFOfWord T.monoid.generators
            (T.rawShiftWord R hR shift hshift)).prod *
          (List.ofFn (fun i : Fin
            (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
              (PallLean.Paper93.NFOfWord T.monoid.generators
                (T.rawFactorWord i)).prod)).prod =
        (T.rawShiftWord R hR shift hshift).prod *
          (List.ofFn (fun i : Fin
            (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
              (T.rawFactorWord i).prod)).prod := by
      rw [hshiftProd, hfactorProd]
    rw [hrowNF]
    exact T.row_mem_rawWordProfile R hR shift hshift

/-- Shortlex-normalized trace data induces ordered local-monoid action data by
using the normalized factor and shift products as the selected local actions. -/
noncomputable def untouchedBackgroundProfileLocalMonoidActionDataForList_of_NFGeneratorActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (NFD : UntouchedBackgroundProfileLocalNFGeneratorActionDataForList
      M n hn2 htb hns S typeBudget) :
    UntouchedBackgroundProfileLocalMonoidActionDataForList
      M n hn2 htb hns S typeBudget where
  monoid := NFD.monoid
  profile := NFD.profile
  profile_admissible := NFD.profile_admissible
  chart := NFD.chart
  totalProfileBudget_le := NFD.totalProfileBudget_le
  factorElement := fun i =>
    (PallLean.Paper93.NFOfWord NFD.monoid.generators
      (NFD.rawFactorWord i)).prod
  shiftElement := fun R hR shift hshift =>
    (PallLean.Paper93.NFOfWord NFD.monoid.generators
      (NFD.rawShiftWord R hR shift hshift)).prod
  row_mem_productProfile := by
    intro R hR shift hshift
    exact NFD.row_mem_NFOfWordProfile R hR shift hshift

/-- Ordered local-monoid action data constructs the profile-aware list-indexed
classifier by using the ordered product normal form as the row classifier. -/
noncomputable def untouchedBackgroundProfileLocalMonoidClassifierForList_of_actionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (A : UntouchedBackgroundProfileLocalMonoidActionDataForList
      M n hn2 htb hns S typeBudget) :
    UntouchedBackgroundProfileLocalMonoidConcreteClassifierForList
      M n hn2 htb hns S typeBudget where
  monoid := A.monoid
  profile := A.profile
  profile_admissible := A.profile_admissible
  chart := A.chart
  totalProfileBudget_le := A.totalProfileBudget_le
  rowMap :=
    { rowNormalForm := fun R hR shift hshift =>
        A.shiftElement R hR shift hshift * (List.ofFn A.factorElement).prod
      projected_row_mem_profileSubspace := by
        intro R hR shift hshift
        simpa [untouchedBackgroundConcreteDataOfLocalMonoidProfiles,
          LinearMap.id_apply] using
          A.row_mem_productProfile R hR shift hshift }

/-- Raw profile-aware generator traces directly produce the list-indexed
profile-aware concrete classifier. -/
noncomputable def untouchedBackgroundProfileLocalMonoidClassifierForList_of_rawTraceActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (T : UntouchedBackgroundProfileRawGeneratorTraceActionDataForList
      M n hn2 htb hns S typeBudget) :
    UntouchedBackgroundProfileLocalMonoidConcreteClassifierForList
      M n hn2 htb hns S typeBudget :=
  untouchedBackgroundProfileLocalMonoidClassifierForList_of_actionData
    M n hn2 htb hns S
    (untouchedBackgroundProfileLocalMonoidActionDataForList_of_NFGeneratorActionData
      M n hn2 htb hns S
      (untouchedBackgroundProfileLocalNFGeneratorActionDataForList_of_rawTraceActionData
        M n hn2 htb hns S T))

/-- Raw profile-aware generator traces directly produce the downstream concrete
normal-form classifier used by the touched/background Route B bridge. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifierForList_of_profileRawTraceActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (T : UntouchedBackgroundProfileRawGeneratorTraceActionDataForList
      M n hn2 htb hns S typeBudget) :
    UntouchedBackgroundConcreteNormalFormClassifierForList
      M n hn2 htb hns S typeBudget :=
  untouchedBackgroundConcreteNormalFormClassifierForList_of_profileLocalMonoidClassifier
    M n hn2 htb hns S
    (untouchedBackgroundProfileLocalMonoidClassifierForList_of_rawTraceActionData
      M n hn2 htb hns S T)

/-- Type-generator alphabet data directly supplies the downstream concrete
normal-form classifier, while keeping all untouched factor types visible. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifierForList_of_profileTypeGeneratorActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (A : UntouchedBackgroundProfileTypeGeneratorActionDataForList
      M n hn2 htb hns S typeBudget) :
    UntouchedBackgroundConcreteNormalFormClassifierForList
      M n hn2 htb hns S typeBudget :=
  untouchedBackgroundConcreteNormalFormClassifierForList_of_profileRawTraceActionData
    M n hn2 htb hns S
    (untouchedBackgroundProfileRawGeneratorTraceActionDataForList_of_typeGeneratorActionData
      M n hn2 htb hns S A)

/-- Concrete atom-trace compiled-chart data directly supplies the downstream
normal-form classifier with both factor and shift atoms fixed in the finite
local alphabet. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifierForList_of_atomTraceCompiledChartRows
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : SPDP.BlockPartition (cookLevinTableau M n hn2 htb hns).numVars)
    (ℓ : ℕ) {typeBudget : ℕ}
    (A : UntouchedBackgroundConcreteAtomTraceCompiledChartRowsForList
      M n hn2 htb hns S B ℓ typeBudget) :
    UntouchedBackgroundConcreteNormalFormClassifierForList
      M n hn2 htb hns S typeBudget :=
  untouchedBackgroundConcreteNormalFormClassifierForList_of_profileRawTraceActionData
    M n hn2 htb hns S
    (untouchedBackgroundProfileRawGeneratorTraceActionDataForList_of_atomTraceCompiledChartRows
      M n hn2 htb hns S B ℓ A)

/-- Concrete constraint-type trace action data directly supplies the downstream
normal-form classifier; this is the fixed finite local alphabet/action seam for
the exact filtered untouched background. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifierForList_of_concreteTypeTraceActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (A : UntouchedBackgroundConcreteConstraintTypeTraceActionDataForList
      M n hn2 htb hns S typeBudget) :
    UntouchedBackgroundConcreteNormalFormClassifierForList
      M n hn2 htb hns S typeBudget :=
  untouchedBackgroundConcreteNormalFormClassifierForList_of_profileTypeGeneratorActionData
    M n hn2 htb hns S
    (untouchedBackgroundProfileTypeGeneratorActionDataForList_of_concreteTypeTraceActionData
      M n hn2 htb hns S A)

/-- Final convenience constructor: a list-indexed §9.3 local-monoid/profile
action theorem directly supplies the exact untouched-background concrete
normal-form classifier used by Route B. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifierForList_of_profileLocalMonoidActionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    {typeBudget : ℕ}
    (A : UntouchedBackgroundProfileLocalMonoidActionDataForList
      M n hn2 htb hns S typeBudget) :
    UntouchedBackgroundConcreteNormalFormClassifierForList
      M n hn2 htb hns S typeBudget :=
  untouchedBackgroundConcreteNormalFormClassifierForList_of_profileLocalMonoidClassifier
    M n hn2 htb hns S
    (untouchedBackgroundProfileLocalMonoidClassifierForList_of_actionData
      M n hn2 htb hns S A)


/-- A list-indexed zero-profile post-span containment constructs the concrete
row classifier for the exact filtered untouched background over the original
row list `S`. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifierForList_of_zeroProfilePostSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hpost :
      WithinProfileBound.allBoundedProfilePostSpan
          (cookLevinTableau M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
            (untouchedBackgroundFactorList M n hn2 htb hns S).get i)
          (untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S)
          zeroProfileHistogram
        ≤ profileSubspace zeroProfileHistogram
            (zeroProfileConcreteLocalChart_concreteW
              (n := (cookLevinTableau M n hn2 htb hns).numVars)
              hn4 zeroProfileHistogram).W) :
    UntouchedBackgroundConcreteNormalFormClassifierForList M n hn2 htb hns S
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) where
  data := zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
    (n := (cookLevinTableau M n hn2 htb hns).numVars)
    (κ := Nat.log 2 n) hn4
  rowMap := by
    classical
    refine
      { rowNormalForm := fun _ _ _ _ => PUnit.unit
        projected_row_mem_profileSubspace := ?_ }
    intro R hR shift hshift
    let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length →
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
      fun i => (untouchedBackgroundFactorList M n hn2 htb hns S).get i
    let ctype := untouchedBackgroundConstraintTypeFamilyForList M n hn2 htb hns S
    have hrowSet :
        MultilinearSPDP.mlProj (shift * Finset.univ.prod factors) ∈
          zeroProfileShiftImageSet (Nat.log 2 n) factors := by
      simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
        Set.mem_singleton_iff]
      exact ⟨R, hR, shift, hshift, rfl⟩
    have hrowPost :
        MultilinearSPDP.mlProj (shift * Finset.univ.prod factors) ∈
          WithinProfileBound.allBoundedProfilePostSpan
            (cookLevinTableau M n hn2 htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            factors ctype zeroProfileHistogram := by
      rw [allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan
        (cookLevinTableau M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) factors ctype]
      exact Submodule.subset_span hrowSet
    have hmem :
        MultilinearSPDP.mlProj (shift * Finset.univ.prod factors) ∈
          profileSubspace zeroProfileHistogram
            (zeroProfileConcreteLocalChart_concreteW
              (n := (cookLevinTableau M n hn2 htb hns).numVars)
              hn4 zeroProfileHistogram).W := by
      exact hpost hrowPost
    simpa [LinearMap.id_apply, factors, ctype,
      zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW,
      zeroProfileConcreteNormalFormData_singletonZeroProfile] using hmem

/-- The list-indexed paper §9.3 zero-profile per-generator theorem constructs
the concrete untouched-background classifier for the exact list `S`. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifierForList_of_zeroProfilePerTypeSpanning
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hspan : UntouchedBackgroundZeroProfilePerTypeSpanning_concreteW_forList
      M n hn2 htb hns hn4 S) :
    UntouchedBackgroundConcreteNormalFormClassifierForList M n hn2 htb hns S
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  untouchedBackgroundConcreteNormalFormClassifierForList_of_zeroProfilePostSpan
    M n hn2 htb hns hn4 S
    (untouchedBackgroundZeroProfilePostSpan_le_of_perTypeSpanning_concreteW_forList
      M n hn2 htb hns hn4 S hspan)

/-- List-indexed shifted-base-product control constructs the concrete
untouched-background classifier for the exact list `S`. -/
noncomputable def untouchedBackgroundConcreteNormalFormClassifierForList_of_zeroProfileShiftRows
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : (cookLevinTableau M n hn2 htb hns).numVars ≥ 4)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hshiftRows : UntouchedBackgroundZeroProfileShiftRows_concreteW_forList
      M n hn2 htb hns hn4 S) :
    UntouchedBackgroundConcreteNormalFormClassifierForList M n hn2 htb hns S
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  untouchedBackgroundConcreteNormalFormClassifierForList_of_zeroProfilePerTypeSpanning
    M n hn2 htb hns hn4 S
    (untouchedBackgroundZeroProfilePerTypeSpanning_of_shiftRows_concreteW_forList
      M n hn2 htb hns hn4 S hshiftRows)

/-- A list-indexed concrete classifier induces the projected normal-form row map
needed by the list-faithful touched/background product bridge. -/
noncomputable def UntouchedBackgroundConcreteNormalFormClassifierForList.toProjectedRowMap
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)}
    {typeBudget : ℕ}
    (C : UntouchedBackgroundConcreteNormalFormClassifierForList
      M n hn2 htb hns S typeBudget) :
    ZeroProfileProjectedNormalFormRowMap
      (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
        (untouchedBackgroundFactorList M n hn2 htb hns S).get i)
      (LinearMap.id :
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
          MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (zeroProfileProjectedNormalFormFamily_of_concreteData C.data) :=
  zeroProfileProjectedNormalFormRowMap_of_concreteRowMap
    (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length =>
      (untouchedBackgroundFactorList M n hn2 htb hns S).get i)
    (LinearMap.id :
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    C.data C.rowMap

/-- A list-indexed concrete §9.3 untouched-background classifier supplies the
exact background normal-form span used by the list-faithful touched/local
Khatri--Rao product basis. -/
theorem touchedMonomialSplitRow_mem_rowWindowProductBasis_of_concreteBackgroundConcreteNormalForm_list
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S.toFinset)
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S → alloc i = [])
    {typeBudget : ℕ}
    (C : UntouchedBackgroundConcreteNormalFormClassifierForList
      M n hn2 htb hns S typeBudget) :
    touchedMonomialSplitRow M n hn2 htb hns S T alloc ∈
      Submodule.span ℚ
        (↑(mlProjProductBasis
          (MlProjFar.mlMonomialBasis
            (cookLevinRowLocalWindow M n hn2 htb hns S))
          (zeroProfileProjectedNormalFormGlobalBasis
            (zeroProfileProjectedNormalFormFamily_of_concreteData C.data))) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  let factors : Fin (untouchedBackgroundFactorList M n hn2 htb hns S).length →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
    fun i => (untouchedBackgroundFactorList M n hn2 htb hns S).get i
  let F := zeroProfileProjectedNormalFormFamily_of_concreteData C.data
  have hB :
      MultilinearSPDP.mlProj
          (untouchedBackgroundProduct M n hn2 htb hns S) ∈
        Submodule.span ℚ
          (↑(zeroProfileProjectedNormalFormGlobalBasis F) : Set
            (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
    exact mlProj_untouchedBackground_mem_normalFormGlobalBasis_of_idRowMap
      M n hn2 htb hns S factors F C.toProjectedRowMap
      (untouchedBackgroundFactorFamily_prod_eq M n hn2 htb hns S)
  exact touchedMonomialSplitRow_mem_rowWindowProductBasis_of_projectedBackgroundSpan_list
    M n hn2 htb hns S T alloc hT hout
    (zeroProfileProjectedNormalFormGlobalBasis F) hB

/-- The list-indexed concrete classifier's global projected basis obeys its
concrete profile/symmetric-power budget. -/
theorem untouchedBackgroundConcreteNormalFormForListGlobalBasis_card_le
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)}
    {typeBudget : ℕ}
    (C : UntouchedBackgroundConcreteNormalFormClassifierForList
      M n hn2 htb hns S typeBudget) :
    (zeroProfileProjectedNormalFormGlobalBasis
      (zeroProfileProjectedNormalFormFamily_of_concreteData C.data)).card ≤
        typeBudget :=
  zeroProfileProjectedNormalFormGlobalBasis_card_le_typeBudget
    (zeroProfileProjectedNormalFormFamily_of_concreteData C.data)

/-- The same concrete classifier induces the projected normal-form row map
needed by the touched/background product-composition theorem. -/
noncomputable def UntouchedBackgroundConcreteNormalFormClassifier.toProjectedRowMap
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars)}
    {typeBudget : ℕ}
    (C : UntouchedBackgroundConcreteNormalFormClassifier
      M n hn2 htb hns S typeBudget) :
    ZeroProfileProjectedNormalFormRowMap
      (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length =>
        (untouchedBackgroundFactorList M n hn2 htb hns S.toList).get i)
      (LinearMap.id :
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
          MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (zeroProfileProjectedNormalFormFamily_of_concreteData C.data) :=
  zeroProfileProjectedNormalFormRowMap_of_concreteRowMap
    (fun i : Fin (untouchedBackgroundFactorList M n hn2 htb hns S.toList).length =>
      (untouchedBackgroundFactorList M n hn2 htb hns S.toList).get i)
    (LinearMap.id :
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
        MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    C.data C.rowMap

/-- A concrete §9.3 untouched-background classifier supplies the exact
background normal-form span used by the touched/local Khatri--Rao product
basis. -/
theorem touchedMonomialSplitRow_mem_rowWindowProductBasis_of_concreteBackgroundConcreteNormalForm
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S)
    (hout : ∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S.toList → alloc i = [])
    {typeBudget : ℕ}
    (C : UntouchedBackgroundConcreteNormalFormClassifier
      M n hn2 htb hns S typeBudget) :
    touchedMonomialSplitRow M n hn2 htb hns S.toList T alloc ∈
      Submodule.span ℚ
        (↑(mlProjProductBasis
          (MlProjFar.mlMonomialBasis
            (cookLevinRowLocalWindow M n hn2 htb hns S.toList))
          (zeroProfileProjectedNormalFormGlobalBasis
            (zeroProfileProjectedNormalFormFamily_of_concreteData C.data))) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  exact touchedMonomialSplitRow_mem_rowWindowProductBasis_of_concreteBackgroundNormalForm
    M n hn2 htb hns S T alloc hT hout
    (zeroProfileProjectedNormalFormFamily_of_concreteData C.data)
    C.toProjectedRowMap

/-- The concrete classifier's global projected basis obeys its concrete
profile/symmetric-power budget. -/
theorem untouchedBackgroundConcreteNormalFormGlobalBasis_card_le
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars)}
    {typeBudget : ℕ}
    (C : UntouchedBackgroundConcreteNormalFormClassifier
      M n hn2 htb hns S typeBudget) :
    (zeroProfileProjectedNormalFormGlobalBasis
      (zeroProfileProjectedNormalFormFamily_of_concreteData C.data)).card ≤
        typeBudget :=
  zeroProfileProjectedNormalFormGlobalBasis_card_le_typeBudget
    (zeroProfileProjectedNormalFormFamily_of_concreteData C.data)

/-- At paper scale, a concrete §9.3 classifier with polynomial profile budget
gives the touched/background product-basis polynomial budget. -/
theorem rowWindowBackgroundConcreteNormalFormProductBasis_card_le_pow_add
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hS : S.card ≤ Nat.log 2 n)
    {typeBudget Cexp : ℕ}
    (C : UntouchedBackgroundConcreteNormalFormClassifier
      M n hn2 htb hns S typeBudget)
    (hbudget : typeBudget ≤ n ^ Cexp) :
    (mlProjProductBasis
      (MlProjFar.mlMonomialBasis
        (cookLevinRowLocalWindow M n hn2 htb hns S.toList))
      (zeroProfileProjectedNormalFormGlobalBasis
        (zeroProfileProjectedNormalFormFamily_of_concreteData C.data))).card ≤
        n ^ (200 + Cexp) := by
  exact rowWindowProductBasis_card_le_pow_add_budget
    M n hn hn2 htb hns S hS
    (zeroProfileProjectedNormalFormGlobalBasis
      (zeroProfileProjectedNormalFormFamily_of_concreteData C.data))
    ((untouchedBackgroundConcreteNormalFormGlobalBasis_card_le C).trans hbudget)

/-- At paper scale, if the normal-form family budget is itself bounded by
`n^C`, then the combined touched/background product basis has size
`n^(200+C)`. -/
theorem rowWindowBackgroundNormalFormProductBasis_card_le_pow_add
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hS : S.card ≤ Nat.log 2 n)
    {typeBudget C : ℕ}
    (F : ZeroProfileProjectedNormalFormFamily
      (cookLevinTableau M n hn2 htb hns).numVars (Nat.log 2 n) typeBudget)
    (hbudget : typeBudget ≤ n ^ C) :
    (mlProjProductBasis
      (MlProjFar.mlMonomialBasis
        (cookLevinRowLocalWindow M n hn2 htb hns S.toList))
      (zeroProfileProjectedNormalFormGlobalBasis F)).card ≤
        n ^ (200 + C) := by
  exact rowWindowProductBasis_card_le_pow_add_budget
    M n hn hn2 htb hns S hS
    (zeroProfileProjectedNormalFormGlobalBasis F)
    ((zeroProfileProjectedNormalFormGlobalBasis_card_le_typeBudget F).trans hbudget)

/-! ## Axiom audit anchors -/

#print axioms untouchedBackgroundConstraintIdxList_map_factor_eq
#print axioms untouchedBackgroundConcreteNormalFormClassifier_of_zeroProfilePostSpan
#print axioms untouchedBackgroundZeroProfilePostSpan_le_of_perTypeSpanning_concreteW
#print axioms untouchedBackgroundZeroProfileShiftRows_of_perTypeSpanning_concreteW
#print axioms untouchedBackgroundZeroProfilePerTypeSpanning_of_shiftRows_concreteW
#print axioms untouchedBackgroundConcreteNormalFormClassifier_of_zeroProfileShiftRows
#print axioms untouchedBackgroundRawTraceActionData_of_shiftRows_and_words
#print axioms untouchedBackgroundConcreteNormalFormClassifier_of_shiftRows_and_words
#print axioms untouchedBackgroundLocalNFGeneratorActionData_of_rawTraceActionData
#print axioms untouchedBackgroundConcreteNormalFormClassifier_of_rawTraceActionData
#print axioms untouchedBackgroundLocalGeneratorActionData_of_NFGeneratorActionData
#print axioms untouchedBackgroundConcreteNormalFormClassifier_of_localNFGeneratorActionData
#print axioms untouchedBackgroundLocalMonoidActionData_of_generatorActionData
#print axioms untouchedBackgroundConcreteNormalFormClassifier_of_localGeneratorActionData
#print axioms untouchedBackgroundLocalMonoidConcreteClassifier_of_actionData
#print axioms untouchedBackgroundConcreteNormalFormClassifier_of_localMonoidActionData
#print axioms untouchedBackgroundZeroProfileShiftRows_of_localMonoidConcreteClassifier
#print axioms untouchedBackgroundConcreteNormalFormClassifier_of_localMonoidConcreteClassifier
#print axioms untouchedBackgroundConcreteNormalFormClassifier_of_zeroProfilePerTypeSpanning
#print axioms UntouchedBackgroundConcreteNormalFormClassifier.toFiniteClassifier
#print axioms UntouchedBackgroundConcreteNormalFormClassifier.toProjectedRowMap
#print axioms untouchedBackgroundConstraintTypeFamilyForList
#print axioms untouchedBackgroundZeroProfileShiftRows_of_perTypeSpanning_concreteW_forList
#print axioms untouchedBackgroundZeroProfilePerTypeSpanning_of_shiftRows_concreteW_forList
#print axioms untouchedBackgroundZeroProfilePostSpan_le_of_perTypeSpanning_concreteW_forList
#print axioms untouchedBackgroundConcreteNormalFormClassifierForList_of_zeroProfilePostSpan
#print axioms untouchedBackgroundConcreteNormalFormClassifierForList_of_zeroProfilePerTypeSpanning
#print axioms untouchedBackgroundConcreteDataOfLocalMonoidProfiles
#print axioms untouchedBackgroundAtomTraceProfile_admissible
#print axioms untouchedBackgroundAtomTraceActionProfile_admissible
#print axioms untouchedBackgroundAtomTraceExactTypeBudget
#print axioms untouchedBackgroundConcreteAtomTraceExactCompiledChartRowsForList_of_localAlgebra
#print axioms untouchedBackgroundConcreteAtomTraceCompiledChartRowsForList_of_exact
#print axioms untouchedBackgroundProfileRawGeneratorTraceActionDataForList_of_atomTraceCompiledChartRows
#print axioms untouchedBackgroundConcreteNormalFormClassifierForList_of_atomTraceCompiledChartRows
#print axioms untouchedBackgroundConstraintTypeTraceProfile_admissible
#print axioms untouchedBackgroundConstraintTypeTraceActionProfile_admissible
#print axioms untouchedBackgroundConcreteConstraintTypeTraceActionDataForList_of_compiledChartRows
#print axioms untouchedBackgroundProfileTypeGeneratorActionDataForList_of_concreteTypeTraceActionData
#print axioms untouchedBackgroundConcreteNormalFormClassifierForList_of_concreteTypeTraceActionData
#print axioms untouchedBackgroundProfileRawGeneratorTraceActionDataForList_of_typeGeneratorActionData
#print axioms untouchedBackgroundConcreteNormalFormClassifierForList_of_profileTypeGeneratorActionData
#print axioms untouchedBackgroundProfileLocalNFGeneratorActionDataForList_of_rawTraceActionData
#print axioms untouchedBackgroundProfileLocalMonoidActionDataForList_of_NFGeneratorActionData
#print axioms untouchedBackgroundProfileLocalMonoidClassifierForList_of_rawTraceActionData
#print axioms untouchedBackgroundConcreteNormalFormClassifierForList_of_profileRawTraceActionData
#print axioms untouchedBackgroundConcreteNormalFormClassifierForList_of_profileLocalMonoidClassifier
#print axioms untouchedBackgroundProfileLocalMonoidClassifierForList_of_actionData
#print axioms untouchedBackgroundConcreteNormalFormClassifierForList_of_profileLocalMonoidActionData
#print axioms untouchedBackgroundConcreteNormalFormClassifierForList_of_zeroProfileShiftRows
#print axioms UntouchedBackgroundConcreteNormalFormClassifierForList.toProjectedRowMap
#print axioms touchedMonomialSplitRow_mem_rowWindowProductBasis_of_concreteBackgroundConcreteNormalForm_list
#print axioms untouchedBackgroundConcreteNormalFormForListGlobalBasis_card_le
#print axioms mlProj_touchedMonomialLocalPart_mem_rowWindowMonomialSpan_list
#print axioms touchedMonomialSplitRow_mem_rowWindowProductBasis_of_projectedBackgroundSpan_list
#print axioms touchedMonomialSplitRow_mem_rowWindowProductBasis_of_concreteBackgroundConcreteNormalForm
#print axioms untouchedBackgroundConcreteNormalFormGlobalBasis_card_le
#print axioms rowWindowBackgroundConcreteNormalFormProductBasis_card_le_pow_add
#print axioms untouchedBackgroundFactorList_prod_eq
#print axioms untouchedBackgroundFactorFamily_prod_eq
#print axioms mlProj_product_mem_normalFormGlobalBasis_of_idRowMap
#print axioms mlProj_untouchedBackground_mem_normalFormGlobalBasis_of_idRowMap
#print axioms untouchedBackgroundNormalFormGlobalBasis_card_le
#print axioms touchedMonomialSplitRow_mem_rowWindowProductBasis_of_backgroundNormalForm
#print axioms touchedMonomialSplitRow_mem_rowWindowProductBasis_of_concreteBackgroundNormalForm
#print axioms rowWindowBackgroundNormalFormProductBasis_card_le_pow_add

end PallLean.Paper93.DeepMath.PathB
