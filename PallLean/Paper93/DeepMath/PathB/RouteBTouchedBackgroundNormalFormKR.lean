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
