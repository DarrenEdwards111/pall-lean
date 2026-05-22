import PallLean.Paper93.DeepMath.PathC.PiPlusDistributedStabilityAllocationFactors
import PallLean.Paper93.DeepMath.PathC.PiPlusPaperRemark21MultilinearizeRank
import PallLean.Paper93.Lemma31ProfileSubspaceCompiledBasis
import PallLean.Paper93.Closure.ShiftClosure

/-!
# Allocated product normalization at the rank level

This file composes the exact allocated-product Boolean normalization theorem with
Remark 21's rank-level multilinearization inequality.  The point is deliberately
narrow: the normalized factor product is the Boolean representative of the
allocated derivative product, while the rank bound is paid for at the raw
allocated-product row space.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open WithinProfileBound
open SymmetricPowerBound
open PallLean.Paper93.Closure

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- The normalized product of the individually normalized allocated derivative
factors, kept as an expression-level abbreviation so later row-certificate
lemmas can point to the exact product that appears after quotient
normalization. -/
noncomputable abbrev piPlusBooleanProjectedAllocatedNormalizedFactorProduct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ :=
  Finset.univ.prod (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
      M n hn2 htb hns D).length =>
    zeroProfileBooleanNormalize
      (iterDerivList (alloc i)
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D)[i.val]))

/-- Exact Boolean-representative statement for the allocated Leibniz product:
multilinearizing the allocated derivative product is the same Boolean object as
multilinearizing the product of the normalized local derivative factors. -/
theorem multilinearize_allocatedDerivativeProduct_eq_normalizedFactorProduct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    multilinearize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) =
      multilinearize
        (piPlusBooleanProjectedAllocatedNormalizedFactorProduct
          M n hn2 htb hns D alloc) := by
  apply BoolPoly.ext
  simp only [coe_multilinearize]
  exact zeroProfileBooleanNormalize_allocatedDerivativeProduct_eq_normalizedFactorProduct
    M n hn2 htb hns D alloc

/-- Rank-level form of the previous equality plus Remark 21.  The normalized
factor product is identified as the Boolean representative, but the SPDP rank
cost is bounded by the raw allocated-product row space.  This is the exact
normalization/rank handoff needed before the remaining Booleanity row
certificate synthesis. -/
theorem allocatedNormalizedFactorProduct_multilinearizedRank_le_rawAllocatedProductRank
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : ℕ) :
    multilinearize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) =
      multilinearize
        (piPlusBooleanProjectedAllocatedNormalizedFactorProduct
          M n hn2 htb hns D alloc) ∧
    rkSPDP_multilinearized B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) := by
  exact ⟨
    multilinearize_allocatedDerivativeProduct_eq_normalizedFactorProduct
      M n hn2 htb hns D alloc,
    multilinearize_rank_le_direct B κ ℓ
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc)⟩


/-! ## Raw allocated-product rank from a finite profile cover

The normalization handoff above leaves the real P-side cost at the raw row
space of the allocated derivative product.  The next lemmas isolate the exact
linear-algebra closeout needed after the Leibniz/profile work: if every raw
SPDP generator row is covered by a finite sum of profile-compressed spaces, and
each such space has the Lemma-31 dimension budget, then the raw rank is bounded
by `number_of_spaces * withinProfileBound κ`.
-/

/-- Kernel-clean finite-cover rank bound for raw SPDP rows.  This is just
`Submodule.finrank_mono` followed by the finite `iSup` dimension inequality and
the per-summand dimension budgets. -/
theorem rawRank_le_sum_subspaces_of_rawSubspace_le {N r : Nat}
    (B : BlockPartition N) (κ ℓ C : Nat)
    (p : MvPolynomial (Fin N) ℚ)
    (W : Fin r → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    [∀ i, Module.Finite ℚ (W i)]
    (hcover : rawBlockedSpdpSubspace B κ ℓ p ≤ ⨆ i : Fin r, W i)
    (hdim : ∀ i : Fin r, Module.finrank ℚ (W i) ≤ C) :
    rkSPDP B κ ℓ p ≤ r * C := by
  unfold rkSPDP rawBlockedSpdpRank
  calc
    Module.finrank ℚ (rawBlockedSpdpSubspace B κ ℓ p)
        ≤ Module.finrank ℚ ↥(⨆ i : Fin r, W i) :=
          Submodule.finrank_mono hcover
    _ ≤ ∑ i : Fin r, Module.finrank ℚ (W i) :=
          finrank_iSup_fin_le r W
    _ ≤ ∑ _i : Fin r, C :=
          Finset.sum_le_sum (fun i _hi => hdim i)
    _ = r * C := by
          simp [Finset.sum_const]

/-- Generator-row form of `rawRank_le_sum_subspaces_of_rawSubspace_le`: it is
enough to classify each raw generator `m * ∂_S p` into the finite profile cover.
This is the form consumed by a Leibniz expansion proof. -/
theorem rawRank_le_sum_subspaces_of_generator_rows {N r : Nat}
    (B : BlockPartition N) (κ ℓ C : Nat)
    (p : MvPolynomial (Fin N) ℚ)
    (W : Fin r → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    [∀ i, Module.Finite ℚ (W i)]
    (hrow : ∀ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible B S →
      m * iterDerivList S p ∈ ⨆ i : Fin r, W i)
    (hdim : ∀ i : Fin r, Module.finrank ℚ (W i) ≤ C) :
    rkSPDP B κ ℓ p ≤ r * C := by
  refine rawRank_le_sum_subspaces_of_rawSubspace_le B κ ℓ C p W ?_ hdim
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hSlen, hmdeg, hmvars, hadm, rfl⟩
  exact hrow S m hSlen hmdeg hmvars hadm

/-- Allocated-product specialization with a Lemma-31-style budget.  Once the
Leibniz expansion plus per-factor/profile compression proves the generator-row
cover into `W`, the raw rank of the allocated derivative product is bounded by
`r * withinProfileBound κ`. -/
theorem allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
    {r : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (W : Fin r → Submodule ℚ
      (MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))
    [∀ i, Module.Finite ℚ (W i)]
    (hrow : ∀
      (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible B S →
      m * iterDerivList S
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ∈ ⨆ i : Fin r, W i)
    (hdim : ∀ i : Fin r, Module.finrank ℚ (W i) ≤ withinProfileBound κ) :
    rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      r * withinProfileBound κ := by
  exact rawRank_le_sum_subspaces_of_generator_rows B κ ℓ (withinProfileBound κ)
    (piPlusBooleanProjectedAllocatedDerivativeProduct M n hn2 htb hns D alloc)
    W hrow hdim

/-- Paper-scale name for the allocated-product raw rank target.  The only
remaining mathematical input is the `hrow` classifier: expand raw rows by
Leibniz, classify each per-factor derivative into its local span, place each
summand in one of the finite profile-compressed spaces `W`, then use Lemma 31 to
discharge `hdim`. -/
theorem paperScale_allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
    {r : Nat}
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (κ ℓ : Nat)
    (W : Fin r → Submodule ℚ
      (MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ))
    [∀ i, Module.Finite ℚ (W i)]
    (hrow : ∀
      (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition S →
      m * iterDerivList S
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ∈
        ⨆ i : Fin r, W i)
    (hdim : ∀ i : Fin r, Module.finrank ℚ (W i) ≤ withinProfileBound κ) :
    rkSPDP
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ≤
      r * withinProfileBound κ := by
  exact allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    alloc
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ W hrow hdim


/-! ## Private-chart fallback: derivative-image sum plus polynomial shifts

The σ-only `W_τ` bridge is not the right target for Boolean-projected `Pi+`
factors in private coordinates.  The first unconditional option-2 closeout is
therefore deliberately chart-indexed: collect the actual `κ`-fold derivative
images, then close under the SPDP degree-`ℓ` shifts using the existing finite
`shiftClosure` machinery.  This bypasses any global canonical-interface claim.
-/

/-- The finite span of all ordered `κ`-fold derivative images of a polynomial.
The index is `List.Vector (Fin N) κ`, so no quotient or canonical ordering is
imposed; this is the polynomial-sum envelope before multiplying by SPDP shifts. -/
noncomputable def kappaDerivativeImageSpan {N : Nat}
    (κ : Nat) (p : MvPolynomial (Fin N) ℚ) :
    Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  Submodule.span ℚ
    (Set.range (fun S : List.Vector (Fin N) κ => iterDerivList S.toList p))

instance kappaDerivativeImageSpan_finite {N : Nat}
    (κ : Nat) (p : MvPolynomial (Fin N) ℚ) :
    Module.Finite ℚ ↥(kappaDerivativeImageSpan κ p) := by
  classical
  apply Module.Finite.span_of_finite
  exact Set.toFinite _


/-- The chart-indexed Leibniz product span: union over ordered `κ`-derivative
lists of the bounded Leibniz products of a factor family.  A generator is a
product of differentiated local/private factors, with total derivative mass at
most `κ`. -/
noncomputable def kappaLeibnizProductSpan {N L : Nat}
    (κ : Nat) (factors : Fin L → MvPolynomial (Fin N) ℚ) :
    Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  Submodule.span ℚ
    (⋃ S : List.Vector (Fin N) κ,
      boundedDistribDerivProds Finset.univ factors S.toList κ)

/-- The `κ`-derivative image span of a product of local factors is contained in
`kappaLeibnizProductSpan`.  This is the formal product step of option 2: after
Leibniz expansion, every derivative image is a linear combination of products
of differentiated private/local factors with total derivative mass `≤ κ`. -/
theorem kappaDerivativeImageSpan_prod_le_kappaLeibnizProductSpan {N L : Nat}
    (κ : Nat) (factors : Fin L → MvPolynomial (Fin N) ℚ) :
    kappaDerivativeImageSpan κ (Finset.univ.prod factors) ≤
      kappaLeibnizProductSpan κ factors := by
  classical
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, rfl⟩
  have hmem : iterDerivList S.toList (Finset.univ.prod factors) ∈
      Submodule.span ℚ (boundedDistribDerivProds Finset.univ factors S.toList S.toList.length) :=
    iterDerivList_finset_prod_mem_bounded_span S.toList factors
  have hlen : S.toList.length = κ := S.2
  have hsub : boundedDistribDerivProds Finset.univ factors S.toList S.toList.length ⊆
      (⋃ T : List.Vector (Fin N) κ,
        boundedDistribDerivProds Finset.univ factors T.toList κ) := by
    intro g hg
    refine Set.mem_iUnion.mpr ⟨S, ?_⟩
    simpa [hlen] using hg
  exact Submodule.span_mono hsub hmem


/-- Monomial exponents of total degree at most `ℓ` whose support is contained in
`S`.  This is the SPDP-restricted shift index for a fixed derivative window. -/
def RestrictedMonoIdx {N : Nat} (S : Finset (Fin N)) (ℓ : Nat) : Type :=
  { α : Fin N →₀ Nat // (α.sum fun _ e => e) ≤ ℓ ∧ α.support ⊆ S }

noncomputable instance RestrictedMonoIdx.fintype {N : Nat} (S : Finset (Fin N)) (ℓ : Nat) :
    Fintype (RestrictedMonoIdx S ℓ) := by
  classical
  let φ : RestrictedMonoIdx S ℓ → (Fin N → Fin (ℓ + 1)) := fun α i =>
    ⟨α.1 i, by
      by_cases hzero : α.1 i = 0
      · rw [hzero]; exact Nat.succ_pos _
      · have hi : i ∈ α.1.support := Finsupp.mem_support_iff.mpr hzero
        have hle_sum : α.1 i ≤ α.1.sum (fun _ e => e) :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        exact Nat.lt_succ_of_le (hle_sum.trans α.2.1)⟩
  refine Fintype.ofInjective φ ?_
  intro a b h
  apply Subtype.ext
  ext i
  have hi := congrArg Fin.val (congrFun h i)
  exact hi

instance RestrictedMonoIdx.finite {N : Nat} (S : Finset (Fin N)) (ℓ : Nat) :
    Finite (RestrictedMonoIdx S ℓ) := by
  classical
  infer_instance

/-- Restricted monomial shift closure for a fixed SPDP derivative window `S`:
only monomial shifts of degree `≤ ℓ` whose variables lie in `S` are allowed. -/
noncomputable def restrictedMonomialShiftClosure {N : Nat}
    (S : Finset (Fin N)) (ℓ : Nat)
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ)) :
    Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  ⨆ α : RestrictedMonoIdx S ℓ,
    W.map (mulByPoly (n := N) (MvPolynomial.monomial α.1 (1 : ℚ)))

instance restrictedMonomialShiftClosure_finite {N : Nat}
    (S : Finset (Fin N)) (ℓ : Nat)
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ)) [Module.Finite ℚ W] :
    Module.Finite ℚ ↥(restrictedMonomialShiftClosure S ℓ W) := by
  classical
  unfold restrictedMonomialShiftClosure
  haveI : ∀ α : RestrictedMonoIdx S ℓ,
      Module.Finite ℚ ↥(W.map (mulByPoly (n := N)
        (MvPolynomial.monomial α.1 (1 : ℚ)))) :=
    fun α => mulByPoly_map_finite W (MvPolynomial.monomial α.1 (1 : ℚ))
  infer_instance

/-- Finrank of the fixed-window restricted shift closure is bounded by the
number of supported degree-`≤ℓ` monomials times `finrank W`. -/
theorem finrank_restrictedMonomialShiftClosure_le {N : Nat}
    (S : Finset (Fin N)) (ℓ : Nat)
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ)) [Module.Finite ℚ W] :
    Module.finrank ℚ ↥(restrictedMonomialShiftClosure S ℓ W) ≤
      Fintype.card (RestrictedMonoIdx S ℓ) * Module.finrank ℚ ↥W := by
  classical
  set r : Nat := Fintype.card (RestrictedMonoIdx S ℓ) with hr
  let e : RestrictedMonoIdx S ℓ ≃ Fin r := Fintype.equivFin (RestrictedMonoIdx S ℓ)
  let U : Fin r → Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
    fun i => W.map (mulByPoly (n := N)
      (MvPolynomial.monomial (e.symm i).1 (1 : ℚ)))
  haveI : ∀ i, Module.Finite ℚ ↥(U i) := by
    intro i
    exact mulByPoly_map_finite W (MvPolynomial.monomial (e.symm i).1 (1 : ℚ))
  have hreindex : restrictedMonomialShiftClosure S ℓ W =
      (⨆ i : Fin r, U i : Submodule ℚ (MvPolynomial (Fin N) ℚ)) := by
    unfold restrictedMonomialShiftClosure
    apply le_antisymm
    · refine iSup_le (fun α => ?_)
      have hα : α = e.symm (e α) := (e.symm_apply_apply α).symm
      have hstep : W.map (mulByPoly (n := N) (MvPolynomial.monomial α.1 (1 : ℚ))) = U (e α) := by
        show W.map (mulByPoly (n := N) (MvPolynomial.monomial α.1 (1 : ℚ))) =
          W.map (mulByPoly (n := N) (MvPolynomial.monomial (e.symm (e α)).1 (1 : ℚ)))
        rw [← hα]
      rw [hstep]
      exact le_iSup (fun i : Fin r => U i) (e α)
    · refine iSup_le (fun i => ?_)
      exact le_iSup
        (fun α : RestrictedMonoIdx S ℓ =>
          W.map (mulByPoly (n := N) (MvPolynomial.monomial α.1 (1 : ℚ))))
        (e.symm i)
  have hsum : (∑ i : Fin r, Module.finrank ℚ ↥(U i)) ≤
      r * Module.finrank ℚ ↥W := by
    have hpt : ∀ i : Fin r, Module.finrank ℚ ↥(U i) ≤ Module.finrank ℚ ↥W := by
      intro i
      exact mulByPoly_map_finrank_le W (MvPolynomial.monomial (e.symm i).1 (1 : ℚ))
    calc
      (∑ i : Fin r, Module.finrank ℚ ↥(U i)) ≤
          ∑ _ : Fin r, Module.finrank ℚ ↥W := Finset.sum_le_sum (fun i _ => hpt i)
      _ = r * Module.finrank ℚ ↥W := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  calc
    Module.finrank ℚ ↥(restrictedMonomialShiftClosure S ℓ W)
        = Module.finrank ℚ ↥(⨆ i : Fin r, U i) := by rw [hreindex]
    _ ≤ ∑ i : Fin r, Module.finrank ℚ ↥(U i) :=
        SPDP.finrank_iSup_fin_le (F := ℚ) r U
    _ ≤ r * Module.finrank ℚ ↥W := hsum

/-- For a polynomial shift supported on the fixed derivative window, multiplying
an element of `W` stays in the restricted monomial shift closure. -/
theorem mul_mem_restrictedMonomialShiftClosure {N : Nat}
    (S : Finset (Fin N)) (ℓ : Nat)
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ))
    {f m : MvPolynomial (Fin N) ℚ}
    (hf : f ∈ W) (hmdeg : m.totalDegree ≤ ℓ) (hmvars : m.vars ⊆ S) :
    f * m ∈ restrictedMonomialShiftClosure S ℓ W := by
  classical
  rw [show f * m = f * ∑ β ∈ m.support, MvPolynomial.monomial β (MvPolynomial.coeff β m) by
    rw [← MvPolynomial.as_sum m]]
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ (fun β hβ => ?_)
  have hβdeg : (β.sum fun _ e => e) ≤ ℓ := le_trans (le_totalDegree hβ) hmdeg
  have hβsupp : β.support ⊆ S := by
    intro x hx
    exact hmvars ((MvPolynomial.mem_vars x).mpr ⟨β, hβ, hx⟩)
  let idx : RestrictedMonoIdx S ℓ := ⟨β, hβdeg, hβsupp⟩
  have hmon :
      (MvPolynomial.coeff β m) • (f * (MvPolynomial.monomial β (1 : ℚ) : MvPolynomial (Fin N) ℚ)) =
        f * (MvPolynomial.monomial β (MvPolynomial.coeff β m) : MvPolynomial (Fin N) ℚ) := by
    rw [show (MvPolynomial.coeff β m) • (f * MvPolynomial.monomial β (1 : ℚ)) =
            f * (MvPolynomial.coeff β m) • (MvPolynomial.monomial β (1 : ℚ) : MvPolynomial (Fin N) ℚ)
              from (Algebra.mul_smul_comm _ f (MvPolynomial.monomial β (1 : ℚ))).symm,
        smul_monomial, smul_eq_mul, mul_one]
  rw [← hmon]
  have hfmap : f * (MvPolynomial.monomial β (1 : ℚ) : MvPolynomial (Fin N) ℚ) ∈
      W.map (mulByPoly (n := N) (MvPolynomial.monomial β (1 : ℚ))) := by
    exact ⟨f, hf, rfl⟩
  have hsub : W.map (mulByPoly (n := N) (MvPolynomial.monomial idx.1 (1 : ℚ))) ≤
      restrictedMonomialShiftClosure S ℓ W := by
    exact le_iSup
      (fun α : RestrictedMonoIdx S ℓ =>
        W.map (mulByPoly (n := N) (MvPolynomial.monomial α.1 (1 : ℚ)))) idx
  exact (restrictedMonomialShiftClosure S ℓ W).smul_mem (MvPolynomial.coeff β m) (hsub hfmap)

/-- Symmetric form for the actual SPDP row convention. -/
theorem shift_mul_mem_restrictedMonomialShiftClosure {N : Nat}
    (S : Finset (Fin N)) (ℓ : Nat)
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ))
    {f m : MvPolynomial (Fin N) ℚ}
    (hf : f ∈ W) (hmdeg : m.totalDegree ≤ ℓ) (hmvars : m.vars ⊆ S) :
    m * f ∈ restrictedMonomialShiftClosure S ℓ W := by
  rw [mul_comm]
  exact mul_mem_restrictedMonomialShiftClosure S ℓ W hf hmdeg hmvars

/-- A concrete row `m * ∂_S p` lies in the shift closure of the finite
`κ`-derivative image span.  This is the raw linear-algebra bridge for option 2:
the derivative side is a finite chart-indexed sum, while arbitrary SPDP shifts
are handled by `shiftClosure`. -/
theorem rawGenerator_mem_shiftClosure_kappaDerivativeImageSpan {N : Nat}
    (κ ℓ : Nat) (p : MvPolynomial (Fin N) ℚ)
    (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ)
    (hSlen : S.length = κ) (hmdeg : m.totalDegree ≤ ℓ) :
    m * iterDerivList S p ∈
      shiftClosure (kappaDerivativeImageSpan κ p) ℓ := by
  classical
  let Sv : List.Vector (Fin N) κ := ⟨S, hSlen⟩
  have hderiv : iterDerivList S p ∈ kappaDerivativeImageSpan κ p := by
    apply Submodule.subset_span
    refine ⟨Sv, ?_⟩
    simp [Sv]
  have hmap : iterDerivList S p * m ∈
      Submodule.map (mulByPoly (n := N) m) (kappaDerivativeImageSpan κ p) := by
    exact ⟨iterDerivList S p, hderiv, rfl⟩
  have hle : Submodule.map (mulByPoly (n := N) m) (kappaDerivativeImageSpan κ p) ≤
      shiftClosure (kappaDerivativeImageSpan κ p) ℓ := by
    exact le_iSup
      (fun s : { s : MvPolynomial (Fin N) ℚ // s.totalDegree ≤ ℓ } =>
        Submodule.map (mulByPoly (n := N) s.1) (kappaDerivativeImageSpan κ p))
      (⟨m, hmdeg⟩ : { s : MvPolynomial (Fin N) ℚ // s.totalDegree ≤ ℓ })
  exact hle (by simpa [mul_comm] using hmap)

/-- The whole raw SPDP row space is contained in the shift closure of the finite
`κ`-derivative image span.  This is independent of any canonical `W_τ`. -/
theorem rawBlockedSpdpSubspace_le_shiftClosure_kappaDerivativeImageSpan {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat) (p : MvPolynomial (Fin N) ℚ) :
    rawBlockedSpdpSubspace B κ ℓ p ≤
      shiftClosure (kappaDerivativeImageSpan κ p) ℓ := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hSlen, hmdeg, _hmvars, _hadm, rfl⟩
  exact rawGenerator_mem_shiftClosure_kappaDerivativeImageSpan κ ℓ p S m hSlen hmdeg

/-- Option-2 rank bound in its unconditional finite-sum form.  The private
chart/product work only has to bound the derivative-image span; the degree-`ℓ`
shift cost is paid once by `MonoIdx N ℓ`. -/
theorem rawRank_le_shiftClosure_kappaDerivativeImageSpan {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat) (p : MvPolynomial (Fin N) ℚ) :
    rkSPDP B κ ℓ p ≤
      Fintype.card (MonoIdx N ℓ) *
        Module.finrank ℚ ↥(kappaDerivativeImageSpan κ p) := by
  unfold rkSPDP rawBlockedSpdpRank
  calc
    Module.finrank ℚ ↥(rawBlockedSpdpSubspace B κ ℓ p)
        ≤ Module.finrank ℚ ↥(shiftClosure (kappaDerivativeImageSpan κ p) ℓ) :=
          Submodule.finrank_mono
            (rawBlockedSpdpSubspace_le_shiftClosure_kappaDerivativeImageSpan B κ ℓ p)
    _ ≤ Fintype.card (MonoIdx N ℓ) *
          Module.finrank ℚ ↥(kappaDerivativeImageSpan κ p) :=
        finrank_shiftClosure_le (kappaDerivativeImageSpan κ p) ℓ


/-- Block-admissible ordered derivative windows of length `κ`. -/
def AdmissibleDerivativeWindow {N : Nat} (B : BlockPartition N) (κ : Nat) : Type :=
  { S : List.Vector (Fin N) κ // isBlockAdmissible B S.toList }

noncomputable instance AdmissibleDerivativeWindow.fintype {N : Nat}
    (B : BlockPartition N) (κ : Nat) : Fintype (AdmissibleDerivativeWindow B κ) := by
  classical
  let φ : AdmissibleDerivativeWindow B κ → (Fin κ → Fin N) := fun S i => S.1.get i
  refine Fintype.ofInjective φ ?_
  intro A B h
  apply Subtype.ext
  apply List.Vector.eq
  apply List.ext_getElem
  · simp [A.1.2, B.1.2]
  · intro n hn1 hn2
    have hnκ : n < κ := by simpa [A.1.2] using hn1
    have := congrFun h ⟨n, hnκ⟩
    simpa [φ, List.Vector.get, List.get_eq_getElem] using this

instance AdmissibleDerivativeWindow.finite {N : Nat} (B : BlockPartition N) (κ : Nat) :
    Finite (AdmissibleDerivativeWindow B κ) := by
  classical
  infer_instance

/-- Per-window derivative image: for fixed `S`, this is just the 1-dimensional
span of the actual derivative row `∂_S p`.  Private charts enter downstream by
bounding/identifying this derivative image via Leibniz products of private local
factor charts. -/
noncomputable def perWindowDerivativeImageSpan {N : Nat}
    (p : MvPolynomial (Fin N) ℚ) (S : List (Fin N)) :
    Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  Submodule.span ℚ ({iterDerivList S p} : Set (MvPolynomial (Fin N) ℚ))

instance perWindowDerivativeImageSpan_finite {N : Nat}
    (p : MvPolynomial (Fin N) ℚ) (S : List (Fin N)) :
    Module.Finite ℚ ↥(perWindowDerivativeImageSpan p S) := by
  classical
  apply Module.Finite.span_of_finite
  exact Set.finite_singleton _

/-- The per-window derivative image has dimension at most one. -/
theorem perWindowDerivativeImageSpan_finrank_le_one {N : Nat}
    (p : MvPolynomial (Fin N) ℚ) (S : List (Fin N)) :
    Module.finrank ℚ ↥(perWindowDerivativeImageSpan p S) ≤ 1 := by
  classical
  simpa [perWindowDerivativeImageSpan] using
    (finrank_span_finset_le_card ({iterDerivList S p} : Finset (MvPolynomial (Fin N) ℚ)))

/-- The SPDP-restricted option-2 cover: for each admissible derivative window
`S`, close the single derivative image `∂_S p` only under shifts supported on
`S`.  This is the tightened replacement for the loose global `shiftClosure`. -/
noncomputable def admissibleRestrictedShiftDerivativeCover {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat) (p : MvPolynomial (Fin N) ℚ) :
    AdmissibleDerivativeWindow B κ → Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  fun S => restrictedMonomialShiftClosure S.1.toList.toFinset ℓ
    (perWindowDerivativeImageSpan p S.1.toList)

/-- Every raw SPDP generator row lands in the admissible-window restricted
shift cover.  This is the key tightening: the shift support hypothesis
`m.vars ⊆ S.toFinset` is consumed instead of being forgotten. -/
theorem rawBlockedSpdpSubspace_le_admissibleRestrictedShiftDerivativeCover {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat) (p : MvPolynomial (Fin N) ℚ) :
    rawBlockedSpdpSubspace B κ ℓ p ≤
      ⨆ S : AdmissibleDerivativeWindow B κ,
        admissibleRestrictedShiftDerivativeCover B κ ℓ p S := by
  classical
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hSlen, hmdeg, hmvars, hadm, rfl⟩
  let Sv : List.Vector (Fin N) κ := ⟨S, hSlen⟩
  let A : AdmissibleDerivativeWindow B κ := ⟨Sv, by simpa [Sv] using hadm⟩
  have hderiv : iterDerivList S p ∈ perWindowDerivativeImageSpan p S := by
    exact Submodule.subset_span (by simp [perWindowDerivativeImageSpan])
  have hrow : m * iterDerivList S p ∈
      admissibleRestrictedShiftDerivativeCover B κ ℓ p A := by
    simpa [admissibleRestrictedShiftDerivativeCover, A, Sv] using
      shift_mul_mem_restrictedMonomialShiftClosure S.toFinset ℓ
        (perWindowDerivativeImageSpan p S) hderiv hmdeg hmvars
  exact (le_iSup (fun A : AdmissibleDerivativeWindow B κ =>
    admissibleRestrictedShiftDerivativeCover B κ ℓ p A) A) hrow

/-- Per-admissible-window finrank bound: only monomials supported in the fixed
`κ`-window are counted. -/
theorem admissibleRestrictedShiftDerivativeCover_finrank_le {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat) (p : MvPolynomial (Fin N) ℚ)
    (S : AdmissibleDerivativeWindow B κ) :
    Module.finrank ℚ ↥(admissibleRestrictedShiftDerivativeCover B κ ℓ p S) ≤
      Fintype.card (RestrictedMonoIdx S.1.toList.toFinset ℓ) := by
  classical
  calc
    Module.finrank ℚ ↥(admissibleRestrictedShiftDerivativeCover B κ ℓ p S)
        ≤ Fintype.card (RestrictedMonoIdx S.1.toList.toFinset ℓ) *
            Module.finrank ℚ ↥(perWindowDerivativeImageSpan p S.1.toList) := by
          simpa [admissibleRestrictedShiftDerivativeCover] using
            finrank_restrictedMonomialShiftClosure_le S.1.toList.toFinset ℓ
              (perWindowDerivativeImageSpan p S.1.toList)
    _ ≤ Fintype.card (RestrictedMonoIdx S.1.toList.toFinset ℓ) * 1 :=
          Nat.mul_le_mul_left _ (perWindowDerivativeImageSpan_finrank_le_one p S.1.toList)
    _ = Fintype.card (RestrictedMonoIdx S.1.toList.toFinset ℓ) := by omega



/-- Finite-type version of `finrank_iSup_fin_le`, obtained by reindexing through
`Fintype.equivFin`. -/
theorem finrank_iSup_fintype_le' {N : Nat} {ι : Type*} [Fintype ι]
    (U : ι → Submodule ℚ (MvPolynomial (Fin N) ℚ)) [∀ i, Module.Finite ℚ ↥(U i)] :
    Module.finrank ℚ ↥(⨆ i : ι, U i) ≤ ∑ i : ι, Module.finrank ℚ ↥(U i) := by
  classical
  set r : Nat := Fintype.card ι with hr
  let e : ι ≃ Fin r := Fintype.equivFin ι
  let V : Fin r → Submodule ℚ (MvPolynomial (Fin N) ℚ) := fun j => U (e.symm j)
  haveI : ∀ j, Module.Finite ℚ ↥(V j) := by intro j; infer_instance
  have hreindex : (⨆ i : ι, U i : Submodule ℚ (MvPolynomial (Fin N) ℚ)) = ⨆ j : Fin r, V j := by
    apply le_antisymm
    · refine iSup_le (fun i => ?_)
      have hi : i = e.symm (e i) := (e.symm_apply_apply i).symm
      have hstep : U i = V (e i) := by
        show U i = U (e.symm (e i)); rw [← hi]
      rw [hstep]
      exact le_iSup (fun j : Fin r => V j) (e i)
    · refine iSup_le (fun j => ?_)
      exact le_iSup (fun i : ι => U i) (e.symm j)
  have hsum : (∑ j : Fin r, Module.finrank ℚ ↥(V j)) = ∑ i : ι, Module.finrank ℚ ↥(U i) := by
    simpa [V] using
      (Equiv.sum_comp e.symm (fun i : ι => Module.finrank ℚ ↥(U i)))
  calc
    Module.finrank ℚ ↥(⨆ i : ι, U i) = Module.finrank ℚ ↥(⨆ j : Fin r, V j) := by rw [hreindex]
    _ ≤ ∑ j : Fin r, Module.finrank ℚ ↥(V j) := SPDP.finrank_iSup_fin_le (F := ℚ) r V
    _ = ∑ i : ι, Module.finrank ℚ ↥(U i) := hsum

/-- The tightened option-2 raw rank bound: rank is bounded by the sum over
block-admissible derivative windows of the number of supported degree-`≤ℓ`
shift monomials.  This is the formal target on which Lemma 29/profile
compression must act to turn the admissible-window sum into `R^O(1)`. -/
theorem rawRank_le_sum_admissibleRestrictedShiftCounts {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat) (p : MvPolynomial (Fin N) ℚ) :
    rkSPDP B κ ℓ p ≤
      ∑ S : AdmissibleDerivativeWindow B κ,
        Fintype.card (RestrictedMonoIdx S.1.toList.toFinset ℓ) := by
  classical
  unfold rkSPDP rawBlockedSpdpRank
  haveI : ∀ S : AdmissibleDerivativeWindow B κ,
      Module.Finite ℚ ↥(admissibleRestrictedShiftDerivativeCover B κ ℓ p S) := by
    intro S
    unfold admissibleRestrictedShiftDerivativeCover
    infer_instance
  calc
    Module.finrank ℚ ↥(rawBlockedSpdpSubspace B κ ℓ p)
        ≤ Module.finrank ℚ ↥(⨆ S : AdmissibleDerivativeWindow B κ,
            admissibleRestrictedShiftDerivativeCover B κ ℓ p S) :=
          Submodule.finrank_mono
            (rawBlockedSpdpSubspace_le_admissibleRestrictedShiftDerivativeCover B κ ℓ p)
    _ ≤ ∑ S : AdmissibleDerivativeWindow B κ,
          Module.finrank ℚ ↥(admissibleRestrictedShiftDerivativeCover B κ ℓ p S) := by
          simpa using finrank_iSup_fintype_le'
            (fun S : AdmissibleDerivativeWindow B κ =>
              admissibleRestrictedShiftDerivativeCover B κ ℓ p S)
    _ ≤ ∑ S : AdmissibleDerivativeWindow B κ,
          Fintype.card (RestrictedMonoIdx S.1.toList.toFinset ℓ) :=
          Finset.sum_le_sum (fun S _ =>
            admissibleRestrictedShiftDerivativeCover_finrank_le B κ ℓ p S)

/-- Uniformized form: if the number of admissible derivative windows and the
per-window supported-shift count are bounded, then the tightened route gives a
polynomial product bound.  Supplying the first hypothesis is precisely the
Lemma-29/profile-compression content; the second is the fixed-window shift
count `C(κ+ℓ,ℓ)` or any convenient polynomial upper bound. -/
theorem rawRank_le_admissibleWindowCount_mul_shiftCount {N : Nat}
    (B : BlockPartition N) (κ ℓ Cwin Cshift : Nat)
    (p : MvPolynomial (Fin N) ℚ)
    (hwin : Fintype.card (AdmissibleDerivativeWindow B κ) ≤ Cwin)
    (hshift : ∀ S : AdmissibleDerivativeWindow B κ,
      Fintype.card (RestrictedMonoIdx S.1.toList.toFinset ℓ) ≤ Cshift) :
    rkSPDP B κ ℓ p ≤ Cwin * Cshift := by
  classical
  calc
    rkSPDP B κ ℓ p ≤
        ∑ S : AdmissibleDerivativeWindow B κ,
          Fintype.card (RestrictedMonoIdx S.1.toList.toFinset ℓ) :=
      rawRank_le_sum_admissibleRestrictedShiftCounts B κ ℓ p
    _ ≤ ∑ _S : AdmissibleDerivativeWindow B κ, Cshift :=
      Finset.sum_le_sum (fun S _ => hshift S)
    _ = Fintype.card (AdmissibleDerivativeWindow B κ) * Cshift := by
      simp [Finset.sum_const, smul_eq_mul]
    _ ≤ Cwin * Cshift := Nat.mul_le_mul_right _ hwin

/-- Allocated-product specialization of the tightened admissible-window route. -/
theorem allocatedDerivativeProduct_rank_le_admissibleWindowCount_mul_shiftCount
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ Cwin Cshift : Nat)
    (hwin : Fintype.card (AdmissibleDerivativeWindow B κ) ≤ Cwin)
    (hshift : ∀ S : AdmissibleDerivativeWindow B κ,
      Fintype.card (RestrictedMonoIdx S.1.toList.toFinset ℓ) ≤ Cshift) :
    rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      Cwin * Cshift := by
  exact rawRank_le_admissibleWindowCount_mul_shiftCount B κ ℓ Cwin Cshift
    (piPlusBooleanProjectedAllocatedDerivativeProduct M n hn2 htb hns D alloc)
    hwin hshift


/-- Coarse polynomial bound for fixed-window supported shifts: an exponent
supported on `S` and of total degree `≤ ℓ` is determined by assigning each
variable of `S` a value in `0..ℓ`.  The sharper stars-and-bars count is
`Nat.choose (S.card + ℓ) ℓ`; this injection gives the sufficient polynomial
bound `(ℓ+1)^S.card` without extra combinatorics. -/
theorem card_RestrictedMonoIdx_le_pow_card {N : Nat}
    (S : Finset (Fin N)) (ℓ : Nat) :
    Fintype.card (RestrictedMonoIdx S ℓ) ≤ (ℓ + 1) ^ S.card := by
  classical
  let φ : RestrictedMonoIdx S ℓ → ({i // i ∈ S} → Fin (ℓ + 1)) := fun α i =>
    ⟨α.1 i.1, by
      by_cases hzero : α.1 i.1 = 0
      · rw [hzero]; exact Nat.succ_pos _
      · have hi : i.1 ∈ α.1.support := Finsupp.mem_support_iff.mpr hzero
        have hle_sum : α.1 i.1 ≤ α.1.sum (fun _ e => e) :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        exact Nat.lt_succ_of_le (hle_sum.trans α.2.1)⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ S
    · have hval := congrArg Fin.val (congrFun hab ⟨i, hi⟩)
      exact hval
    · have hai : a.1 i = 0 := by
        by_contra hne
        exact hi (a.2.2 (Finsupp.mem_support_iff.mpr hne))
      have hbi : b.1 i = 0 := by
        by_contra hne
        exact hi (b.2.2 (Finsupp.mem_support_iff.mpr hne))
      rw [hai, hbi]
  calc
    Fintype.card (RestrictedMonoIdx S ℓ)
        ≤ Fintype.card ({i // i ∈ S} → Fin (ℓ + 1)) :=
          Fintype.card_le_of_injective φ hφ
    _ = (ℓ + 1) ^ S.card := by
      simp [Fintype.card_fin]

/-- Since every admissible SPDP window has length `κ`, its support set has
cardinality at most `κ`; hence the fixed-window shift count is bounded by
`(ℓ+1)^κ`. -/
theorem card_RestrictedMonoIdx_admissibleWindow_le {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat) (S : AdmissibleDerivativeWindow B κ) :
    Fintype.card (RestrictedMonoIdx S.1.toList.toFinset ℓ) ≤ (ℓ + 1) ^ κ := by
  calc
    Fintype.card (RestrictedMonoIdx S.1.toList.toFinset ℓ)
        ≤ (ℓ + 1) ^ S.1.toList.toFinset.card :=
          card_RestrictedMonoIdx_le_pow_card S.1.toList.toFinset ℓ
    _ ≤ (ℓ + 1) ^ κ := by
      apply Nat.pow_le_pow_right (Nat.succ_pos ℓ)
      calc S.1.toList.toFinset.card ≤ S.1.toList.length := List.toFinset_card_le _
          _ = κ := S.1.2

/-- Concrete polynomial-form tightened route: once Lemma 29/profile compression
bounds the admissible-window count by `Cwin`, the shift side contributes only
`(ℓ+1)^κ`. -/
theorem rawRank_le_admissibleWindowCount_mul_polyShift {N : Nat}
    (B : BlockPartition N) (κ ℓ Cwin : Nat) (p : MvPolynomial (Fin N) ℚ)
    (hwin : Fintype.card (AdmissibleDerivativeWindow B κ) ≤ Cwin) :
    rkSPDP B κ ℓ p ≤ Cwin * (ℓ + 1) ^ κ := by
  exact rawRank_le_admissibleWindowCount_mul_shiftCount B κ ℓ Cwin ((ℓ + 1) ^ κ)
    p hwin (card_RestrictedMonoIdx_admissibleWindow_le B κ ℓ)

/-- Allocated-product specialization of the polynomial-form tightened route. -/
theorem allocatedDerivativeProduct_rank_le_admissibleWindowCount_mul_polyShift
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ Cwin : Nat)
    (hwin : Fintype.card (AdmissibleDerivativeWindow B κ) ≤ Cwin) :
    rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      Cwin * (ℓ + 1) ^ κ := by
  exact rawRank_le_admissibleWindowCount_mul_polyShift B κ ℓ Cwin
    (piPlusBooleanProjectedAllocatedDerivativeProduct M n hn2 htb hns D alloc) hwin


/-- Paper-scale allocated-product specialization of the polynomial-form
tightened route.  The only remaining external input is the Lemma-29/profile
compression bound on the number of admissible derivative windows. -/
theorem paperScale_allocatedDerivativeProduct_rank_le_admissibleWindowCount_mul_polyShift
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (κ ℓ Cwin : Nat)
    (hwin : Fintype.card (AdmissibleDerivativeWindow
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ) ≤ Cwin) :
    rkSPDP
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ≤
      Cwin * (ℓ + 1) ^ κ := by
  exact allocatedDerivativeProduct_rank_le_admissibleWindowCount_mul_polyShift
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    alloc
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ Cwin hwin


/-- Direct cardinality bound for admissible derivative windows.  This is the
literal finite-window side before any Lemma-29 quotient/compression: a window is
an ordered `κ`-tuple of variables, so the admissible subtype injects into
`Fin κ → Fin N`. -/
theorem admissibleDerivativeWindow_card_le_pow {N : Nat}
    (B : BlockPartition N) (κ : Nat) :
    Fintype.card (AdmissibleDerivativeWindow B κ) ≤ N ^ κ := by
  classical
  let φ : AdmissibleDerivativeWindow B κ → (Fin κ → Fin N) := fun S i => S.1.get i
  have hφ : Function.Injective φ := by
    intro A B h
    apply Subtype.ext
    apply List.Vector.eq
    apply List.ext_getElem
    · simp [A.1.2, B.1.2]
    · intro n hn1 hn2
      have hnκ : n < κ := by simpa [A.1.2] using hn1
      have := congrFun h ⟨n, hnκ⟩
      simpa [φ, List.Vector.get, List.get_eq_getElem] using this
  calc
    Fintype.card (AdmissibleDerivativeWindow B κ)
        ≤ Fintype.card (Fin κ → Fin N) := Fintype.card_le_of_injective φ hφ
    _ = N ^ κ := by simp [Fintype.card_fin]

/-- Paper-scale admissible-window cardinality bound at the concrete κ=804.  This
is an unconditional polynomial bound (`n^804` for `n = 2^804`).  It is weaker
than the paper's Lemma-29/profile-compressed `R^O(1)` count, but sufficient to
make the tightened option-2 route polynomial at the fixed paper scale. -/
theorem admissibleDerivativeWindow_card_le_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    Fintype.card (AdmissibleDerivativeWindow
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition 804) ≤
      (2 ^ 804) ^ 804 := by
  simpa [cook_levin_compilation] using
    admissibleDerivativeWindow_card_le_pow
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition 804

/-- Arithmetic closeout for the direct paper-scale option-2 budget:
`n^804 * 805^804 ≤ n^1000` at `n = 2^804`. -/
theorem paperScale_directWindowShiftBudget_le_pow1000 :
    (2 ^ 804) ^ 804 * (804 + 1) ^ 804 ≤ (2 ^ 804) ^ 1000 := by
  have h805_2pow10 : 804 + 1 ≤ (2 ^ 10 : Nat) := by norm_num
  have hshift : (804 + 1) ^ 804 ≤ (2 ^ 804) ^ 10 := by
    calc
      (804 + 1) ^ 804 ≤ (2 ^ 10 : Nat) ^ 804 :=
        Nat.pow_le_pow_left h805_2pow10 804
      _ = (2 ^ 804 : Nat) ^ 10 := by rw [← pow_mul, ← pow_mul]
  calc
    (2 ^ 804) ^ 804 * (804 + 1) ^ 804
        ≤ (2 ^ 804) ^ 804 * (2 ^ 804) ^ 10 :=
          Nat.mul_le_mul_left _ hshift
    _ = (2 ^ 804) ^ (804 + 10) := by rw [← pow_add]
    _ ≤ (2 ^ 804) ^ 1000 := by
      apply Nat.pow_le_pow_right
      · norm_num
      · norm_num

/-- Unconditional paper-scale polynomial closeout for the tightened option-2
allocated-product route.  This uses the direct ordered-window count above; a
future Lemma-29 quotient/profile-compression replacement can lower the exponent,
but the route is already strictly polynomial. -/
theorem paperScale_allocatedDerivativeProduct_rank_le_pow1000_directWindowCount
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars)) :
    rkSPDP
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        804 804
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ≤
      (2 ^ 804) ^ 1000 := by
  have hrank := paperScale_allocatedDerivativeProduct_rank_le_admissibleWindowCount_mul_polyShift
    M htb hns alloc 804 804 ((2 ^ 804) ^ 804)
    (admissibleDerivativeWindow_card_le_paperScale M htb hns)
  exact hrank.trans paperScale_directWindowShiftBudget_le_pow1000

/-- Allocated-product specialization of the private-chart finite-sum route. -/
theorem allocatedDerivativeProduct_rank_le_shiftClosure_kappaDerivativeImageSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat) :
    rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      Fintype.card (MonoIdx (cook_levin_compilation M n hn2 htb hns).numVars ℓ) *
        Module.finrank ℚ ↥(kappaDerivativeImageSpan κ
          (piPlusBooleanProjectedAllocatedDerivativeProduct
            M n hn2 htb hns D alloc)) := by
  exact rawRank_le_shiftClosure_kappaDerivativeImageSpan B κ ℓ
    (piPlusBooleanProjectedAllocatedDerivativeProduct M n hn2 htb hns D alloc)

/-- Paper-scale specialization of the unconditional private-chart finite-sum
route for allocated products. -/
theorem paperScale_allocatedDerivativeProduct_rank_le_shiftClosure_kappaDerivativeImageSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (κ ℓ : Nat) :
    rkSPDP
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ≤
      Fintype.card (MonoIdx
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars ℓ) *
        Module.finrank ℚ ↥(kappaDerivativeImageSpan κ
          (piPlusBooleanProjectedAllocatedDerivativeProduct
            M (2 ^ 804) paperScale_ge_two htb hns
            (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc)) := by
  exact allocatedDerivativeProduct_rank_le_shiftClosure_kappaDerivativeImageSpan
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    alloc
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ



/-! ## Admissible-profile cover for the allocated-product `hrow` classifier -/

/-- The finite type of genuinely admissible profiles at radius `κ`.  This is the
right index type for the raw allocated-product cover: every Leibniz distribution
partitioning an SPDP derivative list has total profile mass at most `κ`, so it
selects an element of this subtype rather than merely a bounded profile. -/
def AdmissibleProfile (κ : Nat) : Type :=
  { h : ProfileHistogram // ProfileAdmissible κ h }

namespace AdmissibleProfile

/-- Forget an admissible profile to the existing bounded-profile enumeration. -/
def toBoundedProfile {κ : Nat} (ap : AdmissibleProfile κ) : BoundedProfile κ :=
  admissibleToBounded ap.property

@[simp] theorem toBoundedProfile_toHistogram {κ : Nat}
    (ap : AdmissibleProfile κ) :
    ap.toBoundedProfile.toHistogram = ap.val := rfl

noncomputable instance (κ : Nat) : Fintype (AdmissibleProfile κ) := by
  classical
  exact Fintype.ofInjective
    (fun ap : AdmissibleProfile κ => ap.toBoundedProfile)
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg BoundedProfile.toHistogram h)

end AdmissibleProfile

/-- Number of admissible profiles in the raw allocated-product profile cover. -/
noncomputable abbrev admissibleProfileCoverCard (κ : Nat) : Nat :=
  Fintype.card (AdmissibleProfile κ)

/-- Enumeration of admissible profiles by `Fin admissibleProfileCoverCard`. -/
noncomputable abbrev admissibleProfileCoverEnum (κ : Nat) :
    Fin (admissibleProfileCoverCard κ) → AdmissibleProfile κ :=
  (Fintype.equivFin (AdmissibleProfile κ)).symm

/-- The natural Lemma-31 profile cover space
`V_h = profileSubspace h (interfaceSpace_compiledBasis B κ ℓ)`. -/
noncomputable abbrev admissibleProfileCoverSpace {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat) :
    Fin (admissibleProfileCoverCard κ) →
      Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  fun i => profileSubspace ((admissibleProfileCoverEnum κ i).val)
    (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ σ)

/-- Generic finite-dimensionality of `profileSubspace` from finite-dimensional
per-type interface spaces.  Kept local here so the raw-rank closeout can provide
the `Module.Finite` instances required by `finrank_iSup_fin_le`. -/
theorem profileSubspace_finite_of_finite_local
    {N : Nat} (h : ProfileHistogram)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ (W τ)) :
    Module.Finite ℚ (profileSubspace h W) := by
  classical
  unfold profileSubspace
  set d : ConstraintType → Nat := fun τ => Module.finrank ℚ (W τ) with hd_def
  let b : ∀ τ, Module.Basis (Fin (d τ)) ℚ (W τ) :=
    fun τ => Module.finBasis ℚ (W τ)
  have hle :
      profileSubspace h W ≤
        Submodule.span ℚ
          (Set.range (profileSymProd W b : ProfileIndex h d → _)) :=
    profileSubspace_le_profileSymProd_span W b
  haveI hfin_big : Module.Finite ℚ
      (Submodule.span ℚ
        (Set.range (profileSymProd W b : ProfileIndex h d → _))) := by
    apply Module.Finite.span_of_finite
    exact Set.finite_range _
  exact Module.Finite.of_injective
    ((Submodule.inclusion hle) : _ →ₗ[ℚ] _)
    (Submodule.inclusion_injective hle)

/-- Each admissible-profile cover space is finite-dimensional. -/
theorem admissibleProfileCoverSpace_finite {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (i : Fin (admissibleProfileCoverCard κ)) :
    Module.Finite ℚ (admissibleProfileCoverSpace B κ ℓ i) := by
  classical
  exact profileSubspace_finite_of_finite_local
    ((admissibleProfileCoverEnum κ i).val)
    (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ σ)
    (fun σ => PallLean.Paper93.interfaceSpace_compiledBasis_finite B κ ℓ σ)

/-- Step (c): the `hdim` side of `hrow`, discharged directly by Lemma 31 for
compiled-basis profile subspaces. -/
theorem admissibleProfileCoverSpace_finrank_le_withinProfileBound {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (i : Fin (admissibleProfileCoverCard κ)) :
    Module.finrank ℚ (admissibleProfileCoverSpace B κ ℓ i) ≤
      withinProfileBound κ := by
  classical
  exact PallLean.Paper93.profileSubspace_compiledBasis_finrank_le_withinProfileBound
    B κ ℓ ((admissibleProfileCoverEnum κ i).val)
    ((admissibleProfileCoverEnum κ i).property)

/-- Step (b), isolated as the single remaining classifier statement.  Expanding
`iterDerivList S` of the allocated product by Leibniz should classify every
summand into one admissible profile space; linearity then gives this membership
in the finite `iSup` cover. -/
def AllocatedDerivativeProductAdmissibleProfileHrow
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    isBlockAdmissible B S →
    m * iterDerivList S
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈
      ⨆ i : Fin (admissibleProfileCoverCard κ),
        admissibleProfileCoverSpace B κ ℓ i



/-- Local factors whose product is the allocated derivative product. -/
noncomputable abbrev allocatedDerivativeLocalFactors
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ :=
  fun i => iterDerivList (alloc i)
    (piPlusBooleanProjectedTransformedConstraintFactors
      M n hn2 htb hns D)[i.val]

/-- The allocated derivative product is exactly the product of its allocated
local factors. -/
theorem piPlusBooleanProjectedAllocatedDerivativeProduct_eq_prod_localFactors
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    piPlusBooleanProjectedAllocatedDerivativeProduct M n hn2 htb hns D alloc =
      Finset.univ.prod (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc) := by
  rfl


/-- Allocated-product version of the product-span containment.  The derivative
image span of the Boolean-projected allocated product is contained in the
Leibniz product span of the allocated local/private factors. -/
theorem kappaDerivativeImageSpan_allocatedProduct_le_kappaLeibnizProductSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (κ : Nat) :
    kappaDerivativeImageSpan κ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      kappaLeibnizProductSpan κ
        (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc) := by
  rw [piPlusBooleanProjectedAllocatedDerivativeProduct_eq_prod_localFactors]
  exact kappaDerivativeImageSpan_prod_le_kappaLeibnizProductSpan κ
    (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc)

/-- Paper-scale allocated-product containment into the private/local Leibniz
product span. -/
theorem paperScale_kappaDerivativeImageSpan_allocatedProduct_le_kappaLeibnizProductSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (κ : Nat) :
    kappaDerivativeImageSpan κ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ≤
      kappaLeibnizProductSpan κ
        (allocatedDerivativeLocalFactors M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) := by
  exact kappaDerivativeImageSpan_allocatedProduct_le_kappaLeibnizProductSpan
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc κ

/-- Multiplication by a fixed left factor transports span membership to the
span of multiplied generators. -/
theorem mul_mem_span_image_of_mem_span {N : Nat}
    (m : MvPolynomial (Fin N) ℚ) (A : Set (MvPolynomial (Fin N) ℚ))
    {p : MvPolynomial (Fin N) ℚ}
    (hp : p ∈ Submodule.span ℚ A) :
    m * p ∈ Submodule.span ℚ ((fun q => m * q) '' A) := by
  classical
  refine Submodule.span_induction
    (s := A) (p := fun x _hx => m * x ∈ Submodule.span ℚ ((fun q => m * q) '' A))
    ?mem ?zero ?add ?smul hp
  · intro x hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · simp
  · intro x y _ _ hx hy
    simpa [mul_add] using Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [Algebra.smul_def]
    change m * (C a * x) ∈ Submodule.span ℚ ((fun q => m * q) '' A)
    rw [← mul_assoc, mul_comm m (C a), mul_assoc]
    simpa [Algebra.smul_def] using Submodule.smul_mem
      (Submodule.span ℚ ((fun q => m * q) '' A)) a hx



/-- A profile-local membership classifier for bounded Leibniz summands closes the
`hsummand` obligation: every bounded product-choice generator has a derivative
count profile `h`; admissibility transports `h` into the finite admissible-profile
cover, and the supplied membership places the shifted summand in that cover
component. -/
theorem boundedLeibnizSummandCover_of_profileSubspaceClassifier
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ)
    (hSlen : S.length = κ)
    (hclassifier : ∀ (h : ProfileHistogram) (g : MvPolynomial (Fin N) ℚ),
      g ∈ boundedProfileClassifiedSet factors constraintType S h →
      m * g ∈ profileSubspace h
        (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ σ)) :
    ∀ g ∈ boundedDistribDerivProds Finset.univ factors S S.length,
      m * g ∈ ⨆ i : Fin (admissibleProfileCoverCard κ),
        admissibleProfileCoverSpace B κ ℓ i := by
  classical
  intro g hg
  have hg_union := (boundedDistribDerivProds_subset_iUnion_bounded
    factors constraintType S) hg
  simp only [Set.mem_iUnion] at hg_union
  rcases hg_union with ⟨h, hg_profile⟩
  have hadmS : ProfileAdmissible S.length h :=
    boundedProfileClassifiedSet_profile_admissible
      factors constraintType S h g hg_profile
  have hadmκ : ProfileAdmissible κ h := by
    simpa [hSlen] using hadmS
  let ap : AdmissibleProfile κ := ⟨h, hadmκ⟩
  let i : Fin (admissibleProfileCoverCard κ) :=
    (Fintype.equivFin (AdmissibleProfile κ)) ap
  have hi : (admissibleProfileCoverEnum κ i).val = h := by
    show ((Fintype.equivFin (AdmissibleProfile κ)).symm
      ((Fintype.equivFin (AdmissibleProfile κ)) ap)).val = h
    simp [ap]
  apply Submodule.mem_iSup_of_mem i
  change m * g ∈ profileSubspace ((admissibleProfileCoverEnum κ i).val)
    (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ σ)
  simpa [hi] using hclassifier h g hg_profile

/-- Step-(b) reduction: it is enough to classify every bounded Leibniz summand
`g` of the outer derivative of the allocated local-factor product after the
left shift `m`.  The generic bounded Leibniz theorem then gives the full `hrow`
membership. -/
theorem allocatedDerivativeProduct_hrow_of_boundedLeibnizSummandCover
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (_hSlen : S.length = κ)
    (_hmdeg : m.totalDegree ≤ ℓ)
    (_hmvars : m.vars ⊆ S.toFinset)
    (_hadm : isBlockAdmissible B S)
    (hsummand : ∀ g ∈ boundedDistribDerivProds Finset.univ
        (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc) S S.length,
      m * g ∈ ⨆ i : Fin (admissibleProfileCoverCard κ),
        admissibleProfileCoverSpace B κ ℓ i) :
    m * iterDerivList S
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈
      ⨆ i : Fin (admissibleProfileCoverCard κ),
        admissibleProfileCoverSpace B κ ℓ i := by
  classical
  let A := boundedDistribDerivProds Finset.univ
        (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc) S S.length
  have hLeibniz : iterDerivList S
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈ Submodule.span ℚ A := by
    simpa [A, piPlusBooleanProjectedAllocatedDerivativeProduct_eq_prod_localFactors]
      using iterDerivList_finset_prod_mem_bounded_span S
        (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc)
  have hmul : m * iterDerivList S
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈
      Submodule.span ℚ ((fun g => m * g) '' A) :=
    mul_mem_span_image_of_mem_span m A hLeibniz
  refine (Submodule.span_le.mpr ?_) hmul
  intro q hq
  rcases hq with ⟨g, hg, rfl⟩
  simpa [A] using hsummand g hg

/-- Uniform Step-(b) reduction to the named `hrow` classifier. -/
theorem allocatedDerivativeProduct_admissibleProfileHrow_of_boundedLeibnizSummandCover
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (hsummand : ∀
      (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible B S →
      ∀ g ∈ boundedDistribDerivProds Finset.univ
          (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc) S S.length,
        m * g ∈ ⨆ i : Fin (admissibleProfileCoverCard κ),
          admissibleProfileCoverSpace B κ ℓ i) :
    AllocatedDerivativeProductAdmissibleProfileHrow
      M n hn2 htb hns D alloc B κ ℓ := by
  intro S m hSlen hmdeg hmvars hadm
  exact allocatedDerivativeProduct_hrow_of_boundedLeibnizSummandCover
    M n hn2 htb hns D alloc B κ ℓ S m hSlen hmdeg hmvars hadm
    (hsummand S m hSlen hmdeg hmvars hadm)

/-- Full allocated-product hrow from a profile-local classifier for every bounded
Leibniz summand of the allocated local-factor product.  This is the narrow final
math seam: prove `hclassifier` using per-factor derivative spans and
`profileProduct_mem_profileSubspace`; the rest of the raw-rank bound is now
formal plumbing. -/
theorem allocatedDerivativeProduct_admissibleProfileHrow_of_profileSubspaceClassifier
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (constraintType : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length → ConstraintType)
    (hclassifier : ∀
      (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible B S →
      ∀ (h : ProfileHistogram) (g : MvPolynomial
          (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
        g ∈ boundedProfileClassifiedSet
          (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc)
          constraintType S h →
        m * g ∈ profileSubspace h
          (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ σ)) :
    AllocatedDerivativeProductAdmissibleProfileHrow
      M n hn2 htb hns D alloc B κ ℓ := by
  refine allocatedDerivativeProduct_admissibleProfileHrow_of_boundedLeibnizSummandCover
    M n hn2 htb hns D alloc B κ ℓ ?_
  intro S m hSlen hmdeg hmvars hadm g hg
  exact boundedLeibnizSummandCover_of_profileSubspaceClassifier
    B κ ℓ
    (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc)
    constraintType S m hSlen
    (hclassifier S m hSlen hmdeg hmvars hadm) g hg

/-- Paper-scale version of the profile-local classifier closeout. -/
theorem paperScale_allocatedDerivativeProduct_admissibleProfileHrow_of_profileSubspaceClassifier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (κ ℓ : Nat)
    (constraintType : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length → ConstraintType)
    (hclassifier : ∀
      (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition S →
      ∀ (h : ProfileHistogram) (g : MvPolynomial
          (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ),
        g ∈ boundedProfileClassifiedSet
          (allocatedDerivativeLocalFactors M (2 ^ 804) paperScale_ge_two htb hns
            (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc)
          constraintType S h →
        m * g ∈ profileSubspace h
          (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis
            (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ σ)) :
    AllocatedDerivativeProductAdmissibleProfileHrow
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
      alloc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      κ ℓ := by
  exact allocatedDerivativeProduct_admissibleProfileHrow_of_profileSubspaceClassifier
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    alloc
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ constraintType hclassifier


/-- Step (a)+(c) closeout: once the Step-(b) `hrow` classifier is proved for
the admissible-profile cover, the raw allocated-product rank has the expected
`#admissible_profiles × withinProfileBound κ` budget. -/
theorem allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_hrow
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (hrow : AllocatedDerivativeProductAdmissibleProfileHrow
      M n hn2 htb hns D alloc B κ ℓ) :
    rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      admissibleProfileCoverCard κ * withinProfileBound κ := by
  classical
  haveI : ∀ i : Fin (admissibleProfileCoverCard κ),
      Module.Finite ℚ (admissibleProfileCoverSpace B κ ℓ i) :=
    fun i => admissibleProfileCoverSpace_finite B κ ℓ i
  exact allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
    M n hn2 htb hns D alloc B κ ℓ
    (admissibleProfileCoverSpace B κ ℓ)
    hrow
    (admissibleProfileCoverSpace_finrank_le_withinProfileBound B κ ℓ)



/-- Direct raw-rank closeout from the profile-local classifier. -/
theorem allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_profileSubspaceClassifier
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (constraintType : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length → ConstraintType)
    (hclassifier : ∀
      (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible B S →
      ∀ (h : ProfileHistogram) (g : MvPolynomial
          (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
        g ∈ boundedProfileClassifiedSet
          (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc)
          constraintType S h →
        m * g ∈ profileSubspace h
          (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ σ)) :
    rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      admissibleProfileCoverCard κ * withinProfileBound κ := by
  exact allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_hrow
    M n hn2 htb hns D alloc B κ ℓ
    (allocatedDerivativeProduct_admissibleProfileHrow_of_profileSubspaceClassifier
      M n hn2 htb hns D alloc B κ ℓ constraintType hclassifier)

/-- Paper-scale specialization of the admissible-profile-cover closeout. -/
theorem paperScale_allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_hrow
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (κ ℓ : Nat)
    (hrow : AllocatedDerivativeProductAdmissibleProfileHrow
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
      alloc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      κ ℓ) :
    rkSPDP
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ≤
      admissibleProfileCoverCard κ * withinProfileBound κ := by
  exact allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_hrow
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    alloc
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ hrow



/-! ## Closure via the existing post-shift profile span

The raw `profileSubspace` target is too small for shifted/background rows.  The
correct closure target is the repository's existing post-shift profile span
`allBoundedProfilePostSpan`, packaged by `BoundedWithinProfileFinrankClaim`.
The theorem below is intentionally a direct closeout: the allocated product is a
literal product of the allocated local factors, so the existing bounded-profile
rank assembly applies without introducing another abstraction layer. -/

/-- Closure-only adjusted target: once the allocated local-factor family has the
existing post-shift bounded within-profile finrank claim, the allocated product
has the combined profile SPDP rank bound. -/
theorem allocatedDerivativeProduct_rank_le_combinedProfileBound_of_boundedWithinProfileFinrank
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (constraintType : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length → ConstraintType)
    (hwithin : BoundedWithinProfileFinrankClaim B κ ℓ
      (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc)
      constraintType) :
    mlBlockedSpdpRank B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      combinedProfileBound κ := by
  exact rank_bound_of_boundedWithinProfileFinrank B κ ℓ
    (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc)
    constraintType
    (piPlusBooleanProjectedAllocatedDerivativeProduct M n hn2 htb hns D alloc)
    (piPlusBooleanProjectedAllocatedDerivativeProduct_eq_prod_localFactors
      M n hn2 htb hns D alloc)
    hwithin

/-- Paper-scale specialization of the post-shift profile-span closure for the
allocated derivative product. -/
theorem paperScale_allocatedDerivativeProduct_rank_le_combinedProfileBound_of_boundedWithinProfileFinrank
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (κ ℓ : Nat)
    (constraintType : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length → ConstraintType)
    (hwithin : BoundedWithinProfileFinrankClaim
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
      (allocatedDerivativeLocalFactors M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc)
      constraintType) :
    mlBlockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ≤
      combinedProfileBound κ := by
  exact allocatedDerivativeProduct_rank_le_combinedProfileBound_of_boundedWithinProfileFinrank
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    alloc
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ constraintType hwithin

/-! ## Axiom audit anchors -/

#print axioms admissibleDerivativeWindow_card_le_pow
#print axioms admissibleDerivativeWindow_card_le_paperScale
#print axioms paperScale_directWindowShiftBudget_le_pow1000
#print axioms paperScale_allocatedDerivativeProduct_rank_le_pow1000_directWindowCount
#print axioms RestrictedMonoIdx
#print axioms restrictedMonomialShiftClosure
#print axioms finrank_restrictedMonomialShiftClosure_le
#print axioms mul_mem_restrictedMonomialShiftClosure
#print axioms AdmissibleDerivativeWindow
#print axioms rawBlockedSpdpSubspace_le_admissibleRestrictedShiftDerivativeCover
#print axioms rawRank_le_sum_admissibleRestrictedShiftCounts
#print axioms card_RestrictedMonoIdx_admissibleWindow_le
#print axioms rawRank_le_admissibleWindowCount_mul_polyShift
#print axioms allocatedDerivativeProduct_rank_le_admissibleWindowCount_mul_polyShift
#print axioms paperScale_allocatedDerivativeProduct_rank_le_admissibleWindowCount_mul_polyShift
#print axioms kappaDerivativeImageSpan
#print axioms kappaLeibnizProductSpan
#print axioms kappaDerivativeImageSpan_prod_le_kappaLeibnizProductSpan
#print axioms kappaDerivativeImageSpan_allocatedProduct_le_kappaLeibnizProductSpan
#print axioms paperScale_kappaDerivativeImageSpan_allocatedProduct_le_kappaLeibnizProductSpan
#print axioms rawGenerator_mem_shiftClosure_kappaDerivativeImageSpan
#print axioms rawBlockedSpdpSubspace_le_shiftClosure_kappaDerivativeImageSpan
#print axioms rawRank_le_shiftClosure_kappaDerivativeImageSpan
#print axioms allocatedDerivativeProduct_rank_le_shiftClosure_kappaDerivativeImageSpan
#print axioms paperScale_allocatedDerivativeProduct_rank_le_shiftClosure_kappaDerivativeImageSpan
#print axioms multilinearize_allocatedDerivativeProduct_eq_normalizedFactorProduct
#print axioms allocatedNormalizedFactorProduct_multilinearizedRank_le_rawAllocatedProductRank
#print axioms rawRank_le_sum_subspaces_of_rawSubspace_le
#print axioms rawRank_le_sum_subspaces_of_generator_rows
#print axioms allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
#print axioms paperScale_allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
#print axioms boundedLeibnizSummandCover_of_profileSubspaceClassifier
#print axioms allocatedDerivativeProduct_admissibleProfileHrow_of_profileSubspaceClassifier
#print axioms paperScale_allocatedDerivativeProduct_admissibleProfileHrow_of_profileSubspaceClassifier
#print axioms allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_profileSubspaceClassifier
#print axioms allocatedDerivativeProduct_hrow_of_boundedLeibnizSummandCover
#print axioms allocatedDerivativeProduct_admissibleProfileHrow_of_boundedLeibnizSummandCover
#print axioms allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_hrow
#print axioms paperScale_allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_hrow
#print axioms allocatedDerivativeProduct_rank_le_combinedProfileBound_of_boundedWithinProfileFinrank
#print axioms paperScale_allocatedDerivativeProduct_rank_le_combinedProfileBound_of_boundedWithinProfileFinrank

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
