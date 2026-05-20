import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPLowerTransport

/-!
# Kernel criterion for raw-to-Boolean NP rank transport

The remaining NP-side quotient issue is exactly whether Boolean normalization
collapses any vector in the raw NP source row span.  This file packages that as
a kernel-disjoint/injectivity criterion and proves it implies the raw-to-Boolean
rank noncollapse seam used by the final Boolean Route-C bridge.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- Abstract raw-to-Boolean rank noncollapse from two exact facts:
1. Boolean normalization maps the chosen raw source row span onto the Boolean row
   span; and
2. its kernel is disjoint from that raw source row span.

The image equality is deliberately explicit because the raw polynomial need not
be definitionally the normal representative used by a `BoolPoly`. -/
theorem rawBlockedSpdpRank_le_boolBlockedSpdpRank_of_image_eq_of_disjoint_ker {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin n) ℚ) (p : BoolPoly n)
    (himage : Submodule.map (liftToBoolLinearMap n)
        (rawBlockedSpdpSubspace B κ ℓ q) = boolBlockedSpdpSubspace B κ ℓ p)
    (hdisj : Disjoint
      (rawBlockedSpdpSubspace B κ ℓ q)
      (LinearMap.ker (liftToBoolLinearMap n))) :
    rawBlockedSpdpRank B κ ℓ q ≤ boolBlockedSpdpRank B κ ℓ p := by
  unfold rawBlockedSpdpRank boolBlockedSpdpRank
  rw [← himage]
  let U := rawBlockedSpdpSubspace B κ ℓ q
  let f := liftToBoolLinearMap n
  let g : U →ₗ[ℚ] Submodule.map f U := {
    toFun := fun x => ⟨f x, Submodule.mem_map_of_mem x.property⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      simp
    map_smul' := by
      intro a x
      apply Subtype.ext
      simp }
  have hinj : Function.Injective g := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hzero : f.domRestrict U (x - y) = 0 := by
      rw [map_sub]
      change f x - f y = 0
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    have hmemU : ((x - y : U) : MvPolynomial (Fin n) ℚ) ∈ U := (x - y : U).property
    have hker : ((x - y : U) : MvPolynomial (Fin n) ℚ) ∈ LinearMap.ker f := by
      simpa [LinearMap.domRestrict_apply] using hzero
    exact Subtype.ext (Submodule.disjoint_def.mp hdisj
      ((x - y : U) : MvPolynomial (Fin n) ℚ) hmemU hker)
  exact LinearMap.finrank_le_finrank_of_injective (f := g) hinj

/-- Paper-scale image-exactness form of the raw-to-Boolean NP source transport
seam: Boolean normalization sends the raw Cook-Levin source row span onto the
Boolean source row span. -/
def PaperScaleCookLevinRawToBoolSourceNPImageExact
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  Submodule.map (liftToBoolLinearMap
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars)
    (rawBlockedSpdpSubspace
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) =
    boolBlockedSpdpSubspace
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (paperScaleCompiledBoolPoly M htb hns)

/-- Paper-scale kernel-disjoint form of the raw-to-Boolean NP source transport
seam. -/
def PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  Disjoint
    (rawBlockedSpdpSubspace
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
    (LinearMap.ker (liftToBoolLinearMap
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))

/-- Exact kernel-disjointness criterion for the raw-to-Boolean quotient map:
`U` is disjoint from the Boolean-normalization kernel iff Boolean normalization
is injective on `U`.  This removes the vague "noncollapse" phrasing: the NP
transport needs precisely this restricted injectivity statement. -/
theorem disjoint_liftToBool_kernel_iff_normalize_injective_on {n : ℕ}
    (U : Submodule ℚ (MvPolynomial (Fin n) ℚ)) :
    Disjoint U (LinearMap.ker (liftToBoolLinearMap n)) ↔
      ∀ x : MvPolynomial (Fin n) ℚ, x ∈ U →
        zeroProfileBooleanNormalize x = 0 → x = 0 := by
  constructor
  · intro hdisj x hxU hnorm
    have hxker : x ∈ LinearMap.ker (liftToBoolLinearMap n) := by
      change liftToBoolLinearMap n x = 0
      apply BoolPoly.ext
      simpa using hnorm
    exact Submodule.disjoint_def.mp hdisj x hxU hxker
  · intro hinj
    rw [Submodule.disjoint_def]
    intro x hxU hxker
    apply hinj x hxU
    have hc := congrArg (fun r : BoolPoly n => (r : MvPolynomial (Fin n) ℚ)) hxker
    simpa [liftToBoolLinearMap, liftToBool, zero] using hc

/-- Submodule of raw polynomials whose every supported monomial is multilinear.
Unlike the quotient-normal-form space, this is an honest linear subspace of the
raw polynomial ring. -/
noncomputable def multilinearSupportSubmodule (n : ℕ) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) where
  carrier := {p | IsMultilinear p}
  zero_mem' := by
    intro α hα i
    simp at hα
  add_mem' := by
    intro p q hp hq α hα i
    have hsub : (p + q).support ⊆ p.support ∪ q.support := Finsupp.support_add
    have hαu := hsub hα
    simp only [Finset.mem_union] at hαu
    cases hαu with
    | inl hpα => exact hp α hpα i
    | inr hqα => exact hq α hqα i
  smul_mem' := by
    intro c p hp α hα i
    have hsub : (c • p).support ⊆ p.support := Finsupp.support_smul
    exact hp α (hsub hα) i

@[simp] theorem mem_multilinearSupportSubmodule_iff {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    p ∈ multilinearSupportSubmodule n ↔ IsMultilinear p := Iff.rfl

/-- Boolean normalization is injective on genuinely multilinear polynomials:
if every monomial already has all exponents at most one, normalization is the
identity, so a normalized zero polynomial was zero already. -/
theorem zeroProfileBooleanNormalize_eq_zero_of_isMultilinear_iff_zero {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (hp : IsMultilinear p) :
    zeroProfileBooleanNormalize p = 0 ↔ p = 0 := by
  constructor
  · intro h
    rw [zeroProfileBooleanNormalize_of_support_isMultilinear p hp] at h
    exact h
  · intro h
    rw [h]
    simp

/-- A subspace consisting entirely of multilinear polynomials is disjoint from
the Boolean-normalization kernel.  This is the clean positive algebraic route
around square-residual collapse. -/
theorem disjoint_liftToBool_kernel_of_forall_isMultilinear {n : ℕ}
    (U : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hU : ∀ x : MvPolynomial (Fin n) ℚ, x ∈ U → IsMultilinear x) :
    Disjoint U (LinearMap.ker (liftToBoolLinearMap n)) := by
  rw [disjoint_liftToBool_kernel_iff_normalize_injective_on]
  intro x hxU hnorm
  exact (zeroProfileBooleanNormalize_eq_zero_of_isMultilinear_iff_zero x (hU x hxU)).mp hnorm

/-- A subspace contained in the multilinear-support submodule is disjoint from
the Boolean-normalization kernel. -/
theorem disjoint_liftToBool_kernel_of_le_multilinearSupportSubmodule {n : ℕ}
    (U : Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hU : U ≤ multilinearSupportSubmodule n) :
    Disjoint U (LinearMap.ker (liftToBoolLinearMap n)) := by
  exact disjoint_liftToBool_kernel_of_forall_isMultilinear U
    (fun x hx => (mem_multilinearSupportSubmodule_iff x).mp (hU hx))

/-- Generator-level multilinearity for a raw strict-κ SPDP source span. -/
def RawBlockedSpdpGeneratorsMultilinear {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ),
    S.length = κ → m.totalDegree ≤ ℓ → m.vars ⊆ S.toFinset →
    isBlockAdmissible B S → IsMultilinear (m * iterDerivList S q)

/-- If all raw SPDP generators are multilinear, then the raw source span is
contained in the multilinear-support submodule. -/
theorem rawBlockedSpdpSubspace_le_multilinearSupportSubmodule_of_generators {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ)
    (hgen : RawBlockedSpdpGeneratorsMultilinear B κ ℓ q) :
    rawBlockedSpdpSubspace B κ ℓ q ≤ multilinearSupportSubmodule n := by
  unfold rawBlockedSpdpSubspace
  apply Submodule.span_le.mpr
  intro r hr
  rcases hr with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  exact (mem_multilinearSupportSubmodule_iff _).mpr
    (hgen S m hlen hdeg hvars hadm)

/-- Generator-level multilinearity closes kernel-disjointness for the raw source
span. -/
theorem rawBlockedSpdp_kernelDisjoint_of_generators_multilinear {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ)
    (hgen : RawBlockedSpdpGeneratorsMultilinear B κ ℓ q) :
    Disjoint (rawBlockedSpdpSubspace B κ ℓ q)
      (LinearMap.ker (liftToBoolLinearMap n)) := by
  exact disjoint_liftToBool_kernel_of_le_multilinearSupportSubmodule _
    (rawBlockedSpdpSubspace_le_multilinearSupportSubmodule_of_generators
      B κ ℓ q hgen)

/-- Paper-scale kernel-disjointness is exactly restricted injectivity of Boolean
normalization on the Cook--Levin raw NP source row span. -/
theorem paperScaleCookLevinRawToBoolSourceNPKernelDisjoint_iff_normalize_injective_on
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns ↔
      ∀ x : MvPolynomial
          (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ,
        x ∈ rawBlockedSpdpSubspace
          (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
          (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
          (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)) →
        zeroProfileBooleanNormalize x = 0 → x = 0 := by
  unfold PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint
  exact disjoint_liftToBool_kernel_iff_normalize_injective_on _

/-- Paper-scale generator-level multilinearity of the Cook--Levin raw NP source
rows. -/
def PaperScaleCookLevinRawToBoolSourceNPGeneratorsMultilinear
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  RawBlockedSpdpGeneratorsMultilinear
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- If the Cook--Levin raw NP source generators are multilinear, then the
raw-to-Boolean kernel-disjointness field follows. -/
theorem paperScaleCookLevinRawToBoolSourceNPKernelDisjoint_of_generators_multilinear
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hgen : PaperScaleCookLevinRawToBoolSourceNPGeneratorsMultilinear M htb hns) :
    PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns := by
  unfold PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint
    PaperScaleCookLevinRawToBoolSourceNPGeneratorsMultilinear at *
  exact rawBlockedSpdp_kernelDisjoint_of_generators_multilinear
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hgen

/-- If the Cook--Levin raw NP source row span is multilinear, then the required
raw-to-Boolean kernel-disjointness follows.  This turns the quotient-noncollapse
problem into the concrete row-shape theorem: every raw NP source row must already
be multilinear. -/
theorem paperScaleCookLevinRawToBoolSourceNPKernelDisjoint_of_rawSpan_isMultilinear
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hml : ∀ x : MvPolynomial
          (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ,
        x ∈ rawBlockedSpdpSubspace
          (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
          (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
          (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)) →
        IsMultilinear x) :
    PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns := by
  unfold PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint
  exact disjoint_liftToBool_kernel_of_forall_isMultilinear _ hml

/-! ## Booleanity obstruction to the naive multilinear-source route -/

/-- The shifted derivative of the one-variable Booleanity product is not
multilinear.  Concretely, `X * ∂(1 - X + X²)` contains the raw monomial
`2 X²`.  This pins down why the sufficient multilinearity criterion above is
not automatic for Cook--Levin Booleanity factors. -/
theorem X_mul_iterDerivList_cookLevinBooleanFactorProd_oneVar_not_isMultilinear :
    ¬ IsMultilinear
      ((X (0 : Fin 1)) * iterDerivList [(0 : Fin 1)] (cookLevinBooleanFactorProd 1) :
        MvPolynomial (Fin 1) ℚ) := by
  intro hml
  have hpoly :
      (X (0 : Fin 1)) * iterDerivList [(0 : Fin 1)] (cookLevinBooleanFactorProd 1) =
        (X (0 : Fin 1)) * (((-1 : MvPolynomial (Fin 1) ℚ) + 2 * X 0)) := by
    unfold iterDerivList
    simp only [List.foldl_cons, List.foldl_nil]
    rw [cookLevinBooleanFactorProd_eq_finRange]
    simp [List.finRange]
    rw [pderiv_cookLevinBooleanFactor_self]
  have hcoeff : coeff (Finsupp.single (0 : Fin 1) 2)
      ((X (0 : Fin 1)) * (((-1 : MvPolynomial (Fin 1) ℚ) + 2 * X 0))) = 2 := by
    ring_nf
    rw [MvPolynomial.coeff_add]
    have hneg : coeff (Finsupp.single (0 : Fin 1) 2)
        (-(X (0 : Fin 1)) : MvPolynomial (Fin 1) ℚ) = 0 := by
      simp [MvPolynomial.X]
    rw [hneg]
    simp only [zero_add]
    rw [MvPolynomial.X_pow_eq_monomial]
    change coeff (Finsupp.single (0 : Fin 1) 2)
      (((MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 2)) (1 : ℚ)) * C (2 : ℚ)) = 2
    rw [show ((MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 2)) (1 : ℚ)) * C (2 : ℚ) =
        C (2 : ℚ) * ((MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 2)) (1 : ℚ)) by ring]
    rw [MvPolynomial.C_mul_monomial]
    rw [MvPolynomial.coeff_monomial]
    simp
  have hsupp : Finsupp.single (0 : Fin 1) 2 ∈
      ((X (0 : Fin 1)) * (((-1 : MvPolynomial (Fin 1) ℚ) + 2 * X 0)) :
        MvPolynomial (Fin 1) ℚ).support := by
    rw [MvPolynomial.mem_support_iff]
    rw [hcoeff]
    norm_num
  rw [hpoly] at hml
  have hle := hml (Finsupp.single (0 : Fin 1) 2) hsupp (0 : Fin 1)
  simp at hle

/-- Therefore the generator-level multilinearity condition is false already for
the minimal Booleanity source when the one active derivative window is
admissible. -/
theorem not_RawBlockedSpdpGeneratorsMultilinear_oneVar_booleanity
    (B : BlockPartition 1)
    (hadm : isBlockAdmissible B [(0 : Fin 1)]) :
    ¬ RawBlockedSpdpGeneratorsMultilinear B 1 1 (cookLevinBooleanFactorProd 1) := by
  intro hgen
  exact X_mul_iterDerivList_cookLevinBooleanFactorProd_oneVar_not_isMultilinear
    (hgen [(0 : Fin 1)] (X (0 : Fin 1)) (by simp) (by simp) (by simp) hadm)

/-- The same non-multilinear shifted derivative is an actual raw SPDP generator
in the one-variable Booleanity source span. -/
theorem X_mul_iterDerivList_cookLevinBooleanFactorProd_oneVar_mem_rawBlockedSpdpSubspace
    (B : BlockPartition 1)
    (hadm : isBlockAdmissible B [(0 : Fin 1)]) :
    ((X (0 : Fin 1)) * iterDerivList [(0 : Fin 1)] (cookLevinBooleanFactorProd 1) :
        MvPolynomial (Fin 1) ℚ) ∈ rawBlockedSpdpSubspace B 1 1 (cookLevinBooleanFactorProd 1) := by
  unfold rawBlockedSpdpSubspace
  apply Submodule.subset_span
  exact ⟨[(0 : Fin 1)], X (0 : Fin 1), by simp, by simp, by simp, hadm, rfl⟩

/-- Hence the one-variable Booleanity raw source span is not contained in the
raw multilinear-support submodule.  The remaining noncollapse theorem must use
a more delicate invariant than blanket raw multilinearity. -/
theorem not_rawBlockedSpdpSubspace_le_multilinearSupportSubmodule_oneVar_booleanity
    (B : BlockPartition 1)
    (hadm : isBlockAdmissible B [(0 : Fin 1)]) :
    ¬ rawBlockedSpdpSubspace B 1 1 (cookLevinBooleanFactorProd 1) ≤ multilinearSupportSubmodule 1 := by
  intro hle
  exact X_mul_iterDerivList_cookLevinBooleanFactorProd_oneVar_not_isMultilinear
    ((mem_multilinearSupportSubmodule_iff _).mp
      (hle (X_mul_iterDerivList_cookLevinBooleanFactorProd_oneVar_mem_rawBlockedSpdpSubspace B hadm)))

/-- Evaluation at the Booleanity critical point `X = 1/2` in one variable. -/
noncomputable def evalHalfOneVar (p : MvPolynomial (Fin 1) ℚ) : ℚ :=
  MvPolynomial.eval (fun _ : Fin 1 => (1/2 : ℚ)) p

/-- The raw square residual does not vanish at `X = 1/2`. -/
theorem evalHalfOneVar_square_residual :
    evalHalfOneVar (X (0 : Fin 1) * X (0 : Fin 1) - X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ) = (-1/4 : ℚ) := by
  simp [evalHalfOneVar]
  norm_num

/-- The differentiated one-variable Booleanity factor vanishes at `X = 1/2`. -/
theorem evalHalfOneVar_deriv_booleanity :
    evalHalfOneVar (iterDerivList [(0 : Fin 1)] (cookLevinBooleanFactorProd 1)) = 0 := by
  unfold evalHalfOneVar
  unfold iterDerivList
  simp only [List.foldl_cons, List.foldl_nil]
  rw [cookLevinBooleanFactorProd_eq_finRange]
  simp [List.finRange]
  rw [pderiv_cookLevinBooleanFactor_self]
  simp

/-- Every row in the one-variable Booleanity raw source span vanishes at `X = 1/2`. -/
theorem evalHalfOneVar_eq_zero_of_mem_raw_oneVar_booleanity
    (B : BlockPartition 1)
    {x : MvPolynomial (Fin 1) ℚ}
    (hx : x ∈ rawBlockedSpdpSubspace B 1 1 (cookLevinBooleanFactorProd 1)) :
    evalHalfOneVar x = 0 := by
  unfold rawBlockedSpdpSubspace at hx
  refine Submodule.span_induction (p := fun x _ => evalHalfOneVar x = 0) ?hgen ?hzero ?hadd ?hsmul hx
  · intro q hq
    rcases hq with ⟨S, m, hlen, hdeg, hvars, hAdm, rfl⟩
    have hS : S = [(0 : Fin 1)] := by
      cases S with
      | nil => simp at hlen
      | cons a t =>
        have ha : a = (0 : Fin 1) := by ext; simp
        have ht : t = [] := by
          cases t with
          | nil => rfl
          | cons b u => simp at hlen
        simp [ha, ht]
    subst S
    unfold evalHalfOneVar
    rw [map_mul]
    have hD : (MvPolynomial.eval (fun _ : Fin 1 => (1 / 2 : ℚ))
        (iterDerivList [(0 : Fin 1)] (cookLevinBooleanFactorProd 1))) = 0 := by
      simpa [evalHalfOneVar] using evalHalfOneVar_deriv_booleanity
    rw [hD]
    ring
  · simp [evalHalfOneVar]
  · intro x y _ _ hx hy
    unfold evalHalfOneVar at *
    rw [map_add, hx, hy]
    ring
  · intro a x _ hx
    unfold evalHalfOneVar at *
    simpa using Or.inr hx

/-- Consequently, the square residual `X² - X` is not in the one-variable
Booleanity raw source span.  This is a positive nonmembership result beyond the
failed blanket multilinearity criterion. -/
theorem square_residual_not_mem_raw_oneVar_booleanity (B : BlockPartition 1) :
    (X (0 : Fin 1) * X (0 : Fin 1) - X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ) ∉
      rawBlockedSpdpSubspace B 1 1 (cookLevinBooleanFactorProd 1) := by
  intro hmem
  have hzero := evalHalfOneVar_eq_zero_of_mem_raw_oneVar_booleanity B hmem
  have hval := evalHalfOneVar_square_residual
  rw [hval] at hzero
  norm_num at hzero


/-- The Boolean square residual is always killed by the raw-to-Boolean quotient
map.  This is the concrete kernel direction that any NP noncollapse proof must
exclude from the raw source row span. -/
theorem square_residual_mem_liftToBool_kernel {n : ℕ} (i : Fin n) :
    (X i * X i - X i : MvPolynomial (Fin n) ℚ) ∈
      LinearMap.ker (liftToBoolLinearMap n) := by
  change liftToBoolLinearMap n (X i * X i - X i : MvPolynomial (Fin n) ℚ) = 0
  change liftToBool (X i * X i - X i : MvPolynomial (Fin n) ℚ) = 0
  exact lift_square_residual_eq_zero i

/-- The Boolean square residual is nonzero in the raw polynomial ring.  Hence it
is a genuine potential kernel witness, not syntactic noise. -/
theorem square_residual_ne_zero {n : ℕ} (i : Fin n) :
    (X i * X i - X i : MvPolynomial (Fin n) ℚ) ≠ 0 := by
  intro h
  have hc2 := congrArg (fun p : MvPolynomial (Fin n) ℚ =>
    coeff (Finsupp.single i 2) p) h
  have hone_two : (Finsupp.single i 1 : Fin n →₀ Nat) ≠ Finsupp.single i 2 := by
    intro h12
    have hv := congrArg (fun f : Fin n →₀ Nat => f i) h12
    simp at hv
  have hcoeff_x : coeff (Finsupp.single i 2) (X i : MvPolynomial (Fin n) ℚ) = 0 := by
    simp [MvPolynomial.X, hone_two]
  have hcoeff_x2 : coeff (Finsupp.single i 2)
      (X i * X i : MvPolynomial (Fin n) ℚ) = 1 := by
    rw [← pow_two]
    rw [MvPolynomial.X_pow_eq_monomial]
    rw [MvPolynomial.coeff_monomial]
    simp
  simp [hcoeff_x, hcoeff_x2] at hc2

/-- The square residual is not multilinear as a raw polynomial: the `Xᵢ²`
coefficient survives before quotienting. -/
theorem square_residual_not_isMultilinear {n : ℕ} (i : Fin n) :
    ¬ IsMultilinear (X i * X i - X i : MvPolynomial (Fin n) ℚ) := by
  intro hml
  have hone_two : (Finsupp.single i 1 : Fin n →₀ Nat) ≠ Finsupp.single i 2 := by
    intro h12
    have hv := congrArg (fun f : Fin n →₀ Nat => f i) h12
    simp at hv
  have hcoeff_x : coeff (Finsupp.single i 2) (X i : MvPolynomial (Fin n) ℚ) = 0 := by
    simp [MvPolynomial.X, hone_two]
  have hcoeff_x2 : coeff (Finsupp.single i 2)
      (X i * X i : MvPolynomial (Fin n) ℚ) = 1 := by
    rw [← pow_two]
    rw [MvPolynomial.X_pow_eq_monomial]
    rw [MvPolynomial.coeff_monomial]
    simp
  have hsupp : Finsupp.single i 2 ∈
      (X i * X i - X i : MvPolynomial (Fin n) ℚ).support := by
    rw [MvPolynomial.mem_support_iff]
    simp [hcoeff_x, hcoeff_x2]
  have hle := hml (Finsupp.single i 2) hsupp i
  simp at hle

/-- Equivalently, the square residual is excluded from the multilinear-support
submodule. -/
theorem square_residual_not_mem_multilinearSupportSubmodule {n : ℕ} (i : Fin n) :
    (X i * X i - X i : MvPolynomial (Fin n) ℚ) ∉ multilinearSupportSubmodule n := by
  intro hmem
  exact square_residual_not_isMultilinear i
    ((mem_multilinearSupportSubmodule_iff _).mp hmem)

/-- If a row span is contained in the multilinear-support submodule, then it
cannot contain any square residual.  This gives a concrete exclusion theorem for
the simplest Boolean-quotient kernel witnesses. -/
theorem square_residual_not_mem_of_le_multilinearSupportSubmodule {n : ℕ}
    (U : Submodule ℚ (MvPolynomial (Fin n) ℚ)) (i : Fin n)
    (hU : U ≤ multilinearSupportSubmodule n) :
    (X i * X i - X i : MvPolynomial (Fin n) ℚ) ∉ U := by
  intro hmem
  exact square_residual_not_mem_multilinearSupportSubmodule i (hU hmem)

/-- Generator-level multilinearity excludes square residuals from raw SPDP
source spans. -/
theorem square_residual_not_mem_rawBlockedSpdpSubspace_of_generators_multilinear {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ)
    (hgen : RawBlockedSpdpGeneratorsMultilinear B κ ℓ q) (i : Fin n) :
    (X i * X i - X i : MvPolynomial (Fin n) ℚ) ∉ rawBlockedSpdpSubspace B κ ℓ q := by
  exact square_residual_not_mem_of_le_multilinearSupportSubmodule _ i
    (rawBlockedSpdpSubspace_le_multilinearSupportSubmodule_of_generators
      B κ ℓ q hgen)

/-- Paper-scale version: generator-level multilinearity excludes every Boolean
square residual from the Cook--Levin raw NP source span. -/
theorem square_residual_not_mem_paperScaleCookLevinRawSource_of_generators_multilinear
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hgen : PaperScaleCookLevinRawToBoolSourceNPGeneratorsMultilinear M htb hns)
    (i : Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) :
    (X i * X i - X i : MvPolynomial
        (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ) ∉
      rawBlockedSpdpSubspace
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)) := by
  unfold PaperScaleCookLevinRawToBoolSourceNPGeneratorsMultilinear at hgen
  exact square_residual_not_mem_rawBlockedSpdpSubspace_of_generators_multilinear
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hgen i

/-- Kernel-disjointness fails as soon as the raw source span contains a nonzero
square residual.  This isolates the exact obstruction to closing the Boolean
NP-source lower bound by a blanket quotient-injectivity claim. -/
theorem not_disjoint_liftToBool_kernel_of_square_residual_mem {n : ℕ}
    (U : Submodule ℚ (MvPolynomial (Fin n) ℚ)) (i : Fin n)
    (hmem : (X i * X i - X i : MvPolynomial (Fin n) ℚ) ∈ U) :
    ¬ Disjoint U (LinearMap.ker (liftToBoolLinearMap n)) := by
  intro hdisj
  have hzero := Submodule.disjoint_def.mp hdisj
    (X i * X i - X i : MvPolynomial (Fin n) ℚ)
    hmem (square_residual_mem_liftToBool_kernel i)
  exact square_residual_ne_zero i hzero

/-- Paper-scale obstruction surface: to prove the Cook--Levin raw-to-Boolean NP
kernel-disjointness, one must prove that no Boolean square residual occurs in
the raw NP source span.  If such a residual is present, the desired
kernel-disjoint field is false. -/
theorem not_paperScaleCookLevinRawToBoolSourceNPKernelDisjoint_of_square_residual_mem
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (i : Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars)
    (hmem : (X i * X i - X i : MvPolynomial
        (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ) ∈
      rawBlockedSpdpSubspace
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) :
    ¬ PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns := by
  unfold PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint
  exact not_disjoint_liftToBool_kernel_of_square_residual_mem _ i hmem

/-- The kernel-disjoint criterion closes the raw-to-Boolean NP rank lower seam. -/
theorem paperScaleCookLevinRawToBoolSourceNPRankLower_of_imageExact_of_kernelDisjoint
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (himage : PaperScaleCookLevinRawToBoolSourceNPImageExact M htb hns)
    (hdisj : PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns) :
    PaperScaleCookLevinRawToBoolSourceNPRankLower M htb hns := by
  unfold PaperScaleCookLevinRawToBoolSourceNPImageExact
    PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint
    PaperScaleCookLevinRawToBoolSourceNPRankLower at *
  exact rawBlockedSpdpRank_le_boolBlockedSpdpRank_of_image_eq_of_disjoint_ker
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    (paperScaleCompiledBoolPoly M htb hns)
    himage hdisj

/-- Final no-decider surface using the kernel-disjoint Boolean-normalization
criterion rather than an opaque raw-to-Boolean rank inequality. -/
theorem no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPKernelDisjointFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HrowInc : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns)
    (Hrow : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns)
    (HP : DecidesSAT M → PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns)
    (Himage : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPImageExact M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolRowPayloadsAndRawToBoolNPTransportFromDecider
    M htb hns HrowInc Hrow HP
  intro hdec
  exact paperScaleCookLevinRawToBoolSourceNPRankLower_of_imageExact_of_kernelDisjoint
    M htb hns (Himage hdec) (Hker hdec)

/-! ## Axiom audit anchors -/

#print axioms rawBlockedSpdpRank_le_boolBlockedSpdpRank_of_image_eq_of_disjoint_ker
#print axioms multilinearSupportSubmodule
#print axioms disjoint_liftToBool_kernel_iff_normalize_injective_on
#print axioms zeroProfileBooleanNormalize_eq_zero_of_isMultilinear_iff_zero
#print axioms disjoint_liftToBool_kernel_of_forall_isMultilinear
#print axioms disjoint_liftToBool_kernel_of_le_multilinearSupportSubmodule
#print axioms rawBlockedSpdpSubspace_le_multilinearSupportSubmodule_of_generators
#print axioms rawBlockedSpdp_kernelDisjoint_of_generators_multilinear
#print axioms paperScaleCookLevinRawToBoolSourceNPKernelDisjoint_iff_normalize_injective_on
#print axioms paperScaleCookLevinRawToBoolSourceNPKernelDisjoint_of_generators_multilinear
#print axioms paperScaleCookLevinRawToBoolSourceNPKernelDisjoint_of_rawSpan_isMultilinear
#print axioms X_mul_iterDerivList_cookLevinBooleanFactorProd_oneVar_not_isMultilinear
#print axioms not_RawBlockedSpdpGeneratorsMultilinear_oneVar_booleanity
#print axioms X_mul_iterDerivList_cookLevinBooleanFactorProd_oneVar_mem_rawBlockedSpdpSubspace
#print axioms not_rawBlockedSpdpSubspace_le_multilinearSupportSubmodule_oneVar_booleanity
#print axioms evalHalfOneVar_square_residual
#print axioms evalHalfOneVar_deriv_booleanity
#print axioms evalHalfOneVar_eq_zero_of_mem_raw_oneVar_booleanity
#print axioms square_residual_not_mem_raw_oneVar_booleanity
#print axioms square_residual_mem_liftToBool_kernel
#print axioms square_residual_ne_zero
#print axioms square_residual_not_isMultilinear
#print axioms square_residual_not_mem_multilinearSupportSubmodule
#print axioms square_residual_not_mem_of_le_multilinearSupportSubmodule
#print axioms square_residual_not_mem_rawBlockedSpdpSubspace_of_generators_multilinear
#print axioms square_residual_not_mem_paperScaleCookLevinRawSource_of_generators_multilinear
#print axioms not_disjoint_liftToBool_kernel_of_square_residual_mem
#print axioms not_paperScaleCookLevinRawToBoolSourceNPKernelDisjoint_of_square_residual_mem
#print axioms paperScaleCookLevinRawToBoolSourceNPRankLower_of_imageExact_of_kernelDisjoint
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPKernelDisjointFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
