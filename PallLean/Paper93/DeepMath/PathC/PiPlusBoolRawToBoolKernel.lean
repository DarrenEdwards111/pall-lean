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
#print axioms disjoint_liftToBool_kernel_iff_normalize_injective_on
#print axioms paperScaleCookLevinRawToBoolSourceNPKernelDisjoint_iff_normalize_injective_on
#print axioms square_residual_mem_liftToBool_kernel
#print axioms square_residual_ne_zero
#print axioms not_disjoint_liftToBool_kernel_of_square_residual_mem
#print axioms not_paperScaleCookLevinRawToBoolSourceNPKernelDisjoint_of_square_residual_mem
#print axioms paperScaleCookLevinRawToBoolSourceNPRankLower_of_imageExact_of_kernelDisjoint
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPKernelDisjointFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
