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
#print axioms paperScaleCookLevinRawToBoolSourceNPRankLower_of_imageExact_of_kernelDisjoint
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPKernelDisjointFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
