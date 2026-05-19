import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPDerivativeErasureObstruction

/-!
# Corrected Boolean SPDP surface: raw-derivative image rows

The obstruction in `PiPlusBoolNPDerivativeErasureObstruction` shows ordinary
partial derivatives do not descend to the Boolean quotient: quotient-equivalent
polynomials can have non-equivalent ordinary derivatives.

So the paper-faithful Boolean ambient cannot define NP rows by differentiating an
arbitrary Boolean-normal representative.  The corrected surface is:

1. take ordinary SPDP derivative rows in the raw full-ring representative;
2. map those rows into the Boolean ambient via `liftToBool`.

This makes the Boolean row space an image subspace.  The remaining NP-side rank
question is then exactly whether quotienting loses dimension, i.e. a kernel
intersection/noncollapse condition.
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
set_option maxRecDepth 4096

namespace BoolPoly

/-- Corrected Boolean SPDP subspace: raw derivative rows mapped into the Boolean
ambient.  This avoids differentiating a quotient representative. -/
noncomputable def boolRawImageBlockedSpdpSubspace {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ) :
    Submodule ℚ (BoolPoly n) :=
  Submodule.map (liftToBoolLinearMap n) (rawBlockedSpdpSubspace B κ ℓ q)

/-- Corrected Boolean SPDP rank: dimension of the raw-row image in the Boolean
ambient. -/
noncomputable def boolRawImageBlockedSpdpRank {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ) : ℕ :=
  Module.finrank ℚ (boolRawImageBlockedSpdpSubspace B κ ℓ q)

/-- Image rows are finite-dimensional because the raw source row space is. -/
instance boolRawImageBlockedSpdpSubspace_finite {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ) :
    Module.Finite ℚ (boolRawImageBlockedSpdpSubspace B κ ℓ q) := by
  unfold boolRawImageBlockedSpdpSubspace
  infer_instance

/-- The image rank is bounded above by the raw rank. -/
theorem boolRawImageBlockedSpdpRank_le_rawBlockedSpdpRank {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ) :
    boolRawImageBlockedSpdpRank B κ ℓ q ≤ rawBlockedSpdpRank B κ ℓ q := by
  unfold boolRawImageBlockedSpdpRank rawBlockedSpdpRank boolRawImageBlockedSpdpSubspace
  exact Submodule.finrank_map_le (liftToBoolLinearMap n) (rawBlockedSpdpSubspace B κ ℓ q)

/-- If the quotient kernel is disjoint from the raw row space, then the corrected
Boolean image rank is at least the raw rank. -/
theorem rawBlockedSpdpRank_le_boolRawImageBlockedSpdpRank_of_kernelDisjoint {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ)
    (hker : Disjoint (rawBlockedSpdpSubspace B κ ℓ q)
      (LinearMap.ker (liftToBoolLinearMap n))) :
    rawBlockedSpdpRank B κ ℓ q ≤ boolRawImageBlockedSpdpRank B κ ℓ q := by
  unfold rawBlockedSpdpRank boolRawImageBlockedSpdpRank boolRawImageBlockedSpdpSubspace
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
    have hmemKer : ((x - y : U) : MvPolynomial (Fin n) ℚ) ∈ LinearMap.ker f := by
      simpa [LinearMap.domRestrict_apply] using hzero
    exact Subtype.ext (Submodule.disjoint_def.mp hker
      ((x - y : U) : MvPolynomial (Fin n) ℚ) hmemU hmemKer)
  exact LinearMap.finrank_le_finrank_of_injective (f := g) hinj

/-- With kernel-disjointness, the corrected Boolean image rank equals raw rank. -/
theorem boolRawImageBlockedSpdpRank_eq_rawBlockedSpdpRank_of_kernelDisjoint {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ)
    (hker : Disjoint (rawBlockedSpdpSubspace B κ ℓ q)
      (LinearMap.ker (liftToBoolLinearMap n))) :
    boolRawImageBlockedSpdpRank B κ ℓ q = rawBlockedSpdpRank B κ ℓ q := by
  exact le_antisymm
    (boolRawImageBlockedSpdpRank_le_rawBlockedSpdpRank B κ ℓ q)
    (rawBlockedSpdpRank_le_boolRawImageBlockedSpdpRank_of_kernelDisjoint B κ ℓ q hker)

/-- Paper-scale corrected Boolean image rank for Cook--Levin source rows. -/
noncomputable def paperScaleCookLevinBoolRawImageSourceNPRank
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : ℕ :=
  boolRawImageBlockedSpdpRank
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale kernel-disjointness for the corrected raw-image source rank. -/
def PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  Disjoint
    (rawBlockedSpdpSubspace
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
    (LinearMap.ker (liftToBoolLinearMap
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))

/-- A direct raw NP lower transports to the corrected Boolean raw-image source
rank under the kernel-disjointness criterion.  This theorem deliberately avoids
unfolding the huge paper-scale legacy lower-bound wrapper; the legacy-to-raw
transport is already available separately as
`paperScaleCookLevinRawSourceNPLowerBound_of_legacyLower`. -/
theorem paperScaleCookLevinBoolRawImageSourceNPRankLower_of_rawLower_of_kernelDisjoint
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hraw : 2 ^ 804 ≤
      rawBlockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
    (hker : PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    2 ^ 804 ≤ paperScaleCookLevinBoolRawImageSourceNPRank M htb hns := by
  unfold PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint at hker
  unfold paperScaleCookLevinBoolRawImageSourceNPRank
  exact le_trans hraw
    (rawBlockedSpdpRank_le_boolRawImageBlockedSpdpRank_of_kernelDisjoint
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
      hker)

/-! ## Axiom audit anchors -/

#print axioms boolRawImageBlockedSpdpRank_le_rawBlockedSpdpRank
#print axioms rawBlockedSpdpRank_le_boolRawImageBlockedSpdpRank_of_kernelDisjoint
#print axioms boolRawImageBlockedSpdpRank_eq_rawBlockedSpdpRank_of_kernelDisjoint
#print axioms paperScaleCookLevinBoolRawImageSourceNPRankLower_of_rawLower_of_kernelDisjoint

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
