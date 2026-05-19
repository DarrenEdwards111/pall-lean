import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawToBoolKernel

/-!
# Generator criteria for Boolean NP image exactness

`PiPlusBoolRawToBoolKernel` reduces raw-to-Boolean NP rank transport to image
exactness plus kernel-disjointness.  This file opens the image-exactness seam:
it is enough to prove the two generator-level inclusions between raw lifted rows
and Boolean rows.
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

/-- Forward generator image criterion: every lifted raw generator lands in the
Boolean row space. -/
def RawToBoolImageForwardGenerators {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin n) ℚ) (p : BoolPoly n) : Prop :=
  ∀ (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ),
    S.length = κ → m.totalDegree ≤ ℓ → m.vars ⊆ S.toFinset →
    isBlockAdmissible B S →
      liftToBool (m * iterDerivList S q) ∈ boolBlockedSpdpSubspace B κ ℓ p

/-- Reverse generator image criterion: every Boolean generator has a preimage in
the raw row span after Boolean normalization. -/
def RawToBoolImageReverseGenerators {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin n) ℚ) (p : BoolPoly n) : Prop :=
  ∀ (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ),
    S.length = κ → m.totalDegree ≤ ℓ → m.vars ⊆ S.toFinset →
    isBlockAdmissible B S →
      liftToBool (m * iterDerivList S (p : MvPolynomial (Fin n) ℚ)) ∈
        Submodule.map (liftToBoolLinearMap n) (rawBlockedSpdpSubspace B κ ℓ q)

/-- Forward generator criterion implies forward subspace inclusion. -/
theorem rawToBool_image_forward_of_generators {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin n) ℚ) (p : BoolPoly n)
    (hgen : RawToBoolImageForwardGenerators B κ ℓ q p) :
    Submodule.map (liftToBoolLinearMap n) (rawBlockedSpdpSubspace B κ ℓ q) ≤
      boolBlockedSpdpSubspace B κ ℓ p := by
  rw [rawBlockedSpdpSubspace, Submodule.map_span]
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨r, hr, rfl⟩
  rcases hr with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  exact hgen S m hlen hdeg hvars hadm

/-- Reverse generator criterion implies reverse subspace inclusion. -/
theorem rawToBool_image_reverse_of_generators {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin n) ℚ) (p : BoolPoly n)
    (hgen : RawToBoolImageReverseGenerators B κ ℓ q p) :
    boolBlockedSpdpSubspace B κ ℓ p ≤
      Submodule.map (liftToBoolLinearMap n) (rawBlockedSpdpSubspace B κ ℓ q) := by
  rw [boolBlockedSpdpSubspace]
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  exact hgen S m hlen hdeg hvars hadm

/-- The two generator criteria imply exact image equality. -/
theorem rawToBool_image_exact_of_generators {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin n) ℚ) (p : BoolPoly n)
    (hfwd : RawToBoolImageForwardGenerators B κ ℓ q p)
    (hrev : RawToBoolImageReverseGenerators B κ ℓ q p) :
    Submodule.map (liftToBoolLinearMap n) (rawBlockedSpdpSubspace B κ ℓ q) =
      boolBlockedSpdpSubspace B κ ℓ p :=
  le_antisymm
    (rawToBool_image_forward_of_generators B κ ℓ q p hfwd)
    (rawToBool_image_reverse_of_generators B κ ℓ q p hrev)

/-- Paper-scale forward generator criterion for Cook-Levin NP image exactness. -/
def PaperScaleCookLevinRawToBoolSourceNPImageForwardGenerators
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  RawToBoolImageForwardGenerators
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    (paperScaleCompiledBoolPoly M htb hns)

/-- Paper-scale reverse generator criterion for Cook-Levin NP image exactness. -/
def PaperScaleCookLevinRawToBoolSourceNPImageReverseGenerators
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  RawToBoolImageReverseGenerators
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    (paperScaleCompiledBoolPoly M htb hns)

/-- Paper-scale generator criteria imply the image-exactness field used by the
kernel criterion. -/
theorem paperScaleCookLevinRawToBoolSourceNPImageExact_of_generators
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfwd : PaperScaleCookLevinRawToBoolSourceNPImageForwardGenerators M htb hns)
    (hrev : PaperScaleCookLevinRawToBoolSourceNPImageReverseGenerators M htb hns) :
    PaperScaleCookLevinRawToBoolSourceNPImageExact M htb hns := by
  unfold PaperScaleCookLevinRawToBoolSourceNPImageExact
    PaperScaleCookLevinRawToBoolSourceNPImageForwardGenerators
    PaperScaleCookLevinRawToBoolSourceNPImageReverseGenerators at *
  exact rawToBool_image_exact_of_generators
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    (paperScaleCompiledBoolPoly M htb hns)
    hfwd hrev

/-- Final no-decider surface with image exactness split into generator-level
forward/reverse obligations. -/
theorem no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPImageGeneratorsKernelFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HrowInc : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns)
    (Hrow : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns)
    (HP : DecidesSAT M → PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns)
    (Hfwd : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPImageForwardGenerators M htb hns)
    (Hrev : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPImageReverseGenerators M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPKernelDisjointFromDecider
    M htb hns HrowInc Hrow HP
  · intro hdec
    exact paperScaleCookLevinRawToBoolSourceNPImageExact_of_generators
      M htb hns (Hfwd hdec) (Hrev hdec)
  · exact Hker

/-! ## Axiom audit anchors -/

#print axioms rawToBool_image_forward_of_generators
#print axioms rawToBool_image_reverse_of_generators
#print axioms rawToBool_image_exact_of_generators
#print axioms paperScaleCookLevinRawToBoolSourceNPImageExact_of_generators
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPImageGeneratorsKernelFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
