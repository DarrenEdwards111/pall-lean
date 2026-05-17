import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedCookLevinLocalAction

/-!
# Strict Cook--Levin lift for Boolean-projected Pi+

The old `PiPlusSATTransform.block_local_hadamard_lift` field is only a `Prop`,
and the concrete block-coordinate transform currently inhabits it with `True`.
That proves the coordinate bookkeeping, but it does **not** connect the
Hadamard block action to the Cook--Levin compiled polynomial or to the SPDP row
spaces.

This file adds the non-fake replacement interface.  A strict lift must carry the
actual row-space transport facts needed by the Boolean-projected local-action
lemma.  No axiom is introduced here, and the concrete paper-scale transform is
not silently upgraded: whoever closes Route C still has to prove the two fields
below from Cook--Levin locality.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- A strict, non-vacuous block-local Cook--Levin lift for `Pi+ᵦ`.

This is the theorem content that `block_local_hadamard_lift := True` did not
supply: the block-coordinate Hadamard action has to transport the final
Cook--Levin SPDP rows in exactly the two ways consumed by the Route-C closeout.
-/
structure PiPlusStrictCookLevinBooleanProjectedLift
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop where
  /-- The old coordinate/locality token is retained, but is no longer treated as
  mathematical payload by itself. -/
  block_local : piP.block_local_hadamard_lift
  /-- P-side row theorem: every final-window row of `Pi+ᵦ(compiledPoly)` has a
  raw `Pi+` pullback lying in the one-window enlarged source SPDP subspace. -/
  compiled_row_pullback :
    PiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
      extraK extraL M n hn2 htb hns piP
  /-- NP-side row theorem: the source final-window compiled SPDP row space is
  contained in the Boolean-projected target final-window row space. -/
  np_window_row_space_transport :
    PiPlusBooleanProjectedNPWindowSubspaceInclusion M n hn2 htb hns piP

/-- The strict lift is exactly strong enough to produce the existing local-action
lemma; this is a real bridge, not a `True` placeholder. -/
theorem cookLevinLocalActionLemma_of_strictLift
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hstrict : PiPlusStrictCookLevinBooleanProjectedLift
      extraK extraL M n hn2 htb hns piP) :
    PiPlusBooleanProjectedCookLevinLocalActionLemma
      extraK extraL M n hn2 htb hns piP where
  p_compiled_generator_pullback := hstrict.compiled_row_pullback
  np_compiled_window_preservation := hstrict.np_window_row_space_transport

/-- Paper-scale strict lift: the honest replacement for treating
`block_local_hadamard_lift := True` as if it solved the Cook--Levin row theorem.
-/
abbrev PaperScalePiPlusStrictCookLevinBooleanProjectedLift
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusStrictCookLevinBooleanProjectedLift 1 0
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale strict lift supplies the existing paper-scale local-action lemma.
-/
theorem paperScale_cookLevinLocalActionLemma_of_strictLift
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hstrict : PaperScalePiPlusStrictCookLevinBooleanProjectedLift M htb hns) :
    PaperScalePiPlusBooleanProjectedCookLevinLocalActionLemma M htb hns :=
  cookLevinLocalActionLemma_of_strictLift
    1 0 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hstrict

/-- Full final-data bridge from the strict Cook--Levin row-space theorem.  This
keeps the remaining Route-B blockers explicit and avoids poisoning the branch
with a fake closure. -/
def localWindowFinalData_of_strictCookLevinLift
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hstrict : PaperScalePiPlusStrictCookLevinBooleanProjectedLift M htb hns)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (zero_common_span :
      CookLevinOneWindowZeroHistogramShiftCommonSpan
        M (2 ^ 804) paperScale_ge_two htb hns)
    (per_type_spanning :
      CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
        M (2 ^ 804) paperScale_ge_two htb hns W) :
    PaperScalePiPlusBooleanProjectedLocalWindowFinalData M htb hns :=
  localWindowFinalData_of_cookLevinLocalActionLemma
    M htb hns
    (paperScale_cookLevinLocalActionLemma_of_strictLift M htb hns hstrict)
    W W_finite W_dim zero_common_span per_type_spanning

/-! ## Axiom audit anchors -/

#print axioms cookLevinLocalActionLemma_of_strictLift
#print axioms paperScale_cookLevinLocalActionLemma_of_strictLift
#print axioms localWindowFinalData_of_strictCookLevinLift

end PallLean.Paper93.DeepMath.PathC
