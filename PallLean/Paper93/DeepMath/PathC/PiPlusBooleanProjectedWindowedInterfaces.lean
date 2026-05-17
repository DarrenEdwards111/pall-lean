import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedWindowedClosureBridge

/-!
# Sharpened interfaces for the windowed Pi+ closure path

This file adds two small but useful pieces of real infrastructure after the
same-window obstruction:

* monotonicity of the inclusive multilinear SPDP subspace/rank in both window
  parameters;
* a max-window P-side envelope that is often easier for Route B to supply than
  the exact `RouteBSATWindowedIncPSideRankBound` field.

The mathematical blockers are unchanged, but the remaining P-side target is now
usable with any stronger inclusive-window estimate.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Inclusive multilinear SPDP subspaces are monotone in both the derivative
window and the shift-degree window. -/
theorem mlBlockedSpdpSubspaceInc_mono_params
    {n : Nat} {F : Type*} [CommRing F]
    (B : BlockPartition n) {κ₁ κ₂ ℓ₁ ℓ₂ : Nat}
    (hκ : κ₁ ≤ κ₂) (hℓ : ℓ₁ ≤ ℓ₂)
    (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspaceInc B κ₁ ℓ₁ p ≤
      mlBlockedSpdpSubspaceInc B κ₂ ℓ₂ p := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hSlen, hmdeg, hmvars, hadm, hq⟩
  exact Submodule.subset_span
    ⟨S, m, le_trans hSlen hκ, le_trans hmdeg hℓ, hmvars, hadm, hq⟩

/-- Inclusive multilinear SPDP rank is monotone in both window parameters. -/
theorem mlBlockedSpdpRankInc_mono_params
    {n : Nat} (B : BlockPartition n) {κ₁ κ₂ ℓ₁ ℓ₂ : Nat}
    (hκ : κ₁ ≤ κ₂) (hℓ : ℓ₁ ≤ ℓ₂)
    (p : MvPolynomial (Fin n) ℚ) :
    mlBlockedSpdpRankInc B κ₁ ℓ₁ p ≤
      mlBlockedSpdpRankInc B κ₂ ℓ₂ p := by
  unfold mlBlockedSpdpRankInc
  exact Submodule.finrank_mono
    (mlBlockedSpdpSubspaceInc_mono_params B hκ hℓ p)

/-- A max-window inclusive P-side envelope.  Route B may prove this stronger
uniform-looking statement once, and then instantiate the exact Route-C windowed
P-side field by monotonicity. -/
def RouteBSATWindowedIncPSideRankEnvelope
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (κ ℓ : Nat),
    κ ≤ Nat.log 2 n + extraK →
    ℓ ≤ Nat.log 2 n + extraL →
      mlBlockedSpdpRankInc
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200

/-- The max-window envelope immediately supplies the exact windowed P-side
bound consumed by the corrected Route-C closure path. -/
theorem routeBSATWindowedIncPSideRankBound_of_envelope
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (henv : RouteBSATWindowedIncPSideRankEnvelope
      extraK extraL M n hn2 htb hns) :
    RouteBSATWindowedIncPSideRankBound
      extraK extraL M n hn2 htb hns := by
  unfold RouteBSATWindowedIncPSideRankBound
  exact henv (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
    (le_rfl) (le_rfl)

/-- A one-derivative, no-extra-shift specialization suggested by the local
Hadamard obstruction/realization. -/
abbrev PaperScalePiPlusBooleanProjectedOneWindowContradictionData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PaperScalePiPlusBooleanProjectedWindowedContradictionData 1 0 M htb hns

/-- The one-window specialization rules out a bounded SAT decider whenever its
three concrete fields are supplied. -/
theorem no_decidesSAT_at_paperScale_of_oneWindowContradictionData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedOneWindowContradictionData M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_windowedContradictionData
    1 0 M htb hns D

/-! ## Axiom audit anchors -/

#print axioms mlBlockedSpdpSubspaceInc_mono_params
#print axioms mlBlockedSpdpRankInc_mono_params
#print axioms routeBSATWindowedIncPSideRankBound_of_envelope
#print axioms no_decidesSAT_at_paperScale_of_oneWindowContradictionData

end PallLean.Paper93.DeepMath.PathC
