import PallLean.Paper93.DeepMath.PathC.PiPlusRouteBOneWindowPerTypeFrontier

/-!
# One-window per-type discharge interface

This file sharpens the remaining nonzero Route-B blocker.  The previous
frontier exposed

`CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases`.

Here we reduce that profile-local spanning statement to the two genuinely local
ingredients needed at the enlarged window `κ = log₂ n + 1`:

* every Cook-Levin factor has all derivatives of length at most `κ` in its
  per-type subspace;
* the per-type profile subspace is closed under the local `shift`/`mlProj`
  generator at the same one-window profile.

This is intentionally a one-window analogue of the older `H3+H4+H5` plumbing,
without reusing the old hardcoded `log₂ n` interfaces.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec

/-- One-window derivative membership for every Cook-Levin factor in its
constraint-type subspace.  This packages H3+H4 at radius `log₂ n + 1`, avoiding
any accidental reuse of the older `log₂ n`-only API. -/
def CookLevinFactorDerivativeMemPerTypeOneWindow
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) : Prop :=
  ∀ (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (d : List (Fin n)),
    d.length ≤ Nat.log 2 n + 1 →
      iterDerivList d ((cookLevinFactorList M n hn htb hns).get i)
        ∈ W (cookLevinConstraintType M n hn htb hns i)

/-- One-window profile-local closure for the `shift`/`mlProj` generator once
all factor-derivatives already lie in their per-type subspaces. -/
def PerTypeShiftMlprojClosureAtOneWindowBoundedProfile {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (bp : BoundedProfile (Nat.log 2 n + 1)) : Prop :=
  ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n + 1)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (g : MvPolynomial (Fin n) ℚ)
    (_hg_prod :
      ∃ (L : ℕ) (factors : Fin L → MvPolynomial (Fin n) ℚ)
        (constraintType : Fin L → ConstraintType)
        (d : Fin L → List (Fin n)),
        (∀ i, ∀ v ∈ d i, v ∈ S) ∧
        (∀ i, iterDerivList (d i) (factors i) ∈ W (constraintType i)) ∧
        g = Finset.univ.prod (fun i => iterDerivList (d i) (factors i)) ∧
        derivCountProfile constraintType d = bp.toHistogram ∧
        ∑ i : Fin L, (d i).length ≤ S.length),
    mlProj (shift * g) ∈ profileSubspace bp.toHistogram W

/-- The one-window derivative-membership and shift/`mlProj` closure ingredients
produce the exact profile-local per-type spanning statement used by the final
Route-B one-window frontier. -/
theorem cookLevinOneWindowPerTypeSpanningAtBoundedProfile_of_derivativeMem_and_shiftClosure
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (bp : BoundedProfile (Nat.log 2 n + 1))
    (hDeriv : CookLevinFactorDerivativeMemPerTypeOneWindow M n hn htb hns W)
    (hShiftMlprojAt : PerTypeShiftMlprojClosureAtOneWindowBoundedProfile W bp) :
    CookLevinOneWindowPerTypeSpanningAtBoundedProfile
      M n hn htb hns W bp := by
  classical
  intro S hSlen shift hshiftvars g hg
  obtain ⟨d, hd_elts, hg_prod, hprof, hsum⟩ := hg
  have hEachMem :
      ∀ i : Fin (cookLevinFactorList M n hn htb hns).length,
        iterDerivList (d i)
            ((fun j => (cookLevinFactorList M n hn htb hns).get j) i)
          ∈ W (cookLevinConstraintType M n hn htb hns i) := by
    intro i
    have hdi_le : (d i).length ≤ Nat.log 2 n + 1 := by
      have hsingle : (d i).length ≤
          ∑ j : Fin (cookLevinFactorList M n hn htb hns).length, (d j).length := by
        refine Finset.single_le_sum (f := fun j => (d j).length) ?_
          (Finset.mem_univ i)
        intro j _
        exact Nat.zero_le _
      exact le_trans (le_trans hsingle hsum) hSlen
    exact hDeriv i (d i) hdi_le
  exact hShiftMlprojAt S hSlen shift hshiftvars g
    ⟨(cookLevinFactorList M n hn htb hns).length,
     (fun j => (cookLevinFactorList M n hn htb hns).get j),
     cookLevinConstraintType M n hn htb hns, d,
     hd_elts, hEachMem, hg_prod, hprof, hsum⟩

/-- Concrete data sufficient for all nonzero active one-window per-type
spanning cases. -/
structure CookLevinOneWindowPerTypeSpanningActiveData
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) : Prop where
  factor_derivatives :
    CookLevinFactorDerivativeMemPerTypeOneWindow M n hn htb hns W
  shift_mlproj_active :
    ∀ bp : ActiveAdmissibleProfile (Nat.log 2 n + 1),
      bp.toHistogram ≠ zeroProfileHistogram →
        PerTypeShiftMlprojClosureAtOneWindowBoundedProfile W
          bp.toActiveBoundedProfile.toBoundedProfile

/-- The local active data discharges the nonzero active per-type blocker. -/
theorem cookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases_of_activeData
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hdata : CookLevinOneWindowPerTypeSpanningActiveData M n hn htb hns W) :
    CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
      M n hn htb hns W := by
  intro bp hne
  exact cookLevinOneWindowPerTypeSpanningAtBoundedProfile_of_derivativeMem_and_shiftClosure
    M n hn htb hns W bp.toActiveBoundedProfile.toBoundedProfile
    hdata.factor_derivatives
    (hdata.shift_mlproj_active bp hne)

/-- Paper-scale specialization of the one-window active per-type discharge. -/
theorem paperScale_cookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases_of_activeData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (hdata : CookLevinOneWindowPerTypeSpanningActiveData
      M (2 ^ 804) paperScale_ge_two htb hns W) :
    CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
      M (2 ^ 804) paperScale_ge_two htb hns W :=
  cookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases_of_activeData
    M (2 ^ 804) paperScale_ge_two htb hns W hdata

/-- Route-B one-window P-side bound from the corrected zero-profile common-span
blocker plus the local active-data discharge for all nonzero profiles. -/
theorem routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_activeData
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hzero : CookLevinOneWindowZeroHistogramShiftCommonSpan M n hn htb hns)
    (hdata : CookLevinOneWindowPerTypeSpanningActiveData M n hn htb hns W) :
    RouteBSATWindowedIncPSideRankBound 1 0 M n hn htb hns :=
  routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_perTypeSpanning
    M n hn htb hns hn4 W hW_fin hW_dim hzero
    (cookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases_of_activeData
      M n hn htb hns W hdata)

/-- Paper-scale Route-B P-side specialization from zero common-span and local
active data. -/
theorem paperScale_routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_activeData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hzero : CookLevinOneWindowZeroHistogramShiftCommonSpan
      M (2 ^ 804) paperScale_ge_two htb hns)
    (hdata : CookLevinOneWindowPerTypeSpanningActiveData
      M (2 ^ 804) paperScale_ge_two htb hns W) :
    RouteBSATWindowedIncPSideRankBound
      1 0 M (2 ^ 804) paperScale_ge_two htb hns :=
  routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_activeData
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four
    W hW_fin hW_dim hzero hdata

/-! ## Axiom audit anchors -/

#print axioms cookLevinOneWindowPerTypeSpanningAtBoundedProfile_of_derivativeMem_and_shiftClosure
#print axioms cookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases_of_activeData
#print axioms paperScale_cookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases_of_activeData
#print axioms routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_activeData
#print axioms paperScale_routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_activeData

end PallLean.Paper93.DeepMath.PathC
