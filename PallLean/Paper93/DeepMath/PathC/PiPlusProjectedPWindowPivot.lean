import PallLean.GodMoveCore
import PallLean.PaperFaithfulCompilation

/-!
# Paper-faithful projected P-window pivot

This file records the Route-C/Route-W pivot that avoids the failed raw Route-B
rank sandwich.  The P-side input is no longer an upper bound on the unprojected
Cook-Levin source rank, nor on an enlarged source window.  It is a direct
finite-span cover of the already projected/gauged Cook-Levin P-window.

The intended producer is the paper-faithful row-indexed Route-W normal-form
surface, but this kernel-facing file consumes only the linear-algebra payload
that actually matters: a projected P-window cover and a separate projected
NP-side preservation input for the same gauge.

The file is deliberately independent of the older Route-B wrapper modules,
because those wrappers still route through the now-broken raw source-rank upper
bound.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Polynomial space for a Cook-Levin projected-pivot gauge. -/
abbrev ProjectedPivotGaugeSpace
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Type :=
  MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) Rat

/-- Linear gauge type used by the projected-pivot socket. -/
abbrev ProjectedPivotGaugeMap
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Type :=
  ProjectedPivotGaugeSpace M n hn2 htb hns →ₗ[Rat]
    ProjectedPivotGaugeSpace M n hn2 htb hns

/-- The projected Cook-Levin P-window for a selected gauge map. -/
noncomputable abbrev projectedPWindowSubspace
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns) :
    Submodule Rat (ProjectedPivotGaugeSpace M n hn2 htb hns) :=
  mlBlockedSpdpSubspace
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)))

/-- Direct finite-span cover of the projected P-window.  This is the P-side
pivot payload: it bounds the rank after the selected gauge/projection, not the
raw source compiled polynomial. -/
structure ProjectedPWindowFiniteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns) where
  span : Submodule Rat (ProjectedPivotGaugeSpace M n hn2 htb hns)
  finite : Module.Finite Rat span
  contains : projectedPWindowSubspace M n hn2 htb hns gauge <= span
  rank_bound : Module.finrank Rat span <= n ^ 200

/-- P-side rank bound on the projected/gauged Cook-Levin object. -/
def ProjectedPivotPSideBound
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns) : Prop :=
  mlBlockedSpdpRank
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) <= n ^ 200

/-- NP-side identity-minor preservation on the same projected/gauged object. -/
def ProjectedPivotNPIdentityMinorPreservation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns) : Prop :=
  DecidesSAT M ->
    Nat.choose (n / 3) (Nat.log 2 n) <=
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)))

/-- A direct projected P-window cover proves the P-side gauge bound without any
unprojected/source-rank upper bound. -/
theorem projectedPivotPSideBound_of_projectedPWindowFiniteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns)
    (cover : ProjectedPWindowFiniteSpanCover
      M n hn2 htb hns gauge) :
    ProjectedPivotPSideBound M n hn2 htb hns gauge := by
  unfold ProjectedPivotPSideBound mlBlockedSpdpRank
  letI := cover.finite
  exact le_trans (Submodule.finrank_mono cover.contains) cover.rank_bound

/-- Generic contradiction-facing pivot data: direct projected P-side cover plus
NP identity-minor preservation for the same projected/gauged object. -/
structure ProjectedPWindowPivotData
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns) where
  projected_p_cover : ProjectedPWindowFiniteSpanCover M n hn2 htb hns gauge
  np_identity_minor :
    ProjectedPivotNPIdentityMinorPreservation M n hn2 htb hns gauge

/-- The projected pivot data gives exactly the incompatible P/NP pair. -/
theorem pSide_and_npIdentityMinor_of_projectedPWindowPivotData
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns)
    (D : ProjectedPWindowPivotData M n hn2 htb hns gauge) :
    ProjectedPivotPSideBound M n hn2 htb hns gauge ∧
      ProjectedPivotNPIdentityMinorPreservation M n hn2 htb hns gauge :=
  ⟨projectedPivotPSideBound_of_projectedPWindowFiniteSpanCover
      M n hn2 htb hns gauge D.projected_p_cover,
    D.np_identity_minor⟩

/-- At paper scale, projected pivot data rules out a SAT decider. -/
theorem no_decidesSAT_at_large_n_of_projectedPWindowPivotData
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (gauge : ProjectedPivotGaugeMap M n hn2 htb hns)
    (D : ProjectedPWindowPivotData M n hn2 htb hns gauge) :
    ¬ DecidesSAT M := by
  intro hdec
  rcases pSide_and_npIdentityMinor_of_projectedPWindowPivotData
    M n hn2 htb hns gauge D with ⟨hP, hNP⟩
  have hchoose_le : Nat.choose (n / 3) (Nat.log 2 n) <= n ^ 200 :=
    le_trans (hNP hdec) hP
  exact not_lt_of_ge hchoose_le
    (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn)

/-- Paper-scale size lower bound, kept local so this pivot file does not import
the heavier concrete `Pi+` construction chain. -/
theorem projectedPivot_paperScale_ge_two : 2 ^ 804 >= 2 := by
  exact @Nat.le_self_pow 804 (by norm_num : 804 ≠ 0) 2

/-- Paper-scale projected pivot data for a selected gauge.  The intended
selected gauge is the Boolean-projected `Π+`/Route-W normal-form gauge, but the
socket is stated for any gauge so it does not smuggle in the false raw Route-B
source-rank upper bound. -/
abbrev PaperScaleProjectedPWindowPivotData
    (M : DTM) (htb : M.timeBound <= 4)
    (hns : M.numStates <= 2 ^ 804)
    (gauge : ProjectedPivotGaugeMap M (2 ^ 804)
      projectedPivot_paperScale_ge_two htb hns) :=
  ProjectedPWindowPivotData M (2 ^ 804)
    projectedPivot_paperScale_ge_two htb hns gauge

/-- Final paper-scale theorem for the pivot: a direct projected P-window cover
and projected NP preservation rule out a SAT decider, without invoking the raw
Route-B source-rank upper bound. -/
theorem no_decidesSAT_at_paperScale_of_projectedPWindowPivotData
    (M : DTM) (htb : M.timeBound <= 4)
    (hns : M.numStates <= 2 ^ 804)
    (gauge : ProjectedPivotGaugeMap M (2 ^ 804)
      projectedPivot_paperScale_ge_two htb hns)
    (D : PaperScaleProjectedPWindowPivotData M htb hns gauge) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_large_n_of_projectedPWindowPivotData
    M (2 ^ 804) (le_rfl : 2 ^ 804 >= 2 ^ 804)
    projectedPivot_paperScale_ge_two htb hns gauge D

/-! ## Axiom audit anchors -/

#print axioms projectedPivotPSideBound_of_projectedPWindowFiniteSpanCover
#print axioms pSide_and_npIdentityMinor_of_projectedPWindowPivotData
#print axioms no_decidesSAT_at_large_n_of_projectedPWindowPivotData
#print axioms projectedPivot_paperScale_ge_two
#print axioms no_decidesSAT_at_paperScale_of_projectedPWindowPivotData

end PallLean.Paper93.DeepMath.PathC
