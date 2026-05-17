import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedWindowedInterfaces

/-!
# Route B windowed inclusive P-side bound

This file does the Route-B-facing work needed by the corrected Route-C `Pi+ᵦ`
path.  The key change after the local obstruction is that the source-side
P-bound is inclusive in `κ` and uses the enlarged window.  The existing
within-profile compression machinery is already built over `S.length ≤ κ`, so
we expose the corresponding inclusive-rank theorem directly.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec

/-- Inclusive-SPDP analogue of the usual within-profile rank assembly.

The proof is the same profile-cover argument as
`WithinProfileBound.hasFiniteProfileCover_of_boundedWithinProfileFinrank`, but
applied to `mlBlockedSpdpSubspaceInc`, whose generators already have
`S.length ≤ κ`. -/
theorem rankInc_bound_of_boundedWithinProfileFinrank
    {n L : Nat}
    (B : BlockPartition n) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (p : MvPolynomial (Fin n) ℚ)
    (hp : p = Finset.univ.prod factors)
    (hwithin : BoundedWithinProfileFinrankClaim B κ ℓ factors constraintType) :
    mlBlockedSpdpRankInc B κ ℓ p ≤ combinedProfileBound κ := by
  set P := Fintype.card (BoundedProfile κ)
  let enum := (Fintype.equivFin (BoundedProfile κ)).symm
  let spaces : Fin P → Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    fun i => allBoundedProfilePostSpan B κ ℓ factors constraintType (enum i).toHistogram
  have hcover : mlBlockedSpdpSubspaceInc B κ ℓ p ≤ ⨆ i, spaces i := by
    apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨S, shift, hSle, _hdeg, hvars, _hadm, rfl⟩
    rw [hp]
    have hLeibniz := iterDerivList_finset_prod_mem_bounded_span S factors
    have hpost := SymmetricPower.mlProj_mul_mem_span_image shift
      (boundedDistribDerivProds Finset.univ factors S S.length)
      (iterDerivList S (Finset.univ.prod factors))
      hLeibniz
    suffices hsuff : mlProj (shift * iterDerivList S (Finset.univ.prod factors)) ∈
        ⨆ (bp : BoundedProfile κ),
          allBoundedProfilePostSpan B κ ℓ factors constraintType bp.toHistogram by
      have hle : ⨆ (bp : BoundedProfile κ),
          allBoundedProfilePostSpan B κ ℓ factors constraintType bp.toHistogram ≤
          ⨆ (i : Fin P), spaces i := by
        apply iSup_le
        intro bp
        let i := (Fintype.equivFin (BoundedProfile κ)) bp
        apply le_trans _ (le_iSup spaces i)
        show allBoundedProfilePostSpan B κ ℓ factors constraintType bp.toHistogram ≤ spaces i
        have : (enum i).toHistogram = bp.toHistogram := by
          show ((Fintype.equivFin (BoundedProfile κ)).symm
            ((Fintype.equivFin (BoundedProfile κ)) bp)).toHistogram = bp.toHistogram
          simp [Equiv.symm_apply_apply]
        rw [← this]
      exact hle hsuff
    apply Submodule.span_le.mpr _ hpost
    intro q' hq'
    rcases hq' with ⟨g, hg_mem, rfl⟩
    rcases hg_mem with ⟨d, hd_elts, hg_eq, hd_len⟩
    have hadm : ProfileAdmissible κ (derivCountProfile constraintType d) := by
      exact derivCountProfile_admissible_of_total_le constraintType d
        (le_trans hd_len hSle)
    set bp := admissibleToBounded hadm
    apply Submodule.mem_iSup_of_mem bp
    apply Submodule.subset_span
    simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨S, hSle, shift, hvars, g,
      ⟨d, hd_elts, hg_eq, rfl, hd_len⟩, rfl⟩
  unfold mlBlockedSpdpRankInc
  calc
    Module.finrank ℚ ↥(mlBlockedSpdpSubspaceInc B κ ℓ p)
        ≤ Module.finrank ℚ ↥(⨆ i : Fin P, spaces i) :=
          Submodule.finrank_mono hcover
    _ ≤ ∑ i : Fin P, Module.finrank ℚ ↥(spaces i) :=
          finrank_iSup_fin_le P spaces
    _ ≤ ∑ _i : Fin P, withinProfileBound κ :=
          Finset.sum_le_sum (fun i _ => (hwithin (enum i).toHistogram).2)
    _ = P * withinProfileBound κ := by simp [Finset.sum_const]
    _ ≤ profileCount κ * withinProfileBound κ :=
          Nat.mul_le_mul_right _ (boundedProfile_card_le_profileCount κ)
    _ = combinedProfileBound κ := rfl

/-- The direct `WithinProfileFinrankBound` version of the inclusive assembly. -/
theorem rankInc_bound_of_withinProfileFinrankBound
    {n L : Nat}
    (B : BlockPartition n) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (p : MvPolynomial (Fin n) ℚ)
    (hp : p = Finset.univ.prod factors)
    (hbound : WithinProfileFinrankBound B κ ℓ factors constraintType) :
    mlBlockedSpdpRankInc B κ ℓ p ≤ combinedProfileBound κ :=
  rankInc_bound_of_boundedWithinProfileFinrank B κ ℓ factors constraintType p hp
    (boundedWithinProfileFinrankClaim_of_finrankBound B κ ℓ factors constraintType hbound)

/-- Arithmetic slack for the one-derivative enlarged Route-C window:
`combinedProfileBound (log₂ n + 1) ≤ n^200`. -/
theorem combinedProfileBound_log_succ_le_pow_200
    (n : Nat) (hn : n ≥ 2) :
    combinedProfileBound (Nat.log 2 n + 1) ≤ n ^ 200 := by
  rw [combinedProfileBound_eq]
  have hbase : Nat.log 2 n + 1 + 1 ≤ 2 * n := by
    have hlog : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
    omega
  calc
    (Nat.log 2 n + 1 + 1) ^ 12 ≤ (2 * n) ^ 12 :=
      Nat.pow_le_pow_left hbase 12
    _ = 2 ^ 12 * n ^ 12 := by ring
    _ ≤ n ^ 188 * n ^ 12 := by
      apply Nat.mul_le_mul_right
      calc
        (2 : Nat) ^ 12 ≤ 2 ^ 188 := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ n ^ 188 := Nat.pow_le_pow_left hn 188
    _ = n ^ 200 := by ring

/-- Route-B one-window inclusive P-side bound from the concrete Cook-Levin
within-profile finrank theorem at the enlarged derivative window. -/
theorem routeBSATWindowedIncPSideRankBound_one_zero_of_withinProfileFinrankBound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbound : WithinProfileFinrankBound
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n + 1) (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      (cookLevinConstraintType M n hn2 htb hns)) :
    RouteBSATWindowedIncPSideRankBound 1 0 M n hn2 htb hns := by
  unfold RouteBSATWindowedIncPSideRankBound
  let T := cook_levin_compilation M n hn2 htb hns
  let factors : List (MvPolynomial (Fin n) ℚ) := cookLevinFactorList M n hn2 htb hns
  have hcompiled : compiledPoly T = factors.prod := by
    simpa [T, factors, cookLevinFactorList] using
      compiledPoly_eq_constraints_prod M n hn2 htb hns
  have hp : compiledPoly T = Finset.univ.prod (fun i : Fin factors.length => factors.get i) := by
    rw [hcompiled, ← Fin.prod_univ_getElem]
    simp [List.get_eq_getElem]
  simpa [T, factors, Nat.add_assoc] using
    le_trans
      (rankInc_bound_of_withinProfileFinrankBound
        T.partition
        (Nat.log 2 n + 1) (Nat.log 2 n)
        (fun i : Fin factors.length => factors.get i)
        (cookLevinConstraintType M n hn2 htb hns)
        (compiledPoly T)
        hp
        hbound)
      (combinedProfileBound_log_succ_le_pow_200 n hn2)

/-- Paper-scale version of the Route-B one-window P-side bridge. -/
theorem paperScale_routeBSATWindowedIncPSideRankBound_one_zero_of_withinProfileFinrankBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hbound : WithinProfileFinrankBound
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804))
      (fun i => (cookLevinFactorList M (2 ^ 804) paperScale_ge_two htb hns).get i)
      (cookLevinConstraintType M (2 ^ 804) paperScale_ge_two htb hns)) :
    RouteBSATWindowedIncPSideRankBound
      1 0 M (2 ^ 804) paperScale_ge_two htb hns :=
  routeBSATWindowedIncPSideRankBound_one_zero_of_withinProfileFinrankBound
    M (2 ^ 804) paperScale_ge_two htb hns hbound

/-! ## Axiom audit anchors -/

#print axioms rankInc_bound_of_boundedWithinProfileFinrank
#print axioms rankInc_bound_of_withinProfileFinrankBound
#print axioms combinedProfileBound_log_succ_le_pow_200
#print axioms routeBSATWindowedIncPSideRankBound_one_zero_of_withinProfileFinrankBound
#print axioms paperScale_routeBSATWindowedIncPSideRankBound_one_zero_of_withinProfileFinrankBound

end PallLean.Paper93.DeepMath.PathC
