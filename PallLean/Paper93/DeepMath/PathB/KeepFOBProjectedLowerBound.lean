import PallLean.GodMoveReal
import PallLean.Paper93.DeepMath.PathB.KeepFOBProjectedLinearIndependence
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeKeepFOBNP

/-!
# Projected keepFOB lower bound

This file assembles the final keepFOB projected lower bound from the exact
missing local ingredient: linear independence of the first-of-block SPDP
generators after applying the keepFOB projection to the compiled polynomial.

The assembly mirrors `CompiledBoolFactorBridge.weakened_bound_from_compiled_independence`,
but is stated for the projected polynomial.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open TuringMachine

attribute [local instance] Classical.dec

/-- Generic finrank lower bound from linearly independent derivative rows. -/
theorem mlBlockedSpdpRank_lower_bound_from_derivative_independence
    {N : Nat} (B : BlockPartition N) (kappa ell : Nat)
    (p : MvPolynomial (Fin N) Rat)
    (F : Finset (Finset (Fin N)))
    (hcard : ∀ S, S ∈ F -> S.card = kappa)
    (hadm : ∀ S, S ∈ F -> isBlockAdmissible B S.toList)
    (hli : LinearIndependent Rat (fun S : F =>
      mlProj (iterDerivList (S : Finset (Fin N)).toList p))) :
    F.card <= mlBlockedSpdpRank B kappa ell p := by
  have hmem : ∀ (S : F),
      mlProj (iterDerivList (S : Finset (Fin N)).toList p) ∈
        mlBlockedSpdpSubspace B kappa ell p := by
    intro S
    rcases S with ⟨S, hS⟩
    refine Submodule.subset_span ?_
    refine ⟨S.toList, (1 : MvPolynomial (Fin N) Rat), ?_, ?_, ?_, ?_, ?_⟩
    · simp [hcard S hS]
    · simp
    · simp
    · exact hadm S hS
    · simp
  set f : F -> mlBlockedSpdpSubspace B kappa ell p :=
    fun S => ⟨mlProj (iterDerivList (S : Finset (Fin N)).toList p), hmem S⟩
    with hf_def
  have hli_sub : LinearIndependent Rat f := by
    rw [linearIndependent_iff'] at hli ⊢
    intro s w hw i hi
    apply hli s w ?_ i hi
    have hval :
        (∑ j ∈ s, w j • f j).val =
          (0 : mlBlockedSpdpSubspace B kappa ell p).val :=
      congrArg Subtype.val hw
    simpa only [hf_def, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_mk,
      Submodule.coe_zero, ZeroMemClass.coe_zero] using hval
  unfold mlBlockedSpdpRank
  rw [show F.card = Fintype.card F from (Fintype.card_coe F).symm]
  exact hli_sub.fintype_card_le_finrank

/-- The missing projected linear-independence obligation for keepFOB. -/
def SatDeciderGaugeKeepFOBProjectionProjectedLinearIndependence
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  LinearIndependent Rat (fun S : GodMoveReal.fobFamily n (Nat.log 2 n) =>
    mlProj (iterDerivList (S : Finset (Fin n)).toList
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)))))

/-- The projected linear-independence obligation is discharged by the
projected FOB coefficient-matrix theorem. -/
theorem satDeciderGaugeKeepFOBProjection_projected_linear_independence
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    SatDeciderGaugeKeepFOBProjectionProjectedLinearIndependence
      M n hn2 htb hns := by
  unfold SatDeciderGaugeKeepFOBProjectionProjectedLinearIndependence
  have hκ1 : Nat.log 2 n >= 1 := by
    have hmono : Nat.log 2 (2 ^ 804) <= Nat.log 2 n :=
      Nat.log_mono_right hn
    set_option exponentiation.threshold 1000 in
    have hlog804 : Nat.log 2 (2 ^ 804) = 804 :=
      Nat.log_pow (by norm_num : 1 < 2) 804
    omega
  have hcard :
      ∀ S ∈ GodMoveReal.fobFamily n (Nat.log 2 n),
        S.card = Nat.log 2 n := by
    intro S hS
    exact GodMoveReal.fobFamily_mem_card n (Nat.log 2 n) S hS
  have hfob :
      ∀ S ∈ GodMoveReal.fobFamily n (Nat.log 2 n),
        ∀ v ∈ S, 3 ∣ v.val := by
    intro S hS v hv
    exact GodMoveReal.fobFamily_mem_fob n (Nat.log 2 n) S hS v hv
  exact linearIndependent_mlProj_keepFOBProjected_compiled_fob
    M n hn2 htb hns (Nat.log 2 n) hκ1 hcard hfob

/-- Conditional assembly of the projected keepFOB compiled lower bound. -/
theorem satDeciderGaugeKeepFOBProjection_projected_compiled_lower_bound_of_projected_linear_independence
    (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hli :
      SatDeciderGaugeKeepFOBProjectionProjectedLinearIndependence
        M n hn2 htb hns) :
    Nat.choose (n / 3) (Nat.log 2 n) <=
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) := by
  let F : Finset (Finset (Fin n)) := GodMoveReal.fobFamily n (Nat.log 2 n)
  have hFcard : F.card = Nat.choose (n / 3) (Nat.log 2 n) := by
    simpa [F] using GodMoveReal.fobFamily_card n (Nat.log 2 n)
  have hcard : ∀ S, S ∈ F -> S.card = Nat.log 2 n := by
    intro S hS
    exact GodMoveReal.fobFamily_mem_card n (Nat.log 2 n) S (by simpa [F] using hS)
  have hadm : ∀ S, S ∈ F ->
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S.toList := by
    intro S hS
    exact GodMoveReal.fobFamily_mem_blockAdmissible n hn2 (Nat.log 2 n)
      M htb hns S (by simpa [F] using hS)
  have hliF : LinearIndependent Rat (fun S : F =>
      mlProj (iterDerivList (S : Finset (Fin n)).toList
        (satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))))) := by
    simpa [F, SatDeciderGaugeKeepFOBProjectionProjectedLinearIndependence] using hli
  rw [← hFcard]
  exact mlBlockedSpdpRank_lower_bound_from_derivative_independence
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (satDeciderGaugeKeepFOBProjection M n hn2 htb hns
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
    F hcard hadm hliF

/-- Conditional NP preservation for keepFOB from projected linear independence. -/
theorem satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation_of_projected_linear_independence
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hli :
      SatDeciderGaugeKeepFOBProjectionProjectedLinearIndependence
        M n hn2 htb hns) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) := by
  exact satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
    M n hn2 htb hns
    (satDeciderGaugeKeepFOBProjection M n hn2 htb hns)
    (satDeciderGaugeKeepFOBProjection_projected_compiled_lower_bound_of_projected_linear_independence
      M n hn hn2 htb hns hli)

/-- The projected keepFOB compiled polynomial has the first-of-block
identity-minor lower bound. -/
theorem satDeciderGaugeKeepFOBProjection_projected_compiled_lower_bound
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Nat.choose (n / 3) (Nat.log 2 n) <=
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (satDeciderGaugeKeepFOBProjection M n hn2 htb hns
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) :=
  satDeciderGaugeKeepFOBProjection_projected_compiled_lower_bound_of_projected_linear_independence
    M n hn hn2 htb hns
    (satDeciderGaugeKeepFOBProjection_projected_linear_independence
      M n hn hn2 htb hns)

/-- The keepFOB projection preserves the SAT-decider NP identity-minor lower
bound. -/
theorem satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) :=
  satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
    M n hn2 htb hns
    (satDeciderGaugeKeepFOBProjection M n hn2 htb hns)
    (satDeciderGaugeKeepFOBProjection_projected_compiled_lower_bound
      M n hn hn2 htb hns)

end PallLean.Paper93.DeepMath.PathB
