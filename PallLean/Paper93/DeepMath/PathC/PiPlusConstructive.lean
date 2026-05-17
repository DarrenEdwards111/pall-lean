import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeDischargeSubgoals
import PallLean.Paper93.DeepMath.PathB.RouteBWidthRankPSide
import Mathlib.LinearAlgebra.Pi

/-!
# Route C: constructive paper-faithful `Pi+` surface

Route C is deliberately separate from Route B.  Route B keeps the variational /
N-frame / log-det / amplituhedron bridge alive as an interpretive and backup
route.  This file starts the constructive, paper-faithful `Pi+` route:

* `Pi+` is modelled as an **invertible** block-local Hadamard/Fourier change of
  basis, not as a quotient compressor.
* Compression is therefore not claimed to come from rank-decrease of `Pi+`.
  The P-side bound must come from CEW / diagonal-basis / Width⇒Rank data.
* NP-side identity-minor preservation is a separate invertible-basis obligation.

The concrete kernel-checked object below is the radius-one local Hadamard block
`(x₀,x₁) ↦ (x₀+x₁, x₀-x₁)` over `ℚ`, together with its block-diagonal lift.
The SAT-polynomial-level interface is then stated as exact fields: rank
invariance/monotonicity, Width⇒Rank P-side, and identity-minor preservation.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-! ## Explicit radius-one Hadamard/Fourier block -/

/-- The local two-point Hadamard/Fourier transform.  This is intentionally
unnormalised over `ℚ`: `(x false, x true) ↦ (x false + x true, x false - x true)`.
Its inverse is half the same transform. -/
noncomputable def localHadamardPair : (Bool → ℚ) ≃ₗ[ℚ] (Bool → ℚ) where
  toFun x := fun b => if b = false then x false + x true else x false - x true
  invFun y := fun b => if b = false then (y false + y true) / 2 else (y false - y true) / 2
  map_add' x y := by
    ext b
    by_cases hb : b = false
    · simp [hb, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    · simp [hb, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' a x := by
    ext b
    by_cases hb : b = false
    · simp [hb, mul_add, mul_sub]
    · simp [hb, mul_add, mul_sub]
  left_inv x := by
    ext b
    cases b <;> simp
  right_inv y := by
    ext b
    cases b <;> simp <;> ring

@[simp] theorem localHadamardPair_apply_false (x : Bool → ℚ) :
    localHadamardPair x false = x false + x true := by
  simp [localHadamardPair]

@[simp] theorem localHadamardPair_apply_true (x : Bool → ℚ) :
    localHadamardPair x true = x false - x true := by
  simp [localHadamardPair]

@[simp] theorem localHadamardPair_symm_apply_false (x : Bool → ℚ) :
    localHadamardPair.symm x false = (x false + x true) / 2 := by
  simp [localHadamardPair]

@[simp] theorem localHadamardPair_symm_apply_true (x : Bool → ℚ) :
    localHadamardPair.symm x true = (x false - x true) / 2 := by
  simp [localHadamardPair]

/-- Block-diagonal lift of the local Hadamard transform across independent
radius-one blocks indexed by `ι`. -/
noncomputable def blockLocalHadamard (ι : Type*) :
    (ι → Bool → ℚ) ≃ₗ[ℚ] (ι → Bool → ℚ) where
  toFun x := fun i => localHadamardPair (x i)
  invFun y := fun i => localHadamardPair.symm (y i)
  map_add' x y := by
    ext i b
    simp
  map_smul' a x := by
    ext i b
    simp
  left_inv x := by
    ext i b
    simp
  right_inv y := by
    ext i b
    simp

@[simp] theorem blockLocalHadamard_apply_false {ι : Type*}
    (x : ι → Bool → ℚ) (i : ι) :
    blockLocalHadamard ι x i false = x i false + x i true := by
  simp [blockLocalHadamard]

@[simp] theorem blockLocalHadamard_apply_true {ι : Type*}
    (x : ι → Bool → ℚ) (i : ι) :
    blockLocalHadamard ι x i true = x i false - x i true := by
  simp [blockLocalHadamard]

/-- Sanity check: the block-local Hadamard transform is an equivalence, hence
has no quotient/compression kernel. -/
theorem blockLocalHadamard_ker_eq_bot {ι : Type*} :
    LinearMap.ker (blockLocalHadamard ι).toLinearMap = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr (blockLocalHadamard ι).injective

/-! ## SAT-polynomial-level Route C interface -/

/-- A candidate polynomial-space `Pi+` transform is a linear equivalence whose
underlying linear map has the SAT-decider gauge-map type.  The concrete
Hadamard block above is the local model; this structure records the exact
polynomial-space lift still to be constructed from the Cook--Levin block
coordinates. -/
structure PiPlusSATTransform
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  equiv :
    PathB.SATDeciderGaugeSpace M n hn2 htb hns ≃ₗ[ℚ]
      PathB.SATDeciderGaugeSpace M n hn2 htb hns
  block_local_hadamard_lift : Prop

namespace PiPlusSATTransform

/-- The gauge map induced by an invertible `Pi+` transform. -/
abbrev gauge {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) :
    PathB.SATDeciderGaugeMap M n hn2 htb hns :=
  piP.equiv.toLinearMap

/-- Invertibility sanity check at polynomial-space level: `Pi+` has trivial
kernel as a linear map. -/
theorem gauge_ker_eq_bot {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) :
    LinearMap.ker piP.gauge = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr piP.equiv.injective

end PiPlusSATTransform

/-- Route C rank-invariance obligation.  Because `Pi+` is invertible, the
paper-faithful target is equality/invariance of the SPDP rank under the
block-local basis change, not rank decrease by projection. -/
def PiPlusRankInvariant
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : Nat) (p : PathB.SATDeciderGaugeSpace M n hn2 htb hns),
    mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ (piP.gauge p) =
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ p

/-- Rank invariance immediately gives the gauge rank-monotonicity field. -/
theorem piPlus_rankMonotonicity_of_rankInvariant
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrank : PiPlusRankInvariant M n hn2 htb hns piP) :
    PathB.SATDeciderGaugeRankMonotonicity M n hn2 htb hns piP.gauge := by
  intro κ ℓ p
  rw [hrank κ ℓ p]

/-- Width⇒Rank P-side data after the invertible `Pi+` basis change.  This is
kept separate from rank invariance because the intended compression source is
CEW / diagonal-basis / Width⇒Rank, not `Pi+` quotienting. -/
def PiPlusWidthRankPSide
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (piP.gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤ n ^ 200

/-- NP-side identity-minor preservation after the invertible `Pi+` basis change. -/
def PiPlusIdentityMinorPreservation
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  DecidesSAT M →
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (piP.gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)))

/-- The exact constructive Route C obligation package: explicit block-local
`Pi+`, rank invariance, Width⇒Rank P-side, and identity-minor preservation. -/
def PiPlusConstructiveSATGaugeData
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ piP : PiPlusSATTransform M n hn2 htb hns,
    piP.block_local_hadamard_lift ∧
      PiPlusRankInvariant M n hn2 htb hns piP ∧
        PiPlusWidthRankPSide M n hn2 htb hns piP ∧
          PiPlusIdentityMinorPreservation M n hn2 htb hns piP

/-- Route C data discharges the existing three SAT-decider gauge subgoals. -/
theorem satDeciderGaugeSubgoals_of_piPlusConstructiveData
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hPi : PiPlusConstructiveSATGaugeData M n hn2 htb hns) :
    ∃ gauge : PathB.SATDeciderGaugeMap M n hn2 htb hns,
      PathB.SATDeciderGaugeSubgoals M n hn2 htb hns gauge := by
  rcases hPi with ⟨piP, _hlocal, hrank, hp, hnp⟩
  exact ⟨piP.gauge,
    piPlus_rankMonotonicity_of_rankInvariant M n hn2 htb hns piP hrank,
    hp,
    hnp⟩

/-- Uniform Route C data closes the current SAT-decider-specific gauge frontier.
This is the handoff point to the already-existing R70/God-Move chain. -/
def Step247UniformPiPlusConstructiveData : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    PiPlusConstructiveSATGaugeData M n hn2 htb hns

theorem satDeciderSpecificGaugeSubgoalDischarge_of_uniformPiPlus
    (hPi : Step247UniformPiPlusConstructiveData) :
    PathB.SATDeciderSpecificGaugeSubgoalDischarge := by
  intro M n hn hn2 htb hns hdec
  exact satDeciderGaugeSubgoals_of_piPlusConstructiveData
    M n hn2 htb hns (hPi M n hn hn2 htb hns hdec)

/-- Full existing Path-B/R70 conditional surface from Route C data.  Route B is
not deleted or changed; Route C simply feeds the same final SAT-gauge socket. -/
theorem pathB_surface_of_uniformPiPlus
    (hPi : Step247UniformPiPlusConstructiveData) :
    PathB.PathBUpstreamAxiomPNESurface :=
  PathB.pathB_if_sat_decider_specific_gauge_subgoals
    (satDeciderSpecificGaugeSubgoalDischarge_of_uniformPiPlus hPi)

/-! ## Axiom audit anchors -/

#print axioms localHadamardPair
#print axioms blockLocalHadamard_ker_eq_bot
#print axioms piPlus_rankMonotonicity_of_rankInvariant
#print axioms satDeciderGaugeSubgoals_of_piPlusConstructiveData
#print axioms satDeciderSpecificGaugeSubgoalDischarge_of_uniformPiPlus
#print axioms pathB_surface_of_uniformPiPlus

end PallLean.Paper93.DeepMath.PathC
