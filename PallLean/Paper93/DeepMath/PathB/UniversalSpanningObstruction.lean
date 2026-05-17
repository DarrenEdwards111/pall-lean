import PallLean.Paper93.Closure.PerTypeClosure
import PallLean.Paper93.DeepMath.PathB.ConcreteWShiftMlprojClosure

/-!
# Universal spanning obstruction diagnostics

This file records a checked pressure point found while pushing on
`CookLevinPerTypeSpanning_universal` from first principles: the current universal
I2/I5 interfaces quantify over an arbitrary per-type family `W`.  Already at the
all-zero profile, shift closure forces every one-variable shift of the empty
product into the zero-profile subspace.

This is not a contradiction by itself, but it isolates the precise over-strong
interface: a genuine proof must either instantiate a concrete shift-stable `W`,
or weaken the universal target so it no longer asks arbitrary `W` to absorb
external shifts at zero derivative profile.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Closure
open PallLean.Paper93.Spanning
open scoped BigOperators

attribute [local instance] Classical.dec

/-- Universal I2 at the zero profile forces the one-variable polynomial `X v`
into the all-zero profile subspace, for every arbitrary family `W`.

This is the smallest checked obstruction to the current `..._universal` route:
zero derivative profile has no derivative slots, but the shift side condition
still permits `shift = X v` whenever `S = [v]`. -/
theorem perTypeShiftClosure_forces_zeroProfile_X_mem
    (n : ℕ) (hn4 : n ≥ 4)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hI2 : PerTypeShiftClosure (n := n) W)
    (v : Fin n) :
    MvPolynomial.X v ∈
      cookLevinProfileSubspace (n := n)
        (zeroBoundedProfile (Nat.log 2 n)) W := by
  classical
  have hSlen : [v].length ≤ Nat.log 2 n :=
    singleton_length_le_log_two_of_ge_four n hn4 v
  have hshift :
      (MvPolynomial.X v : MvPolynomial (Fin n) ℚ).vars ⊆ [v].toFinset := by
    intro x hx
    simpa [MvPolynomial.vars_X] using hx
  have hone : (1 : MvPolynomial (Fin n) ℚ) ∈
      cookLevinProfileSubspace (n := n)
        (zeroBoundedProfile (Nat.log 2 n)) W := by
    unfold cookLevinProfileSubspace profileSubspace
    apply Submodule.subset_span
    refine ⟨(fun _ : ConstraintType => 1), ?_, ?_⟩
    · intro σ
      unfold PallLean.SymTensorPowerDim.symPower
      apply Submodule.subset_span
      refine ⟨(fun i : Fin 0 => False.elim (Fin.elim0 i)), ?_, ?_⟩
      · intro i
        exact False.elim (Fin.elim0 i)
      · simp
    · simp
  have hmem := hI2 (zeroBoundedProfile (Nat.log 2 n)) [v] hSlen
    (MvPolynomial.X v) hshift 1 hone
  simpa [mul_one] using hmem

/-- Universal I5 has the same zero-profile pressure point directly, without
splitting through I2. -/
theorem perTypeShiftMlprojClosure_forces_zeroProfile_X_mem
    (n : ℕ) (hn4 : n ≥ 4)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hI5 : PerTypeShiftMlprojClosure (n := n) W)
    (v : Fin n) :
    MvPolynomial.X v ∈
      cookLevinProfileSubspace (n := n)
        (zeroBoundedProfile (Nat.log 2 n)) W := by
  classical
  have hSlen : [v].length ≤ Nat.log 2 n :=
    singleton_length_le_log_two_of_ge_four n hn4 v
  have hshift :
      (MvPolynomial.X v : MvPolynomial (Fin n) ℚ).vars ⊆ [v].toFinset := by
    intro x hx
    simpa [MvPolynomial.vars_X] using hx
  have hmem :
      mlProj ((MvPolynomial.X v : MvPolynomial (Fin n) ℚ) *
          (1 : MvPolynomial (Fin n) ℚ)) ∈
        cookLevinProfileSubspace (n := n)
          (zeroBoundedProfile (Nat.log 2 n)) W := by
    refine hI5 (zeroBoundedProfile (Nat.log 2 n)) [v] hSlen
      (MvPolynomial.X v) hshift 1 ?_
    refine ⟨0, (fun i => False.elim (Fin.elim0 i)),
      (fun i => False.elim (Fin.elim0 i)),
      (fun i => False.elim (Fin.elim0 i)), ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact False.elim (Fin.elim0 i)
    · intro i
      exact False.elim (Fin.elim0 i)
    · simp
    · funext tau
      simp [derivCountProfile, zeroProfileHistogram]
    · simp
  simpa [mul_one, SymmetricPower.mlProj_X] using hmem

/-- With `W = ⊥`, the zero-profile subspace is exactly the scalar line.
This is the algebra behind the obstruction: zero derivative slots leave only the
empty product in each per-type symmetric power. -/
theorem cookLevinProfileSubspace_zero_bot_eq_span_one
    (n : ℕ) :
    cookLevinProfileSubspace (n := n)
        (zeroBoundedProfile (Nat.log 2 n))
        (fun _ : ConstraintType => (⊥ : Submodule ℚ (MvPolynomial (Fin n) ℚ))) =
      Submodule.span ℚ ({(1 : MvPolynomial (Fin n) ℚ)} : Set (MvPolynomial (Fin n) ℚ)) := by
  classical
  unfold cookLevinProfileSubspace profileSubspace
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨f, hf, rfl⟩
    have hf_scalar : ∀ σ : ConstraintType,
        f σ ∈ Submodule.span ℚ
          ({(1 : MvPolynomial (Fin n) ℚ)} : Set (MvPolynomial (Fin n) ℚ)) := by
      intro σ
      have h := hf σ
      unfold PallLean.SymTensorPowerDim.symPower at h
      simpa using h
    choose c hc using fun σ => Submodule.mem_span_singleton.mp (hf_scalar σ)
    refine Submodule.mem_span_singleton.mpr ⟨∏ σ, c σ, ?_⟩
    calc
      (∏ σ : ConstraintType, c σ) • (1 : MvPolynomial (Fin n) ℚ)
          = ∏ σ : ConstraintType, (c σ • (1 : MvPolynomial (Fin n) ℚ)) := by
            simp_rw [← MvPolynomial.C_eq_smul_one]
            simp [map_prod]
      _ = ∏ σ : ConstraintType, f σ := by
            apply Finset.prod_congr rfl
            intro σ _
            exact hc σ
  · apply Submodule.span_le.mpr
    intro p hp
    have hp1 : p = (1 : MvPolynomial (Fin n) ℚ) := by simpa using hp
    subst p
    apply Submodule.subset_span
    refine ⟨(fun _ : ConstraintType => 1), ?_, ?_⟩
    · intro σ
      unfold PallLean.SymTensorPowerDim.symPower
      apply Submodule.subset_span
      refine ⟨(fun i : Fin 0 => False.elim (Fin.elim0 i)), ?_, ?_⟩
      · intro i
        exact False.elim (Fin.elim0 i)
      · simp
    · simp

/-- The polynomial variable `X v` is not in the scalar line. -/
theorem X_not_mem_span_one
    {n : ℕ} (v : Fin n) :
    ¬ MvPolynomial.X v ∈
      Submodule.span ℚ ({(1 : MvPolynomial (Fin n) ℚ)} : Set (MvPolynomial (Fin n) ℚ)) := by
  intro h
  rcases Submodule.mem_span_singleton.mp h with ⟨c, hc⟩
  have hcoeff := congrArg
    (fun q : MvPolynomial (Fin n) ℚ => MvPolynomial.coeff (Finsupp.single v 1) q) hc
  change MvPolynomial.coeff (Finsupp.single v 1) (c • (1 : MvPolynomial (Fin n) ℚ)) =
      MvPolynomial.coeff (Finsupp.single v 1) (MvPolynomial.X v) at hcoeff
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_one, MvPolynomial.coeff_X'] at hcoeff
  have hne : (Finsupp.single v 1 : Fin n →₀ ℕ) ≠ 0 := by
    exact Finsupp.single_ne_zero.mpr (by norm_num)
  rw [if_neg hne.symm] at hcoeff
  norm_num at hcoeff

/-- Consequently the current universal I2 interface is false: it asks every
arbitrary `W`, including `⊥`, to absorb one-variable shifts at zero profile. -/
theorem not_PerTypeShiftClosure_bot
    (n : ℕ) (hn4 : n ≥ 4) (v : Fin n) :
    ¬ PerTypeShiftClosure (n := n)
      (fun _ : ConstraintType => (⊥ : Submodule ℚ (MvPolynomial (Fin n) ℚ))) := by
  intro hI2
  have hx := perTypeShiftClosure_forces_zeroProfile_X_mem n hn4
    (fun _ : ConstraintType => (⊥ : Submodule ℚ (MvPolynomial (Fin n) ℚ))) hI2 v
  rw [cookLevinProfileSubspace_zero_bot_eq_span_one n] at hx
  exact X_not_mem_span_one v hx

/-- Same obstruction for the composed universal I5 interface. -/
theorem not_PerTypeShiftMlprojClosure_bot
    (n : ℕ) (hn4 : n ≥ 4) (v : Fin n) :
    ¬ PerTypeShiftMlprojClosure (n := n)
      (fun _ : ConstraintType => (⊥ : Submodule ℚ (MvPolynomial (Fin n) ℚ))) := by
  intro hI5
  have hx := perTypeShiftMlprojClosure_forces_zeroProfile_X_mem n hn4
    (fun _ : ConstraintType => (⊥ : Submodule ℚ (MvPolynomial (Fin n) ℚ))) hI5 v
  rw [cookLevinProfileSubspace_zero_bot_eq_span_one n] at hx
  exact X_not_mem_span_one v hx

#print axioms perTypeShiftClosure_forces_zeroProfile_X_mem
#print axioms perTypeShiftMlprojClosure_forces_zeroProfile_X_mem
#print axioms cookLevinProfileSubspace_zero_bot_eq_span_one
#print axioms X_not_mem_span_one
#print axioms not_PerTypeShiftClosure_bot
#print axioms not_PerTypeShiftMlprojClosure_bot

end PallLean.Paper93.DeepMath.PathB
