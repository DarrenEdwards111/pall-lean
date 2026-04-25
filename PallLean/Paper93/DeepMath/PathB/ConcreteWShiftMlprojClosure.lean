import PallLean.Paper93.Closure.PerTypeClosure
import PallLean.Paper93.DeepMath.PathB.ConcreteWRowEmbeddingBridge
import PallLean.Paper93.DeepMath.PathB.FixedProfileZeroHistogram
import PallLean.Paper93.Wiring.ConcreteW
import PallLean.SymmetricPower

/-!
# concreteW shift / mlProj closure reductions

This file is the concrete row-embedding I5 work surface for Agent J1's
canonical family

`fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau`.

The full `PerTypeShiftMlprojClosure` target is intentionally very strong: it
quantifies over arbitrary `shift` polynomials and arbitrary product witnesses.
The checked content below does two things.

* It packages the existing I1/I2/I3 closure interfaces directly at the concrete
  `concreteW` family and proves the exact I5 term consumed by H3/H4/H5.
* It isolates a zero-profile obstruction forced by any proof of the full I5
  target: even the empty product plus a one-variable shift must land in the
  all-zero profile subspace.  This is the remaining mathematical blocker for a
  hypothesis-free proof of the current I5 statement.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Closure
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW)
open scoped BigOperators

attribute [local instance] Classical.dec

/-- The canonical concrete row-embedding family used by the PathB bridge. -/
noncomputable def concreteWCanonical
    (n : ℕ) (hn4 : n ≥ 4) :
    ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau

/-! ## Concrete component interfaces -/

/-- I1, specialised to the canonical `concreteW` family. -/
def ConcreteWProductGrouping (n : ℕ) (hn4 : n ≥ 4) : Prop :=
  PerTypeProductGrouping (n := n) (concreteWCanonical n hn4)

/-- I2, specialised to the canonical `concreteW` family. -/
def ConcreteWShiftClosure (n : ℕ) (hn4 : n ≥ 4) : Prop :=
  PerTypeShiftClosure (n := n) (concreteWCanonical n hn4)

/-- I3, specialised to the canonical `concreteW` family. -/
def ConcreteWMlprojClosure (n : ℕ) (hn4 : n ≥ 4) : Prop :=
  PerTypeMlprojClosure (n := n) (concreteWCanonical n hn4)

/-- The exact I5 target for the canonical `concreteW` row embedding. -/
def ConcreteWShiftMlprojClosure (n : ℕ) (hn4 : n ≥ 4) : Prop :=
  PerTypeShiftMlprojClosure (n := n) (concreteWCanonical n hn4)

/-- Concrete I1 + I2 + I3 compose to the exact concrete I5 package consumed by
`ConcreteWRowEmbeddingBridge`. -/
theorem concreteW_shiftMlprojClosure_of_components
    (n : ℕ) (hn4 : n ≥ 4)
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    ConcreteWShiftMlprojClosure n hn4 :=
  perTypeShiftMlprojClosure_discharged
    (concreteWCanonical n hn4) hI1 hI2 hI3

/-- Same theorem with the target unfolded to the bridge's literal
`fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau` form. -/
theorem concreteW_perTypeShiftMlprojClosure_of_components
    (n : ℕ) (hn4 : n ≥ 4)
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    PerTypeShiftMlprojClosure (n := n)
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) :=
  concreteW_shiftMlprojClosure_of_components n hn4 hI1 hI2 hI3

/-- Directly consumable H3/H4/I1/I2/I3 frontier package for the concrete row
embedding bridge. -/
theorem concreteW_closureFrontier_of_H3_H4_components
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hDeriv :
      DerivClosurePerType (n := n)
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau))
    (hI1 : ConcreteWProductGrouping n hn4)
    (hI2 : ConcreteWShiftClosure n hn4)
    (hI3 : ConcreteWMlprojClosure n hn4) :
    CookLevinConcreteWRowEmbeddingClosureFrontier M n hn htb hns hn4 :=
  ⟨hFactor, hDeriv,
    concreteW_perTypeShiftMlprojClosure_of_components n hn4 hI1 hI2 hI3⟩

/-! ## Zero-profile pressure point for the full I5 statement -/

/-- The all-zero bounded profile at radius `k`. -/
def zeroBoundedProfile (k : ℕ) : BoundedProfile k :=
  ⟨zeroProfileHistogram, by intro tau; simp [zeroProfileHistogram]⟩

@[simp] theorem zeroBoundedProfile_toHistogram (k : ℕ) :
    (zeroBoundedProfile k).toHistogram = zeroProfileHistogram := rfl

/-- For `n ≥ 4`, a singleton derivative-variable list is within the
`Nat.log 2 n` budget. -/
theorem singleton_length_le_log_two_of_ge_four
    (n : ℕ) (hn4 : n ≥ 4) (v : Fin n) :
    [v].length ≤ Nat.log 2 n := by
  have hpow : 2 ^ 1 ≤ n := by omega
  have hlog : 1 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
  simpa using hlog

/-- Any proof of the concrete I5 package forces the one-variable shift of the
empty product to lie in the all-zero profile subspace.

This is a deliberately small, checked obstruction: the current I5 interface has
no side condition tying the shift degree to the profile histogram, so the
zero-profile case already requires this membership. -/
theorem concreteW_shiftMlprojClosure_forces_zeroProfile_X_mem
    (n : ℕ) (hn4 : n ≥ 4)
    (hI5 : ConcreteWShiftMlprojClosure n hn4)
    (v : Fin n) :
    MvPolynomial.X v ∈
      cookLevinProfileSubspace (n := n)
        (zeroBoundedProfile (Nat.log 2 n))
        (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) := by
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
          (zeroBoundedProfile (Nat.log 2 n))
          (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) := by
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

#print axioms concreteW_shiftMlprojClosure_of_components
#print axioms concreteW_perTypeShiftMlprojClosure_of_components
#print axioms concreteW_closureFrontier_of_H3_H4_components
#print axioms singleton_length_le_log_two_of_ge_four
#print axioms concreteW_shiftMlprojClosure_forces_zeroProfile_X_mem

end PallLean.Paper93.DeepMath.PathB
