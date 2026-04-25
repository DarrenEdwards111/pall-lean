import PallLean.Paper93.Closure.PerTypeClosure
import PallLean.Paper93.Wiring.ConcreteW

/-!
# Augmented concreteW I5 route

The original `PerTypeShiftMlprojClosure` keeps the same bounded profile before
and after multiplication by `shift`.  That is too strong for raw
`concreteW`: at the zero profile it would make `mlProj shift` live in the
zero-profile space.

This file records the corrected composition shape.  Product grouping lands in
the derivative profile; shift multiplication must then be charged into a
possibly different target profile; `mlProj` is applied at that target profile.
The remaining side condition is the charged shift closure itself.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial SymmetricPowerBound
open WithinProfileBound SPDP MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Spanning
open PallLean.Paper93.Closure
open PallLean.Paper93.Wiring

attribute [local instance] Classical.dec

/-- A relation saying that a `shift` supported on `S` moves a source profile to
a target profile.  This is intentionally a relation rather than a function:
call sites may have several admissible charged targets, or none. -/
abbrev ProfileCharge (n : ℕ) :=
  BoundedProfile (Nat.log 2 n) →
    List (Fin n) →
      MvPolynomial (Fin n) ℚ →
        BoundedProfile (Nat.log 2 n) → Prop

/-- Corrected I2 side condition: multiplying an element of a source profile by
`shift` lands in a charged target profile. -/
def PerTypeChargedShiftClosure {n : ℕ}
    (charge : ProfileCharge n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) : Prop :=
  ∀ (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (p : MvPolynomial (Fin n) ℚ),
    charge bpSrc S shift bpTgt →
      p ∈ cookLevinProfileSubspace bpSrc W →
        shift * p ∈ cookLevinProfileSubspace bpTgt W

/-- Corrected I5 target: the product has derivative profile `bpSrc`, while the
shifted/projected polynomial lands in the charged target profile `bpTgt`. -/
def PerTypeShiftMlprojClosureCharged {n : ℕ}
    (charge : ProfileCharge n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) : Prop :=
  ∀ (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (g : MvPolynomial (Fin n) ℚ)
    (_hg_prod :
      ∃ (L : ℕ) (factors : Fin L → MvPolynomial (Fin n) ℚ)
        (constraintType : Fin L → ConstraintType)
        (d : Fin L → List (Fin n)),
        (∀ i, ∀ v ∈ d i, v ∈ S) ∧
        (∀ i, iterDerivList (d i) (factors i) ∈ W (constraintType i)) ∧
        g = Finset.univ.prod (fun i => iterDerivList (d i) (factors i)) ∧
        derivCountProfile constraintType d = bpSrc.toHistogram ∧
        ∑ i : Fin L, (d i).length ≤ S.length),
    charge bpSrc S shift bpTgt →
      mlProj (shift * g) ∈ cookLevinProfileSubspace bpTgt W

/-- Charged I5 composition.  This is the corrected replacement for the raw
same-profile I5 route: I1 gives the unshifted product at `bpSrc`, the charged
I2 side condition moves it to `bpTgt`, and I3 applies `mlProj` at `bpTgt`. -/
theorem perTypeShiftMlprojClosure_charged_discharged {n : ℕ}
    (charge : ProfileCharge n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hI1 : PerTypeProductGrouping (n := n) W)
    (hI2c : PerTypeChargedShiftClosure (n := n) charge W)
    (hI3 : PerTypeMlprojClosure (n := n) W) :
    PerTypeShiftMlprojClosureCharged (n := n) charge W := by
  classical
  intro bpSrc bpTgt S hSlen shift hshiftvars g hg_prod hcharge
  obtain ⟨L, factors, constraintType, d,
          hd_elts, hFactorMem, hg_prod_eq, hprof, hsum⟩ := hg_prod
  have hProdMem :
      (Finset.univ.prod (fun i => iterDerivList (d i) (factors i)))
        ∈ cookLevinProfileSubspace bpSrc W :=
    hI1 bpSrc S hSlen L factors constraintType d
      hd_elts hFactorMem hprof hsum
  have hgMem : g ∈ cookLevinProfileSubspace bpSrc W := by
    rw [hg_prod_eq]
    exact hProdMem
  have hShiftMem : shift * g ∈ cookLevinProfileSubspace bpTgt W :=
    hI2c bpSrc bpTgt S hSlen shift hshiftvars g hcharge hgMem
  exact hI3 bpTgt (shift * g) hShiftMem

/-! ## Same-profile recovery

The old I5 shape is exactly the special case where the charge relation forces
`bpTgt = bpSrc`.  This section is useful for comparing the corrected interface
with the existing closure props, but it is not the route to use for raw
`concreteW`.
-/

/-- Same-profile charge relation, included only to connect the corrected
interface to the existing `PerTypeShiftClosure` API. -/
def sameProfileCharge {n : ℕ} : ProfileCharge n :=
  fun bpSrc _ _ bpTgt => bpTgt = bpSrc

/-- Existing same-profile shift closure is the same-profile instance of the
charged shift side condition. -/
theorem perTypeChargedShiftClosure_sameProfile_of_shiftClosure {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hI2 : PerTypeShiftClosure (n := n) W) :
    PerTypeChargedShiftClosure (n := n) sameProfileCharge W := by
  intro bpSrc bpTgt S hSlen shift hshiftvars p hcharge hp
  rw [hcharge]
  exact hI2 bpSrc S hSlen shift hshiftvars p hp

/-- Composing the existing I1/I2/I3 interfaces gives the same-profile charged
I5 statement.  This is deliberately separated from the concreteW theorem below:
same-profile shift closure is the problematic raw-concreteW assumption. -/
theorem perTypeShiftMlprojClosure_charged_sameProfile_from_I1_I2_I3 {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hI1 : PerTypeProductGrouping (n := n) W)
    (hI2 : PerTypeShiftClosure (n := n) W)
    (hI3 : PerTypeMlprojClosure (n := n) W) :
    PerTypeShiftMlprojClosureCharged (n := n) sameProfileCharge W :=
  perTypeShiftMlprojClosure_charged_discharged
    (n := n) sameProfileCharge W hI1
    (perTypeChargedShiftClosure_sameProfile_of_shiftClosure W hI2)
    hI3

/-- The existing H5 `PerTypeShiftMlprojClosure` is the same-profile charged
statement with the charge proof supplied by reflexivity. -/
theorem perTypeShiftMlprojClosure_of_charged_sameProfile {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (h :
      PerTypeShiftMlprojClosureCharged (n := n) sameProfileCharge W) :
    PerTypeShiftMlprojClosure (n := n) W := by
  intro bp S hSlen shift hshiftvars g hg_prod
  exact h bp bp S hSlen shift hshiftvars g hg_prod rfl

/-! ## Augmented concreteW specialisation

`augmentedConcreteW` is a conservative wrapper: callers choose the additional
per-type submodule `extra`.  The checked theorem below does not assert the
charged shift side condition; it isolates it as the remaining mathematical
obligation for the chosen augmentation and charge relation.
-/

/-- ConcreteW enlarged by an arbitrary per-type `extra` submodule.

This is kept distinct from `AugmentedConcreteW.augmentedConcreteW`, which is a
global ambient span over all variables.  Here we preserve the row-indexed
`concreteW` core and add a caller-supplied extra submodule. -/
noncomputable def augmentedConcreteWWithExtra
    (n : ℕ) (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n)
    (extra : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (τ : ConstraintType) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  concreteW n hn4 σ τ ⊔ extra τ

/-- Raw `concreteW` embeds into every augmented concreteW. -/
theorem concreteW_le_augmentedConcreteWWithExtra
    (n : ℕ) (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n)
    (extra : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (τ : ConstraintType) :
    concreteW n hn4 σ τ ≤ augmentedConcreteWWithExtra n hn4 σ extra τ := by
  unfold augmentedConcreteWWithExtra
  exact le_sup_left

/-- Canonical-row augmented concreteW family used by PathB call sites. -/
noncomputable def canonicalAugmentedConcreteW
    (n : ℕ) (hn4 : n ≥ 4)
    (extra : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) :
    ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  augmentedConcreteWWithExtra n hn4 (Fin.castLEEmb hn4) extra

/-- Corrected charged I5 for any augmented concreteW family.  The only
remaining side condition is `PerTypeChargedShiftClosure charge` for that
chosen augmentation. -/
theorem perTypeShiftMlprojClosure_charged_augmentedConcreteW {n : ℕ}
    (hn4 : n ≥ 4) (σ : Fin 4 ↪ Fin n)
    (extra : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (charge : ProfileCharge n)
    (hI1 :
      PerTypeProductGrouping (n := n)
        (augmentedConcreteWWithExtra n hn4 σ extra))
    (hI2c :
      PerTypeChargedShiftClosure (n := n) charge
        (augmentedConcreteWWithExtra n hn4 σ extra))
    (hI3 :
      PerTypeMlprojClosure (n := n)
        (augmentedConcreteWWithExtra n hn4 σ extra)) :
    PerTypeShiftMlprojClosureCharged (n := n) charge
      (augmentedConcreteWWithExtra n hn4 σ extra) :=
  perTypeShiftMlprojClosure_charged_discharged
    (n := n) charge (augmentedConcreteWWithExtra n hn4 σ extra) hI1 hI2c hI3

/-- Canonical-row specialisation of the corrected charged I5 route. -/
theorem perTypeShiftMlprojClosure_charged_canonicalAugmentedConcreteW {n : ℕ}
    (hn4 : n ≥ 4)
    (extra : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (charge : ProfileCharge n)
    (hI1 :
      PerTypeProductGrouping (n := n)
        (canonicalAugmentedConcreteW n hn4 extra))
    (hI2c :
      PerTypeChargedShiftClosure (n := n) charge
        (canonicalAugmentedConcreteW n hn4 extra))
    (hI3 :
      PerTypeMlprojClosure (n := n)
        (canonicalAugmentedConcreteW n hn4 extra)) :
    PerTypeShiftMlprojClosureCharged (n := n) charge
      (canonicalAugmentedConcreteW n hn4 extra) :=
  perTypeShiftMlprojClosure_charged_discharged
    (n := n) charge (canonicalAugmentedConcreteW n hn4 extra) hI1 hI2c hI3

#print axioms perTypeShiftMlprojClosure_charged_discharged
#print axioms perTypeChargedShiftClosure_sameProfile_of_shiftClosure
#print axioms perTypeShiftMlprojClosure_charged_sameProfile_from_I1_I2_I3
#print axioms perTypeShiftMlprojClosure_of_charged_sameProfile
#print axioms concreteW_le_augmentedConcreteWWithExtra
#print axioms perTypeShiftMlprojClosure_charged_augmentedConcreteW
#print axioms perTypeShiftMlprojClosure_charged_canonicalAugmentedConcreteW

end PallLean.Paper93.DeepMath.PathB
