import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteWChargedClosure

/-!
# Route B charged endpoint shift-closure progress

This file makes a local, paper-faithful reduction on the actual endpoint
charged shift-closure frontier

`EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge`.

It does not replace the charged target by raw same-profile closure, and it does
not assert the endpoint closure.  The checked content below separates the part
already covered by a charged closure for the canonical concreteW profile
subspace from the genuinely endpoint-augmentation residual.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.DeepMath.PathB
open PallLean.SymTensorPowerDim (symPower)
open SymmetricPowerBound
open WithinProfileBound

open scoped BigOperators

attribute [local instance] Classical.dec

/-! ## Monotonicity through profile subspaces -/

/-- Symmetric powers are monotone under enlargement of the underlying
submodule. -/
theorem symPower_mono_of_le
    {n k : ℕ}
    {W W' : Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (hW : W ≤ W') :
    symPower ℚ k W ≤ symPower ℚ k W' := by
  classical
  unfold symPower
  refine Submodule.span_mono ?_
  rintro p ⟨f, hf, rfl⟩
  exact ⟨f, fun i => hW (hf i), rfl⟩

/-- Profile subspaces are monotone under pointwise enlargement of the per-type
family. -/
theorem profileSubspace_mono_of_le
    {n : ℕ} {h : ProfileHistogram}
    {W W' : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (hW : ∀ τ, W τ ≤ W' τ) :
    profileSubspace h W ≤ profileSubspace h W' := by
  classical
  unfold profileSubspace
  refine Submodule.span_mono ?_
  rintro p ⟨f, hf, rfl⟩
  exact ⟨f, fun τ => symPower_mono_of_le (hW τ) (hf τ), rfl⟩

/-- Cook-Levin profile subspaces inherit pointwise monotonicity of the per-type
family. -/
theorem cookLevinProfileSubspace_mono_of_le
    {n : ℕ} (bp : BoundedProfile (Nat.log 2 n))
    {W W' : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (hW : ∀ τ, W τ ≤ W' τ) :
    cookLevinProfileSubspace bp W ≤ cookLevinProfileSubspace bp W' := by
  unfold cookLevinProfileSubspace
  exact profileSubspace_mono_of_le hW

/-- The canonical concreteW family embeds pointwise into the
endpoint-augmented family. -/
theorem concreteWCanonical_le_endpointAugmentedConcreteW
    (n : ℕ) (hn4 : n ≥ 4) (τ : ConstraintType) :
    concreteWCanonical n hn4 τ ≤ endpointAugmentedConcreteW n hn4 τ := by
  unfold endpointAugmentedConcreteW
  exact le_sup_left

/-- Therefore every canonical concreteW profile subspace embeds into the
corresponding endpoint-augmented profile subspace. -/
theorem cookLevinProfileSubspace_concreteWCanonical_le_endpointAugmentedConcreteW
    (n : ℕ) (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n)) :
    cookLevinProfileSubspace bp (concreteWCanonical n hn4) ≤
      cookLevinProfileSubspace bp (endpointAugmentedConcreteW n hn4) :=
  cookLevinProfileSubspace_mono_of_le bp
    (concreteWCanonical_le_endpointAugmentedConcreteW n hn4)

/-! ## Charged endpoint progress -/

/-- Canonical-source part of the endpoint charged shift frontier.

If the source element is already in the canonical concreteW profile subspace,
then canonical charged shift closure lands in the canonical target profile, and
monotonicity embeds that result into the endpoint-augmented target profile.
This keeps the original `charge` relation; no same-profile fallback is used. -/
theorem endpointAugmentedConcreteW_chargedShiftClosure_on_concreteProfile
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hCanon : ConcreteWChargedShiftClosure n hn4 charge)
    (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (hshift : shift.vars ⊆ S.toFinset)
    (p : MvPolynomial (Fin n) ℚ)
    (hcharge : charge bpSrc S shift bpTgt)
    (hp : p ∈ cookLevinProfileSubspace bpSrc (concreteWCanonical n hn4)) :
    shift * p ∈
      cookLevinProfileSubspace bpTgt (endpointAugmentedConcreteW n hn4) := by
  exact
    cookLevinProfileSubspace_concreteWCanonical_le_endpointAugmentedConcreteW
      n hn4 bpTgt
      (hCanon bpSrc bpTgt S hSlen shift hshift p hcharge hp)

/-- Residual endpoint-extra obligation after removing the canonical concreteW
profile component.

This is not asserted below.  It is the remaining endpoint-specific work needed
after `endpointAugmentedConcreteW_chargedShiftClosure_on_concreteProfile` handles
the canonical-source contribution. -/
def EndpointAugmentedConcreteWChargedShiftResidualClosure
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) : Prop :=
  ∀ (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (p : MvPolynomial (Fin n) ℚ),
    charge bpSrc S shift bpTgt →
      p ∈ cookLevinProfileSubspace bpSrc (endpointAugmentedConcreteW n hn4) →
        ∃ pc pr : MvPolynomial (Fin n) ℚ,
          pc ∈ cookLevinProfileSubspace bpSrc (concreteWCanonical n hn4) ∧
          p = pc + pr ∧
          shift * pr ∈
            cookLevinProfileSubspace bpTgt (endpointAugmentedConcreteW n hn4)

/-- Quotient form of the endpoint-extra residual obligation.

The source polynomial may be changed by a canonical-profile element before the
charged shift is tested.  This is the same content as the existential
`pc + pr` residual split, but it exposes the exact quotient-by-canonical
shape of the remaining endpoint-extra work. -/
def EndpointAugmentedConcreteWChargedShiftQuotientResidualClosure
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) : Prop :=
  ∀ (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (p : MvPolynomial (Fin n) ℚ),
    charge bpSrc S shift bpTgt →
      p ∈ cookLevinProfileSubspace bpSrc (endpointAugmentedConcreteW n hn4) →
        ∃ pc : MvPolynomial (Fin n) ℚ,
          pc ∈ cookLevinProfileSubspace bpSrc (concreteWCanonical n hn4) ∧
          shift * (p - pc) ∈
            cookLevinProfileSubspace bpTgt (endpointAugmentedConcreteW n hn4)

/-- The canonical-source slice of the residual split is already closed:
choose the whole source as the canonical component and zero residual. -/
theorem endpointAugmentedConcreteW_chargedShiftResidual_witness_of_concreteProfile
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (p : MvPolynomial (Fin n) ℚ)
    (_hcharge : charge bpSrc S shift bpTgt)
    (hp : p ∈ cookLevinProfileSubspace bpSrc (concreteWCanonical n hn4)) :
    ∃ pc pr : MvPolynomial (Fin n) ℚ,
      pc ∈ cookLevinProfileSubspace bpSrc (concreteWCanonical n hn4) ∧
      p = pc + pr ∧
      shift * pr ∈
        cookLevinProfileSubspace bpTgt (endpointAugmentedConcreteW n hn4) := by
  refine ⟨p, 0, hp, by simp, ?_⟩
  simp

/-- The split residual and quotient residual formulations are equivalent. -/
theorem endpointAugmentedConcreteW_chargedShiftResidualClosure_iff_quotientResidualClosure
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) :
    EndpointAugmentedConcreteWChargedShiftResidualClosure n hn4 charge ↔
      EndpointAugmentedConcreteWChargedShiftQuotientResidualClosure
        n hn4 charge := by
  constructor
  · intro hResidual bpSrc bpTgt S hSlen shift hshift p hcharge hp
    obtain ⟨pc, pr, hpc, hp_eq, hpr⟩ :=
      hResidual bpSrc bpTgt S hSlen shift hshift p hcharge hp
    refine ⟨pc, hpc, ?_⟩
    have hp_sub : p - pc = pr := by
      rw [hp_eq]
      simp [sub_eq_add_neg, add_assoc]
    simpa [hp_sub] using hpr
  · intro hQuot bpSrc bpTgt S hSlen shift hshift p hcharge hp
    obtain ⟨pc, hpc, hpr⟩ :=
      hQuot bpSrc bpTgt S hSlen shift hshift p hcharge hp
    refine ⟨pc, p - pc, hpc, ?_, hpr⟩
    simp [sub_eq_add_neg, add_left_comm]

/-- The endpoint charged shift closure follows from canonical charged closure
plus the residual endpoint-extra split above.

This theorem is a checked reduction of the actual target.  The residual
hypothesis is intentionally explicit: proving it, not this wrapper, is the
remaining hard endpoint-augmentation mathematics. -/
theorem endpointAugmentedConcreteW_chargedShiftClosure_of_canonical_and_residual
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hCanon : ConcreteWChargedShiftClosure n hn4 charge)
    (hResidual :
      EndpointAugmentedConcreteWChargedShiftResidualClosure n hn4 charge) :
    EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge := by
  intro bpSrc bpTgt S hSlen shift hshift p hcharge hp
  obtain ⟨pc, pr, hpc, hp_eq, hpr⟩ :=
    hResidual bpSrc bpTgt S hSlen shift hshift p hcharge hp
  have hpc_shift :
      shift * pc ∈
        cookLevinProfileSubspace bpTgt (endpointAugmentedConcreteW n hn4) :=
    endpointAugmentedConcreteW_chargedShiftClosure_on_concreteProfile
      n hn4 charge hCanon bpSrc bpTgt S hSlen shift hshift pc hcharge hpc
  rw [hp_eq, mul_add]
  exact Submodule.add_mem
    (cookLevinProfileSubspace bpTgt (endpointAugmentedConcreteW n hn4))
    hpc_shift hpr

/-- The actual endpoint charged closure implies the residual split, by taking
zero canonical component.  Consequently the residual split above is not, by
itself, a weaker target. -/
theorem endpointAugmentedConcreteW_chargedShiftResidualClosure_of_chargedShiftClosure
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hEndpoint :
      EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge) :
    EndpointAugmentedConcreteWChargedShiftResidualClosure n hn4 charge := by
  intro bpSrc bpTgt S hSlen shift hshift p hcharge hp
  refine ⟨0, p, Submodule.zero_mem _, by simp, ?_⟩
  exact hEndpoint bpSrc bpTgt S hSlen shift hshift p hcharge hp

/-- Exact no-go/equivalence for the current residual obligation: once the
canonical charged closure is available, proving the residual split is
equivalent to proving the full endpoint-augmented charged closure. -/
theorem endpointAugmentedConcreteW_chargedShiftClosure_iff_residualClosure_of_canonical
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hCanon : ConcreteWChargedShiftClosure n hn4 charge) :
    EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge ↔
      EndpointAugmentedConcreteWChargedShiftResidualClosure n hn4 charge := by
  constructor
  · exact
      endpointAugmentedConcreteW_chargedShiftResidualClosure_of_chargedShiftClosure
        n hn4 charge
  · intro hResidual
    exact
      endpointAugmentedConcreteW_chargedShiftClosure_of_canonical_and_residual
        n hn4 charge hCanon hResidual

/-- Same equivalence in quotient-residual form.  This is the sharper residual
frontier: endpoint closure is exactly the statement that every endpoint source
class modulo the canonical profile has a charged-shift representative landing
in the endpoint target profile. -/
theorem endpointAugmentedConcreteW_chargedShiftClosure_iff_quotientResidualClosure_of_canonical
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hCanon : ConcreteWChargedShiftClosure n hn4 charge) :
    EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge ↔
      EndpointAugmentedConcreteWChargedShiftQuotientResidualClosure
        n hn4 charge := by
  exact
    (endpointAugmentedConcreteW_chargedShiftClosure_iff_residualClosure_of_canonical
      n hn4 charge hCanon).trans
      (endpointAugmentedConcreteW_chargedShiftResidualClosure_iff_quotientResidualClosure
        n hn4 charge)

/-! ## Axiom audit anchors -/

#print axioms symPower_mono_of_le
#print axioms profileSubspace_mono_of_le
#print axioms cookLevinProfileSubspace_mono_of_le
#print axioms concreteWCanonical_le_endpointAugmentedConcreteW
#print axioms cookLevinProfileSubspace_concreteWCanonical_le_endpointAugmentedConcreteW
#print axioms endpointAugmentedConcreteW_chargedShiftClosure_on_concreteProfile
#print axioms endpointAugmentedConcreteW_chargedShiftResidual_witness_of_concreteProfile
#print axioms endpointAugmentedConcreteW_chargedShiftResidualClosure_iff_quotientResidualClosure
#print axioms endpointAugmentedConcreteW_chargedShiftClosure_of_canonical_and_residual
#print axioms endpointAugmentedConcreteW_chargedShiftResidualClosure_of_chargedShiftClosure
#print axioms endpointAugmentedConcreteW_chargedShiftClosure_iff_residualClosure_of_canonical
#print axioms endpointAugmentedConcreteW_chargedShiftClosure_iff_quotientResidualClosure_of_canonical

end PallLean.Paper93.Paper283
