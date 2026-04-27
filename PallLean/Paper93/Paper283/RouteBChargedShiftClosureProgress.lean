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

/-! ## Endpoint-span-only charged subcase -/

/-- The endpoint repair span, viewed as a constant per-type family. -/
noncomputable def concreteWEndpointSpanFamily
    (n : ℕ) (hn4 : n ≥ 4) :
    ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  fun _ => concreteWEndpointSpan n hn4

/-- Multiplying a symmetric-power element by one element of the underlying
submodule raises the symmetric-power degree by one. -/
theorem symPower_mul_left_mem_succ
    {n k : ℕ} {W : Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    {a b : MvPolynomial (Fin n) ℚ}
    (ha : a ∈ W) (hb : b ∈ symPower ℚ k W) :
    a * b ∈ symPower ℚ (k + 1) W := by
  classical
  unfold symPower at hb ⊢
  let T : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    Submodule.span ℚ
      {p : MvPolynomial (Fin n) ℚ |
        ∃ f : Fin (k + 1) → MvPolynomial (Fin n) ℚ,
          (∀ i, f i ∈ W) ∧ p = ∏ i, f i}
  change a * b ∈ T
  refine Submodule.span_induction
    (p := fun q : MvPolynomial (Fin n) ℚ => fun _ => a * q ∈ T)
    ?_ ?_ ?_ ?_ hb
  · rintro q ⟨f, hf, rfl⟩
    refine Submodule.subset_span ?_
    let g : Fin (k + 1) → MvPolynomial (Fin n) ℚ :=
      Fin.cases a f
    refine ⟨g, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact ha
      | succ i => exact hf i
    · simpa [g] using (Fin.prod_univ_succ g).symm
  · simp [T]
  · intro p q _ _ hp hq
    rw [mul_add]
    exact Submodule.add_mem T hp hq
  · intro c q _ hq
    simpa [smul_eq_C_mul, mul_assoc, mul_left_comm, mul_comm] using
      Submodule.smul_mem T c hq

/-- The endpoint repair span embeds pointwise into the endpoint-augmented
concreteW family. -/
theorem concreteWEndpointSpan_le_endpointAugmentedConcreteW
    (n : ℕ) (hn4 : n ≥ 4) (τ : ConstraintType) :
    concreteWEndpointSpan n hn4 ≤ endpointAugmentedConcreteW n hn4 τ := by
  unfold endpointAugmentedConcreteW
  exact le_sup_right

/-- Generator-level charged closure for the endpoint-only profile subspace.

This is deliberately stricter than the broad residual above: the source
generators are products of symmetric powers of the concrete endpoint repair
span alone, not arbitrary endpoint-augmented profile elements. -/
def EndpointAugmentedConcreteWEndpointSpanGeneratorChargedShiftClosure
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) : Prop :=
  ∀ (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (f : ConstraintType → MvPolynomial (Fin n) ℚ),
    charge bpSrc S shift bpTgt →
      (∀ τ : ConstraintType,
        f τ ∈
          symPower ℚ (bpSrc.toHistogram τ)
            (concreteWEndpointSpan n hn4)) →
        shift * (∏ τ : ConstraintType, f τ) ∈
          cookLevinProfileSubspace bpTgt
            (endpointAugmentedConcreteW n hn4)

/-- A concrete one-step charge compatibility condition for endpoint-span
generators.

For every charged shift, the shift itself lies in the endpoint repair span and
the target profile is obtained from the source by adding one endpoint-span
factor to a single constraint type. -/
def EndpointAugmentedConcreteWEndpointSpanOneStepChargeCompatible
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) : Prop :=
  ∀ (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset),
    charge bpSrc S shift bpTgt →
      ∃ τ0 : ConstraintType,
        shift ∈ concreteWEndpointSpan n hn4 ∧
        bpTgt.toHistogram τ0 = bpSrc.toHistogram τ0 + 1 ∧
        ∀ τ : ConstraintType, τ ≠ τ0 →
          bpTgt.toHistogram τ = bpSrc.toHistogram τ

/-- A one-step endpoint-compatible charge relation proves the endpoint-span
generator residual. -/
theorem endpointAugmentedConcreteW_endpointSpanGeneratorChargedShiftClosure_of_oneStepChargeCompatible
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hCompat :
      EndpointAugmentedConcreteWEndpointSpanOneStepChargeCompatible
        n hn4 charge) :
    EndpointAugmentedConcreteWEndpointSpanGeneratorChargedShiftClosure
      n hn4 charge := by
  intro bpSrc bpTgt S hSlen shift hshift f hcharge hf
  obtain ⟨τ0, hshiftEndpoint, hbump, hsame⟩ :=
    hCompat bpSrc bpTgt S hSlen shift hshift hcharge
  unfold cookLevinProfileSubspace profileSubspace
  refine Submodule.subset_span ?_
  let f' : ConstraintType → MvPolynomial (Fin n) ℚ :=
    Function.update f τ0 (shift * f τ0)
  refine ⟨f', ?_, ?_⟩
  · intro τ
    by_cases hτ : τ = τ0
    · subst τ
      have hmulEndpoint :
          shift * f τ0 ∈
            symPower ℚ (bpSrc.toHistogram τ0 + 1)
              (concreteWEndpointSpan n hn4) :=
        symPower_mul_left_mem_succ hshiftEndpoint (hf τ0)
      have hmulAug :
          shift * f τ0 ∈
            symPower ℚ (bpSrc.toHistogram τ0 + 1)
              (endpointAugmentedConcreteW n hn4 τ0) :=
        symPower_mono_of_le
          (concreteWEndpointSpan_le_endpointAugmentedConcreteW n hn4 τ0)
          hmulEndpoint
      simpa [f', hbump] using hmulAug
    · have hfAug :
          f τ ∈
            symPower ℚ (bpSrc.toHistogram τ)
              (endpointAugmentedConcreteW n hn4 τ) :=
        symPower_mono_of_le
          (concreteWEndpointSpan_le_endpointAugmentedConcreteW n hn4 τ)
          (hf τ)
      simpa [f', hτ, hsame τ hτ] using hfAug
  · have hprod :
        (∏ τ : ConstraintType, f' τ) =
          shift * (∏ τ : ConstraintType, f τ) := by
      have hcompl :
          (∏ x ∈ ({τ0}ᶜ : Finset ConstraintType), f' x) =
            ∏ x ∈ ({τ0}ᶜ : Finset ConstraintType), f x := by
        refine Finset.prod_congr rfl ?_
        intro x hx
        have hxne : x ≠ τ0 := by
          simpa using hx
        simp [f', hxne]
      rw [Fintype.prod_eq_mul_prod_compl τ0 f',
        Fintype.prod_eq_mul_prod_compl τ0 f]
      rw [hcompl]
      simp [f', mul_assoc]
    exact hprod.symm

/-- Charged closure for the endpoint-only profile subspace. -/
def EndpointAugmentedConcreteWEndpointSpanProfileChargedShiftClosure
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n) : Prop :=
  ∀ (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (p : MvPolynomial (Fin n) ℚ),
    charge bpSrc S shift bpTgt →
      p ∈ cookLevinProfileSubspace bpSrc
        (concreteWEndpointSpanFamily n hn4) →
        shift * p ∈
          cookLevinProfileSubspace bpTgt
            (endpointAugmentedConcreteW n hn4)

/-- The generator-level endpoint-span residual extends by linearity to the
whole endpoint-only profile subspace. -/
theorem endpointAugmentedConcreteW_endpointSpanProfileChargedShiftClosure_of_generatorClosure
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hGen :
      EndpointAugmentedConcreteWEndpointSpanGeneratorChargedShiftClosure
        n hn4 charge) :
    EndpointAugmentedConcreteWEndpointSpanProfileChargedShiftClosure
      n hn4 charge := by
  intro bpSrc bpTgt S hSlen shift hshift p hcharge hp
  let Vt :=
    cookLevinProfileSubspace bpTgt
      (endpointAugmentedConcreteW n hn4)
  change shift * p ∈ Vt
  unfold cookLevinProfileSubspace profileSubspace concreteWEndpointSpanFamily at hp
  refine Submodule.span_induction
    (p := fun q : MvPolynomial (Fin n) ℚ => fun _ => shift * q ∈ Vt)
    ?_ ?_ ?_ ?_ hp
  · rintro q ⟨f, hf, rfl⟩
    exact hGen bpSrc bpTgt S hSlen shift hshift f hcharge hf
  · simp [Vt]
  · intro p q _ _ hp hq
    rw [mul_add]
    exact Submodule.add_mem Vt hp hq
  · intro a q _ hq
    simpa [smul_eq_C_mul, mul_assoc, mul_left_comm, mul_comm] using
      Submodule.smul_mem Vt a hq

/-- A strict structural residual: every endpoint-augmented source profile
element splits as a canonical-profile part plus an endpoint-span-only profile
part.

This is not asserted by the file.  It identifies the algebraic source of the
remaining endpoint work: products coming from symmetric powers of
`concreteWCanonical τ ⊔ concreteWEndpointSpan` must be decomposed without using
the full endpoint charged closure. -/
def EndpointAugmentedConcreteWCanonicalEndpointSpanSplitSource
    (n : ℕ) (hn4 : n ≥ 4) : Prop :=
  ∀ (bp : BoundedProfile (Nat.log 2 n))
    (p : MvPolynomial (Fin n) ℚ),
    p ∈ cookLevinProfileSubspace bp
      (endpointAugmentedConcreteW n hn4) →
      ∃ pc pe : MvPolynomial (Fin n) ℚ,
        pc ∈ cookLevinProfileSubspace bp
          (concreteWCanonical n hn4) ∧
        pe ∈ cookLevinProfileSubspace bp
          (concreteWEndpointSpanFamily n hn4) ∧
        p = pc + pe

/-- The actual charged endpoint closure holds on any source element with an
explicit canonical-plus-endpoint-span split. -/
theorem endpointAugmentedConcreteW_chargedShiftClosure_on_canonical_endpointSpan_split_source
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hCanon : ConcreteWChargedShiftClosure n hn4 charge)
    (hEndpoint :
      EndpointAugmentedConcreteWEndpointSpanProfileChargedShiftClosure
        n hn4 charge)
    (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (S : List (Fin n)) (hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (hshift : shift.vars ⊆ S.toFinset)
    (p pc pe : MvPolynomial (Fin n) ℚ)
    (hcharge : charge bpSrc S shift bpTgt)
    (hpc :
      pc ∈ cookLevinProfileSubspace bpSrc
        (concreteWCanonical n hn4))
    (hpe :
      pe ∈ cookLevinProfileSubspace bpSrc
        (concreteWEndpointSpanFamily n hn4))
    (hp : p = pc + pe) :
    shift * p ∈
      cookLevinProfileSubspace bpTgt
        (endpointAugmentedConcreteW n hn4) := by
  have hpc_shift :
      shift * pc ∈
        cookLevinProfileSubspace bpTgt
          (endpointAugmentedConcreteW n hn4) :=
    endpointAugmentedConcreteW_chargedShiftClosure_on_concreteProfile
      n hn4 charge hCanon bpSrc bpTgt S hSlen shift hshift pc hcharge hpc
  have hpe_shift :
      shift * pe ∈
        cookLevinProfileSubspace bpTgt
          (endpointAugmentedConcreteW n hn4) :=
    hEndpoint bpSrc bpTgt S hSlen shift hshift pe hcharge hpe
  rw [hp, mul_add]
  exact Submodule.add_mem
    (cookLevinProfileSubspace bpTgt (endpointAugmentedConcreteW n hn4))
    hpc_shift hpe_shift

/-- Canonical charged closure plus endpoint-span charged closure proves the
full endpoint charged closure once the strict split-source residual is
available. -/
theorem endpointAugmentedConcreteW_chargedShiftClosure_of_canonical_endpointSpanProfile_and_split
    (n : ℕ) (hn4 : n ≥ 4) (charge : ProfileCharge n)
    (hCanon : ConcreteWChargedShiftClosure n hn4 charge)
    (hEndpoint :
      EndpointAugmentedConcreteWEndpointSpanProfileChargedShiftClosure
        n hn4 charge)
    (hSplit :
      EndpointAugmentedConcreteWCanonicalEndpointSpanSplitSource n hn4) :
    EndpointAugmentedConcreteWChargedShiftClosure n hn4 charge := by
  intro bpSrc bpTgt S hSlen shift hshift p hcharge hp
  obtain ⟨pc, pe, hpc, hpe, hp_eq⟩ := hSplit bpSrc p hp
  exact
    endpointAugmentedConcreteW_chargedShiftClosure_on_canonical_endpointSpan_split_source
      n hn4 charge hCanon hEndpoint bpSrc bpTgt S hSlen shift hshift
      p pc pe hcharge hpc hpe hp_eq

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
#print axioms symPower_mul_left_mem_succ
#print axioms concreteWEndpointSpan_le_endpointAugmentedConcreteW
#print axioms endpointAugmentedConcreteW_endpointSpanGeneratorChargedShiftClosure_of_oneStepChargeCompatible
#print axioms endpointAugmentedConcreteW_endpointSpanProfileChargedShiftClosure_of_generatorClosure
#print axioms endpointAugmentedConcreteW_chargedShiftClosure_on_canonical_endpointSpan_split_source
#print axioms endpointAugmentedConcreteW_chargedShiftClosure_of_canonical_endpointSpanProfile_and_split

end PallLean.Paper93.Paper283
