import PallLean.Paper93.DeepMath.PathC.PiPlusShiftAugmentedLeibnizExpansion

/-!
# Paper-faithful Route W surface

The paper distinguishes the global God-Move **gauge** (`Π+ = A`, the shared
compiled coordinate system) from the actual codimension-collapse/normal-form map
`Π_Φ`, which is block-local and instance/window specific.  In particular, the
Route-W composition should not be represented by one arbitrary global
`project : V →ₗ V` that is expected to perform Boolean one-coordinate collapse
and all adjacency/transition endpoint transports simultaneously.

This file records the paper-faithful Lean interface: the global gauge is fixed by
the transformed Cook--Levin factor family, while the quotient/normal-form action
is row-indexed.  A row receives its own block-local normal-form transport and its
own natural profile.  The old fixed-project socket is recovered only when a
single project/classifier is deliberately supplied.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open SymmetricPowerBound
open WithinProfileBound
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Paper-faithful row-indexed Route-W normal-form data.

For each generated row `mlProj (shift * g)`, the paper allows a block-local
normal-form/collapse determined by the concrete canonical window/row.  The map is
therefore indexed by `(h,S,shift,g)` rather than being one global linear map.
The assigned `profile` is the natural interface-anonymous profile of the
transported row. -/
structure RouteWRowNormalFormTransport {N L : Nat}
    (κ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType) where
  project :
    (h : ProfileHistogram) →
      List (Fin N) → MvPolynomial (Fin N) ℚ → MvPolynomial (Fin N) ℚ →
        MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ
  profile :
    ProfileHistogram →
      List (Fin N) → MvPolynomial (Fin N) ℚ → MvPolynomial (Fin N) ℚ →
        ProfileHistogram
  profile_admissible :
    ∀ (h : ProfileHistogram)
      (S : List (Fin N)) (_hS : S.length ≤ κ)
      (shift : MvPolynomial (Fin N) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
      (g : MvPolynomial (Fin N) ℚ),
        g ∈ boundedProfileClassifiedSet factors constraintType S h →
          ProfileAdmissible κ (profile h S shift g)

/-- The transported row determined by a paper-faithful row-indexed Route-W
normal-form structure. -/
noncomputable def routeWTransportedRow {N L : Nat} {κ : Nat}
    {factors : Fin L → MvPolynomial (Fin N) ℚ}
    {constraintType : Fin L → ConstraintType}
    (transport : RouteWRowNormalFormTransport κ factors constraintType)
    (h : ProfileHistogram) (S : List (Fin N))
    (shift g : MvPolynomial (Fin N) ℚ) : MvPolynomial (Fin N) ℚ :=
  transport.project h S shift g (mlProj (shift * g))

/-- Paper-faithful natural-profile generator containment: each row is first sent
through its own block-local normal-form transport, then placed in the
shift-augmented profile space for its transported natural profile. -/
def RouteWRowIndexedNaturallyProfiledGeneratorContainment {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (transport : RouteWRowNormalFormTransport κ factors constraintType) : Prop :=
  ∀ (h : ProfileHistogram)
    (S : List (Fin N)) (_hS : S.length ≤ κ)
    (shift : MvPolynomial (Fin N) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (g : MvPolynomial (Fin N) ℚ),
      g ∈ boundedProfileClassifiedSet factors constraintType S h →
        routeWTransportedRow transport h S shift g ∈
          profileSubspace (transport.profile h S shift g)
            (fun σ : ConstraintType =>
              shiftAugmentedInterfaceSpace_compiledBasis B κ ℓ σ)

/-- Finite same-profile slot-expansion form of the paper-faithful row-indexed
Route-W generator containment. -/
def RouteWRowIndexedGeneratorExpansion {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (transport : RouteWRowNormalFormTransport κ factors constraintType) : Prop :=
  ∀ (h : ProfileHistogram)
    (S : List (Fin N)) (_hS : S.length ≤ κ)
    (shift : MvPolynomial (Fin N) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (g : MvPolynomial (Fin N) ℚ),
      g ∈ boundedProfileClassifiedSet factors constraintType S h →
        ShiftAugmentedProfileSlotExpansion B κ ℓ
          (transport.profile h S shift g)
          (routeWTransportedRow transport h S shift g)

/-- Slot expansions discharge the row-indexed paper-faithful Route-W containment.
This is the analogue of the old fixed-project closeout, but with the project and
natural profile indexed by the actual row/window. -/
theorem routeWRowIndexedNaturallyProfiledGeneratorContainment_of_expansion
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (transport : RouteWRowNormalFormTransport κ factors constraintType)
    (hexp : RouteWRowIndexedGeneratorExpansion
      B κ ℓ factors constraintType transport) :
    RouteWRowIndexedNaturallyProfiledGeneratorContainment
      B κ ℓ factors constraintType transport := by
  intro h S hS shift hshift g hg
  exact shiftAugmentedProfileSlotExpansion_mem_profileSubspace
    B κ ℓ (transport.profile h S shift g)
    (routeWTransportedRow transport h S shift g)
    (hexp h S hS shift hshift g hg)

/-- A fixed global `project`/`classifier` is a special case of the row-indexed
paper-faithful interface.  This theorem preserves compatibility with the old
API while making explicit that the fixed-project model is an extra
specialization, not the primitive Route-W object. -/
noncomputable def fixedProjectRouteWTransport {N L : Nat}
    (κ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (classifier : ProjectedPostRowProfileClassifier κ factors constraintType) :
    RouteWRowNormalFormTransport κ factors constraintType where
  project := fun _h _S _shift _g => project
  profile := classifier.profile
  profile_admissible := classifier.profile_admissible

@[simp] theorem fixedProjectRouteWTransport_project_apply {N L : Nat}
    (κ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (classifier : ProjectedPostRowProfileClassifier κ factors constraintType)
    (h : ProfileHistogram) (S : List (Fin N))
    (shift g row : MvPolynomial (Fin N) ℚ) :
    (fixedProjectRouteWTransport κ factors constraintType project classifier).project
        h S shift g row = project row := rfl

@[simp] theorem fixedProjectRouteWTransport_profile_apply {N L : Nat}
    (κ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (classifier : ProjectedPostRowProfileClassifier κ factors constraintType)
    (h : ProfileHistogram) (S : List (Fin N))
    (shift g : MvPolynomial (Fin N) ℚ) :
    (fixedProjectRouteWTransport κ factors constraintType project classifier).profile
        h S shift g = classifier.profile h S shift g := rfl

/-- Paper-scale abbreviation for Cook--Levin in the global `Π+ = A` gauge, with
row-indexed Route-W normal-form transport. -/
abbrev CookLevinRouteWRowNormalFormTransport_paperScale
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ : Nat) :=
  RouteWRowNormalFormTransport κ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)

/-- Paper-scale row-indexed generator expansion socket.  This is the replacement
for treating Route W as one global arbitrary projection. -/
abbrev CookLevinRouteWRowIndexedGeneratorExpansion_paperScale
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (transport : CookLevinRouteWRowNormalFormTransport_paperScale M htb hns κ) : Prop :=
  RouteWRowIndexedGeneratorExpansion
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)
    transport

/-- Paper-scale row-indexed generator containment. -/
abbrev CookLevinRouteWRowIndexedNaturallyProfiledGeneratorContainment_paperScale
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (transport : CookLevinRouteWRowNormalFormTransport_paperScale M htb hns κ) : Prop :=
  RouteWRowIndexedNaturallyProfiledGeneratorContainment
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)
    transport

/-- Paper-scale closeout for the row-indexed Route-W surface. -/
theorem cookLevinRouteWRowIndexedNaturallyProfiledGeneratorContainment_paperScale_of_expansion
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (transport : CookLevinRouteWRowNormalFormTransport_paperScale M htb hns κ)
    (hexp : CookLevinRouteWRowIndexedGeneratorExpansion_paperScale
      M htb hns κ ℓ transport) :
    CookLevinRouteWRowIndexedNaturallyProfiledGeneratorContainment_paperScale
      M htb hns κ ℓ transport :=
  routeWRowIndexedNaturallyProfiledGeneratorContainment_of_expansion
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)
    transport hexp

/-! ## Axiom audit anchors -/

#print axioms routeWRowIndexedNaturallyProfiledGeneratorContainment_of_expansion
#print axioms fixedProjectRouteWTransport
#print axioms cookLevinRouteWRowIndexedNaturallyProfiledGeneratorContainment_paperScale_of_expansion

end PallLean.Paper93.DeepMath.PathC
