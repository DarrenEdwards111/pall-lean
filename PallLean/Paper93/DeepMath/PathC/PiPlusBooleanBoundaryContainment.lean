import PallLean.Paper93.DeepMath.PathC.PiPlusBoundaryProject
import PallLean.Paper93.DeepMath.PathC.PiPlusCompiledCoordinateTransport

/-!
# Route W: Boolean-boundary profile containment seam

This file keeps the Route-W project at the coefficient level.  The projection is
Boolean normal-form reduction (`zeroProfileBooleanNormalize`), while `Π+` remains
transport and `can(·)` remains an upstream window-index normalisation.

The theorems here reduce `ProjectedPostSpanProfileContainment` to the exact
coefficient-level generator statement needed next: every Boolean-normalized
post-row generator of a fixed profile lies in the compiled-basis profile
subspace.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93
open PallLean.SymTensorPowerDim
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Generator-level form of Route-W profile containment.  Since
`projectedAllBoundedProfilePostSpan` is a span of projected generators, it is
enough to prove each projected generator lies in the appropriate Lemma-31
profile subspace. -/
def ProjectedPostSpanGeneratorContainment {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ) : Prop :=
  ∀ (h : ProfileHistogram), ProfileAdmissible κ h →
    ∀ (S : List (Fin N)), S.length ≤ κ →
    ∀ (shift : MvPolynomial (Fin N) ℚ), shift.vars ⊆ S.toFinset →
    ∀ (g : MvPolynomial (Fin N) ℚ),
      g ∈ boundedProfileClassifiedSet factors constraintType S h →
        project (mlProj (shift * g)) ∈
          profileSubspace h
            (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)

/-- Span closeout: generator-level containment implies the Route-W
`ProjectedPostSpanProfileContainment` socket. -/
theorem projectedPostSpanProfileContainment_of_generatorContainment {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (hgen : ProjectedPostSpanGeneratorContainment
      B κ ℓ factors constraintType project) :
    ProjectedPostSpanProfileContainment B κ ℓ factors constraintType project := by
  intro h hadm
  apply Submodule.span_le.mpr
  intro q hq
  simp only [Set.mem_iUnion, Set.mem_image] at hq
  rcases hq with ⟨S, hS, shift, hshift, g, hg, rfl⟩
  exact hgen h hadm S hS shift hshift g hg


/-- Boundary quotient certificate constructor for the one-coordinate Booleanity
project, conditional on the two real Route-W obligations: idempotence of the
normalized collapse project and generator/profile containment after projection.
This wires the new project into `BoundaryQuotientCompressionCertificate` without
claiming the unprojected row-space rank is recovered from the quotient rank. -/
noncomputable def booleanityOneCoordinateBoundaryQuotientCertificate_of_generatorContainment
    {L : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (factors : Fin L → SATDeciderGaugeSpace M n hn2 htb hns)
    (constraintType : Fin L → ConstraintType)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hidem : BooleanityOneCoordinateBoundaryProjectIdempotent
      M n hn2 htb hns D v)
    (hgen : ProjectedPostSpanGeneratorContainment B κ ℓ factors constraintType
      (booleanityOneCoordinateBoundaryProject M n hn2 htb hns D v)) :
    BoundaryQuotientCompressionCertificate B κ ℓ factors constraintType where
  project := booleanityOneCoordinateBoundaryProject M n hn2 htb hns D v
  project_idempotent :=
    booleanityOneCoordinateBoundaryProject_idempotent_of_obligation
      M n hn2 htb hns D v hidem
  profile_containment :=
    projectedPostSpanProfileContainment_of_generatorContainment
      B κ ℓ factors constraintType
      (booleanityOneCoordinateBoundaryProject M n hn2 htb hns D v) hgen

/-- Boolean-normalized generator containment is the concrete coefficient-level
Route-W obligation for the Boolean boundary quotient project. -/
def BooleanBoundaryPostSpanGeneratorContainment {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType) : Prop :=
  ∀ (h : ProfileHistogram), ProfileAdmissible κ h →
    ∀ (S : List (Fin N)), S.length ≤ κ →
    ∀ (shift : MvPolynomial (Fin N) ℚ), shift.vars ⊆ S.toFinset →
    ∀ (g : MvPolynomial (Fin N) ℚ),
      g ∈ boundedProfileClassifiedSet factors constraintType S h →
        zeroProfileBooleanNormalize (mlProj (shift * g)) ∈
          profileSubspace h
            (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)

/-- Booleanity-only profile with `k` Booleanity slots and zero mass in every
other constraint type. -/
def booleanityOnlyProfile (k : Nat) : ProfileHistogram :=
  fun σ : ConstraintType => if σ = ConstraintType.booleanity then k else 0

@[simp] theorem booleanityOnlyProfile_booleanity (k : Nat) :
    booleanityOnlyProfile k ConstraintType.booleanity = k := by
  simp [booleanityOnlyProfile]

@[simp] theorem booleanityOnlyProfile_of_ne_booleanity {k : Nat}
    {σ : ConstraintType} (hσ : σ ≠ ConstraintType.booleanity) :
    booleanityOnlyProfile k σ = 0 := by
  simp [booleanityOnlyProfile, hσ]

/-- A Booleanity-only slot expansion: after Boolean normalization, the row is a
finite sum of products of `k` Booleanity interface slots.  This is the first
constraint-type target for Route W; the theorem below converts it into the full
all-interface slot-expansion shape consumed by `booleanBoundary...`. -/
def BooleanityFactorSlotExpansion {N : Nat}
    (B : BlockPartition N) (κ ℓ k : Nat)
    (row : MvPolynomial (Fin N) ℚ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι),
  ∃ (coeff : ι → ℚ),
  ∃ (bslot : ι → Fin k → MvPolynomial (Fin N) ℚ),
    (∀ t j, bslot t j ∈
      interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity) ∧
    row = ∑ t : ι, coeff t • (∏ j : Fin k, bslot t j)

/-- Extract an explicit finite Booleanity slot expansion from membership in the
`k`-fold symmetric power of the Booleanity interface space.  This is the pure
coefficient-level algebraic core of the Booleanity Route-W step. -/
theorem booleanityFactorSlotExpansion_of_mem_symPower {N : Nat}
    (B : BlockPartition N) (κ ℓ k : Nat)
    (row : MvPolynomial (Fin N) ℚ)
    (hrow : row ∈ symPower ℚ k
      (interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity)) :
    BooleanityFactorSlotExpansion B κ ℓ k row := by
  classical
  unfold symPower at hrow
  rcases (Submodule.mem_span_iff_exists_finset_subset.mp hrow) with
    ⟨coeff0, t, ht_subset, _hcoeff_support, hsum⟩
  let ι : Type := {p : MvPolynomial (Fin N) ℚ // p ∈ t}
  haveI : Fintype ι := inferInstance
  have hslotWitness : ∀ p : ι,
      ∃ f : Fin k → MvPolynomial (Fin N) ℚ,
        (∀ j, f j ∈ interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity) ∧
        p.1 = ∏ j, f j := by
    intro p
    have hp_set : p.1 ∈ { q : MvPolynomial (Fin N) ℚ |
        ∃ f : Fin k → MvPolynomial (Fin N) ℚ,
          (∀ j, f j ∈ interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity) ∧
          q = ∏ j, f j } := ht_subset p.2
    rcases hp_set with ⟨f, hfmem, hpeq⟩
    exact ⟨f, hfmem, hpeq⟩
  choose bslot hbslot_mem hbslot_eq using hslotWitness
  refine ⟨ι, inferInstance, (fun p : ι => coeff0 p.1), bslot, hbslot_mem, ?_⟩
  calc
    row = ∑ p ∈ t, coeff0 p • p := hsum.symm
    _ = ∑ p : ι, coeff0 p.1 • p.1 := by
      simpa [ι] using
        (Finset.sum_subtype (s := t) (p := fun p : MvPolynomial (Fin N) ℚ => p ∈ t)
          (by intro p; rfl) (f := fun p => coeff0 p • p))
    _ = ∑ p : ι, coeff0 p.1 • (∏ j : Fin k, bslot p j) := by
      refine Finset.sum_congr rfl ?_
      intro p _
      rw [hbslot_eq p]

/-- Booleanity slot expansion for a normalized projected Cook--Levin row once
the local Booleanity algebra has placed that row in the Booleanity symmetric
power.  The `hg` classified-product hypothesis is retained in the statement so
call sites can pass the exact Route-W generator data unchanged; the algebraic
payload is the final `hrow` membership. -/
theorem booleanityFactorSlotExpansion {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (h : ProfileHistogram)
    (S : List (Fin N)) (shift : MvPolynomial (Fin N) ℚ)
    (g : MvPolynomial (Fin N) ℚ)
    (_hg : g ∈ boundedProfileClassifiedSet factors constraintType S h)
    (hrow : zeroProfileBooleanNormalize (mlProj (shift * g)) ∈
      symPower ℚ (h ConstraintType.booleanity)
        (interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity)) :
    BooleanityFactorSlotExpansion B κ ℓ (h ConstraintType.booleanity)
      (zeroProfileBooleanNormalize (mlProj (shift * g))) := by
  exact booleanityFactorSlotExpansion_of_mem_symPower B κ ℓ
    (h ConstraintType.booleanity)
    (zeroProfileBooleanNormalize (mlProj (shift * g))) hrow

/-- Profile-classified Booleanity symmetric-power bridge.  This is the precise
Route-W wiring socket after the local k-fold product result: every generator in
`boundedProfileClassifiedSet` has its Boolean-normalized projected post-row in
the `h.booleanity`-fold symmetric power of the compiled-basis Booleanity
interface space. -/
def BooleanityProfileClassifiedSymPowerBridge {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType) : Prop :=
  ∀ (h : ProfileHistogram)
    (S : List (Fin N)) (shift : MvPolynomial (Fin N) ℚ)
    (g : MvPolynomial (Fin N) ℚ),
      g ∈ boundedProfileClassifiedSet factors constraintType S h →
        zeroProfileBooleanNormalize (mlProj (shift * g)) ∈
          symPower ℚ (h ConstraintType.booleanity)
            (interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity)

/-- The profile-classified symmetric-power bridge closes the Booleanity slot
expansion socket for every classified generator. -/
theorem booleanityFactorSlotExpansion_of_profileClassifiedBridge {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (hbridge : BooleanityProfileClassifiedSymPowerBridge B κ ℓ factors constraintType)
    (h : ProfileHistogram)
    (S : List (Fin N)) (shift : MvPolynomial (Fin N) ℚ)
    (g : MvPolynomial (Fin N) ℚ)
    (hg : g ∈ boundedProfileClassifiedSet factors constraintType S h) :
    BooleanityFactorSlotExpansion B κ ℓ (h ConstraintType.booleanity)
      (zeroProfileBooleanNormalize (mlProj (shift * g))) := by
  exact booleanityFactorSlotExpansion B κ ℓ factors constraintType h S shift g hg
    (hbridge h S shift g hg)

/-- Booleanity-only specialization of the profile-classified bridge.  For
`booleanityOnlyProfile k`, the bridge gives exactly a `k`-slot Booleanity
expansion. -/
theorem booleanityOnlyFactorSlotExpansion_of_profileClassifiedBridge {N L : Nat}
    (B : BlockPartition N) (κ ℓ k : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (hbridge : BooleanityProfileClassifiedSymPowerBridge B κ ℓ factors constraintType)
    (S : List (Fin N)) (shift : MvPolynomial (Fin N) ℚ)
    (g : MvPolynomial (Fin N) ℚ)
    (hg : g ∈ boundedProfileClassifiedSet factors constraintType S (booleanityOnlyProfile k)) :
    BooleanityFactorSlotExpansion B κ ℓ k
      (zeroProfileBooleanNormalize (mlProj (shift * g))) := by
  simpa using
    booleanityFactorSlotExpansion_of_profileClassifiedBridge
      B κ ℓ factors constraintType hbridge (booleanityOnlyProfile k) S shift g hg

/-- A Booleanity-only slot expansion is a full profile slot expansion for the
profile `booleanityOnlyProfile k`.  The non-Booleanity interfaces contribute
empty products, so no adjacency/transition slots are required. -/
theorem fullSlotExpansion_of_booleanityFactorSlotExpansion {N : Nat}
    (B : BlockPartition N) (κ ℓ k : Nat)
    (row : MvPolynomial (Fin N) ℚ)
    (hbool : BooleanityFactorSlotExpansion B κ ℓ k row) :
    ∃ (ι : Type) (_ : Fintype ι),
    ∃ (coeff : ι → ℚ),
    ∃ (slot : ι → ∀ σ : ConstraintType,
        Fin (booleanityOnlyProfile k σ) → MvPolynomial (Fin N) ℚ),
      (∀ t σ j, slot t σ j ∈ interfaceSpace_compiledBasis B κ ℓ σ) ∧
      row = ∑ t : ι, coeff t •
        (∏ σ : ConstraintType,
          ∏ j : Fin (booleanityOnlyProfile k σ), slot t σ j) := by
  classical
  rcases hbool with ⟨ι, hι, coeff, bslot, hbslot, hrow⟩
  letI : Fintype ι := hι
  let slot : ι → ∀ σ : ConstraintType,
      Fin (booleanityOnlyProfile k σ) → MvPolynomial (Fin N) ℚ :=
    fun t σ j => by
      by_cases hσ : σ = ConstraintType.booleanity
      · subst hσ
        exact bslot t j
      · have hz : booleanityOnlyProfile k σ = 0 :=
          booleanityOnlyProfile_of_ne_booleanity (k := k) hσ
        exact False.elim (Fin.elim0 (hz ▸ j))
  refine ⟨ι, hι, coeff, slot, ?_, ?_⟩
  · intro t σ j
    by_cases hσ : σ = ConstraintType.booleanity
    · subst hσ
      exact hbslot t j
    · have hz : booleanityOnlyProfile k σ = 0 :=
        booleanityOnlyProfile_of_ne_booleanity (k := k) hσ
      exact False.elim (Fin.elim0 (hz ▸ j))
  · rw [hrow]
    refine Finset.sum_congr rfl ?_
    intro t _
    congr 1
    rw [show (∏ σ : ConstraintType,
          ∏ j : Fin (booleanityOnlyProfile k σ), slot t σ j) =
        ∏ j : Fin (booleanityOnlyProfile k ConstraintType.booleanity),
          slot t ConstraintType.booleanity j by
      rw [Fintype.prod_eq_single ConstraintType.booleanity]
      · intro σ hσ
        have hz : booleanityOnlyProfile k σ = 0 :=
          booleanityOnlyProfile_of_ne_booleanity (k := k) hσ
        haveI : IsEmpty (Fin (booleanityOnlyProfile k σ)) := by
          rw [hz]
          infer_instance
        simp]
    rfl

/-- Booleanity-only slot expansions feed the generic Route-W finite-slot
expansion socket.  This is the first-type composition point: once local
Cook--Levin Booleanity algebra proves `BooleanityFactorSlotExpansion` for a row,
this theorem supplies exactly the all-interface `hexpand` witness expected by
`booleanBoundaryPostSpanGeneratorContainment_of_slotExpansion`. -/
theorem genericSlotWitness_of_booleanityFactorSlotExpansion {N : Nat}
    (B : BlockPartition N) (κ ℓ k : Nat)
    (row : MvPolynomial (Fin N) ℚ)
    (hbool : BooleanityFactorSlotExpansion B κ ℓ k row) :
    ∃ (ι : Type) (_ : Fintype ι),
    ∃ (coeff : ι → ℚ),
    ∃ (slot : ι → ∀ σ : ConstraintType,
        Fin (booleanityOnlyProfile k σ) → MvPolynomial (Fin N) ℚ),
      (∀ t σ j, slot t σ j ∈ interfaceSpace_compiledBasis B κ ℓ σ) ∧
      row = ∑ t : ι, coeff t •
        (∏ σ : ConstraintType,
          ∏ j : Fin (booleanityOnlyProfile k σ), slot t σ j) :=
  fullSlotExpansion_of_booleanityFactorSlotExpansion B κ ℓ k row hbool

/-- Finite same-profile slot expansions are enough to discharge the concrete
Boolean-boundary generator containment obligation.  This is the coefficient-level
Property-2 target in its most usable form: after Boolean normalization, each
post-row generator must expand as a finite sum of products whose typed slots lie
in the compiled-basis interface spaces.  Lemma 31's membership constructor then
places the row in the profile subspace. -/
theorem booleanBoundaryPostSpanGeneratorContainment_of_slotExpansion
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (hexpand : ∀ (h : ProfileHistogram), ProfileAdmissible κ h →
      ∀ (S : List (Fin N)), S.length ≤ κ →
      ∀ (shift : MvPolynomial (Fin N) ℚ), shift.vars ⊆ S.toFinset →
      ∀ (g : MvPolynomial (Fin N) ℚ),
        g ∈ boundedProfileClassifiedSet factors constraintType S h →
          ∃ (ι : Type) (_ : Fintype ι),
          ∃ (coeff : ι → ℚ),
          ∃ (slot : ι → ∀ σ : ConstraintType,
              Fin (h σ) → MvPolynomial (Fin N) ℚ),
            (∀ t σ j, slot t σ j ∈
              interfaceSpace_compiledBasis B κ ℓ σ) ∧
            zeroProfileBooleanNormalize (mlProj (shift * g)) =
              ∑ t : ι, coeff t •
                (∏ σ : ConstraintType, ∏ j : Fin (h σ), slot t σ j)) :
    BooleanBoundaryPostSpanGeneratorContainment
      B κ ℓ factors constraintType := by
  classical
  intro h hadm S hS shift hshift g hg
  rcases hexpand h hadm S hS shift hshift g hg with
    ⟨ι, hι, coeff, slot, hslot, hrow⟩
  letI : Fintype ι := hι
  rw [hrow]
  exact profileSlotExpansion_mem_profileSubspace h
    (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)
    coeff slot hslot

/-- Boolean-normalized generator containment closes the Route-W containment
socket for `booleanBoundaryQuotientProject`. -/
theorem booleanBoundary_projectedPostSpanProfileContainment_of_generatorContainment
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (hgen : BooleanBoundaryPostSpanGeneratorContainment
      B κ ℓ factors constraintType) :
    ProjectedPostSpanProfileContainment
      B κ ℓ factors constraintType (booleanBoundaryQuotientProject N) := by
  refine projectedPostSpanProfileContainment_of_generatorContainment
    B κ ℓ factors constraintType (booleanBoundaryQuotientProject N) ?_
  intro h hadm S hS shift hshift g hg
  simpa [booleanBoundaryQuotientProject_apply] using
    hgen h hadm S hS shift hshift g hg

/-- Bundled certificate builder for the Boolean coefficient-level Route-W
quotient.  The only remaining mathematical input is the generator containment
statement above. -/
noncomputable def booleanBoundaryQuotientCompressionCertificate_of_generatorContainment
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (hgen : BooleanBoundaryPostSpanGeneratorContainment
      B κ ℓ factors constraintType) :
    BoundaryQuotientCompressionCertificate B κ ℓ factors constraintType where
  project := booleanBoundaryQuotientProject N
  project_idempotent := booleanBoundaryQuotientProject_idempotent N
  profile_containment :=
    booleanBoundary_projectedPostSpanProfileContainment_of_generatorContainment
      B κ ℓ factors constraintType hgen

/-! ## Paper-scale Cook--Levin Route-W obligation

This is the concrete next target: prove Boolean-normalized generator containment
for the already transformed `Π+ᵦ` Cook--Levin factor family.  It is stated as a
named proposition rather than assumed.
-/

def CookLevinBooleanBoundaryPostSpanGeneratorContainment_paperScale
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat) : Prop :=
  BooleanBoundaryPostSpanGeneratorContainment
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)

/-- Paper-scale Cook--Levin specialization of the same finite slot-expansion
closeout.  This is the direct next target for Route W: construct `hexpand` for
Boolean-normalized Cook--Levin transformed constraint generators. -/
theorem cookLevinBooleanBoundaryPostSpanGeneratorContainment_paperScale_of_slotExpansion
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (hexpand : ∀ (h : ProfileHistogram), ProfileAdmissible κ h →
      ∀ (S : List (Fin (cook_levin_compilation M (2 ^ 804)
        paperScale_ge_two htb hns).numVars)), S.length ≤ κ →
      ∀ (shift : MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804)
        paperScale_ge_two htb hns).numVars) ℚ), shift.vars ⊆ S.toFinset →
      ∀ (g : MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804)
        paperScale_ge_two htb hns).numVars) ℚ),
        g ∈ boundedProfileClassifiedSet
          (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns).length =>
            (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns)[i.val])
          (cookLevinFactorConstraintType_paperScale M htb hns) S h →
          ∃ (ι : Type) (_ : Fintype ι),
          ∃ (coeff : ι → ℚ),
          ∃ (slot : ι → ∀ σ : ConstraintType,
              Fin (h σ) → MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804)
                paperScale_ge_two htb hns).numVars) ℚ),
            (∀ t σ j, slot t σ j ∈
              interfaceSpace_compiledBasis
                (cook_levin_compilation M (2 ^ 804)
                  paperScale_ge_two htb hns).partition κ ℓ σ) ∧
            zeroProfileBooleanNormalize (mlProj (shift * g)) =
              ∑ t : ι, coeff t •
                (∏ σ : ConstraintType, ∏ j : Fin (h σ), slot t σ j)) :
    CookLevinBooleanBoundaryPostSpanGeneratorContainment_paperScale
      M htb hns κ ℓ := by
  exact booleanBoundaryPostSpanGeneratorContainment_of_slotExpansion
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)
    hexpand

/-- Paper-scale certificate builder for Cook--Levin `Π+ᵦ` factors, conditional
only on the coefficient-level generator containment obligation. -/
noncomputable def cookLevinBooleanBoundaryQuotientCompressionCertificate_paperScale_of_generatorContainment
    (M : TuringMachine.DTM) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ 2 ^ 804) (κ ℓ : Nat)
    (hgen : CookLevinBooleanBoundaryPostSpanGeneratorContainment_paperScale
      M htb hns κ ℓ) :
    BoundaryQuotientCompressionCertificate
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      κ ℓ
      (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).length =>
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale M htb hns)[i.val])
      (cookLevinFactorConstraintType_paperScale M htb hns) :=
  booleanBoundaryQuotientCompressionCertificate_of_generatorContainment
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ
    (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length =>
      (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale M htb hns)[i.val])
    (cookLevinFactorConstraintType_paperScale M htb hns)
    hgen

/-! ## Axiom audit anchors -/

#print axioms booleanityFactorSlotExpansion_of_mem_symPower
#print axioms booleanityFactorSlotExpansion
#print axioms booleanityOneCoordinateBoundaryQuotientCertificate_of_generatorContainment
#print axioms BooleanityProfileClassifiedSymPowerBridge
#print axioms booleanityFactorSlotExpansion_of_profileClassifiedBridge
#print axioms booleanityOnlyFactorSlotExpansion_of_profileClassifiedBridge
#print axioms fullSlotExpansion_of_booleanityFactorSlotExpansion
#print axioms genericSlotWitness_of_booleanityFactorSlotExpansion
#print axioms booleanBoundaryPostSpanGeneratorContainment_of_slotExpansion
#print axioms cookLevinBooleanBoundaryPostSpanGeneratorContainment_paperScale_of_slotExpansion
#print axioms projectedPostSpanProfileContainment_of_generatorContainment
#print axioms booleanBoundary_projectedPostSpanProfileContainment_of_generatorContainment
#print axioms booleanBoundaryQuotientCompressionCertificate_of_generatorContainment
#print axioms cookLevinBooleanBoundaryQuotientCompressionCertificate_paperScale_of_generatorContainment

end PallLean.Paper93.DeepMath.PathC
