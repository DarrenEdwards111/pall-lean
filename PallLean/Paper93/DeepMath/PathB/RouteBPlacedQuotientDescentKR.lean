import PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction
import PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiSingletonQuotientFinal

/-!
# Route B placed quotient descent exposure

This file is the paper-faithful replacement for the broken atom-trace/global
chart target.  The §9.3 object is not an unplaced `X₀/X₁` chart containing the
full untouched Cook--Levin product; it is a placed local-interface expansion,
followed by quotient/descent to the interface-anonymous profile subspace
`⊗_σ Sym^{h σ}(W_σ)`.

The adapters below expose that exact surface at Step 247 scale and route it
through the already checked Paper283 placed-local quotient machinery.
-/

set_option exponentiation.threshold 1024
set_option maxHeartbeats 800000

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open SymmetricPowerBound
open WithinProfileBound
open scoped BigOperators

/-- A one-block dummy partition for fixed local Cook--Levin interface templates.
The canonical interface polynomials ignore the partition parameter. -/
def routeBLocalInterfaceBlockPartition : SPDP.BlockPartition maxConstraintArity where
  numBlocks := 1
  assign := fun _ => 0

/-- The local template corresponding to a canonical interface slot. -/
noncomputable def routeBLocalTemplateOfCanonicalSlot
    (σ : ConstraintType) (j : Fin d₀) :
    MvPolynomial (Fin maxConstraintArity) ℚ :=
  canonicalInterfacePolynomial routeBLocalInterfaceBlockPartition 0 0 σ j

/-- Every canonical slot template lands in the local-coordinate Cook--Levin
interface space.  This is deliberately stated at the subspace level rather than
as literal finite-family membership: the canonical normal form includes zero
slots for dormant/unused positions, while the nonzero local template family need
not list `0` as a generator. -/
theorem routeBLocalTemplateOfCanonicalSlot_mem_localInterfaceSpace
    (σ : ConstraintType) (j : Fin d₀) :
    routeBLocalTemplateOfCanonicalSlot σ j ∈
      cookLevinCanonicalLocalInterfaceSpace σ := by
  classical
  fin_cases σ <;> fin_cases j
  all_goals first
    | exact Submodule.zero_mem _
    | (unfold routeBLocalTemplateOfCanonicalSlot cookLevinCanonicalLocalInterfaceSpace
       apply Submodule.subset_span
       simp [canonicalInterfacePolynomial, cookLevinCanonicalInterfaceFamily,
         canonicalLocalX, canonicalLocalX1, canonicalLocalBoolFactor,
         SymmetricPower.boolFactor, cookLevinLocalCoord0, cookLevinLocalCoord1,
         maxConstraintArity])

/-- Embed the fixed local Cook--Levin arity into an ambient coordinate set with
at least two coordinates.  Coordinates `0` and `1` are preserved; all higher
local coordinates are harmlessly sent to `0` because the Route-B canonical
interface templates only use the first two local coordinates. -/
noncomputable def routeBLocalAmbientCoord (N : ℕ) (hN2 : 2 ≤ N) :
    Fin maxConstraintArity → Fin N :=
  fun k =>
    if h0 : k.1 = 0 then ⟨0, by omega⟩
    else if h1 : k.1 = 1 then ⟨1, by omega⟩
    else ⟨0, by omega⟩

/-- Placing a local canonical slot and then applying a chart map agrees with
renaming the corresponding ambient canonical interface polynomial by that chart
map.  This is the concrete coordinate bridge needed to turn renamed-canonical
row expansions into placed local-interface expansions without a fixed global
chart collapse. -/
theorem routeB_rename_localTemplateOfCanonicalSlot_eq_rename_canonicalInterfacePolynomial
    {N : ℕ} (hN2 : 2 ≤ N) (f : Fin N → Fin N)
    (B : SPDP.BlockPartition N) (κ ℓ : ℕ) (σ : ConstraintType) (j : Fin d₀) :
    MvPolynomial.rename (fun k => f (routeBLocalAmbientCoord N hN2 k))
      (routeBLocalTemplateOfCanonicalSlot σ j) =
    MvPolynomial.rename f (canonicalInterfacePolynomial B κ ℓ σ j) := by
  have h0N : 0 < N := by omega
  have h1N : 1 < N := by omega
  fin_cases σ <;> fin_cases j <;>
    simp [routeBLocalTemplateOfCanonicalSlot, routeBLocalAmbientCoord,
      canonicalInterfacePolynomial, canonicalLocalX, canonicalLocalX1,
      canonicalLocalBoolFactor, SymmetricPower.boolFactor, maxConstraintArity,
      h0N, h1N]

/-- A renamed-canonical interface expansion is already a placed local-interface
expansion: each renamed canonical slot is represented by placing the fixed
local canonical template through the explicit row chart.  This is the concrete
bridge from the coefficient/local-chart Lemma-31 surface to the placed
Cook--Levin local-interface surface. -/
noncomputable def routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedLocalInterfaceExpansionData_of_renamedCanonicalInterfaceExpansionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hN2 : 2 ≤ n / 3)
    (D : PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowRenamedCanonicalInterfaceExpansionData
      M n hn2 htb hns) :
    PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedLocalInterfaceExpansionData
      M n hn2 htb hns where
  profileOfCanonicalWindow := D.profileOfCanonicalWindow
  rowExpansionIndex := D.rowExpansionIndex
  rowExpansionIndexFintype := D.rowExpansionIndexFintype
  rowExpansionCoeff := D.rowExpansionCoeff
  rowExpansionPlace := by
    intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ t σ j
    exact fun k =>
      D.rowExpansionChartMap ρ S' shift α hSlen hshiftDegree
        hshiftVars hadm hrow hρ t σ j (routeBLocalAmbientCoord (n / 3) hN2 k)
  rowExpansionLocalTemplate := by
    intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ t σ j
    exact routeBLocalTemplateOfCanonicalSlot σ
      (D.rowExpansionCanonicalSlot ρ S' shift α hSlen hshiftDegree
        hshiftVars hadm hrow hρ t σ j)
  rowExpansionLocalTemplate_mem := by
    intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ t σ j
    exact routeBLocalTemplateOfCanonicalSlot_mem_localInterfaceSpace σ
      (D.rowExpansionCanonicalSlot ρ S' shift α hSlen hshiftDegree
        hshiftVars hadm hrow hρ t σ j)
  canonicalSourceRow_eq_placedLocalInterfaceExpansion := by
    intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ
    have hslot :
        ∀ (t : D.rowExpansionIndex ρ S' shift α hSlen hshiftDegree
              hshiftVars hadm hrow hρ)
          (σ : ConstraintType) (j : Fin (ρ.val σ)),
          MvPolynomial.rename
              (fun k => D.rowExpansionChartMap ρ S' shift α hSlen hshiftDegree
                hshiftVars hadm hrow hρ t σ j (routeBLocalAmbientCoord (n / 3) hN2 k))
              (routeBLocalTemplateOfCanonicalSlot σ
                (D.rowExpansionCanonicalSlot ρ S' shift α hSlen hshiftDegree
                  hshiftVars hadm hrow hρ t σ j)) =
            MvPolynomial.rename
              (D.rowExpansionChartMap ρ S' shift α hSlen hshiftDegree
                hshiftVars hadm hrow hρ t σ j)
              (canonicalInterfacePolynomial D.sourcePartition
                (Nat.log 2 n) (Nat.log 2 n) σ
                (D.rowExpansionCanonicalSlot ρ S' shift α hSlen hshiftDegree
                  hshiftVars hadm hrow hρ t σ j)) := by
      intro t σ j
      exact routeB_rename_localTemplateOfCanonicalSlot_eq_rename_canonicalInterfacePolynomial
        hN2
        (D.rowExpansionChartMap ρ S' shift α hSlen hshiftDegree
          hshiftVars hadm hrow hρ t σ j)
        D.sourcePartition (Nat.log 2 n) (Nat.log 2 n) σ
        (D.rowExpansionCanonicalSlot ρ S' shift α hSlen hshiftDegree
          hshiftVars hadm hrow hρ t σ j)
    rw [D.canonicalSourceRow_eq_renamedCanonicalInterfaceExpansion
      ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ]
    simp [hslot]

/-- Renamed-canonical interface expansion supplies the full placed
quotient/descent datum by taking the selected `W_σ` to be the compiled-basis
interface space and using the coordinate bridge slotwise.  The product/profile
assembly is then exactly the already-checked slot-quotient descent adapter. -/
noncomputable def routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedLocalInterfaceQuotientDescentData_of_renamedCanonicalInterfaceExpansionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hN2 : 2 ≤ n / 3)
    (D : PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowRenamedCanonicalInterfaceExpansionData
      M n hn2 htb hns) :
    PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedLocalInterfaceQuotientDescentData
      M n hn2 htb hns :=
  PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedLocalInterfaceQuotientDescentData_of_slotQuotientData
    M n hn2 htb hns
    { placedExpansionData :=
        routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedLocalInterfaceExpansionData_of_renamedCanonicalInterfaceExpansionData
          M n hn2 htb hns hN2 D
      interfaceSpace := fun σ =>
        interfaceSpace_compiledBasis D.sourcePartition (Nat.log 2 n) (Nat.log 2 n) σ
      interfaceSpace_finite := by
        intro σ
        exact interfaceSpace_compiledBasis_finite D.sourcePartition
          (Nat.log 2 n) (Nat.log 2 n) σ
      interfaceSpace_finrank_le_three := by
        intro σ
        exact interfaceSpace_compiledBasis_finrank_le_three D.sourcePartition
          (Nat.log 2 n) (Nat.log 2 n) σ
      placedLocalSlot_descends_to_interfaceSpace := by
        intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ t σ j
        change
          MvPolynomial.rename
              (fun k => D.rowExpansionChartMap ρ S' shift α hSlen hshiftDegree
                hshiftVars hadm hrow hρ t σ j (routeBLocalAmbientCoord (n / 3) hN2 k))
              (routeBLocalTemplateOfCanonicalSlot σ
                (D.rowExpansionCanonicalSlot ρ S' shift α hSlen hshiftDegree
                  hshiftVars hadm hrow hρ t σ j)) ∈
            interfaceSpace_compiledBasis D.sourcePartition (Nat.log 2 n) (Nat.log 2 n) σ
        rw [routeB_rename_localTemplateOfCanonicalSlot_eq_rename_canonicalInterfacePolynomial]
        exact D.renamedCanonicalSlot_mem_compiledBasis
          ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ t σ j }

/-- Uniform placed-expansion data: the row has first been expanded into actual
placed local Cook--Levin interface templates.  This is strictly weaker than the
ambient selected-chart quotient descent below: it records the honest local
expansion before any quotient/rank soundness claim is made. -/
def Step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedLocalInterfaceExpansionData
        M n hn2 htb hns)

/-- Paper-faithful placed quotient/normal-form data.

This is the manuscript's correction to the false global-chart move.  A placed
Cook--Levin slot is not asserted to lie directly in one fixed raw `X₀/X₁` span.
Instead, one supplies a quotient/normal-form construction whose output is the
slotwise selected-chart quotient datum already consumed by `Paper283`.

Concretely, the intended mathematical content of `slotQuotientData` is:

* choose the selected interface-anonymous chart for each constraint type `σ`;
* quotient/normalise every concrete placement into that chart in the compiled
  blocked/diagonal coefficient basis;
* prove the normalised local template lies in the constant-dimensional `W_σ`;
* then let the existing symmetric-power/profile assembly handle products.

This wrapper deliberately replaces the old attempted proof target “all concrete
placements live in one raw chart” with the paper-faithful normal-form seam. -/
structure RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedInterfaceNormalFormData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  slotQuotientData :
    PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedLocalInterfaceSlotQuotientData
      M n hn2 htb hns

/-- Explicit equivariant quotient-map normal form.

This is the sharper, paper-faithful seam: rather than asking for slot descent
as a black box, it asks for a typewise quotient/normalisation map plus the
row-slot equivariance identity.  The Paper283 adapter then derives slot descent
without any global selected-chart equality. -/
structure RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedInterfaceEquivariantQuotientMapNormalFormData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  quotientMapData :
    PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedLocalInterfaceEquivariantQuotientMapData
      M n hn2 htb hns


/-- Slotwise normal-form data yields the explicit quotient-map normal form by
using the actual placement map as the quotient map on row slots.

This makes the quotient-map seam constructive relative to the already-proved
slot descent data: no ambient/global chart equality is introduced, and the
landing proof is exactly the row-local selected `W_σ` membership carried by the
slot datum. -/
noncomputable def routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedInterfaceEquivariantQuotientMapNormalFormData_of_interfaceNormalFormData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedInterfaceNormalFormData
      M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedInterfaceEquivariantQuotientMapNormalFormData
      M n hn2 htb hns where
  quotientMapData :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedLocalInterfaceEquivariantQuotientMapData_of_slotQuotientData
      M n hn2 htb hns D.slotQuotientData

/-- Equivariant quotient-map normal form instantiates the slotwise normal-form
data consumed by the existing placed quotient/descent chain. -/
noncomputable def routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedInterfaceNormalFormData_of_equivariantQuotientMapNormalFormData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedInterfaceEquivariantQuotientMapNormalFormData
      M n hn2 htb hns) :
    RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedInterfaceNormalFormData
      M n hn2 htb hns where
  slotQuotientData :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedLocalInterfaceSlotQuotientData_of_equivariantQuotientMapData
      M n hn2 htb hns D.quotientMapData

/-- Normal-form data instantiates the checked placed quotient/descent datum:
normalise individual placements first, then use the existing
symmetric/profile-subspace assembly. -/
noncomputable def routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedLocalInterfaceQuotientDescentData_of_interfaceNormalFormData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedInterfaceNormalFormData
      M n hn2 htb hns) :
    PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedLocalInterfaceQuotientDescentData
      M n hn2 htb hns :=
  PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedLocalInterfaceQuotientDescentData_of_slotQuotientData
    M n hn2 htb hns D.slotQuotientData

/-- Uniform paper-faithful normal-form data at Step 247 scale. -/
def Step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceNormalFormData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedInterfaceNormalFormData
        M n hn2 htb hns)

/-- Uniform equivariant quotient-map normal-form data at Step 247 scale. -/
def Step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceEquivariantQuotientMapNormalFormData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedInterfaceEquivariantQuotientMapNormalFormData
        M n hn2 htb hns)

/-- Uniform slotwise normal-form data also supplies the explicit equivariant
quotient-map surface. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceEquivariantQuotientMapNormalFormData_of_interfaceNormalFormData
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceNormalFormData) :
    Step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceEquivariantQuotientMapNormalFormData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedInterfaceEquivariantQuotientMapNormalFormData_of_interfaceNormalFormData
    M n hn2 htb hns D⟩

/-- Equivariant quotient-map normal forms supply the slotwise normal-form data. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceNormalFormData_of_equivariantQuotientMapNormalFormData
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceEquivariantQuotientMapNormalFormData) :
    Step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceNormalFormData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedInterfaceNormalFormData_of_equivariantQuotientMapNormalFormData
    M n hn2 htb hns D⟩

/-- Uniform paper-faithful placed quotient/descent data for strict `TΦ`.

This is the replacement theorem surface for the false unplaced background-chart
claim.  For every paper-scale Cook--Levin verifier, the row is first expanded in
actual placed local interface templates, and only then descended through the
compiled-coordinate quotient into the selected anonymous profile subspace. -/
def Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedLocalInterfaceQuotientDescentData
        M n hn2 htb hns)

/-- Uniform renamed-canonical interface expansion data at Step 247 scale.
This is the concrete coefficient/local-chart Lemma-31 source surface; the
adapter below turns it into the placed quotient/descent datum, not merely into a
no-decider wrapper. -/
def Step247UniformRouteBPaperFaithfulTPhiRenamedCanonicalInterfaceExpansionData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowRenamedCanonicalInterfaceExpansionData
        M n hn2 htb hns)

/-- Uniform shifted branch-atom compiled-basis profile data at Step 247 scale.

This is the term-local Lemma-31 source surface: every bounded Leibniz branch
atom selected by the witnessed normal-form word lies in the same selected
compiled-basis profile subspace.  The adapter below linearly assembles these
term-local memberships into the selected full source-row membership. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedBranchAtomCompiledBasisProfileData
        M n hn2 htb hns)

/-- Uniform shifted Leibniz-product compiled-basis profile data at Step 247
scale.

This is one level below the shifted branch-atom surface: it proves membership
for each actual bounded Leibniz distribution product after the selected shift
and `mlProj`.  The adapter below uses the already-proved `NFOfWord`
distribution-permutation theorem to rewrite each such product as its witnessed
shifted branch atom. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductCompiledBasisProfileData
        M n hn2 htb hns)

/-- Uniform shifted Leibniz-product local-algebra data at Step 247 scale.

This is the sharper local-algebra source seam: first place the unshifted
bounded Leibniz product in the selected compiled-basis profile subspace, then
prove the selected row shift plus `mlProj` preserves that same subspace. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductCompiledBasisLocalAlgebraData
        M n hn2 htb hns)

/-- Uniform shifted Leibniz-product interface-contribution data at Step 247
scale.

This is the next lower paper-faithful seam: for each selected profile, split the
unshifted bounded Leibniz product into one contribution per interface type, prove
each contribution is in the corresponding symmetric power of the compiled-basis
space, and keep the selected shift/`mlProj` closure obligation. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceContributionData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductInterfaceContributionData
        M n hn2 htb hns)

/-- Uniform shifted Leibniz-product interface-slot factorization data at Step
247 scale.

This is the literal local-slot Lemma-31 target: produce exactly `ρ.val σ`
compiled-basis local slots for every interface type `σ`, prove the unshifted
Leibniz product is their anonymous product, and prove selected shift/`mlProj`
closure. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductInterfaceSlotFactorizationData
        M n hn2 htb hns)

/-- Uniform shifted Leibniz-product slot-product row-shift data at Step 247
scale.

This is the row-specific replacement for the overly strong uniform operator
closure seam: each bounded Leibniz term has an exact compiled-basis slot product
and the selected row shift/`mlProj` is proved only for that term. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductInterfaceSlotProductRowShiftData
        M n hn2 htb hns)

/-- Row-specific slot-product shift data directly instantiates shifted Leibniz
product profile membership. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData_of_interfaceSlotProductRowShiftData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductCompiledBasisProfileData_of_interfaceSlotProductRowShiftData
    M n hn2 htb hns D⟩

/-- Uniform coherent exact slot-product plus shifted branch-atom data.  This is
 the paper-faithful non-uniform route to the row-specific shifted slot-product
 seam. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData
        M n hn2 htb hns)

/-- Coherent exact slot factorization plus shifted branch-atom membership closes
 the row-specific shifted slot-product seam at Step 247 scale. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_slotProductBranchAtomData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_slotProductBranchAtomData
    M n hn2 htb hns D⟩

/-- Uniform shifted Leibniz-product slot-product plus profile-uniform shift
closure data at Step 247 scale.

This is a sharper version of the slot seam: the product slot construction is
unchanged, but the shift/`mlProj` closure is stated uniformly for the selected
profile subspace rather than depending on the canonical profile-selector proof. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductUniformShiftClosureData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductInterfaceSlotProductUniformShiftClosureData
        M n hn2 htb hns)

/-- Uniform shift-closure slot-product data instantiates slot factorization. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData_of_slotProductUniformShiftClosureData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductUniformShiftClosureData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductInterfaceSlotFactorizationData_of_slotProductUniformShiftClosureData
    M n hn2 htb hns D⟩

/-- Interface-contribution data instantiates the local-algebra seam. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData_of_interfaceContributionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceContributionData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductCompiledBasisLocalAlgebraData_of_interfaceContributionData
    M n hn2 htb hns D⟩

/-- Slot factorization data instantiates interface-contribution data. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceContributionData_of_interfaceSlotFactorizationData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceContributionData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductInterfaceContributionData_of_interfaceSlotFactorizationData
    M n hn2 htb hns D⟩

/-- Slot factorization data therefore supplies the shifted Leibniz local-algebra
source seam. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData_of_interfaceSlotFactorizationData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData :=
  step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData_of_interfaceContributionData
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceContributionData_of_interfaceSlotFactorizationData
      hData)

/-- Local-algebra membership/closure gives shifted Leibniz-product membership. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData_of_localAlgebraData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductCompiledBasisProfileData_of_localAlgebraData
    M n hn2 htb hns D⟩

/-- Shifted Leibniz-product membership gives shifted branch-atom membership by
the witnessed `NFOfWord` permutation bridge. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData_of_shiftedLeibnizProductData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedBranchAtomCompiledBasisProfileData_of_shiftedLeibnizProductData
    M n hn2 htb hns D⟩

/-- Local-algebra data therefore supplies the shifted branch-atom source seam. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData_of_localAlgebraData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData :=
  step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData_of_shiftedLeibnizProductData
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData_of_localAlgebraData
      hData)

/-- Uniform direct profile-subspace row data at Step 247 scale.

This is the literal Lemma-31 containment surface: the selected canonical source
row lies in the concrete compiled-basis profile subspace
`profileSubspace ρ.val W`.  The adapter below unfolds that span into the
explicit finite coefficient/index/slot expansion. -/
def Step247UniformRouteBPaperFaithfulTPhiCompiledBasisProfileSubspaceRowData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedCompiledBasisProfileSubspaceRowData
        M n hn2 htb hns)

/-- Shifted branch-atom profile membership linearly assembles into the direct
selected source-row profile-subspace membership. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiCompiledBasisProfileSubspaceRowData_of_shiftedBranchAtomCompiledBasisProfileData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData) :
    Step247UniformRouteBPaperFaithfulTPhiCompiledBasisProfileSubspaceRowData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedCompiledBasisProfileSubspaceRowData_of_shiftedBranchAtomCompiledBasisProfileData
    M n hn2 htb hns D⟩

/-- Uniform row-interface-slot expansion data at Step 247 scale.

This is the literal selected-row Lemma-31 source surface: the row is already a
finite sum of products of concrete compiled-basis interface slots.  The adapter
below expands each slot into the canonical three-generator interface alphabet by
finite linear algebra and distributivity. -/
def Step247UniformRouteBPaperFaithfulTPhiInterfaceSlotExpansionData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowInterfaceSlotExpansionData
        M n hn2 htb hns)

/-- Direct profile-subspace row membership gives the explicit row-interface-slot
expansion by unfolding the defining span of `profileSubspace`. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiInterfaceSlotExpansionData_of_compiledBasisProfileSubspaceRowData
    (hData : Step247UniformRouteBPaperFaithfulTPhiCompiledBasisProfileSubspaceRowData) :
    Step247UniformRouteBPaperFaithfulTPhiInterfaceSlotExpansionData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedRowInterfaceSlotExpansionData_of_compiledBasisProfileSubspaceRowData
    M n hn2 htb hns D⟩

/-- Uniform canonical-interface expansion data at Step 247 scale.  This is now
the remaining source target after identity-chart transport into the
renamed-canonical surface and then placed quotient/descent. -/
def Step247UniformRouteBPaperFaithfulTPhiCanonicalInterfaceExpansionData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowCanonicalInterfaceExpansionData
        M n hn2 htb hns)

/-- Row-interface-slot expansion gives canonical-interface expansion by expanding
each concrete interface slot in the canonical compiled-basis generator family. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiCanonicalInterfaceExpansionData_of_interfaceSlotExpansionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiInterfaceSlotExpansionData) :
    Step247UniformRouteBPaperFaithfulTPhiCanonicalInterfaceExpansionData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedRowCanonicalInterfaceExpansionData_of_rowInterfaceSlotExpansionData
    M n hn2 htb hns D⟩

/-- Canonical-interface expansion gives renamed-canonical expansion by the
identity-chart adapter. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiRenamedCanonicalInterfaceExpansionData_of_canonicalInterfaceExpansionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiCanonicalInterfaceExpansionData) :
    Step247UniformRouteBPaperFaithfulTPhiRenamedCanonicalInterfaceExpansionData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedRowRenamedCanonicalInterfaceExpansionData_of_canonicalInterfaceExpansionData
    M n hn2 htb hns D⟩

/-- Canonical-interface expansion therefore supplies the actual placed
quotient/descent source datum. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData_of_canonicalInterfaceExpansionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiCanonicalInterfaceExpansionData) :
    Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  have hN2 : 2 ≤ n / 3 := by
    have hpow : 6 ≤ 2 ^ 804 := by
      calc
        6 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ 804 := by
          exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have h6 : 6 ≤ n := le_trans hpow hn
    omega
  exact ⟨routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedLocalInterfaceQuotientDescentData_of_renamedCanonicalInterfaceExpansionData
    M n hn2 htb hns hN2
    (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedRowRenamedCanonicalInterfaceExpansionData_of_canonicalInterfaceExpansionData
      M n hn2 htb hns D)⟩

/-- Paper-scale renamed-canonical expansion gives the actual placed
quotient/descent source datum.  The only arithmetic used here is that
`n ≥ 2^804` gives at least two first-of-block source coordinates after `/ 3`,
so the canonical local coordinates `0,1` can be embedded into the source arity. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData_of_renamedCanonicalInterfaceExpansionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiRenamedCanonicalInterfaceExpansionData) :
    Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  have hN2 : 2 ≤ n / 3 := by
    have hpow : 6 ≤ 2 ^ 804 := by
      calc
        6 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ 804 := by
          exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have h6 : 6 ≤ n := le_trans hpow hn
    omega
  exact ⟨routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedLocalInterfaceQuotientDescentData_of_renamedCanonicalInterfaceExpansionData
    M n hn2 htb hns hN2 D⟩

/-- Uniform bounded local-monoid/profile data at Step 247 scale.

This is the direct paper §9.3--§9.4 surface: the normal-form alphabet is an
explicit finite local-monoid quotient alphabet, not necessarily the raw
`ConstraintType` chart.  The data object contains Lemma 29's bounded profile
count and Lemma 31's selected within-profile row-span membership; the closeout
below only performs the already-checked global Route-B assembly. -/
def Step247UniformRouteBPaperFaithfulTPhiBoundedInterfaceAnonymousLocalMonoidProfileData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictBoundedInterfaceAnonymousLocalMonoidProfileData
        M n hn2 htb hns)

/-- Bounded interface-anonymous local-monoid/profile data gives the strict
ambient `TΦ` P-side bound.

This route is the paper-faithful refactor of Lemma 31: bounded normal forms
feed interface-anonymous profile data, then canonical-window local-monoid data,
and finally the existing profile/orbit matrix assembly.  No fixed global chart
or all-profile common span is introduced here. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiPSideBound_of_boundedInterfaceAnonymousLocalMonoidProfileData
    (hData : Step247UniformRouteBPaperFaithfulTPhiBoundedInterfaceAnonymousLocalMonoidProfileData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      SATDeciderGaugePSideBound M n hn2 htb hns
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge
          M n hn2 htb hns) := by
  intro M n hn hn2 htb hns
  let D := Classical.choice (hData M n hn hn2 htb hns)
  exact
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_pSideBound_of_strictCanonicalWindowLocalMonoidProfileData
      M n hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData_of_interfaceAnonymousLocalMonoidProfileData
        M n hn2 htb hns
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictInterfaceAnonymousLocalMonoidProfileData_of_boundedInterfaceAnonymousLocalMonoidProfileData
          M n hn2 htb hns D))

/-- The manuscript's quotient-normal-form theorem supplies the placed
quotient/descent datum used by the already-checked Route B chain. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData_of_interfaceNormalFormData
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceNormalFormData) :
    Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨routeBPaperFaithfulTPhi_strictSourceSelectedRowPlacedLocalInterfaceQuotientDescentData_of_interfaceNormalFormData
    M n hn2 htb hns D⟩

/-- Uniform placed quotient/descent data gives the strict source selected
profile-subspace datum.

This is the core replacement step: placed local interface expansion plus
slotwise/product quotient descent is assembled into the selected source
`V_h = profileSubspace h W` row membership, with no fixed global chart and no
all-profile/common-span shortcut. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiStrictSourceProfileSubspaceData_of_placedQuotientDescent
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceConstraintTypeProfileSubspaceData
        M n hn2 htb hns := by
  intro M n hn hn2 htb hns
  let D := Classical.choice (hData M n hn hn2 htb hns)
  exact
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceProfileSubspaceData_of_localCompiledProfileSubspaceRowData
      M n hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedLocalCompiledProfileSubspaceRowData_of_placedLocalInterfaceQuotientDescentData
        M n hn2 htb hns D)

/-- Uniform placed quotient/descent data also gives the ambient strict
`ConstraintType` profile-subspace datum by the checked first-of-block rename
transport.

This is the faithful `raw traces → placed slots → quotient/profile subspace →
strict TΦ row` route.  It replaces the previous atom-trace exact chart target,
which attempted to force exact placed factors into an unplaced canonical chart. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData_of_placedQuotientDescent
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
        M n hn2 htb hns := by
  intro M n hn hn2 htb hns
  exact
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData_of_sourceProfileSubspaceData
      M n hn2 htb hns
      (step247UniformRouteBPaperFaithfulTPhiStrictSourceProfileSubspaceData_of_placedQuotientDescent
        hData M n hn hn2 htb hns)

/-- Uniform placed quotient/descent data supplies the bounded
interface-anonymous local-monoid/profile datum.

This records that the placed-quotient route is not a parallel shortcut: after
slotwise/product descent it constructs the selected `V_h` profile-subspace data,
then this adapter packages that data in the paper's bounded normal-form/profile
surface. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiBoundedInterfaceAnonymousLocalMonoidProfileData_of_placedQuotientDescent
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    Step247UniformRouteBPaperFaithfulTPhiBoundedInterfaceAnonymousLocalMonoidProfileData := by
  intro M n hn hn2 htb hns
  exact
    ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictBoundedInterfaceAnonymousLocalMonoidProfileData_of_profileSubspaceData
      M n hn2 htb hns
      (step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData_of_placedQuotientDescent
        hData M n hn hn2 htb hns)⟩

/-- A selected strict `ConstraintType` profile-subspace datum gives the actual
paper `TΦ` P-side bound.

This is the close-out from the new placed route to the landed Route-B rank
surface: convert the selected subspace data to interface-profile data, then to
the finite local-monoid/profile package, and finally use the checked global
profile-span assembly. -/
noncomputable def routeBPaperFaithfulTPhi_pSideBound_of_strictConstraintTypeProfileSubspaceData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
      M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge
        M n hn2 htb hns) :=
  PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_pSideBound_of_strictCanonicalWindowLocalMonoidProfileData
    M n hn2 htb hns
    (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData_of_interfaceAnonymousLocalMonoidProfileData
      M n hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictInterfaceAnonymousLocalMonoidProfileData_of_boundedInterfaceAnonymousLocalMonoidProfileData
        M n hn2 htb hns
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictBoundedInterfaceAnonymousLocalMonoidProfileData_of_constraintTypeInterfaceProfileData
          M n hn2 htb hns
          (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData_of_profileSubspaceData
            M n hn2 htb hns D))))

/-- The ambient strict-`TΦ` gauge P-side bound also bounds the strict coupled
same-target sheet.

The proof uses only the verified first-of-block identification and injective
rename rank preservation: the target is the unrenamed restricted sheet at the
pullback partition, while the ambient gauge is its re-expansion by the same
first-of-block rename. -/
theorem routeBPaperFaithfulTPhi_targetRank_le_of_ambientGaugePSideBound
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hP : SATDeciderGaugePSideBound M n hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge
        M n hn2 htb hns)) :
    MultilinearSPDP.mlBlockedSpdpRank
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiTarget
        M n hn2 htb hns
        (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)).coupledPartition
      (Nat.log 2 n) (Nat.log 2 n)
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiTarget
        M n hn2 htb hns
        (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)).coupledPoly ≤
      n ^ 200 := by
  let p : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (Step4Compiler.Step252.cookLevinStrictFOBFlatMap n)
      (Step4Compiler.Step252.cookLevinStrictFOBFlatMap_injective n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns))
  have hrename :
      MultilinearSPDP.mlBlockedSpdpRank
          (MultilinearSPDP.pullbackPartition
            (cook_levin_compilation M n hn2 htb hns).partition
            (Step4Compiler.Step252.cookLevinStrictFOBFlatMap n))
          (Nat.log 2 n) (Nat.log 2 n) p ≤
        MultilinearSPDP.mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (MvPolynomial.rename (Step4Compiler.Step252.cookLevinStrictFOBFlatMap n) p) :=
    PaperFaithfulCompilation.mlBlockedSpdpRank_rename_ge
      (Step4Compiler.Step252.cookLevinStrictFOBFlatMap n) (Step4Compiler.Step252.cookLevinStrictFOBFlatMap_injective n)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) p
  have hambient :
      MultilinearSPDP.mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (MvPolynomial.rename (Step4Compiler.Step252.cookLevinStrictFOBFlatMap n) p) ≤ n ^ 200 := by
    simpa [SATDeciderGaugePSideBound, p,
      PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge_compiledPoly_eq_reexpandedStrictFOB]
      using hP
  have hflat := hrename.trans hambient
  simpa [PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiTarget,
    Step4Compiler.Step252.cookLevinStrictFOBTarget, p,
    Step4Compiler.Step252.cookLevinStrictFOB_pullbackPartition_eq_flat M n hn2 htb hns
      (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) rfl,
    Step4Compiler.Step252.cookLevinStrictFOB_restrict_embedded_Q_eq_restrict_compiledPoly M n hn2 htb hns]
    using hflat

/-- Target P-side rank plus the strict same-target NP lower bound closes the
paper-scale contradiction, using the target itself as the paper source in the
Theorem-207 transport inequality. -/
theorem false_of_routeBPaperFaithfulTPhi_targetPSideBound
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hTarget :
      MultilinearSPDP.mlBlockedSpdpRank
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiTarget
          M n hn2 htb hns
          (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)).coupledPartition
        (Nat.log 2 n) (Nat.log 2 n)
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiTarget
          M n hn2 htb hns
          (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)).coupledPoly ≤
        n ^ 200) :
    False := by
  let target := PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiTarget
    M n hn2 htb hns
    (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
  let source : GlobalGodMoveGauge.Theorem207PaperSource M n hn hn2 htb hns :=
    { sourceVars := target.coupledVars
      sourcePartition := target.coupledPartition
      sourcePoly := target.coupledPoly }
  exact
    GlobalGodMoveGauge.theorem207PaperSource_transport_false
      M n hn hn2 htb hns target source
      (by
        refine ⟨?_⟩
        simpa [source, target, GlobalGodMoveGauge.Theorem207PaperSource.spdpRank]
          using hTarget)
      (by
        refine ⟨?_⟩
        simp [source, target, GlobalGodMoveGauge.Theorem207PaperSource.spdpRank])
      (routeB_strong_np_from_same_target_identity_minor
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_identity_minor_data
          M n hn hn2 htb hns
          (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) rfl))

/-- Uniform placed quotient/descent data closes the strict paper `TΦ` P-side
rank surface, without routing through the old unplaced atom-trace chart. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiPSideBound_of_placedQuotientDescent
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      SATDeciderGaugePSideBound M n hn2 htb hns
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge
          M n hn2 htb hns) := by
  intro M n hn hn2 htb hns
  exact
    routeBPaperFaithfulTPhi_pSideBound_of_strictConstraintTypeProfileSubspaceData
      M n hn2 htb hns
      (step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData_of_placedQuotientDescent
        hData M n hn hn2 htb hns)

/-- Uniform placed quotient/descent data closes the full paper-scale SAT
contradiction for the strict `TΦ` Route-B path. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescent
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_targetPSideBound M n hn hn2 htb hns
      (routeBPaperFaithfulTPhi_targetRank_le_of_ambientGaugePSideBound
        M n hn2 htb hns
        (step247UniformRouteBPaperFaithfulTPhiPSideBound_of_placedQuotientDescent
          hData M n hn hn2 htb hns))



/-- Uniform full finite-normal-form alphabet data at Step 247 scale.

Unlike the four-bin bounded surface, this keeps the paper's actual finite
normal-form alphabet explicit and carries the final assembled profile budget
directly against the ambient `n^200` envelope. -/
def Step247UniformRouteBPaperFaithfulTPhiLooseInterfaceAnonymousLocalMonoidProfileData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictLooseInterfaceAnonymousLocalMonoidProfileData
        M n hn2 htb hns)

/-- Full finite-normal-form alphabet data gives the strict ambient `TΦ` P-side
bound, with no `ConstraintType` four-bin collapse. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiPSideBound_of_looseInterfaceAnonymousLocalMonoidProfileData
    (hData : Step247UniformRouteBPaperFaithfulTPhiLooseInterfaceAnonymousLocalMonoidProfileData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      SATDeciderGaugePSideBound M n hn2 htb hns
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge
          M n hn2 htb hns) := by
  intro M n hn hn2 htb hns
  let D := Classical.choice (hData M n hn hn2 htb hns)
  exact
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_pSideBound_of_strictLooseInterfaceAnonymousLocalMonoidProfileData
      M n hn2 htb hns D

/-- Uniform `AlphabetWord 1` local-monoid/profile data at Step 247 scale.

This is the first concrete option-2 target: the normal-form alphabet is the
literal finite word alphabet `Σ^{≤1}`, and the profile-count arithmetic is
proved in `RouteBPaperFaithfulTPhiExtraction`.  The remaining mathematical
content is exactly the selected Lemma-31 row membership for those profiles. -/
def Step247UniformRouteBPaperFaithfulTPhiAlphabetWordOneLocalMonoidProfileData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictAlphabetWordOneLocalMonoidProfileData
        M n hn2 htb hns)

/-- The placed quotient/descent construction also supplies the concrete
`AlphabetWord 1` option-2 datum.

The selected `V_h` row membership is first obtained as the existing strict
`ConstraintType` profile-subspace datum, converted to selected interface bases,
and then embedded into the literal `Σ^{≤1}` profile space. The full
17-symbol profile count remains the one used by the downstream budget. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiAlphabetWordOneLocalMonoidProfileData_of_placedQuotientDescent
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    Step247UniformRouteBPaperFaithfulTPhiAlphabetWordOneLocalMonoidProfileData := by
  intro M n hn hn2 htb hns
  let Dsub :=
    step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData_of_placedQuotientDescent
      hData M n hn hn2 htb hns
  let Dct :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData_of_profileSubspaceData
      M n hn2 htb hns Dsub
  exact
    ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictAlphabetWordOneLocalMonoidProfileData_of_constraintTypeInterfaceProfileData
      M n hn2 htb hns Dct⟩

/-- `AlphabetWord 1` data supplies the loose full-alphabet Step247 datum. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiLooseInterfaceAnonymousLocalMonoidProfileData_of_alphabetWordOneProfileData
    (hData : Step247UniformRouteBPaperFaithfulTPhiAlphabetWordOneLocalMonoidProfileData) :
    Step247UniformRouteBPaperFaithfulTPhiLooseInterfaceAnonymousLocalMonoidProfileData := by
  intro M n hn hn2 htb hns
  exact
    ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictLooseInterfaceAnonymousLocalMonoidProfileData_of_alphabetWordOneProfileData
      M n hn2 htb hns
      (Classical.choice (hData M n hn hn2 htb hns))⟩

/-- Uniform bounded local-monoid/profile data closes the full strict `TΦ`
Route-B contradiction.

This is the corrected top-level closeout for the paper route: prove the
finite local-monoid normal forms and selected Lemma-31 profile subspaces, then
the existing same-target extraction/NP lower-bound sandwich rules out bounded
SAT deciders. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiBoundedInterfaceAnonymousLocalMonoidProfileData
    (hData : Step247UniformRouteBPaperFaithfulTPhiBoundedInterfaceAnonymousLocalMonoidProfileData) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_targetPSideBound M n hn hn2 htb hns
      (routeBPaperFaithfulTPhi_targetRank_le_of_ambientGaugePSideBound
        M n hn2 htb hns
        (step247UniformRouteBPaperFaithfulTPhiPSideBound_of_boundedInterfaceAnonymousLocalMonoidProfileData
          hData M n hn hn2 htb hns))



/-- Uniform full finite-normal-form alphabet data closes the strict `TΦ` Route-B
contradiction without collapsing `Σ^{≤q}` to four raw constraint bins. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiLooseInterfaceAnonymousLocalMonoidProfileData
    (hData : Step247UniformRouteBPaperFaithfulTPhiLooseInterfaceAnonymousLocalMonoidProfileData) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_targetPSideBound M n hn hn2 htb hns
      (routeBPaperFaithfulTPhi_targetRank_le_of_ambientGaugePSideBound
        M n hn2 htb hns
        (step247UniformRouteBPaperFaithfulTPhiPSideBound_of_looseInterfaceAnonymousLocalMonoidProfileData
          hData M n hn hn2 htb hns))

/-- Uniform `AlphabetWord 1` profile data closes the strict `TΦ` Route-B
contradiction through the full finite-normal-form alphabet route. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiAlphabetWordOneLocalMonoidProfileData
    (hData : Step247UniformRouteBPaperFaithfulTPhiAlphabetWordOneLocalMonoidProfileData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiLooseInterfaceAnonymousLocalMonoidProfileData
    (step247UniformRouteBPaperFaithfulTPhiLooseInterfaceAnonymousLocalMonoidProfileData_of_alphabetWordOneProfileData hData)

/-- Paper-faithful close-out: the explicit placed interface normal-form seam is
sufficient to close the strict `TΦ` Route-B path.  This is the theorem surface
matching the manuscript's quotient/normal-form solution rather than the false
raw global-chart target. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceNormalFormData
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceNormalFormData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescent
    (step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData_of_interfaceNormalFormData hData)

/-- SAT contradiction from the explicit equivariant quotient-map normal-form
seam. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceEquivariantQuotientMapNormalFormData
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceEquivariantQuotientMapNormalFormData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceNormalFormData
    (step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceNormalFormData_of_equivariantQuotientMapNormalFormData hData)

/-- Projected quotient-normal-form obligation for the strict `TΦ` route.

This is the sound replacement for the impossible ambient selected-place equality:
choose a quotient/normal-form certificate, prove its projected type budget, and
prove semantic restricted residual balance for that chosen projection.  The
existential certificate is deliberate and paper-faithful: the manuscript chooses
a normal form/projection rather than requiring residual balance for every
possible quotient certificate. -/
def Step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    ∃ typeBudget : Nat,
    ∃ cert :
      ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        typeBudget,
      typeBudget ≤ withinProfileBound (Nat.log 2 n) ∧
      PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns cert.project

/-- The projected quotient-normal-form route closes the no-bounded-SAT-decider
statement without asserting that all placed slots live in one ambient chart. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData
    (hData : Step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_quotientTypeCertificate_restrictedResidualBalance
    hData

/-- The same projected quotient-normal-form route yields the rich-projection
discharge used by the broader Route-B bridge. -/
theorem cookLevinRichProjectionDischarge_of_step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData
    (hData : Step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData) :
    CookLevinRichProjectionDischarge :=
  PallLean.Paper93.Paper283.cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_quotientTypeCertificate_restrictedResidualBalance
    hData

/-- Concrete singleton-quotient data instantiates the selected projected
quotient-normal-form gate.

This is the paper-faithful closure surface after the selected-certificate
refactor: concrete per-type row embeddings discharge the projected quotient
budget, normalized non-singleton coefficients give the selected normalized row,
and the derivative fixed-representative condition supplies residual balance for
the chosen singleton quotient projection. -/
theorem step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData_of_singletonQuotient_concreteW_normalizedCoeff_fixedDerivative
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        ∃ hn4 : n ≥ 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
            M n hn2 htb hns ∧
          PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
            M n hn2 htb hns) :
    Step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hn4, hRowEmbeddings, hcoeff, hfix⟩
  let typeBudget : Nat :=
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
  let cert : ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      typeBudget :=
    zeroProfileSingletonQuotientTypeSpaceCertificate_projectedFinrank
      (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
  refine ⟨typeBudget, cert, ?_, ?_⟩
  · exact
      PallLean.Paper93.Paper283.cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_concreteW_rowEmbeddings
        M n hn2 htb hns hn4 hRowEmbeddings
  · have hnorm :
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
          M n hn2 htb hns :=
      PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_normalizedNonSingletonCoeff
        M n hn2 htb hns hcoeff
    have hresSingleton :
        PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
          M n hn2 htb hns
          (zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) :=
      PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_of_normalizedRows_derivativeFixed
        M n hn2 htb hns hnorm hfix
    simpa [cert, typeBudget, zeroProfileSingletonQuotientTypeSpaceCertificate_projectedFinrank]
      using hresSingleton

/-- Closeout from the concrete selected singleton-quotient data, routed through
the selected projected quotient-normal-form gate above. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhi_singletonQuotient_concreteW_normalizedCoeff_fixedDerivative
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        ∃ hn4 : n ≥ 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
            M n hn2 htb hns ∧
          PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
            M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData
    (step247UniformRouteBPaperFaithfulTPhiProjectedQuotientNormalFormData_of_singletonQuotient_concreteW_normalizedCoeff_fixedDerivative
      hcert)

/-- Ambient quotient/rank soundness for the placed local-interface expansion.

This is the precise remaining bridge if one replaces the false fixed raw chart
claim by a genuine quotient-normalisation step: from the placed local expansion,
produce the already checked `PlacedQuotientDescentData` consumed by the Route B
rank chain.  Keeping this as a named implication prevents silently smuggling in
ambient selected-chart equality. -/
def Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessData : Prop :=
  Step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData →
    Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData

/-- Placed expansion plus the explicit ambient quotient/rank soundness bridge
supplies the checked placed quotient/descent datum. -/
theorem step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData_of_placedExpansionData_and_ambientQuotientSoundness
    (hExpansion : Step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData)
    (hSound : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessData) :
    Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData :=
  hSound hExpansion

/-- Close-out through the corrected quotient-normalisation factoring: the local
placed expansion is separated from the ambient quotient/rank soundness bridge,
then the existing checked Route B descent closes the no-decider statement. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData_and_ambientQuotientSoundness
    (hExpansion : Step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData)
    (hSound : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescent
    (step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData_of_placedExpansionData_and_ambientQuotientSoundness
      hExpansion hSound)

/-! ## Axiom audit anchors -/

#print axioms step247UniformRouteBPaperFaithfulTPhiStrictSourceProfileSubspaceData_of_placedQuotientDescent
#print axioms step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData_of_placedQuotientDescent
#print axioms routeBPaperFaithfulTPhi_pSideBound_of_strictConstraintTypeProfileSubspaceData
#print axioms routeBPaperFaithfulTPhi_targetRank_le_of_ambientGaugePSideBound
#print axioms false_of_routeBPaperFaithfulTPhi_targetPSideBound
#print axioms step247UniformRouteBPaperFaithfulTPhiPSideBound_of_placedQuotientDescent
#print axioms noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescent
#print axioms noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceNormalFormData
#print axioms noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedInterfaceEquivariantQuotientMapNormalFormData

end PallLean.Paper93.DeepMath.PathB
