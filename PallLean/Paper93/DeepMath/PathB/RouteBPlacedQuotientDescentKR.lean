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

/-- Uniform local compiled-coordinate profile-subspace row data at Step 247 scale.

This is the direct paper-faithful Lemma-31 row-containment target: for each
selected canonical source row, the row lies in `profileSubspace ρ.val W` for a
local compiled-coordinate family `Wσ` of rank at most three.  It deliberately
avoids the stronger/false requirement that every arbitrary shifted Leibniz
summand individually land in the same selected profile. -/
def Step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedLocalCompiledProfileSubspaceRowData
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

/-- Uniform exact shifted Leibniz-product interface-slot factorization data at
Step 247 scale, with no profile-uniform shift-closure obligation.  This is the
slot-product half consumed by the coherent branch-atom route. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductExactInterfaceSlotFactorizationData
        M n hn2 htb hns)

/-- Uniform selected-shift closure witness on exact slot-factorization data at
Step 247 scale (the only extra field needed to recover witnessed slot data). -/
def Step247UniformRouteBPaperFaithfulTPhiSelectedShiftClosureOnExactInterfaceSlotFactorizationData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductExactInterfaceSlotFactorizationData
      M n hn2 htb hns),
    PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductSelectedShiftClosureFieldOnExactInterfaceSlotFactorizationData
      M n hn2 htb hns D

/-- Paper-faithful paired exact-slot seam: for each machine/scale witness, we
construct an exact-slot payload together with its selected-shift closure field. -/
def Step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    ∃ D : PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductExactInterfaceSlotFactorizationData
          M n hn2 htb hns,
      PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductSelectedShiftClosureFieldOnExactInterfaceSlotFactorizationData
        M n hn2 htb hns D

/-- Paired exact-slot + selected-shift-closure seam upgrades directly to full
witnessed slot-factorization data at Step 247 scale. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData_of_exactInterfaceSlotFactorizationWithSelectedShiftClosureData
    (hData : Step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D, hClosure⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductInterfaceSlotFactorizationData_of_exactInterfaceSlotFactorizationData
    M n hn2 htb hns D hClosure⟩

/-- Exact slot data + selected-shift closure witness upgrades to full witnessed
slot-factorization data at Step 247 scale. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData_of_exactInterfaceSlotFactorizationData_and_selectedShiftClosure
    (hExact : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData)
    (hClosure : Step247UniformRouteBPaperFaithfulTPhiSelectedShiftClosureOnExactInterfaceSlotFactorizationData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData := by
  intro M n hn hn2 htb hns
  rcases hExact M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductInterfaceSlotFactorizationData_of_exactInterfaceSlotFactorizationData
    M n hn2 htb hns D (hClosure M n hn hn2 htb hns D)⟩

/-- Exact slot data plus a closure rule for every exact slot witness directly
constructs the paired paper-faithful seam.  This removes the detour through the
legacy full slot-factorization payload when the proof has already separated the
existence of exact slots from the selected-shift closure lemma. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData_of_exactInterfaceSlotFactorizationData_and_selectedShiftClosure
    (hExact : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData)
    (hClosure : Step247UniformRouteBPaperFaithfulTPhiSelectedShiftClosureOnExactInterfaceSlotFactorizationData) :
    Step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData := by
  intro M n hn hn2 htb hns
  rcases hExact M n hn hn2 htb hns with ⟨D⟩
  exact ⟨D, hClosure M n hn hn2 htb hns D⟩

/-- Any witnessed slot-factorization seam canonically yields the paired exact
slot + selected-shift-closure seam. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData_of_interfaceSlotFactorizationData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData) :
    Step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  let Dexact := PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductExactInterfaceSlotFactorizationData_of_interfaceSlotFactorizationData
    M n hn2 htb hns D
  refine ⟨Dexact, ?_⟩
  intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ p hp
  have hρ' :
      D.profileOfCanonicalWindow
          (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
          hrow.1 = ρ := by
    simpa [Dexact] using hρ
  simpa [Dexact] using D.selectedShift_mlProj_closure_compiledBasisProfileSubspace
    ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ' p hp

/-- The legacy slot-factorization seam forgets to the exact slot-product seam. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData_of_interfaceSlotFactorizationData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductExactInterfaceSlotFactorizationData_of_interfaceSlotFactorizationData
    M n hn2 htb hns D⟩

/-- Uniform factor-indexed exact slot factorization data at Step 247 scale.
This is the paper-faithful local classification of concrete Cook-Levin factors
by anonymous interface slots. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFactorizationData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductIndexedInterfaceSlotFactorizationData
        M n hn2 htb hns)

/-- Factor-indexed slot classification instantiates anonymous exact slots. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData_of_indexedInterfaceSlotFactorizationData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFactorizationData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductExactInterfaceSlotFactorizationData_of_indexedInterfaceSlotFactorizationData
    M n hn2 htb hns D⟩

/-- Uniform factor-fiber partition data at Step 247 scale.

This is the disjoint-covering version of the factor-indexed slot seam: the
exact product identity is derived from the fiber partition rather than carried
as a raw field. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData
        M n hn2 htb hns)

/-- Uniform total slot-classifier data at Step 247 scale.

This is the smaller constructive target below the fibre partition surface: a
single total assignment of each concrete Cook--Levin factor index to an
anonymous slot `(σ,j)`, plus the local compiled-basis membership for the induced
slot fibre products.  The disjointness and cover fields of the fibre-partition
surface are then generated automatically as preimage facts. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotClassifierData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductIndexedInterfaceSlotClassifierData
        M n hn2 htb hns)

/-- A uniform total slot classifier canonically instantiates the disjoint
factor-fibre partition seam. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData_of_classifierData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotClassifierData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData_of_classifierData
    M n hn2 htb hns D⟩

/-- A uniform factor-fiber partition instantiates the existing factor-indexed
slot-factorization data. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFactorizationData_of_fiberPartitionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFactorizationData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductIndexedInterfaceSlotFactorizationData_of_fiberPartitionData
    M n hn2 htb hns D⟩

/-- A uniform factor-fiber partition directly instantiates anonymous exact
interface slots.  This is the constructive exact-slot half of the paper-faithful
row-specific bottom seam: the disjoint factor fibers give indexed slots, and the
indexed-slot adapter forgets the fiber labels to the exact anonymous slot
product. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData_of_fiberPartitionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData :=
  step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData_of_indexedInterfaceSlotFactorizationData
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFactorizationData_of_fiberPartitionData
      hData)

/-- Uniform coherent factor-indexed slot classification plus shifted branch-atom
data. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtomData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtomData
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

/-- Exact slot data plus coherent shifted branch-atom data gives the
row-specific selected-shift closure on those exact slots.

This is the paper-faithful replacement for the over-strong profile-uniform
operator-closure seam: the slot side supplies the exact anonymous product, and
the branch-atom side supplies the selected shifted membership for that same
canonical profile selector and source partition. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_exactSlotData_and_branchAtomData
    (hExact : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductExactInterfaceSlotFactorizationData)
    (hBranch : Step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DSlot := Classical.choice (hExact M n _hn hn2 htb hns)
        let DBr := Classical.choice (hBranch M n _hn hn2 htb hns)
        DBr.sourcePartition = DSlot.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DSlot := Classical.choice (hExact M n _hn hn2 htb hns)
        let DBr := Classical.choice (hBranch M n _hn hn2 htb hns)
        ∀ w hw, DBr.profileOfCanonicalWindow w hw = DSlot.profileOfCanonicalWindow w hw) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData := by
  intro M n hn hn2 htb hns
  let DSlot := Classical.choice (hExact M n hn hn2 htb hns)
  let DBr := Classical.choice (hBranch M n hn hn2 htb hns)
  refine ⟨{ slotData := DSlot
          , branchAtomData := DBr
          , branchAtom_sourcePartition_eq_slot := ?_
          , branchAtom_profileOfCanonicalWindow_eq_slot := ?_ }⟩
  · simpa [DSlot, DBr] using (hPartEq M n hn hn2 htb hns)
  · intro w hw
    simpa [DSlot, DBr] using (hProfEq M n hn hn2 htb hns w hw)

/-- Coherent factor-fiber partitions plus branch atoms directly instantiate the
exact-slot/branch-atom row-specific selected-shift seam.

This simultaneously constructs the two requested uniform bottom pieces from the
lower, paper-local payloads: exact anonymous interface slots are derived from the
factor-fiber partition, while selected-shift membership is supplied by the
coherent branch-atom profile data. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_fiberPartitionData_and_branchAtomData
    (hFib : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData)
    (hBranch : Step247UniformRouteBPaperFaithfulTPhiShiftedBranchAtomCompiledBasisProfileData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DBr := Classical.choice (hBranch M n _hn hn2 htb hns)
        DBr.sourcePartition = DFib.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DBr := Classical.choice (hBranch M n _hn hn2 htb hns)
        ∀ w hw, DBr.profileOfCanonicalWindow w hw = DFib.profileOfCanonicalWindow w hw) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData := by
  intro M n hn hn2 htb hns
  let DFib := Classical.choice (hFib M n hn hn2 htb hns)
  let DIndexed :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductIndexedInterfaceSlotFactorizationData_of_fiberPartitionData
      M n hn2 htb hns DFib
  let DSlot :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductExactInterfaceSlotFactorizationData_of_indexedInterfaceSlotFactorizationData
      M n hn2 htb hns DIndexed
  let DBr := Classical.choice (hBranch M n hn hn2 htb hns)
  refine ⟨{ slotData := DSlot
          , branchAtomData := DBr
          , branchAtom_sourcePartition_eq_slot := ?_
          , branchAtom_profileOfCanonicalWindow_eq_slot := ?_ }⟩
  · simpa [DFib, DIndexed, DSlot, DBr] using (hPartEq M n hn hn2 htb hns)
  · intro w hw
    simpa [DFib, DIndexed, DSlot, DBr] using (hProfEq M n hn hn2 htb hns w hw)

/-- Coherent factor-fiber partitions plus local-algebra data directly instantiate
the exact-slot/branch-atom row-specific selected-shift seam.

Compared with the branch-atom version, this descends the selected-shift side one
step: branch-atom membership is derived from the shifted Leibniz local-algebra
payload by the existing `NFOfWord` permutation bridge.  The only remaining
coherence is that the local-algebra payload and factor-fiber slot payload choose
the same source partition and canonical profile selector. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_fiberPartitionData_and_localAlgebraData
    (hFib : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData)
    (hLocal : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        DLoc.sourcePartition = DFib.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        ∀ w hw, DLoc.profileOfCanonicalWindow w hw = DFib.profileOfCanonicalWindow w hw) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData := by
  intro M n hn hn2 htb hns
  let DFib := Classical.choice (hFib M n hn hn2 htb hns)
  let DIndexed :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductIndexedInterfaceSlotFactorizationData_of_fiberPartitionData
      M n hn2 htb hns DFib
  let DSlot :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductExactInterfaceSlotFactorizationData_of_indexedInterfaceSlotFactorizationData
      M n hn2 htb hns DIndexed
  let DLoc := Classical.choice (hLocal M n hn hn2 htb hns)
  let DComp :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductCompiledBasisProfileData_of_localAlgebraData
      M n hn2 htb hns DLoc
  let DBr :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedBranchAtomCompiledBasisProfileData_of_shiftedLeibnizProductData
      M n hn2 htb hns DComp
  refine ⟨{ slotData := DSlot
          , branchAtomData := DBr
          , branchAtom_sourcePartition_eq_slot := ?_
          , branchAtom_profileOfCanonicalWindow_eq_slot := ?_ }⟩
  · simpa [DFib, DIndexed, DSlot, DLoc, DComp, DBr] using (hPartEq M n hn hn2 htb hns)
  · intro w hw
    simpa [DFib, DIndexed, DSlot, DLoc, DComp, DBr] using (hProfEq M n hn hn2 htb hns w hw)

/-- Coherent factor-fiber partitions plus local-algebra data construct the
primary paired bottom seam: the factor-fiber payload gives exact anonymous
interface slots, while the local-algebra payload supplies the selected
shift/`mlProj` closure field on those exact slots.

This packages the two paper-local constructor obligations without routing
through the branch-atom row-shift seam and without asserting the known-bad
profile-agnostic global closure.  The closure is transported only along the
explicit source-partition/profile-selector coherence hypotheses. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData_of_fiberPartitionData_and_localAlgebraData
    (hFib : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData)
    (hLocal : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        DLoc.sourcePartition = DFib.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        ∀ w hw, DLoc.profileOfCanonicalWindow w hw = DFib.profileOfCanonicalWindow w hw) :
    Step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData := by
  intro M n hn hn2 htb hns
  let DFib := Classical.choice (hFib M n hn hn2 htb hns)
  let DIndexed :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductIndexedInterfaceSlotFactorizationData_of_fiberPartitionData
      M n hn2 htb hns DFib
  let DSlot :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductExactInterfaceSlotFactorizationData_of_indexedInterfaceSlotFactorizationData
      M n hn2 htb hns DIndexed
  let DLoc := Classical.choice (hLocal M n hn hn2 htb hns)
  refine ⟨DSlot, ?_⟩
  intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ p hp
  have hPart : DLoc.sourcePartition = DSlot.sourcePartition := by
    simpa [DFib, DIndexed, DSlot, DLoc] using (hPartEq M n hn hn2 htb hns)
  have hρLoc :
      DLoc.profileOfCanonicalWindow
          (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
          hrow.1 = ρ := by
    have hprof := hProfEq M n hn hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
      hrow.1
    calc
      DLoc.profileOfCanonicalWindow
          (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
          hrow.1
          = DSlot.profileOfCanonicalWindow
              (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
              hrow.1 := by
            simpa [DFib, DIndexed, DSlot, DLoc] using hprof
      _ = ρ := hρ
  have hpLoc :
      p ∈ profileSubspace ρ.val
          (fun τ =>
            interfaceSpace_compiledBasis
              DLoc.sourcePartition (Nat.log 2 n) (Nat.log 2 n) τ) := by
    simpa [hPart] using hp
  have hclosed :=
    DLoc.selectedShift_mlProj_closure_compiledBasisProfileSubspace
      ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρLoc p hpLoc
  simpa [hPart] using hclosed

/-- Coherent total slot-classifier data plus local-algebra data construct the
primary paired bottom seam without passing through a `Classical.choice`d fibre
partition.

The classifier is converted to its canonical preimage fibre partition inside the
same instance, so the coherence hypotheses are stated against the actual
classifier payload (`DCls`) rather than against an arbitrary nonempty choice of
the derived fibre surface.  This is the clean Step-247 target for the remaining
constructive work: build one total factor→slot classifier and one matching
local-algebra package. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData_of_classifierData_and_localAlgebraData
    (hCls : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotClassifierData)
    (hLocal : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DCls := Classical.choice (hCls M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        DLoc.sourcePartition = DCls.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DCls := Classical.choice (hCls M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        ∀ w hw, DLoc.profileOfCanonicalWindow w hw = DCls.profileOfCanonicalWindow w hw) :
    Step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData := by
  intro M n hn hn2 htb hns
  let DCls := Classical.choice (hCls M n hn hn2 htb hns)
  let DFib :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData_of_classifierData
      M n hn2 htb hns DCls
  let DIndexed :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductIndexedInterfaceSlotFactorizationData_of_fiberPartitionData
      M n hn2 htb hns DFib
  let DSlot :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductExactInterfaceSlotFactorizationData_of_indexedInterfaceSlotFactorizationData
      M n hn2 htb hns DIndexed
  let DLoc := Classical.choice (hLocal M n hn hn2 htb hns)
  refine ⟨DSlot, ?_⟩
  intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ p hp
  have hPart : DLoc.sourcePartition = DSlot.sourcePartition := by
    simpa [DCls, DFib, DIndexed, DSlot, DLoc] using (hPartEq M n hn hn2 htb hns)
  have hρLoc :
      DLoc.profileOfCanonicalWindow
          (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
          hrow.1 = ρ := by
    have hprof := hProfEq M n hn hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
      hrow.1
    calc
      DLoc.profileOfCanonicalWindow
          (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
          hrow.1
          = DSlot.profileOfCanonicalWindow
              (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiStrictRawWindowOf n S' shift α)
              hrow.1 := by
            simpa [DCls, DFib, DIndexed, DSlot, DLoc] using hprof
      _ = ρ := hρ
  have hpLoc :
      p ∈ profileSubspace ρ.val
          (fun τ =>
            interfaceSpace_compiledBasis
              DLoc.sourcePartition (Nat.log 2 n) (Nat.log 2 n) τ) := by
    simpa [hPart] using hp
  have hclosed :=
    DLoc.selectedShift_mlProj_closure_compiledBasisProfileSubspace
      ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρLoc p hpLoc
  simpa [hPart] using hclosed

/-- Coherent exact slot factorization plus shifted branch-atom membership closes
 the row-specific shifted slot-product seam at Step 247 scale. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_slotProductBranchAtomData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_slotProductBranchAtomData
    M n hn2 htb hns D⟩

/-- Uniform coherent factor-fiber partition plus shifted branch-atom data. -/
def Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedFiberPartitionBranchAtomData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedFiberPartitionBranchAtomData
        M n hn2 htb hns)

/-- Coherent factor-fiber partitions plus branch atoms instantiate the existing
indexed-slot branch-atom route. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtomData_of_indexedFiberPartitionBranchAtomData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedFiberPartitionBranchAtomData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtomData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtomData_of_indexedFiberPartitionBranchAtomData
    M n hn2 htb hns D⟩

/-- Coherent indexed slots plus branch atoms instantiate the exact-slot
branch-atom route. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_indexedBranchAtomData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtomData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_indexedBranchAtomData
    M n hn2 htb hns D⟩

/-- Coherent indexed slots plus branch atoms also instantiate row-specific
shifted slot-product data. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_indexedBranchAtomData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromIndexedBranchAtomData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData :=
  step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_slotProductBranchAtomData
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_indexedBranchAtomData
      hData)

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

/-- Uniform shift-closure slot-product data also instantiates the paired
paper-faithful seam (exact slots + selected-shift closure witness). -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData_of_slotProductUniformShiftClosureData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductUniformShiftClosureData) :
    Step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData :=
  step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData_of_interfaceSlotFactorizationData
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData_of_slotProductUniformShiftClosureData
      hData)

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

/-- Slot-factorization data supplies the coherent row-shift-from-branch-atom
package by deriving the branch-atom payload from the same upstream slot data. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_interfaceSlotFactorizationData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_interfaceSlotFactorizationData
    M n hn2 htb hns D⟩

/-- Slot-factorization data therefore also supplies the row-specific shifted
slot-product seam through the coherent branch-atom route. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_interfaceSlotFactorizationData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData) :
    Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData :=
  step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftData_of_slotProductBranchAtomData
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotProductRowShiftFromBranchAtomData_of_interfaceSlotFactorizationData
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

This is the active Lemma-31 containment surface after the placed/local-chart
correction: the selected canonical source row lands in a concrete
finite-dimensional compiled-coordinate profile subspace, but the local
`W_σ` family is carried as data rather than forced to be the old fixed
source-coordinate `X₀/X₁` chart.  That fixed chart was too strong for placed
Cook--Levin rows; the paper-faithful object is the local compiled-coordinate
family with `finrank W_σ ≤ 3`. -/
def Step247UniformRouteBPaperFaithfulTPhiCompiledBasisProfileSubspaceRowData : Prop :=
  Step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData

/-- Legacy fixed-chart source-coordinate version of the compiled-basis row
surface.  This is kept only for adapters that explicitly unfold finite slot
expansions from the old `interfaceSpace_compiledBasis sourcePartition ...`
structure.  The active Step247 compiled-basis target above is the placed/local
compiled-coordinate target, not this fixed-chart specialization. -/
def Step247UniformRouteBPaperFaithfulTPhiFixedChartCompiledBasisProfileSubspaceRowData : Prop :=
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
  let Drow :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedCompiledBasisProfileSubspaceRowData_of_shiftedBranchAtomCompiledBasisProfileData
      M n hn2 htb hns D
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedLocalCompiledProfileSubspaceRowData_of_compiledBasisProfileSubspaceRowData
    M n hn2 htb hns Drow⟩

/-- The concrete compiled-basis row target supplies the local compiled-coordinate
row target by taking the local spaces `W_σ` to be the compiled-basis interface
spaces. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData_of_compiledBasisProfileSubspaceRowData
    (hData : Step247UniformRouteBPaperFaithfulTPhiCompiledBasisProfileSubspaceRowData) :
    Step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData :=
  hData

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

/-- Direct row-interface-slot expansion gives the fixed-chart compiled-basis
profile-row surface by the row-level same-profile slot expansion constructor. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiFixedChartCompiledBasisProfileSubspaceRowData_of_interfaceSlotExpansionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiInterfaceSlotExpansionData) :
    Step247UniformRouteBPaperFaithfulTPhiFixedChartCompiledBasisProfileSubspaceRowData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedCompiledBasisProfileSubspaceRowData_of_rowInterfaceSlotExpansionData
    M n hn2 htb hns D⟩

/-- Direct row-interface-slot expansion also gives the active local compiled
profile-row surface by taking the local family to be the fixed-chart
`interfaceSpace_compiledBasis` spaces. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData_of_interfaceSlotExpansionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiInterfaceSlotExpansionData) :
    Step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData := by
  intro M n hn hn2 htb hns
  rcases step247UniformRouteBPaperFaithfulTPhiFixedChartCompiledBasisProfileSubspaceRowData_of_interfaceSlotExpansionData
      hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedLocalCompiledProfileSubspaceRowData_of_compiledBasisProfileSubspaceRowData
    M n hn2 htb hns D⟩

/-- Direct profile-subspace row membership gives the explicit row-interface-slot
expansion by unfolding the defining span of `profileSubspace`. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiInterfaceSlotExpansionData_of_fixedChartCompiledBasisProfileSubspaceRowData
    (hData : Step247UniformRouteBPaperFaithfulTPhiFixedChartCompiledBasisProfileSubspaceRowData) :
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

/-- Uniform placed quotient/descent data gives the direct local compiled-coordinate
profile-subspace row datum.

This is the paper-faithful Route-B move isolated as its own Step247 surface:
placed local-interface expansion descends slotwise/productwise into the selected
`profileSubspace ρ.val W`.  No arbitrary Leibniz-summand same-profile closure is
introduced. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData_of_placedQuotientDescent
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    Step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedLocalCompiledProfileSubspaceRowData_of_placedLocalInterfaceQuotientDescentData
    M n hn2 htb hns D⟩

/-- Renamed-canonical Lemma-31 expansion directly constructs the local
compiled-coordinate profile row datum.

This is the explicit four-step local `W_σ` construction requested by the
paper-faithful Route B path:

1. choose the local `W_σ` spaces supplied by the placed quotient/descent datum;
2. use slotwise descent to prove each placed local slot lands in its `W_σ`;
3. assemble the slot product into `profileSubspace ρ.val W` by the symmetric
   profile-product constructor;
4. rewrite the selected `TΦ` row by the placed-local expansion and close under
   finite sums/scalars in that same profile subspace.

The work is delegated to the checked Paper283 constructors, but the endpoint is
now the active local `W_σ` row-containment target rather than the old fixed
source-chart compiled-basis surface. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData_of_renamedCanonicalInterfaceExpansionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiRenamedCanonicalInterfaceExpansionData) :
    Step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData :=
  step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData_of_placedQuotientDescent
    (step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData_of_renamedCanonicalInterfaceExpansionData
      hData)

/-- Uniform local compiled-coordinate profile-subspace row data gives the strict
source selected profile-subspace datum used by the existing P-side bound. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiStrictSourceProfileSubspaceData_of_localCompiledProfileSubspaceRowData
    (hData : Step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceConstraintTypeProfileSubspaceData
        M n hn2 htb hns := by
  intro M n hn hn2 htb hns
  let D := Classical.choice (hData M n hn hn2 htb hns)
  exact
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceProfileSubspaceData_of_localCompiledProfileSubspaceRowData
      M n hn2 htb hns D

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
        M n hn2 htb hns :=
  step247UniformRouteBPaperFaithfulTPhiStrictSourceProfileSubspaceData_of_localCompiledProfileSubspaceRowData
    (step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData_of_placedQuotientDescent
      hData)

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

/-- Uniform local compiled-coordinate profile-subspace row data gives the strict
paper `TΦ` P-side rank bound. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiPSideBound_of_localCompiledProfileSubspaceRowData
    (hData : Step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      SATDeciderGaugePSideBound M n hn2 htb hns
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge
          M n hn2 htb hns) := by
  intro M n hn hn2 htb hns
  exact
    routeBPaperFaithfulTPhi_pSideBound_of_strictConstraintTypeProfileSubspaceData
      M n hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData_of_sourceProfileSubspaceData
        M n hn2 htb hns
        (step247UniformRouteBPaperFaithfulTPhiStrictSourceProfileSubspaceData_of_localCompiledProfileSubspaceRowData
          hData M n hn hn2 htb hns))

/-- Uniform local compiled-coordinate profile-subspace row data closes the full
paper-scale SAT contradiction for the strict `TΦ` Route-B path. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData
    (hData : Step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_targetPSideBound M n hn hn2 htb hns
      (routeBPaperFaithfulTPhi_targetRank_le_of_ambientGaugePSideBound
        M n hn2 htb hns
        (step247UniformRouteBPaperFaithfulTPhiPSideBound_of_localCompiledProfileSubspaceRowData
          hData M n hn hn2 htb hns))

/-- Uniform concrete compiled-basis profile-subspace row data closes the full
paper-scale SAT contradiction via the local compiled-coordinate row surface. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiCompiledBasisProfileSubspaceRowData
    (hData : Step247UniformRouteBPaperFaithfulTPhiCompiledBasisProfileSubspaceRowData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData
    (step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData_of_compiledBasisProfileSubspaceRowData
      hData)

/-- Uniform placed quotient/descent data closes the full paper-scale SAT
contradiction for the strict `TΦ` Route-B path. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescent
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData
    (step247UniformRouteBPaperFaithfulTPhiLocalCompiledProfileSubspaceRowData_of_placedQuotientDescent
      hData)




/-- Uniform concrete transition-monoid data at Step 247 scale.

This is the paper-faithful source of the local-monoid normal forms: the normal
form type is a finite monoid, the generator list is fixed, and the Leibniz word
is the actual flattened transition word.  The only hard mathematical field left
inside the payload is the row membership in the normal-form local basis. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalTransitionMonoidData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizLocalTransitionMonoidData
        M n hn2 htb hns)

/-- Uniform fixed-`q` event-atom final payload at Step 247 scale.

This is the tight pre-max-card constructive surface: local dimension is fixed to
the actual bounded-word length cap `q`, event-atom bases are singleton, and the
remaining key field is the witnessed row membership for the exact bounded
`NFOfWord` atom basis. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps
        M n hn2 htb hns)

/-- Uniform fixed-`q` event-atom budget scaffolding at Step 247 scale. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData
        M n hn2 htb hns)

/-- Uniform fixed-`q` row-witness seam at Step 247 scale. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimRowWitness : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordEventAtomQDimRowWitness
        M n hn2 htb hns)

/-- Uniform fixed-`q` pointwise target-membership witness at Step 247 scale. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimTargetMembership : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (∀ (ρ : PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
            ConstraintType (Nat.log 2 n))
        (S' : List (Fin (n / 3))) (hS : S'.length ≤ Nat.log 2 n)
        (shift : MvPolynomial (Fin (n / 3)) ℚ)
        (hshift : shift.vars ⊆ S'.toFinset)
        (d : Fin ((cookLevinFactorList M n hn2 htb hns).length) →
          List (Fin (n / 3)))
        (hd_elts : ∀ i, ∀ v ∈ d i, v ∈ S')
        (hlen : ∑ i : Fin ((cookLevinFactorList M n hn2 htb hns).length),
            (d i).length ≤ S'.length),
          PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDim_targetRow
              M n hn2 htb hns S' shift d ∈
            PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDim_targetSpan
              M n hn2 htb hns ρ d)

/-- Uniform minimal max-card `NFOfWord` final payload at Step 247 scale.

This is the sharp paper-faithful end surface before direct-transfer maps:
exact witnessed word-assembled local bases, exact finite max-card budget,
total profile budget, and explicit letterwise transfer. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordMaxCardFinalMaps : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordMaxCardFinalMaps
        M n hn2 htb hns)

/-- Uniform direct exact-`NFOfWord` transfer data at Step 247 scale.

This is the focused constructive seam immediately before trace-letter final
payload: it keeps explicit letter-wise local bases for concrete trace generators
and provides the exact transfer of the witnessed `NFOfWord` row into the
assembled total normal-form basis. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordDirectTransferMaps : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordDirectTransferMaps
        M n hn2 htb hns)

/-- Uniform trace-letter basis data at Step 247 scale.

This is the direct source payload for the bounded-trace monoid seam: for each
bounded machine/window instance, provide profile-local letter bases for concrete
trace generators together with the witnessed Leibniz row membership for the
exact normal-form word. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizTraceLetterBasisData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizTraceLetterBasisData
        M n hn2 htb hns)

/-- Uniform bounded-trace local monoid data at Step 247 scale.

Here the finite local monoid is concretely the bounded append-event trace action
used in §9: normal forms are finite endomorphisms of the bounded trace state and
generators append factor-local derivative events. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizBoundedTraceMonoidData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizBoundedTraceMonoidData
        M n hn2 htb hns)

/-- Uniform witnessed Leibniz local-monoid normal forms at Step 247 scale.

This is the paper §9 local-closure surface: the bounded Leibniz product word is
classified by the selected finite local monoid/normal-form alphabet, and row
membership is in the basis for that normal form.  This is deliberately **not**
the singleton event-atom linear span used only as an over-refined diagnostic
frontier below. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizLocalMonoidNormalForms
        M n hn2 htb hns)

/-- Uniform selected profile-template span data at Step 247 scale.

This is the local-monoid/max-card replacement frontier for the failed
singleton event-atom product span: give each selected profile its own
profile-template basis, bounded by `profileTemplateBound`, and prove the
witnessed Leibniz row lies in that selected span. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizProfileTemplateSpanData
        M n hn2 htb hns)

/-- Uniform term-dependent Lemma-31 local-type family at Step247 scale.

This is the paper-faithful interface-anonymous profile surface immediately
below selected profile-template span: for each selected profile, bounded
Leibniz terms are classified by their own local type, and the assembled local
basis is bounded by the selected `profileTemplateBound`.  It is deliberately
term-dependent and profile-selected; no arbitrary-row uniqueness or common
global span is asserted. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceProfileTemplateTermFamilyData
        M n hn2 htb hns)

/-- Uniform selected profile-template span data at Step247 scale.

This is the row-selected version of the profile-template span frontier: the
basis is still profile-local and bounded by `profileTemplateBound`, while the
membership obligation is only for the profile selected by the canonical row. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceSelectedProfileTemplateSpanData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedProfileTemplateSpanData
        M n hn2 htb hns)

/-- Term-dependent selected-profile local-type families instantiate the
selected profile-template span surface by the checked Lemma-31 assembly.

This intentionally targets the selected/row-guarded surface, not the older
all-`ρ` witnessed span package.  The latter is stronger than the paper needs
and would reintroduce the profile-uniform detour we are avoiding. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceSelectedProfileTemplateSpanData_of_profileTemplateTermFamilyData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceSelectedProfileTemplateSpanData := by
  intro M n hn hn2 htb hns
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedProfileTemplateSpanData_of_profileTemplateTermFamilyData
      M n hn2 htb hns
      (Classical.choice (hData M n hn hn2 htb hns))⟩

/-- Uniform Leibniz-term local-type compression at Step247 scale.

This is the paper §9.3/Lemma-31 payload in its term-local form: every bounded
Leibniz product term for the selected canonical row lands in its own selected
local-type space, and the later assembly sums these into the selected
interface-anonymous profile subspace. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceLeibnizLocalTypeCompressionData
        M n hn2 htb hns)

/-- Shifted Leibniz-product membership gives the concrete Lemma-31 local-type
compression datum directly: for every selected interface-anonymous profile use
its explicit compiled-basis profile-template basis, whose size is bounded by
`profileTemplateBound ρ.val`, and place each bounded Leibniz product term in the
corresponding selected local type space. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_shiftedLeibnizProductData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceLeibnizLocalTypeCompressionData_of_shiftedLeibnizProductCompiledBasisProfileData
    M n hn2 htb hns D⟩

/-- Selected profile-template span data gives the Leibniz-term local-type
compression datum by using the selected template basis as the unique local type
for that selected profile. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_selectedProfileTemplateSpanData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceSelectedProfileTemplateSpanData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData := by
  intro M n hn hn2 htb hns
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceLeibnizLocalTypeCompressionData_of_selectedProfileTemplateSpanData
      M n hn2 htb hns
      (Classical.choice (hData M n hn hn2 htb hns))⟩

/-- Term-dependent local-type families give the selected Leibniz-term
compression surface through the checked profile-template assembly. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_profileTemplateTermFamilyData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData :=
  step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_selectedProfileTemplateSpanData
    (step247UniformRouteBPaperFaithfulTPhiSourceSelectedProfileTemplateSpanData_of_profileTemplateTermFamilyData
      hData)

/-- The paired exact-slot + selected-shift-closure bottom seam directly
constructs the term-local Leibniz local-type compression datum.

This records the paper-faithful route at the level of the actual missing
Lemma-31 witness: exact interface slots plus their selected shift closure first
recover the witnessed slot-factorization seam, then the checked local-algebra
and compiled-basis profile adapters instantiate the selected Leibniz local-type
compression surface. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_exactInterfaceSlotFactorizationWithSelectedShiftClosureData
    (hData : Step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData :=
  step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_shiftedLeibnizProductData
    (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData_of_localAlgebraData
      (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData_of_interfaceSlotFactorizationData
        (step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData_of_exactInterfaceSlotFactorizationWithSelectedShiftClosureData
          hData)))

/-- Coherent factor-fiber partitions plus local-algebra data construct the
term-local Leibniz local-type compression witness from the lowest explicit
paper seam.

The factor-fiber payload provides exact interface slots; the coherent
local-algebra payload supplies precisely the selected shift/`mlProj` closure on
those slots.  The resulting paired seam is then routed through the literal
Leibniz local-type compression constructor above. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_fiberPartitionData_and_localAlgebraData
    (hFib : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotFiberPartitionData)
    (hLocal : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        DLoc.sourcePartition = DFib.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DFib := Classical.choice (hFib M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        ∀ w hw, DLoc.profileOfCanonicalWindow w hw = DFib.profileOfCanonicalWindow w hw) :
    Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData :=
  step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_exactInterfaceSlotFactorizationWithSelectedShiftClosureData
    (step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData_of_fiberPartitionData_and_localAlgebraData
      hFib hLocal hPartEq hProfEq)

/-- Total classifier plus local-algebra data construct the term-local Leibniz
local-type compression witness, with coherence stated at the classifier level
rather than after a noncanonical `Nonempty` choice of the derived fibre data. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_classifierData_and_localAlgebraData
    (hCls : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductIndexedInterfaceSlotClassifierData)
    (hLocal : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData)
    (hPartEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DCls := Classical.choice (hCls M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        DLoc.sourcePartition = DCls.sourcePartition)
    (hProfEq :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        let DCls := Classical.choice (hCls M n _hn hn2 htb hns)
        let DLoc := Classical.choice (hLocal M n _hn hn2 htb hns)
        ∀ w hw, DLoc.profileOfCanonicalWindow w hw = DCls.profileOfCanonicalWindow w hw) :
    Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData :=
  step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_exactInterfaceSlotFactorizationWithSelectedShiftClosureData
    (step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData_of_classifierData_and_localAlgebraData
      hCls hLocal hPartEq hProfEq)

/-- Leibniz-term local-type compression assembles to the strict source
`ConstraintType` profile-subspace datum consumed by the `TΦ` P-side bound. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiStrictSourceConstraintTypeProfileSubspaceData_of_sourceLeibnizLocalTypeCompressionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceConstraintTypeProfileSubspaceData
        M n hn2 htb hns := by
  intro M n hn hn2 htb hns
  exact
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceProfileSubspaceData_of_leibnizLocalTypeCompressionData
      M n hn2 htb hns
      (Classical.choice (hData M n hn hn2 htb hns))

/-- Leibniz-term local-type compression transports from strict source
coordinates to the ambient strict `ConstraintType` profile-subspace datum. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData_of_sourceLeibnizLocalTypeCompressionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
        M n hn2 htb hns := by
  intro M n hn hn2 htb hns
  exact
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData_of_sourceProfileSubspaceData
      M n hn2 htb hns
      (step247UniformRouteBPaperFaithfulTPhiStrictSourceConstraintTypeProfileSubspaceData_of_sourceLeibnizLocalTypeCompressionData
        hData M n hn hn2 htb hns)

/-- Uniform Leibniz-term local-type compression closes the strict `TΦ` P-side
rank surface through the selected profile-subspace/sum-over-profiles assembly. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiPSideBound_of_sourceLeibnizLocalTypeCompressionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      SATDeciderGaugePSideBound M n hn2 htb hns
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge
          M n hn2 htb hns) := by
  intro M n hn hn2 htb hns
  exact
    routeBPaperFaithfulTPhi_pSideBound_of_strictConstraintTypeProfileSubspaceData
      M n hn2 htb hns
      (step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData_of_sourceLeibnizLocalTypeCompressionData
        hData M n hn hn2 htb hns)

/-- Full paper-scale SAT contradiction from the term-local Lemma-31 compression
surface, without arbitrary row uniqueness or profile-uniform closure. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_targetPSideBound M n hn hn2 htb hns
      (routeBPaperFaithfulTPhi_targetRank_le_of_ambientGaugePSideBound
        M n hn2 htb hns
        (step247UniformRouteBPaperFaithfulTPhiPSideBound_of_sourceLeibnizLocalTypeCompressionData
          hData M n hn hn2 htb hns))

/-- Full paper-scale SAT contradiction from the concrete selected compiled-basis
profile-template construction for bounded Leibniz product terms. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData
    (hData : Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisProfileData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData
    (step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_shiftedLeibnizProductData
      hData)

/-- Full Route-B closeout from term-dependent selected-profile local-type
families.  This is the intended paper-faithful path:
canonical row/profile selection → term-local type membership → selected
profile subspace → sum over profiles → `TΦ` rank bound. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData
    (step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_of_profileTemplateTermFamilyData
      hData)

/-- Uniform exact-budget profile-template local-monoid normal forms at Step 247
scale.  This exposes the exact Lemma-31-sized budget rather than merely the
coarser `withinProfileBound` budget. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms
        M n hn2 htb hns)

/-- Profile-template span data instantiates the exact-budget profile-template
local-monoid normal-form Step247 surface. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms_of_profileTemplateSpanData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms := by
  intro M n hn hn2 htb hns
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms_of_profileTemplateSpanData
      M n hn2 htb hns
      (Classical.choice (hData M n hn hn2 htb hns))⟩

/-- Exact-budget profile-template local-monoid normal forms forget to the
general local-monoid normal-form Step247 surface. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms_of_profileTemplateLocalMonoidNormalForms
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms := by
  intro M n hn hn2 htb hns
  exact ⟨
    (Classical.choice (hData M n hn hn2 htb hns)).toRouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizLocalMonoidNormalForms⟩

/-- Profile-template span data forgets to the general local-monoid normal-form
Step247 surface through the exact-budget one-element monoid construction. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms_of_profileTemplateSpanData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms :=
  step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms_of_profileTemplateLocalMonoidNormalForms
    (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms_of_profileTemplateSpanData
      hData)

/-- Concrete transition-monoid data instantiates the Step247 local normal-form
surface by taking the witness word to be the flattened transition word. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms_of_localTransitionMonoidData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalTransitionMonoidData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms := by
  intro M n hn hn2 htb hns
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizLocalMonoidNormalForms_of_transitionMonoidData
      M n hn2 htb hns
      (Classical.choice (hData M n hn hn2 htb hns))⟩

/-- Forget fixed-`q` final payload down to budget scaffolding only. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData_of_qDimFinalMaps
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData := by
  intro M n hn hn2 htb hns
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData_of_qDimFinalMaps
      M n hn2 htb hns
      (Classical.choice (hData M n hn hn2 htb hns))⟩

/-- Any fixed-`q` final payload yields the row-witness seam directly. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimRowWitness_of_qDimFinalMaps
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimRowWitness := by
  intro M n hn hn2 htb hns
  exact ⟨
    (Classical.choice (hData M n hn hn2 htb hns)).leibnizWitness_mem_boundedNFOfWordAtomBasis⟩

/-- Any fixed-`q` final payload yields pointwise target-membership witness. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimTargetMembership_of_qDimFinalMaps
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimTargetMembership := by
  intro M n hn hn2 htb hns
  refine ⟨?_⟩
  exact
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDim_targetMembership_of_qDimFinalMaps
      M n hn2 htb hns (Classical.choice (hData M n hn hn2 htb hns))

/-- Fixed-`q` event-atom final maps instantiate max-card final maps. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordMaxCardFinalMaps_of_NFOfWordEventAtomQDimFinalMaps
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordMaxCardFinalMaps := by
  intro M n hn hn2 htb hns
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordMaxCardFinalMaps_of_boundedWordFinalMaps
      M n hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordBoundedWordFinalMaps_of_qFinalMaps
        M n hn2 htb hns
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordBoundedWordQFinalMaps_of_eventBasisQFinalMaps
          M n hn2 htb hns
          (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventBasisQFinalMaps_of_eventMaxQFinalMaps
            M n hn2 htb hns
            (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventMaxQFinalMaps_of_eventAtomQFinalMaps
              M n hn2 htb hns
              (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQFinalMaps_of_qDimFinalMaps
                M n hn2 htb hns
                (Classical.choice (hData M n hn hn2 htb hns)))))))⟩

/-- Max-card final maps instantiate direct exact-`NFOfWord` transfer maps. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordDirectTransferMaps_of_NFOfWordMaxCardFinalMaps
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordMaxCardFinalMaps) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordDirectTransferMaps := by
  intro M n hn hn2 htb hns
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordDirectTransferMaps_of_maxCardFinalMaps
      M n hn2 htb hns
      (Classical.choice (hData M n hn hn2 htb hns))⟩

/-- Row-witness seam implies pointwise target-membership seam. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimTargetMembership_of_rowWitness
    (hRow : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimRowWitness) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimTargetMembership := by
  intro M n hn hn2 htb hns
  refine ⟨?_⟩
  exact PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDim_targetMembership_of_rowWitness
    M n hn2 htb hns (Classical.choice (hRow M n hn hn2 htb hns))

/-- Event-atom budget scaffolding plus pointwise target-membership witness
instantiates fixed-`q` event-atom final maps. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps_of_budgetData_and_targetMembership
    (hBudget : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData)
    (hMem : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimTargetMembership) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps := by
  intro M n hn hn2 htb hns
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps_of_budgetData_and_targetMembership
      M n hn2 htb hns
      (Classical.choice (hBudget M n hn hn2 htb hns))
      (Classical.choice (hMem M n hn hn2 htb hns))⟩

/-- Event-atom budget scaffolding plus row witness instantiates fixed-`q`
event-atom final maps. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps_of_budgetData_and_rowWitness
    (hBudget : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData)
    (hRow : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimRowWitness) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps :=
  step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps_of_budgetData_and_targetMembership
    hBudget
    (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimTargetMembership_of_rowWitness
      hRow)

/-- Direct exact-`NFOfWord` transfer data instantiates the trace-letter payload. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizTraceLetterBasisData_of_NFOfWordDirectTransferMaps
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordDirectTransferMaps) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizTraceLetterBasisData := by
  intro M n hn hn2 htb hns
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizTraceLetterBasisData_of_directNFOfWordTransferMaps
      M n hn2 htb hns
      (Classical.choice (hData M n hn hn2 htb hns))⟩

/-- Trace-letter basis data instantiates bounded-trace monoid data by assembling
normal-form bases from trace-generator letters. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizBoundedTraceMonoidData_of_traceLetterBasisData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizTraceLetterBasisData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizBoundedTraceMonoidData := by
  intro M n hn hn2 htb hns
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizBoundedTraceMonoidData_of_traceLetterBasisData
      M n hn2 htb hns
      (Classical.choice (hData M n hn hn2 htb hns))⟩

/-- Bounded-trace monoid data instantiates the concrete transition-monoid
surface with the finite append-event trace monoid. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalTransitionMonoidData_of_boundedTraceMonoidData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizBoundedTraceMonoidData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalTransitionMonoidData := by
  intro M n hn hn2 htb hns
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizLocalTransitionMonoidData_of_boundedTraceMonoidData
      M n hn2 htb hns
      (Classical.choice (hData M n hn hn2 htb hns))⟩

/-- Bounded-trace monoid data gives the exact local-monoid normal-form Step247
surface.  This packages the concrete choices for `sourceNormalForm`, finite
instances, generators, local bases, budget, and the normal-form row membership. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms_of_boundedTraceMonoidData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizBoundedTraceMonoidData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms :=
  step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms_of_localTransitionMonoidData
    (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalTransitionMonoidData_of_boundedTraceMonoidData
      hData)

/-- Paper-faithful local-monoid normal forms close Route B directly.

The closeout uses the checked `TΦ` chain from witnessed local monoid normal
forms through local-type/profile assembly and the same-target NP lower bound.
No singleton event-atom product-span claim is inserted. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms) :
    NoBoundedSATDeciderAtPaperScale := by
  exact
    PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizLocalMonoidNormalForms
      (fun M n hn hn2 htb hns _hdec =>
        Classical.choice (hData M n hn hn2 htb hns))

/-- Paper-faithful closeout from exact-budget selected-profile local-monoid
normal forms. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms
    (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms_of_profileTemplateLocalMonoidNormalForms
      hData)

/-- Paper-faithful closeout from selected-profile template span data via the
exact-budget one-element local-monoid route. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms
    (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms_of_profileTemplateSpanData
      hData)


/-- Paper-faithful closeout from the concrete bounded-trace monoid surface. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizBoundedTraceMonoidData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizBoundedTraceMonoidData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms
    (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms_of_boundedTraceMonoidData
      hData)

/-- Step247 closeout from fixed-`q` event-atom budget scaffolding plus
pointwise target-membership witness. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetAndTargetMembership
    (hBudget : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData)
    (hMem : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimTargetMembership) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizBoundedTraceMonoidData
    (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizBoundedTraceMonoidData_of_traceLetterBasisData
      (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizTraceLetterBasisData_of_NFOfWordDirectTransferMaps
        (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordDirectTransferMaps_of_NFOfWordMaxCardFinalMaps
          (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordMaxCardFinalMaps_of_NFOfWordEventAtomQDimFinalMaps
            (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps_of_budgetData_and_targetMembership
              hBudget hMem)))))

/-- Step247 closeout from fixed-`q` event-atom budget scaffolding plus row
witness.

This is the tight constructive no-shortcut target currently exposed: once
uniform budget data and uniform row witness are provided at the `q`-dim
event-atom seam, the checked adapter chain reaches bounded-trace local monoid
normal forms and closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetAndRowWitness
    (hBudget : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData)
    (hRow : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimRowWitness) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetAndTargetMembership
    hBudget
    (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimTargetMembership_of_rowWitness
      hRow)

/-- Step247 closeout from fixed-`q` event-atom final maps via budget+row
extraction. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps_via_budgetAndRowWitness
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetAndRowWitness
    (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData_of_qDimFinalMaps
      hData)
    (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimRowWitness_of_qDimFinalMaps
      hData)


/-- Uniform sufficient exact-profile template-collapse data at Step 247 scale.

This is a checked sufficient route (not the primary frontier): if each bounded
instance provides exact-profile template-collapse payload for the witnessed
Leibniz word, the paper-faithful strict `TΦ` closeout follows. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizExactProfileTemplateCollapseData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizExactProfileTemplateCollapseData
        M n hn2 htb hns)

/-- Step247 closeout through the sufficient exact-profile template-collapse
route. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizExactProfileTemplateCollapseData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizExactProfileTemplateCollapseData) :
    NoBoundedSATDeciderAtPaperScale := by
  exact
    PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_paperRouteB_exactProfileTemplateCollapse
      (fun M n hn hn2 htb hns _hdec =>
        Classical.choice (hData M n hn hn2 htb hns))

/-- Exact-profile template-collapse data constructs the Route-B Lemma-31
selected profile-template span seam uniformly at Step247 scale. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData_of_exactProfileTemplateCollapseData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizExactProfileTemplateCollapseData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizProfileTemplateSpanData_of_exactProfileTemplateCollapseData
    M n hn2 htb hns D⟩

/-- Paper-faithful Lemma-31 closeout routed through exact-profile
template-collapse data. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizExactProfileTemplateCollapseData_via_profileTemplateSpan
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizExactProfileTemplateCollapseData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData
    (step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateSpanData_of_exactProfileTemplateCollapseData
      hData)

/-- Step247-uniform canonical-row exact-profile template-collapse seam.

This is the directly available lower-level sufficient object in the current
library (it carries the decider hypothesis explicitly). -/
def Step247UniformRouteBPaperFaithfulTPhiSourceCanonicalRowExactProfileTemplateCollapseData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceCanonicalRowExactProfileTemplateCollapseData
        M n hn2 htb hns)

/-- Canonical-row exact-profile template-collapse closes Route B at Step247
scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceCanonicalRowExactProfileTemplateCollapseData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceCanonicalRowExactProfileTemplateCollapseData) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceCanonicalRowExactProfileTemplateCollapseData
    (fun M n hn hn2 htb hns hdec =>
      Classical.choice (hData M n hn hn2 htb hns hdec))

/-- Step247-uniform source local-monoid generator-maps seam.

This is the minimal additional uniformity layer needed to pass from
term-level local typing to the strict classifier route: profile-local
**derivative-row** type maps are provided directly (paper-faithful selected-row
surface), then promoted to the source local-monoid classifier by existing
`Paper283` constructors. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidGeneratorMapsData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceLocalMonoidGeneratorMaps
        M n hn2 htb hns)

/-- Step247-uniform source local-monoid classifier seam (paper Lemma-31
algebra-facing frontier). -/
def Step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidClassifierData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceLocalMonoidClassifier
        M n hn2 htb hns)

/-- Step247-uniform source local-type compression seam.

This is the same selected-row algebraic object as the local-monoid classifier,
but stated in the older `source canonical derivative row` packaging.  The
Paper283 bridge rewrites that row to the restricted-factor product. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceLocalTypeCompressionData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceLocalTypeCompressionData
        M n hn2 htb hns)

/-- Source local-type compression data yields the source local-monoid classifier
seam by the checked restricted-factor row identity. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidClassifierData_of_sourceLocalTypeCompressionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLocalTypeCompressionData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidClassifierData := by
  intro M n hn hn2 htb hns hdec
  rcases hData M n hn hn2 htb hns hdec with ⟨D⟩
  exact
    ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceLocalMonoidClassifier_of_sourceLocalTypeCompressionData
      M n hn2 htb hns D⟩

/-- The source local-monoid classifier seam closes Route B at Step247 scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidClassifierData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidClassifierData) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceLocalMonoidClassifier
    (fun M n hn hn2 htb hns hdec =>
      Classical.choice (hData M n hn hn2 htb hns hdec))

/-- Step247-uniform literal source canonical row-span data.

This is the manuscript Lemma-32 surface in source coordinates: after canonical
window/profile selection, `V_h` is literally the span of selected canonical
source rows with profile `h`, and the only remaining content is the
within-profile finite-dimensional bound on those row spans. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceCanonicalProfileRowSpanData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceCanonicalProfileRowSpanData
        M n hn2 htb hns)

/-- Source local-type compression proves the literal source canonical row-span
bound.

The proof is the concrete Lemma-31→Lemma-32 assembly already checked in
Paper283: every selected row lands in its selected compressed local-type space,
so the literal selected row span injects into a finite basis of size
`withinProfileBound`. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceCanonicalProfileRowSpanData_of_sourceLocalTypeCompressionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLocalTypeCompressionData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceCanonicalProfileRowSpanData := by
  intro M n hn hn2 htb hns hdec
  rcases hData M n hn hn2 htb hns hdec with ⟨D⟩
  exact
    ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceCanonicalProfileRowSpanData_of_sourceLocalTypeCompressionData
      M n hn2 htb hns D⟩

/-- Literal source canonical row-span data closes Route B at Step247 scale.

This is the row-span/profile route directly: canonical row spans give selected
source profile subspaces, rank monotonicity transports through strict `TΦ`, and
the SAT-decider-specific lower bound fires on the extracted coupled sheet. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceCanonicalProfileRowSpanData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceCanonicalProfileRowSpanData) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceCanonicalProfileRowSpanData
    (fun M n hn hn2 htb hns hdec =>
      Classical.choice (hData M n hn hn2 htb hns hdec))

/-- Route-B closeout through source local-type compression data, explicitly
routed via the literal canonical row-span/profile bound. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceLocalTypeCompressionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLocalTypeCompressionData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceCanonicalProfileRowSpanData
    (step247UniformRouteBPaperFaithfulTPhiSourceCanonicalProfileRowSpanData_of_sourceLocalTypeCompressionData
      hData)

/-- One-shot assembly of the actual Lemma-31 term-local proof into the literal
source local-type row-compression surface.

The term-level local-type datum owns each bounded Leibniz summand.  Paper283
already proves the finite Leibniz expansion/linearity step, giving the selected
source profile subspace for the whole canonical derivative row; we then choose a
finite basis of that selected `V_h` and package it as a one-type local alphabet.
This is the honest one-shot move from term-local Lemma 31 to the literal
canonical-row `V_h` statement. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceLocalTypeCompressionData_of_sourceLeibnizLocalTypeCompressionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceLocalTypeCompressionData := by
  intro M n hn hn2 htb hns _hdec
  let Dleib := Classical.choice (hData M n hn hn2 htb hns)
  let Dprofile :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceProfileSubspaceData_of_leibnizLocalTypeCompressionData
      M n hn2 htb hns Dleib
  let Dinterface :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceInterfaceProfileData_of_sourceProfileSubspaceData
      M n hn2 htb hns Dprofile
  exact
    ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceLocalTypeCompressionData_of_sourceInterfaceProfileData
      M n hn2 htb hns Dinterface⟩

/-- One-shot Route-B closeout from term-local Lemma-31 compression, explicitly
through the literal source local-type and canonical row-span surfaces. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData_via_sourceLocalTypeCompression
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceLocalTypeCompressionData
    (step247UniformRouteBPaperFaithfulTPhiSourceLocalTypeCompressionData_of_sourceLeibnizLocalTypeCompressionData
      hData)

/-- Generator-maps data yields the source local-monoid classifier seam. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidClassifierData_of_sourceLocalMonoidGeneratorMapsData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidGeneratorMapsData) :
    Step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidClassifierData := by
  intro M n hn hn2 htb hns hdec
  rcases hData M n hn hn2 htb hns hdec with ⟨G⟩
  exact
    ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceLocalMonoidClassifier_of_generatorMaps
      M n hn2 htb hns G⟩

/-- Route-B closeout through the explicit source generator-maps seam. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidGeneratorMapsData
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidGeneratorMapsData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidClassifierData
    (step247UniformRouteBPaperFaithfulTPhiSourceLocalMonoidClassifierData_of_sourceLocalMonoidGeneratorMapsData
      hData)

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

/-- A concrete decomposition of the ambient quotient/rank bridge:
from placed local expansion, recover the canonical-interface expansion surface.
Combined with the checked canonical→placed-quotient adapter, this yields the
ambient quotient soundness implication. -/
def Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaCanonicalInterfaceExpansionData : Prop :=
  Step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData →
    Step247UniformRouteBPaperFaithfulTPhiCanonicalInterfaceExpansionData

/-- Finer decomposition surface (part 1): from placed expansion, build renamed
local-chart expansion data. -/
def Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaRenamedLocalChartExpansionData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowRenamedLocalChartExpansionData
        M n hn2 htb hns)

/-- A renamed-canonical interface expansion directly instantiates renamed
local-chart expansion data by reading row slots as renamed canonical slots. -/
noncomputable def routeBPaperFaithfulTPhi_strictSourceSelectedRowRenamedLocalChartExpansionData_of_renamedCanonicalInterfaceExpansionData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowRenamedCanonicalInterfaceExpansionData
      M n hn2 htb hns) :
    PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowRenamedLocalChartExpansionData
      M n hn2 htb hns where
  rowExpansionData :=
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedRowInterfaceSlotExpansionData_of_renamedCanonicalInterfaceExpansionData
      M n hn2 htb hns D
  rowExpansionCanonicalSlot := D.rowExpansionCanonicalSlot
  rowExpansionChartMap := D.rowExpansionChartMap
  rowExpansionSlot_transport_to_renamedCanonicalChart := by
    intro ρ S' shift α hSlen hshiftDegree hshiftVars hadm hrow hρ t σ j
    rfl

/-- Existing uniform renamed-canonical expansion data supplies the finer
uniform renamed-local-chart expansion surface. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaRenamedLocalChartExpansionData_of_renamedCanonicalInterfaceExpansionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiRenamedCanonicalInterfaceExpansionData) :
    Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaRenamedLocalChartExpansionData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact
    ⟨routeBPaperFaithfulTPhi_strictSourceSelectedRowRenamedLocalChartExpansionData_of_renamedCanonicalInterfaceExpansionData
      M n hn2 htb hns D⟩

/-- Canonical-interface expansion also supplies the renamed-local-chart surface
through the identity-chart renamed-canonical adapter. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaRenamedLocalChartExpansionData_of_canonicalInterfaceExpansionData
    (hData : Step247UniformRouteBPaperFaithfulTPhiCanonicalInterfaceExpansionData) :
    Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaRenamedLocalChartExpansionData :=
  step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaRenamedLocalChartExpansionData_of_renamedCanonicalInterfaceExpansionData
    (step247UniformRouteBPaperFaithfulTPhiRenamedCanonicalInterfaceExpansionData_of_canonicalInterfaceExpansionData
      hData)

/-- Finer decomposition surface (part 2): provide local-chart transport data
for each renamed-local expansion witness. -/
def Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessChartTrivialityData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowRenamedLocalChartExpansionData
      M n hn2 htb hns),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowLocalChartTransportExpansionData
        M n hn2 htb hns)

/-- Concrete chart-map identity seam (packaged form): this is the same witness
surface as chart-triviality, named to track the remaining explicit chart step. -/
def Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessChartMapIdentityOnCanonicalSlotsData : Prop :=
  Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessChartTrivialityData

/-- Packaged chart-map identity immediately yields chart-triviality witnesses. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessChartTrivialityData_of_chartMapIdentityOnCanonicalSlotsData
    (hId : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessChartMapIdentityOnCanonicalSlotsData) :
    Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessChartTrivialityData :=
  hId

/-- Weaker chart-transport seam: only the chosen renamed-local witness at each
`(M,n,...)` needs transport data (rather than all possible witnesses). -/
def Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessChartTrivialityAlongRenamedLocalChartData
    (hRenamed : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaRenamedLocalChartExpansionData) : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    let D := Classical.choice (hRenamed M n _hn hn2 htb hns)
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowLocalChartTransportExpansionData
        M n hn2 htb hns)

/-- Renamed-local expansion plus transport data yields the
`placed-expansion -> canonical-interface-expansion` bridge. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaCanonicalInterfaceExpansionData_of_renamedLocalChartData
    (hRenamed : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaRenamedLocalChartExpansionData)
    (hChart : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessChartTrivialityData) :
    Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaCanonicalInterfaceExpansionData := by
  intro _
  intro M n hn hn2 htb hns
  rcases hRenamed M n hn hn2 htb hns with ⟨D⟩
  let Dtransport := Classical.choice (hChart M n hn hn2 htb hns D)
  exact
    ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedRowCanonicalInterfaceExpansionData_of_localChartTransportExpansionData
      M n hn2 htb hns Dtransport⟩

/-- Variant using the weaker along-chosen-witness chart-transport seam. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaCanonicalInterfaceExpansionData_of_renamedLocalChartDataAlong
    (hRenamed : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaRenamedLocalChartExpansionData)
    (hChart : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessChartTrivialityAlongRenamedLocalChartData hRenamed) :
    Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaCanonicalInterfaceExpansionData := by
  intro _
  intro M n hn hn2 htb hns
  let D := Classical.choice (hRenamed M n hn hn2 htb hns)
  let Dtransport := Classical.choice (hChart M n hn hn2 htb hns)
  exact
    ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedRowCanonicalInterfaceExpansionData_of_localChartTransportExpansionData
      M n hn2 htb hns Dtransport⟩

/-- Ambient quotient/rank soundness for the placed local-interface expansion.

This is the precise remaining bridge if one replaces the false fixed raw chart
claim by a genuine quotient-normalisation step: from the placed local expansion,
produce the already checked `PlacedQuotientDescentData` consumed by the Route B
rank chain.  Keeping this as a named implication prevents silently smuggling in
ambient selected-chart equality. -/
def Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessData : Prop :=
  Step247UniformRouteBPaperFaithfulTPhiPlacedExpansionData →
    Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData

/-- If the placed expansion can be promoted to canonical-interface expansion,
the ambient quotient/rank soundness bridge follows by the existing checked
canonical→placed-quotient adapter. -/
theorem step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessData_of_viaCanonicalInterfaceExpansionData
    (hVia : Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessViaCanonicalInterfaceExpansionData) :
    Step247UniformRouteBPaperFaithfulTPhiAmbientQuotientSoundnessData := by
  intro hExpansion
  exact
    step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData_of_canonicalInterfaceExpansionData
      (hVia hExpansion)

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
