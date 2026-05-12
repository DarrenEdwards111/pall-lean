import PallLean.Paper93.DeepMath.PathB.SATPathBChain

/-!
# Archived singleton event-atom fixed-q seam

This file archives the over-refined singleton event-atom `QDim` route.  It is
kept for reference only and is deliberately outside the active Route B closure
path.  The active paper-faithful closure seam is the §9 witnessed Leibniz
local-monoid normal-form surface in
`Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms`.
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


/-! ## Archived Step247 singleton event-atom surface -/

/-- Uniform fixed-`q` singleton event-atom budget data at Step 247 scale.

This is the bookkeeping half of the strict-source local Cook--Levin seam:
profile selector, finite budgets, and atom-to-total-normal-form embedding,
without the hard row-membership obligation. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData
        M n hn2 htb hns)

/-- Uniform fixed-`q` singleton event-atom `NFOfWord` data at Step 247 scale.

This is the currently most atomic strict-source local Cook--Levin algebra
surface: concrete singleton event atoms and the exact bounded-word-length
`q` local dimension budget. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalMaps : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps
        M n hn2 htb hns)

/-- Uniform fixed-`q` builder from budget scaffolds to full final payloads.

This isolates the single remaining hard local-algebra obligation after the seam
split. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData
      M n hn2 htb hns →
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps
        M n hn2 htb hns)

/-- Uniform target-row membership statement at the fixed-`q` event-atom frontier. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimTargetMembership : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    ∀ (ρ : PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictInterfaceAnonymousProfiles
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
          M n hn2 htb hns ρ d

/-- Uniform hard row-membership witness at the fixed-`q` event-atom frontier. -/
def Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimRowWitness : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordEventAtomQDimRowWitness
      M n hn2 htb hns

/-- Target-membership data implies the fixed-`q` row witness. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimRowWitness_of_targetMembership
    (hTarget : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimTargetMembership) :
    Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimRowWitness := by
  intro M n hn hn2 htb hns
  exact PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDim_rowWitness_of_targetMembership
    M n hn2 htb hns (hTarget M n hn hn2 htb hns)

/-- At Step247 scale, fixed-`q` row-witness and target-membership frontiers are
logically equivalent instance-by-instance. -/
theorem step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimRowWitness_iff_targetMembership
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordEventAtomQDimRowWitness
      M n hn2 htb hns) ↔
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
          M n hn2 htb hns ρ d) :=
  PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDim_rowWitness_iff_targetMembership
    M n hn2 htb hns

/-- Any Step247 fixed-`q` final payload yields the corresponding budget scaffold. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData_of_finalMaps
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalMaps) :
    Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData_of_qDimFinalMaps
    M n hn2 htb hns D⟩

/-- Any Step247 fixed-`q` final payload induces target-row membership data. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimTargetMembership_of_finalMaps
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalMaps) :
    Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimTargetMembership := by
  intro M n hn hn2 htb hns
  rcases hData M n hn hn2 htb hns with ⟨D⟩
  exact
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDim_targetMembership_of_qDimFinalMaps
      M n hn2 htb hns D

/-- Any Step247 fixed-`q` final payload induces a budget-to-final builder. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder_of_finalMaps
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalMaps) :
    Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder := by
  intro M n hn hn2 htb hns D
  exact hData M n hn hn2 htb hns

/-- Budget scaffolds plus a uniform row witness assemble the fixed-`q` final
builder directly. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder_of_budgetData_and_rowWitness
    (hRow : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimRowWitness) :
    Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder := by
  intro M n hn hn2 htb hns D
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps_of_budgetData
      M n hn2 htb hns D (hRow M n hn hn2 htb hns)
  ⟩

/-- Budget scaffolds plus uniform target-membership data assemble the fixed-`q`
final builder directly. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder_of_budgetData_and_targetMembership
    (hTarget : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimTargetMembership) :
    Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder := by
  intro M n hn hn2 htb hns D
  exact ⟨
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps_of_budgetData_and_targetMembership
      M n hn2 htb hns D (hTarget M n hn hn2 htb hns)
  ⟩

/-- Instance-level equivalence: fixed-`q` final payloads are exactly budget
scaffolds plus target-membership data. -/
theorem step247RouteBPaperFaithfulTPhiSourceEventAtomQDimFinalMaps_iff_budget_and_targetMembership
    (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps
        M n hn2 htb hns)) ↔
    (Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData
        M n hn2 htb hns)
      ∧
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
            M n hn2 htb hns ρ d)) := by
  constructor
  · intro hFinal
    rcases hFinal with ⟨D⟩
    refine ⟨?_, ?_⟩
    · exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData_of_qDimFinalMaps
        M n hn2 htb hns D⟩
    · exact PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDim_targetMembership_of_qDimFinalMaps
        M n hn2 htb hns D
  · intro h
    rcases h with ⟨hBudget, hTarget⟩
    rcases hBudget with ⟨B⟩
    exact ⟨PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps_of_budgetData_and_targetMembership
      M n hn2 htb hns B hTarget⟩



/-! ## Archived SAT closeout adapters for singleton event atoms -/

/-- Fixed-`q` singleton event-atom budget seam.

This is the bookkeeping half of the local-algebra target: finite bounds and
basis embedding only, with no row-membership closure claim. -/
theorem SAT_path_B_paperFaithfulSourceEventAtomQDimBudgetData_fromFinalMaps
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalMaps) :
    Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData :=
  step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData_of_finalMaps
    hData

/-- Fixed-`q` singleton event-atom seam from split budget plus an explicit
final-map builder.

This keeps the seam split honest: budget bookkeeping is supplied separately,
and the remaining constructor obligation is isolated as a builder from each
budget payload to a full fixed-`q` final payload. -/
theorem SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_fromBudgetAndBuilder_TPhi_extraction_move
    (hBudget : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData)
    (hBuild : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps
    (fun M n hn hn2 htb hns hdec =>
      let D := Classical.choice (hBudget M n hn hn2 htb hns)
      Classical.choice (hBuild M n hn hn2 htb hns D))

/-- Fixed-`q` singleton event-atom closeout routed through the explicit
uniform target-membership frontier. -/
theorem SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_viaTargetMembership_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalMaps) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_fromBudgetAndBuilder_TPhi_extraction_move
    (step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData_of_finalMaps hData)
    (step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder_of_budgetData_and_targetMembership
      (step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimTargetMembership_of_finalMaps hData))

/-- Fixed-`q` singleton event-atom closeout directly from split budget plus
uniform target-row membership. -/
theorem SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_fromBudgetAndTargetMembership_TPhi_extraction_move
    (hBudget : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData)
    (hTarget : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimTargetMembership) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_fromBudgetAndBuilder_TPhi_extraction_move
    hBudget
    (step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder_of_budgetData_and_targetMembership
      hTarget)

/-- Fixed-`q` singleton event-atom closeout directly from split budget plus
uniform row-membership witness. -/
theorem SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_fromBudgetAndRowWitness_TPhi_extraction_move
    (hBudget : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimBudgetData)
    (hRow : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimRowWitness) :
    NoBoundedSATDeciderAtPaperScale :=
  SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_fromBudgetAndBuilder_TPhi_extraction_move
    hBudget
    (step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalBuilder_of_budgetData_and_rowWitness
      hRow)

/-- Fixed-`q` singleton event-atom `NFOfWord` seam.

This is the currently most atomic exposed Cook--Levin local-algebra target: the
basis letters are the concrete singleton derivative atoms, the local dimension
is the actual bounded-word length `q`, and the remaining row proof is exact
membership of the witnessed product-rule row in that folded atom basis. -/
theorem SAT_path_B_paperFaithfulSourceEventAtomQDimFinalMaps_TPhi_extraction_move
    (hData : Step247UniformRouteBPaperFaithfulTPhiSourceEventAtomQDimFinalMaps) :
    NoBoundedSATDeciderAtPaperScale :=
  PallLean.Paper93.Paper283.noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDimFinalMaps
    (fun M n hn hn2 htb hns hdec =>
      Classical.choice (hData M n hn hn2 htb hns))


end PallLean.Paper93.DeepMath.PathB
