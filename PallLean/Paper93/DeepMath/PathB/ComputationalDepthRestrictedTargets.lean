import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFinalLowerBoundTarget

/-
# Restricted computational-depth targets

This file starts the honest "smaller target" attack after the final
computational-depth lower-bound target was isolated.

The point is deliberately asymmetric:

* bounded treewidth / low-rank / bounded-overlap fragments are expected to be
  SHALLOW once a concrete DP/enumeration compiler is supplied;
* bounded clause width alone is not a smaller target, since 3-SAT already has
  bounded width;
* MKtP/MCSP-style lower bounds remain the metacomplexity frontier.

No P-vs-NP lower bound is asserted here.  The file gives the reusable restricted
socket: for a syntactic class `R : CNF -> Prop`, define restricted shallow/deep
search and prove the same verifier/guard lemmas as in the full SAT layer.
Concrete future work should instantiate `R` with e.g. bounded-treewidth CNF or
low-rank incidence CNF and then provide an actual search compiler.
-/

namespace SATDepthMachine

/-! ## Restricted search/decision sockets -/

/-- Search correctness restricted to formulas satisfying `R`. -/
def RestrictedSearchCorrect
    (U : MachineModel) (R : CNF -> Prop) (M : SearchMachine U) : Prop :=
  ∀ φ : CNF, R φ -> Satisfiable φ ->
    ∃ a : RawAssignment, U.searchRun M.code φ = some a ∧ Satisfies φ a

/-- Shallow search on a restricted formula class. -/
def RestrictedShallowSearch
    (U : MachineModel) (R : CNF -> Prop) : Prop :=
  ∃ M : SearchMachine U, RestrictedSearchCorrect U R M

/-- Deep search on a restricted formula class.  For easy classes this should be
false; for hard explicit classes it is the real lower-bound target. -/
def RestrictedDeepSearch
    (U : MachineModel) (R : CNF -> Prop) : Prop :=
  ¬ RestrictedShallowSearch U R

/-- Decision correctness restricted to formulas satisfying `R`. -/
def RestrictedDecidesSAT
    (U : MachineModel) (R : CNF -> Prop) (M : DecisionMachine U) : Prop :=
  ∀ φ : CNF, R φ -> (U.decisionRun M.code φ = true ↔ Satisfiable φ)

/-- Polynomial-time decision on a restricted formula class. -/
def RestrictedSATDecisionInP
    (U : MachineModel) (R : CNF -> Prop) : Prop :=
  ∃ M : DecisionMachine U, RestrictedDecidesSAT U R M

/-- Easy direction survives restriction: restricted shallow search gives a
restricted decider by verifying the proposed witness. -/
theorem restrictedDecider_of_restrictedShallowSearch
    (U : MachineModel) (R : CNF -> Prop)
    (h : RestrictedShallowSearch U R) :
    RestrictedSATDecisionInP U R := by
  rcases h with ⟨M, hM⟩
  let D : DecisionMachine U := {
    code := U.verifierCode M.code
    budget := M.budget
    polyBudget := M.polyBudget
    steps_le_budget := by
      intro φ
      rw [U.verifier_steps]
      exact M.steps_le_budget φ
  }
  refine ⟨D, ?_⟩
  intro φ hR
  change U.decisionRun (U.verifierCode M.code) φ = true ↔ Satisfiable φ
  rw [U.verifier_run]
  rw [checkSearchOutput_true_iff]
  constructor
  · intro hgood
    rcases hgood with ⟨a, _hrun, hsat⟩
    exact ⟨a, hsat⟩
  · intro hsat
    exact hM φ hR hsat

/-- A particular restricted search machine fails on some satisfiable formula in
`R`. -/
def RestrictedSearchMachineFails
    (U : MachineModel) (R : CNF -> Prop) (M : SearchMachine U) : Prop :=
  ∃ φ : CNF,
    R φ ∧ Satisfiable φ ∧
      ¬ ∃ a : RawAssignment,
        U.searchRun M.code φ = some a ∧ Satisfies φ a

/-- Negating restricted correctness is exactly a restricted failing instance. -/
theorem not_restrictedSearchCorrect_iff_fails
    (U : MachineModel) (R : CNF -> Prop) (M : SearchMachine U) :
    ¬ RestrictedSearchCorrect U R M ↔
      RestrictedSearchMachineFails U R M := by
  classical
  constructor
  · intro hnot
    by_contra hnofail
    apply hnot
    intro φ hR hsat
    by_contra hnowitness
    exact hnofail ⟨φ, hR, hsat, hnowitness⟩
  · intro hfail hcorrect
    rcases hfail with ⟨φ, hR, hsat, hnowitness⟩
    exact hnowitness (hcorrect φ hR hsat)

/-- Restricted depth is exactly: every restricted search machine fails on some
satisfiable formula in the restricted class. -/
theorem restrictedDeepSearch_iff_forall_fails
    (U : MachineModel) (R : CNF -> Prop) :
    RestrictedDeepSearch U R ↔
      ∀ M : SearchMachine U, RestrictedSearchMachineFails U R M := by
  constructor
  · intro hdeep M
    exact (not_restrictedSearchCorrect_iff_fails U R M).mp
      (by
        intro hcorrect
        exact hdeep ⟨M, hcorrect⟩)
  · intro hfail hshallow
    rcases hshallow with ⟨M, hcorrect⟩
    exact ((not_restrictedSearchCorrect_iff_fails U R M).mpr (hfail M))
      hcorrect

/-! ## Concrete syntactic classes to attack -/

/-- Clause-width restriction.  This alone is not a smaller lower-bound target:
3-SAT already lies at constant width. -/
def ClauseWidthAtMost (k : Nat) (φ : CNF) : Prop :=
  ∀ c : Clause, c ∈ φ.clauses -> c.length ≤ k

abbrev ThreeCNF (φ : CNF) : Prop := ClauseWidthAtMost 3 φ

/-- Bounded treewidth placeholder.  A future file should replace this interface
by an actual primal/incidence graph plus tree-decomposition certificate. -/
structure BoundedTreewidthCertificate (w : Nat) (φ : CNF) : Prop where
  certified : True

/-- Bounded-treewidth CNF class.  Expected direction: shallow by dynamic
programming once a concrete compiler is supplied. -/
def BoundedTreewidthCNF (w : Nat) (φ : CNF) : Prop :=
  Nonempty (BoundedTreewidthCertificate w φ)

/-- Low-rank incidence placeholder.  The intended concrete rank is the rank of
the signed variable/clause incidence matrix, or an equivalent compressed
signature map. -/
structure LowRankIncidenceCertificate (r : Nat) (φ : CNF) : Prop where
  certified : True

/-- Low-rank incidence CNF class.  Expected direction: shallow by enumerating
compressed signatures when `r = O(log n)` or otherwise small enough. -/
def LowRankIncidenceCNF (r : Nat) (φ : CNF) : Prop :=
  Nonempty (LowRankIncidenceCertificate r φ)

/-- Bounded-overlap placeholder for the depth-2-threshold/TC0-inspired attack:
shared-variable structure is the real algorithmic cost knob. -/
structure BoundedOverlapCertificate (b : Nat) (φ : CNF) : Prop where
  certified : True

/-- Bounded-overlap CNF class.  Expected direction: shallow by conditioning on
shared variables / bag separators when `b = O(log n)`. -/
def BoundedOverlapCNF (b : Nat) (φ : CNF) : Prop :=
  Nonempty (BoundedOverlapCertificate b φ)

/-! ## Algorithm certificates for easy-side fragments -/

/-- A concrete restricted search algorithm for a class `R` in machine model `U`.
Supplying this is the correct way to prove that a fragment is K^poly-shallow. -/
structure RestrictedSearchAlgorithm
    (U : MachineModel) (R : CNF -> Prop) where
  machine : SearchMachine U
  correct : RestrictedSearchCorrect U R machine

/-- Any certified restricted algorithm gives restricted shallow search. -/
theorem restrictedShallowSearch_of_algorithm
    (U : MachineModel) (R : CNF -> Prop)
    (A : RestrictedSearchAlgorithm U R) :
    RestrictedShallowSearch U R :=
  ⟨A.machine, A.correct⟩

/-- Bounded treewidth is an easy-side target: once a DP compiler is provided,
it yields restricted shallow search. -/
theorem boundedTreewidth_shallow_of_dpAlgorithm
    (U : MachineModel) (w : Nat)
    (A : RestrictedSearchAlgorithm U (BoundedTreewidthCNF w)) :
    RestrictedShallowSearch U (BoundedTreewidthCNF w) :=
  restrictedShallowSearch_of_algorithm U (BoundedTreewidthCNF w) A

/-- Low-rank incidence is an algorithmic target: once a compressed-signature
enumerator is provided, it yields restricted shallow search. -/
theorem lowRankIncidence_shallow_of_signatureAlgorithm
    (U : MachineModel) (r : Nat)
    (A : RestrictedSearchAlgorithm U (LowRankIncidenceCNF r)) :
    RestrictedShallowSearch U (LowRankIncidenceCNF r) :=
  restrictedShallowSearch_of_algorithm U (LowRankIncidenceCNF r) A

/-- Bounded overlap is an algorithmic target: once a separator/conditioning
algorithm is provided, it yields restricted shallow search. -/
theorem boundedOverlap_shallow_of_conditioningAlgorithm
    (U : MachineModel) (b : Nat)
    (A : RestrictedSearchAlgorithm U (BoundedOverlapCNF b)) :
    RestrictedShallowSearch U (BoundedOverlapCNF b) :=
  restrictedShallowSearch_of_algorithm U (BoundedOverlapCNF b) A

/-! ## Distributional and metacomplexity sockets -/

/-- A finite distribution is represented only by its support predicate here.
Future average-case files can add weights/probabilities. -/
structure FormulaDistribution where
  support : CNF -> Prop

/-- Average-case/random-SAT attacks should first restrict to the distributional
support.  A true average-case lower bound needs probability mass, not merely
support, so this is intentionally only the first socket. -/
def DistributionSupportClass (D : FormulaDistribution) : CNF -> Prop :=
  D.support

/-- Toy time-bounded description predicate for the MCSP/MKtP continuation.
`object`, `program`, and `evalsWithin` are abstract on purpose: concrete future
files can instantiate them with truth tables, universal machines, or SAT-search
maps. -/
structure KtDescriptionProblem where
  Object : Type
  Program : Type
  size : Program -> Nat
  evalsWithin : Program -> Nat -> Object -> Prop

/-- An object has a description of size at most `s` within time/budget `t`. -/
def HasKtDescription
    (K : KtDescriptionProblem) (x : K.Object) (s t : Nat) : Prop :=
  ∃ p : K.Program, K.size p ≤ s ∧ K.evalsWithin p t x

/-- Toy lower-bound target for explicit objects.  Counting can prove existence
of hard objects for finite universes; explicit instances are the real frontier. -/
def ExplicitKtLowerBound
    (K : KtDescriptionProblem) (x : K.Object) (s t : Nat) : Prop :=
  ¬ HasKtDescription K x s t

/-- Counting-style lower bound socket: if no small program describes `x`, then
`x` has the corresponding explicit Kt lower bound.  This is tautological, but it
fixes the target shape for future finite counting lemmas. -/
theorem explicitKtLowerBound_of_no_description
    (K : KtDescriptionProblem) (x : K.Object) (s t : Nat)
    (h : ¬ HasKtDescription K x s t) :
    ExplicitKtLowerBound K x s t :=
  h

/-! ## Kernel-only axiom trace -/

#print axioms restrictedDecider_of_restrictedShallowSearch
#print axioms not_restrictedSearchCorrect_iff_fails
#print axioms restrictedDeepSearch_iff_forall_fails
#print axioms restrictedShallowSearch_of_algorithm
#print axioms boundedTreewidth_shallow_of_dpAlgorithm
#print axioms lowRankIncidence_shallow_of_signatureAlgorithm
#print axioms boundedOverlap_shallow_of_conditioningAlgorithm
#print axioms explicitKtLowerBound_of_no_description

end SATDepthMachine
