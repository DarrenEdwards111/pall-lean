import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMachineSemantics
import Mathlib.Tactic

/-
# SAT decision-to-search self-reduction, semantic core

`ComputationalDepthMachineSemantics.lean` isolated the missing converse

  SAT decision in P -> shallow SAT search.

This file proves the real mathematical core of that converse: a prefix
satisfiability oracle lets one reconstruct a satisfying assignment bit by bit.

What remains outside this file is the compiler/accounting layer:

* reduce a prefix query `(φ, p)` to an ordinary CNF SAT query in the chosen
  encoding; and
* compile the resulting adaptive oracle procedure into the repository's coded
  machine model with a polynomial step bound.

No lower bound is asserted here.
-/

namespace SATDepthMachine

/-! ## Prefix-satisfiability semantics -/

/-- `a` extends prefix `p`. -/
def ExtendsPrefix (p a : RawAssignment) : Prop :=
  ∃ s : RawAssignment, a = p ++ s

/-- `φ` has a satisfying assignment extending prefix `p`. -/
def SatisfiableWithPrefix (φ : CNF) (p : RawAssignment) : Prop :=
  ∃ a : RawAssignment, Satisfies φ a ∧ ExtendsPrefix p a

/-- A semantic prefix oracle is correct when it answers exactly whether a
satisfying assignment extending the prefix exists. -/
def PrefixOracleCorrect (Q : CNF -> RawAssignment -> Bool) : Prop :=
  ∀ (φ : CNF) (p : RawAssignment),
    Q φ p = true ↔ SatisfiableWithPrefix φ p

/-- If a full-length prefix is extendable to a satisfying assignment, the prefix
itself is satisfying. -/
theorem satisfies_of_full_prefix
    {φ : CNF} {p : RawAssignment}
    (hlen : p.length = φ.vars)
    (h : SatisfiableWithPrefix φ p) :
    Satisfies φ p := by
  rcases h with ⟨a, hsat, s, ha⟩
  have hslen : s.length = 0 := by
    have hlen_a : a.length = φ.vars := hsat.1
    rw [ha, List.length_append, hlen] at hlen_a
    omega
  cases s with
  | nil =>
      simpa [ha] using hsat
  | cons b rest =>
      simp at hslen

/-- If a prefix can be extended and it is not yet full length, either the
`false` extension or the `true` extension can still be extended. -/
theorem prefix_extend_false_or_true
    {φ : CNF} {p : RawAssignment}
    (hshort : p.length < φ.vars)
    (h : SatisfiableWithPrefix φ p) :
    SatisfiableWithPrefix φ (p ++ [false]) ∨
      SatisfiableWithPrefix φ (p ++ [true]) := by
  rcases h with ⟨a, hsat, s, ha⟩
  have hs_nonempty : s ≠ [] := by
    intro hs
    have hlen_a : a.length = φ.vars := hsat.1
    rw [ha, hs, List.append_nil] at hlen_a
    omega
  cases s with
  | nil =>
      exact (hs_nonempty rfl).elim
  | cons b rest =>
      cases b
      · left
        exact ⟨a, hsat, rest, by simp [ha, List.append_assoc]⟩
      · right
        exact ⟨a, hsat, rest, by simp [ha, List.append_assoc]⟩

/-! ## Bit-by-bit search from prefix queries -/

/-- Extend a prefix for `fuel` remaining variables by querying whether the
`false` branch remains satisfiable. -/
def extendPrefixByOracle
    (Q : CNF -> RawAssignment -> Bool) (φ : CNF) :
    Nat -> RawAssignment -> RawAssignment
  | 0, p => p
  | fuel + 1, p =>
      let pFalse := p ++ [false]
      if Q φ pFalse = true then
        extendPrefixByOracle Q φ fuel pFalse
      else
        extendPrefixByOracle Q φ fuel (p ++ [true])

/-- Main invariant for the bit-by-bit self-reduction. -/
theorem extendPrefixByOracle_correct
    (Q : CNF -> RawAssignment -> Bool)
    (hQ : PrefixOracleCorrect Q)
    (φ : CNF) :
    ∀ (fuel : Nat) (p : RawAssignment),
      p.length + fuel = φ.vars ->
        SatisfiableWithPrefix φ p ->
          Satisfies φ (extendPrefixByOracle Q φ fuel p)
  | 0, p, hlen, hp => by
      have hfull : p.length = φ.vars := by omega
      exact satisfies_of_full_prefix hfull hp
  | fuel + 1, p, hlen, hp => by
      unfold extendPrefixByOracle
      let pFalse := p ++ [false]
      by_cases hfalseQuery : Q φ pFalse = true
      · have hpFalse : SatisfiableWithPrefix φ pFalse :=
          (hQ φ pFalse).mp hfalseQuery
        have hlenFalse : pFalse.length + fuel = φ.vars := by
          dsimp [pFalse]
          simp
          omega
        simp [pFalse, hfalseQuery]
        exact extendPrefixByOracle_correct Q hQ φ fuel pFalse hlenFalse hpFalse
      · have hshort : p.length < φ.vars := by omega
        have hnotFalse : ¬ SatisfiableWithPrefix φ pFalse := by
          intro hpFalse
          exact hfalseQuery ((hQ φ pFalse).mpr hpFalse)
        have hor := prefix_extend_false_or_true hshort hp
        have hpTrue : SatisfiableWithPrefix φ (p ++ [true]) := by
          cases hor with
          | inl hpFalse => exact (hnotFalse hpFalse).elim
          | inr hpTrue => exact hpTrue
        have hlenTrue : (p ++ [true]).length + fuel = φ.vars := by
          simp
          omega
        simp [pFalse, hfalseQuery]
        exact extendPrefixByOracle_correct Q hQ φ fuel (p ++ [true]) hlenTrue hpTrue

/-- The witness-finding map produced by prefix queries. -/
def searchFromPrefixOracle
    (Q : CNF -> RawAssignment -> Bool) (φ : CNF) : RawAssignment :=
  extendPrefixByOracle Q φ φ.vars []

/-- Correctness of the semantic self-reduction from prefix satisfiability to
SAT search. -/
theorem searchFromPrefixOracle_correct
    (Q : CNF -> RawAssignment -> Bool)
    (hQ : PrefixOracleCorrect Q)
    (φ : CNF)
    (hsat : Satisfiable φ) :
    Satisfies φ (searchFromPrefixOracle Q φ) := by
  have hp : SatisfiableWithPrefix φ [] := by
    rcases hsat with ⟨a, ha⟩
    exact ⟨a, ha, a, by simp⟩
  unfold searchFromPrefixOracle
  exact extendPrefixByOracle_correct Q hQ φ φ.vars [] (by simp) hp

/-! ## Ordinary SAT deciders supply prefix oracles after a CNF reduction -/

/-- Reduction of a prefix query to an ordinary CNF formula.  The standard
implementation appends unit clauses fixing the prefix bits; this structure keeps
the syntactic encoding as the remaining machine-accounting obligation. -/
structure PrefixConstraintCNFReduction where
  encode : CNF -> RawAssignment -> CNF
  sound : ∀ (φ : CNF) (p : RawAssignment),
    Satisfiable (encode φ p) ↔ SatisfiableWithPrefix φ p

/-- Build a prefix oracle from an ordinary SAT decider and a prefix-query
CNF reduction. -/
def prefixOracleOfSATDecider
    (R : PrefixConstraintCNFReduction)
    (D : CNF -> Bool) : CNF -> RawAssignment -> Bool :=
  fun φ p => D (R.encode φ p)

/-- Correct SAT decision plus a prefix-query reduction gives a correct prefix
oracle. -/
theorem prefixOracleOfSATDecider_correct
    (R : PrefixConstraintCNFReduction)
    (D : CNF -> Bool)
    (hD : ∀ ψ : CNF, D ψ = true ↔ Satisfiable ψ) :
    PrefixOracleCorrect (prefixOracleOfSATDecider R D) := by
  intro φ p
  unfold prefixOracleOfSATDecider
  exact (hD (R.encode φ p)).trans (R.sound φ p)

/-- Semantic SAT decision-to-search theorem.  This is the non-machine core of
Cook self-reducibility. -/
theorem searchFromSATDecider_correct
    (R : PrefixConstraintCNFReduction)
    (D : CNF -> Bool)
    (hD : ∀ ψ : CNF, D ψ = true ↔ Satisfiable ψ)
    (φ : CNF)
    (hsat : Satisfiable φ) :
    Satisfies φ
      (searchFromPrefixOracle (prefixOracleOfSATDecider R D) φ) := by
  exact searchFromPrefixOracle_correct
    (prefixOracleOfSATDecider R D)
    (prefixOracleOfSATDecider_correct R D hD)
    φ hsat

/-! ## Relation to the machine socket -/

/-- The remaining compiler obligation needed to instantiate
`DecisionToSearchSelfReduction` for a concrete `MachineModel`.

It says the machine model can compile a coded SAT decider into the bit-by-bit
self-reduction searcher above, including the polynomial step accounting. -/
structure MachineDecisionToSearchCompiler
    (U : MachineModel)
    (R : PrefixConstraintCNFReduction) where
  compile : (D : DecisionMachine U) -> DecidesSAT U D -> SearchMachine U
  run_eq :
    ∀ (D : DecisionMachine U) (hD : DecidesSAT U D) (φ : CNF),
      U.searchRun (compile D hD).code φ =
        some (searchFromPrefixOracle
          (prefixOracleOfSATDecider R (fun ψ => U.decisionRun D.code ψ)) φ)

/-- A machine compiler for the semantic self-reduction discharges the earlier
`DecisionToSearchSelfReduction` socket. -/
def MachineDecisionToSearchCompiler.toSelfReduction
    {U : MachineModel}
    {R : PrefixConstraintCNFReduction}
    (C : MachineDecisionToSearchCompiler U R) :
    DecisionToSearchSelfReduction U where
  fromDecider := C.compile
  correct := by
    intro D hD φ hsat
    refine ⟨searchFromPrefixOracle
      (prefixOracleOfSATDecider R (fun ψ => U.decisionRun D.code ψ)) φ,
      ?_, ?_⟩
    · exact C.run_eq D hD φ
    · exact searchFromSATDecider_correct R
        (fun ψ => U.decisionRun D.code ψ) hD φ hsat

/-! ## Kernel-only axiom trace -/

#print axioms satisfies_of_full_prefix
#print axioms prefix_extend_false_or_true
#print axioms extendPrefixByOracle_correct
#print axioms searchFromPrefixOracle_correct
#print axioms prefixOracleOfSATDecider_correct
#print axioms searchFromSATDecider_correct
#print axioms MachineDecisionToSearchCompiler.toSelfReduction

end SATDepthMachine
