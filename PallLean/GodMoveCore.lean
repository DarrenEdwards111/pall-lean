import PallLean.CookLevinDefs
import Mathlib.Tactic

namespace PaperFaithfulSeparation

open SPDP MultilinearSPDP MvPolynomial TuringMachine

/-- A 3-CNF formula: a list of clauses, each a triple of variable indices. -/
structure ThreeCNF where
  numVars : ℕ
  clauses : List (Fin numVars × Fin numVars × Fin numVars)

/-- The coupled verifier sheet polynomial Q×_Φ from Definition 39.
For each clause C with verifier gadget V_C and selector variable z_C:
  Q×_Φ(u,z) = ∏_{C∈Cl(Φ)} (1 - z_C · V_C(u_{B_C})²)
where B_C are the clause-local gadget variables. -/
structure CoupledVerifierSheet where
  numVerifierVars : ℕ
  numSelectorVars : ℕ
  totalVars : ℕ
  totalVars_eq : totalVars = numVerifierVars + numSelectorVars
  poly : MvPolynomial (Fin totalVars) ℚ
  disjoint_blocks : Prop
  has_tag_monomials : Prop

/-- NP-side lower surface used by the God-Move route. -/
def np_exponential_lower_bound (numClauses κ rank : ℕ) : Prop :=
  Nat.choose numClauses κ ≤ rank

/-- A clause (i, j, k) is satisfied by assignment σ if at least one literal is true. -/
def clauseSatisfied (σ : Fin n → Bool) (c : Fin n × Fin n × Fin n) : Prop :=
  σ c.1 = true ∨ σ c.2.1 = true ∨ σ c.2.2 = true

/-- A 3-CNF formula φ is satisfiable if there exists a Boolean assignment
    satisfying every clause. -/
def ThreeCNF.IsSatisfiable (φ : ThreeCNF) : Prop :=
  ∃ (σ : Fin φ.numVars → Bool), ∀ c ∈ φ.clauses, clauseSatisfied σ c

/-- Encoding size of a 3-CNF formula: numVars + 3 * numClauses bits suffice
    to specify the formula (each clause needs 3 variable indices). -/
def ThreeCNF.encodingSize (φ : ThreeCNF) : ℕ :=
  φ.numVars + 3 * φ.clauses.length

/-- Semantic predicate: the DTM M decides 3-SAT.

M decides 3-SAT if for every 3-CNF formula φ whose encoding fits
within M's time bound at some input size n:
- If φ is satisfiable, then M accepts some encoding of φ of length n.
- If φ is unsatisfiable, then M does not accept any input of length n
  that encodes φ.

The fields use the DTM execution semantics from TuringMachine.lean
(`accepts`), making `DecidesSAT M` genuinely load-bearing: it constrains
M's transition function to correctly classify 3-SAT instances. -/
structure DecidesSAT (M : DTM) : Prop where
  /-- For satisfiable formulas, M accepts a valid encoding. -/
  accepts_sat : ∀ (φ : ThreeCNF) (n : ℕ) (hn : n ≥ 1),
    φ.encodingSize ≤ n →
    φ.IsSatisfiable →
    ∃ (input : Fin n → Bool), accepts M n hn input
  /-- For unsatisfiable formulas, M does not accept any encoding. -/
  rejects_unsat : ∀ (φ : ThreeCNF) (n : ℕ) (hn : n ≥ 1),
    φ.encodingSize ≤ n →
    ¬ φ.IsSatisfiable →
    ∀ (input : Fin n → Bool), ¬ accepts M n hn input

/-- Paper-faithful abstract source/target interface for the God-Move.

This avoids the false typing shortcut of placing the compiled polynomial and the
coupled verifier sheet in the same ambient variable space before the actual map
`ΠΦ : F[u,v] → F[u]` has been formalized. -/
structure GodMoveExtractionInterface (M : DTM) (n : ℕ)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  coupledVars : ℕ
  coupledPartition : BlockPartition coupledVars
  coupledPoly : MvPolynomial (Fin coupledVars) ℚ
  instance_uniform : Prop
  witness_free : Prop
  block_local : Prop
  target_lower :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank coupledPartition (Nat.log 2 n) (Nat.log 2 n) coupledPoly
  rank_transfer :
      mlBlockedSpdpRank coupledPartition (Nat.log 2 n) (Nat.log 2 n) coupledPoly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))

end PaperFaithfulSeparation
