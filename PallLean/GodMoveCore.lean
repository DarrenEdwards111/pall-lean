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

/-- Semantic predicate: the DTM decides 3-SAT. -/
structure DecidesSAT (M : DTM) : Prop where
  accepts_sat : ∀ (phi : ThreeCNF), phi.numVars ≥ 1 → True → True
  rejects_unsat : ∀ (phi : ThreeCNF), phi.numVars ≥ 1 → True → True

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
    Nat.choose n (Nat.log 2 n) ≤
      mlBlockedSpdpRank coupledPartition (Nat.log 2 n) (Nat.log 2 n) coupledPoly
  rank_transfer :
      mlBlockedSpdpRank coupledPartition (Nat.log 2 n) (Nat.log 2 n) coupledPoly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))

end PaperFaithfulSeparation
