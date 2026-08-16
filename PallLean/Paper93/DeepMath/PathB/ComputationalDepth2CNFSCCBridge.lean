import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTwoSATFastSAT
import PallLean.Paper93.DeepMath.PathB.ComputationalDepth2CNFPipelineCapstone

/-!
# Bridge from the verified SCC criterion to the observer pipeline's CNF syntax

`ComputationalDepthTwoSATFastSAT` already proves the full semantic 2-SAT criterion for lists of literal pairs:
satisfiability is equivalent to no literal sharing a strongly connected component with its negation.  The newer
observer/restriction development represents a CNF as a finset of finset clauses.  This file connects those interfaces.

A pair becomes the finset `{left, right}`.  Repeated literals therefore represent unit clauses automatically, while
duplicate clauses disappear harmlessly in the outer finset.  Empty residual clauses remain the explicit UNSAT case
handled by the cover-leaf development.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoCNFSCCBridge

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.XorCNFIdentityEmbedding
open PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT

variable {n : ℕ}

/-- Interpret one implication-graph pair clause in the observer pipeline's finset syntax. -/
def pairClause (c : Clause n) : Finset (Literal n) := {c.1, c.2}

/-- Interpret a list of pair clauses as a duplicate-free finite CNF. -/
def pairCNF (cls : List (Clause n)) : CNF n := (cls.map pairClause).toFinset

/-- Pair-clause evaluation agrees exactly across the two syntax representations. -/
theorem eval_pairClause_iff (x : Fin n → Bool) (c : Clause n) :
    evalClause x (pairClause c) ↔ clauseSat x c := by
  simp [pairClause, evalClause, evalLiteral, clauseSat, litVal]

/-- The translated CNF has width at most two. -/
theorem pairCNF_width_two (cls : List (Clause n)) :
    ∀ C ∈ pairCNF cls, C.card ≤ 2 := by
  intro C hC
  simp only [pairCNF, List.mem_toFinset, List.mem_map] at hC
  obtain ⟨c, _hc, rfl⟩ := hC
  exact Finset.card_le_two

/-- Total formula evaluation agrees; erasing duplicate clauses changes no semantics. -/
theorem eval_pairCNF_iff (x : Fin n → Bool) (cls : List (Clause n)) :
    evalCNF x (pairCNF cls) ↔ ∀ c ∈ cls, clauseSat x c := by
  constructor
  · intro h c hc
    have hmem : pairClause c ∈ pairCNF cls := by
      simp only [pairCNF, List.mem_toFinset, List.mem_map]
      exact ⟨c, hc, rfl⟩
    exact (eval_pairClause_iff x c).mp (h (pairClause c) hmem)
  · intro h C hC
    simp only [pairCNF, List.mem_toFinset, List.mem_map] at hC
    obtain ⟨c, hc, rfl⟩ := hC
    exact (eval_pairClause_iff x c).mpr (h c hc)

/-- Satisfiability agrees between the pipeline CNF and the implication-graph pair formula. -/
theorem satisfiable_pairCNF_iff_twoSat (cls : List (Clause n)) :
    (∃ x, evalCNF x (pairCNF cls)) ↔ TwoSat cls := by
  simp only [TwoSat]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (eval_pairCNF_iff x cls).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (eval_pairCNF_iff x cls).mpr hx⟩
  
/-- **SCC criterion in the observer pipeline's CNF semantics (proved).** -/
theorem satisfiable_pairCNF_iff_noContra (cls : List (Clause n)) :
    (∃ x, evalCNF x (pairCNF cls)) ↔ NoContra cls := by
  rw [satisfiable_pairCNF_iff_twoSat, twosat_iff]

end PallLean.Paper93.DeepMath.PathB.TwoCNFSCCBridge

#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFSCCBridge.eval_pairCNF_iff
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFSCCBridge.satisfiable_pairCNF_iff_noContra
