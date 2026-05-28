import PallLean.Paper93.DeepMath.PathB.ComputationalDepthVerifierNormalForm

/-!
# Low-boundary remainder deciders

This file downgrades the global P-vs-NP claim to a restricted-model lower-bound
target.

The old full route repeatedly asked for a theorem of the form "every
polynomial-time SAT decider realizes the God-Move sheet."  The audits showed
that this is either false for arbitrary presentations or equivalent to the
encoded no-SAT-decider endpoint.

The restricted target here is different:

* define a canonical low-boundary N-frame remainder decider model;
* prove that no such model can decide a signed counterfactual/Tseitin-scale
  family once the sheet lower bound exceeds the boundary rank budget;
* leave the statement "every polynomial-time decider embeds into this model"
  as a separate conditional frontier, not as an assumption hidden inside the
  lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Restricted low-boundary model -/

/-- A canonical low-boundary remainder decider at a fixed scale.

The rank objects are deliberately separated:

* `boundaryRank` is the restricted P-side boundary/control capacity;
* `sheetRank` is the NP-side extracted-sheet complexity;
* `sheet_rank_le_boundary` is the model's faithful-compression condition.

This is a restricted model, not a theorem about arbitrary DTMs. -/
structure LowBoundaryRemainderDeciderAt
    (enc : SignedFormulaEncoding)
    (M : DTM) (n : Nat)
    (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (k : Nat) : Type where
  signed_decider : SignedDTMDecidesSAT enc M
  coverage : SignedCounterfactualEKPDirectionCoverage enc M n
  extraction :
    CanonicalTheorem207ExtractionWithRemainder M n hn hn2 htb hns
  remainder_transport :
    Nonempty
      (SignedExtractionRemainderTriAspectSemanticInterface
        extraction.extraction coverage)
  boundaryRank : Nat
  sheetRank : Nat
  boundary_rank_bound : boundaryRank <= n ^ k
  sheet_rank_lower :
    Nat.choose (n / 3) (Nat.log 2 n) <= sheetRank
  sheet_rank_le_boundary : sheetRank <= boundaryRank

namespace LowBoundaryRemainderDeciderAt

/-- Any low-boundary remainder decider sandwiches the binomial/Tseitin sheet
lower bound inside the polynomial boundary budget. -/
theorem binomial_le_boundary_budget
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {k : Nat}
    (A : LowBoundaryRemainderDeciderAt enc M n hn hn2 htb hns k) :
    Nat.choose (n / 3) (Nat.log 2 n) <= n ^ k :=
  le_trans A.sheet_rank_lower
    (le_trans A.sheet_rank_le_boundary A.boundary_rank_bound)

end LowBoundaryRemainderDeciderAt

/-! ## Restricted-model lower bound -/

/-- If the Tseitin/binomial sheet lower bound exceeds the low-boundary budget,
there is no canonical low-boundary remainder decider at that scale. -/
theorem no_lowBoundaryRemainderDeciderAt_of_rankGap
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {k : Nat}
    (hgap : n ^ k < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (Nonempty
      (LowBoundaryRemainderDeciderAt enc M n hn hn2 htb hns k)) := by
  rintro ⟨A⟩
  exact (not_le_of_gt hgap) A.binomial_le_boundary_budget

/-- A named restricted lower-bound statement for the concrete signed 3-CNF
surface.  This is the honest target: not "P ≠ NP", but "signed 3-CNF
counterfactual families are not decidable by this low-boundary remainder
model at scales where the sheet lower bound exceeds the boundary budget." -/
theorem signedThreeCNF_not_lowBoundaryRemainderDeciderAt_of_rankGap
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {k : Nat}
    (hgap : n ^ k < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (Nonempty
      (LowBoundaryRemainderDeciderAt
        signedThreeCNFEncoding M n hn hn2 htb hns k)) :=
  no_lowBoundaryRemainderDeciderAt_of_rankGap hgap

/-! ## Conditional frontier, stated explicitly -/

/-- The speculative embedding theorem, kept separate from the restricted lower
bound.  This is where a full P-vs-NP implication would have to pay the real
price: it would have to show that a signed SAT decider admits the restricted
low-boundary remainder representation at a scale with a rank gap. -/
def SignedSATDeciderEmbedsLowBoundaryAt
    (enc : SignedFormulaEncoding)
    (M : DTM) (n : Nat)
    (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (k : Nat) : Prop :=
  SignedDTMDecidesSAT enc M ->
    Nonempty (LowBoundaryRemainderDeciderAt enc M n hn hn2 htb hns k)

/-- Conditional endpoint: a low-boundary embedding theorem plus the rank gap
rules out the underlying signed SAT decider.  The embedding theorem is not
proved here; this theorem records exactly where the full-P burden would live. -/
theorem no_signedSATDecider_of_lowBoundaryEmbeddingAt_and_rankGap
    {enc : SignedFormulaEncoding}
    {M : DTM} {n : Nat}
    {hn : n >= 2 ^ 804} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {k : Nat}
    (hembed :
      SignedSATDeciderEmbedsLowBoundaryAt enc M n hn hn2 htb hns k)
    (hgap : n ^ k < Nat.choose (n / 3) (Nat.log 2 n)) :
    Not (SignedDTMDecidesSAT enc M) := by
  intro hM
  exact no_lowBoundaryRemainderDeciderAt_of_rankGap
    (enc := enc) (M := M) (n := n) (hn := hn) (hn2 := hn2)
    (htb := htb) (hns := hns) (k := k) hgap (hembed hM)

/-! ## Kernel-only axiom trace -/

#print axioms LowBoundaryRemainderDeciderAt.binomial_le_boundary_budget
#print axioms no_lowBoundaryRemainderDeciderAt_of_rankGap
#print axioms signedThreeCNF_not_lowBoundaryRemainderDeciderAt_of_rankGap
#print axioms no_signedSATDecider_of_lowBoundaryEmbeddingAt_and_rankGap

end PallLean.Paper93.DeepMath.PathB
