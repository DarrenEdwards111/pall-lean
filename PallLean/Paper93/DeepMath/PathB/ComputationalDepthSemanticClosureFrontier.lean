import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheorem207StrictPort

/-!
# Semantic-closure frontier for Theorem 207

The paper's Step 6 asks for semantic closure under P-decidability: a SAT
decider should force the paper's canonical God-Move/SPDP live-boundary
realization, rather than merely deciding the same Boolean language
extensionally.

This file states that request directly, without routing through the older
same-sheet source-transport axiom:

* an encoded SAT-deciding DTM `M`;
* any proposed live-rank presentation `configActionRank`; and
* a paper-scale extraction point where the strict live boundary carries the
  binomial minor.

The result is an audit theorem, not a hidden proof: this direct semantic
closure surface is equivalent to the existing strict live-boundary port, and
therefore equivalent to the encoded no-SAT-decider endpoint already isolated in
`ComputationalDepthTheorem207StrictPort`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Fixed-length direct semantic closure: every encoded SAT-deciding DTM, under
any proposed live-rank bookkeeping, admits a strict live-boundary minor at this
length.

This is the direct Lean version of the paper's Step 6 demand.  The closure is
not just extensional language equality; it says semantic SAT decidability forces
the concrete strict trajectory object used by the Theorem-207 port. -/
def SemanticClosureExtractionAt
    (enc : ThreeCNFEncoding) (n : Nat) : Prop :=
  forall (M : TuringMachine.DTM)
    (hM : DTMDecidesSATWithEncoding enc M)
    (configActionRank : Nat -> Nat),
      Nonempty
        (StrictDynamicNFrameLagrangianLiveMinor enc
          ({ M := M
             configActionRank := configActionRank
             decides := hM } :
            StrictDynamicNFrameLagrangianObserver enc)
          n)

/-- Paper-scale direct semantic closure under P-decidability.

For every polynomial calibration exponent `c`, there is a large enough input
length where every encoded SAT decider, with any live-rank presentation, must
realize the binomial strict live-boundary minor.
-/
def PaperLemma13StrengthSemanticClosure
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    SemanticClosureExtractionAt enc n

/-- The direct semantic-closure surface is exactly the strict Theorem-207
live-boundary port.

This theorem is the precise result of trying to prove Step 6 directly: there is
no weaker compiler-bookkeeping lemma hiding here.  Once semantic closure is
strong enough to force the strict live-boundary minor for every SAT decider, it
is definitionally the strict extraction port. -/
theorem paperSemanticClosure_iff_theorem207StrictPort
    (enc : ThreeCNFEncoding) :
    PaperLemma13StrengthSemanticClosure enc ↔
      Theorem207StrictLiveBoundaryPort enc := by
  constructor
  · intro H c
    rcases H c with ⟨n, hn20, hlog, hAt⟩
    refine ⟨n, hn20, hlog, ?_⟩
    intro L
    simpa using hAt L.M L.decides L.configActionRank
  · intro H c
    rcases H c with ⟨n, hn20, hlog, hAt⟩
    refine ⟨n, hn20, hlog, ?_⟩
    intro M hM configActionRank
    exact hAt
      ({ M := M
         configActionRank := configActionRank
         decides := hM } :
        StrictDynamicNFrameLagrangianObserver enc)

/-- Direct semantic closure is equivalent to the encoded no-SAT-decider
endpoint.

Thus an unconditional proof of this semantic-closure theorem would already be
an unconditional proof of the repository's encoded P-vs-NP endpoint.  Conversely
the no-decider endpoint makes semantic closure vacuous. -/
theorem paperSemanticClosure_iff_no_DTMDecidesSATWithEncoding
    (enc : ThreeCNFEncoding) :
    PaperLemma13StrengthSemanticClosure enc ↔
      Not (exists M : TuringMachine.DTM,
        DTMDecidesSATWithEncoding enc M) := by
  rw [paperSemanticClosure_iff_theorem207StrictPort,
    theorem207StrictPort_iff_no_DTMDecidesSATWithEncoding]

/-- Forward readout: a direct proof of semantic closure would close the
encoded no-SAT-decider endpoint. -/
theorem no_DTMDecidesSATWithEncoding_of_paperSemanticClosure
    (enc : ThreeCNFEncoding)
    (H : PaperLemma13StrengthSemanticClosure enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) :=
  (paperSemanticClosure_iff_no_DTMDecidesSATWithEncoding enc).mp H

/-! ## Kernel-only axiom trace -/

#print axioms paperSemanticClosure_iff_theorem207StrictPort
#print axioms paperSemanticClosure_iff_no_DTMDecidesSATWithEncoding
#print axioms no_DTMDecidesSATWithEncoding_of_paperSemanticClosure

end PallLean.Paper93.DeepMath.PathB
