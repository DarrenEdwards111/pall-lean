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

The quantifier over `configActionRank : Nat -> Nat` is intentionally broad.  It
includes the structure-free presentation `fun _ => 0`.  If the semantic closure
statement were restricted to presentations that already carry high live rank,
the rank lower bound would be built into the definition and the theorem would
no longer imply the SAT lower-bound endpoint.

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

/-- The structure-free strict presentation has zero live-boundary rank at every
state.  This is why the universal quantifier in `SemanticClosureExtractionAt`
is genuinely load-bearing: it must include this presentation. -/
theorem zeroRankPresentation_liveBoundaryRank_eq_zero
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    (hM : DTMDecidesSATWithEncoding enc M)
    (n : Nat) (input : Fin n -> Bool) (time : Nat) :
    (({ M := M
        configActionRank := fun _ => 0
        decides := hM } :
      StrictDynamicNFrameLagrangianObserver enc).toTrajectory.liveBoundaryRank
        n input time) = 0 := by
  simp [StrictDynamicNFrameLagrangianObserver.toTrajectory,
    strictFaithfulTrajectoryObserver, StrictStateRankAt]

/-- At a paper-scale length, the zero-rank strict presentation cannot carry a
strict live-boundary minor.

This is the concrete obstruction behind the semantic-closure frontier: a SAT
decider can always be presented with `configActionRank := fun _ => 0`, and then
the binomial lower bound has nowhere to live. -/
theorem no_strictLiveMinor_of_zeroRankPresentation_at
    {enc : ThreeCNFEncoding}
    {M : TuringMachine.DTM}
    (hM : DTMDecidesSATWithEncoding enc M)
    {n : Nat}
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * (0 + 1) <= Nat.log 2 n) :
    Not
      (Nonempty
        (StrictDynamicNFrameLagrangianLiveMinor enc
          ({ M := M
             configActionRank := fun _ => 0
             decides := hM } :
            StrictDynamicNFrameLagrangianObserver enc)
          n)) := by
  intro hminor
  rcases hminor with ⟨minor⟩
  have hzero :
      minor.liveActionRank = 0 := by
    rw [minor.liveActionRank_eq_boundary]
    exact zeroRankPresentation_liveBoundaryRank_eq_zero hM
      n minor.input minor.time
  have hchoose_pos :
      0 < Nat.choose (n / 3) (Nat.log 2 n) := by
    have hgap :
        n ^ 0 < Nat.choose (n / 3) (Nat.log 2 n) :=
      arithmetic_gap_for_exponent 0 n hn20 hlog
    have hpow_pos : 0 < n ^ 0 := by simp
    exact Nat.lt_trans hpow_pos hgap
  have hchoose_le_zero :
      Nat.choose (n / 3) (Nat.log 2 n) <= 0 := by
    simpa [hzero] using minor.rank_lower
  exact (Nat.not_lt_of_ge hchoose_le_zero) hchoose_pos

/-- If an encoded SAT-deciding DTM exists, then semantic closure at any
paper-scale length fails through the zero-rank presentation. -/
theorem not_semanticClosureExtractionAt_of_zeroRankPresentation
    {enc : ThreeCNFEncoding}
    (hdec : exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M)
    {n : Nat}
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * (0 + 1) <= Nat.log 2 n) :
    Not (SemanticClosureExtractionAt enc n) := by
  intro hAt
  rcases hdec with ⟨M, hM⟩
  exact (no_strictLiveMinor_of_zeroRankPresentation_at hM hn20 hlog)
    (hAt M hM (fun _ => 0))

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

/-- Explicit zero-rank obstruction to the full paper semantic-closure theorem.

This proves the forward no-decider consequence without using the iff theorem:
given a candidate SAT decider, query semantic closure at exponent `0`; the
closure must handle the structure-free rank presentation, but that presentation
cannot contain a positive binomial minor. -/
theorem not_paperSemanticClosure_of_DTMDecidesSATWithEncoding
    {enc : ThreeCNFEncoding}
    (hdec : exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) :
    Not (PaperLemma13StrengthSemanticClosure enc) := by
  intro H
  rcases H 0 with ⟨n, hn20, hlog, hAt⟩
  exact (not_semanticClosureExtractionAt_of_zeroRankPresentation
    hdec hn20 hlog) hAt

/-! ## Kernel-only axiom trace -/

#print axioms zeroRankPresentation_liveBoundaryRank_eq_zero
#print axioms no_strictLiveMinor_of_zeroRankPresentation_at
#print axioms not_semanticClosureExtractionAt_of_zeroRankPresentation
#print axioms paperSemanticClosure_iff_theorem207StrictPort
#print axioms paperSemanticClosure_iff_no_DTMDecidesSATWithEncoding
#print axioms no_DTMDecidesSATWithEncoding_of_paperSemanticClosure
#print axioms not_paperSemanticClosure_of_DTMDecidesSATWithEncoding

end PallLean.Paper93.DeepMath.PathB
