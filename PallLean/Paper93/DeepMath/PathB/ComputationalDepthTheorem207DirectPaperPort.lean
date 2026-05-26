import PallLean.Paper93.DeepMath.PathB.StrictDynamicNFrameLagrangianInvariant

/-!
# Direct paper-faithful Theorem 207 -> strict live-boundary port

This file encodes the strict Route-B port in a paper-first form (from the
`p vs np1` Theorem-207 semantic spine), without routing through the old static
same-object rank sandwich.

This file is an explicit interface layer: if one supplies both an NP-side lower
bound and a transfer into strict live-boundary rank, strict extraction follows
mechanically.  It does **not** claim that transfer is derivable.

Book-1-faithful reading: this is exactly the same-object sandwich surface, so
load-bearing progress should target boundary-budget incompatibility theorems
(exclusion) rather than unconditional extraction inhabitants.

The old same-sheet SPDP realization bridge is deliberately **not** imported
here.  It lives in
`ComputationalDepthTheorem207SameSheetLegacyPort`, keeping the final strict
Book-1 obstruction route independent of the legacy `GlobalGodMoveGauge`
semantic-transport seam axiom.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Direct per-observer paper witness at fixed length `n`.

This is the strict theorem payload needed from the paper Theorem-207 machinery:
`sheet_rank_lower` is the NP-side lower bound on the extracted target, and
`sheet_rank_le_liveBoundary` is the realization/no-loss bridge into the strict
observer trajectory boundary rank.
-/
structure Theorem207DirectPaperWitness
    (enc : ThreeCNFEncoding)
    (n : Nat)
    (L : StrictDynamicNFrameLagrangianObserver enc) where
  input : Fin n -> Bool
  formula : ThreeCNF
  encoded : enc.Encodes input formula
  formula_satisfiable : formula.IsSatisfiable
  time : Nat
  state : Nat
  state_matches : state = L.toTrajectory.stateCode n input time
  nframe_lagrangian_payload : Prop
  nframe_lagrangian_payload_realized : nframe_lagrangian_payload
  pac_holographic_payload : Prop
  pac_holographic_payload_realized : pac_holographic_payload
  amplituhedron_payload : Prop
  amplituhedron_payload_realized : amplituhedron_payload
  extractedSheetRank : Nat
  sheet_rank_lower :
    Nat.choose (n / 3) (Nat.log 2 n) <= extractedSheetRank
  sheet_rank_le_liveBoundary :
    extractedSheetRank <= L.toTrajectory.liveBoundaryRank n input time

/-- A direct paper witness yields a strict live minor. -/
noncomputable def strictLiveMinor_of_theorem207DirectPaperWitness
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : StrictDynamicNFrameLagrangianObserver enc}
    (W : Theorem207DirectPaperWitness enc n L) :
    StrictDynamicNFrameLagrangianLiveMinor enc L n where
  input := W.input
  formula := W.formula
  encoded := W.encoded
  formula_satisfiable := W.formula_satisfiable
  time := W.time
  state := W.state
  state_matches := W.state_matches
  liveActionRank := L.toTrajectory.liveBoundaryRank n W.input W.time
  nframe_lagrangian_payload := W.nframe_lagrangian_payload
  nframe_lagrangian_payload_realized := W.nframe_lagrangian_payload_realized
  pac_holographic_payload := W.pac_holographic_payload
  pac_holographic_payload_realized := W.pac_holographic_payload_realized
  amplituhedron_payload := W.amplituhedron_payload
  amplituhedron_payload_realized := W.amplituhedron_payload_realized
  liveActionRank_eq_boundary := rfl
  rank_lower := Nat.le_trans W.sheet_rank_lower W.sheet_rank_le_liveBoundary

/-- Direct paper theorem surface at fixed `n`: every strict SAT observer has a
Theorem-207 direct witness. -/
def Theorem207DirectPaperAt
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  forall L : StrictDynamicNFrameLagrangianObserver enc,
    Nonempty (Theorem207DirectPaperWitness enc n L)

/-- Direct paper theorem surface (exponent-parametric): this is the precise
port contract needed to derive strict dynamic extraction at paper scale. -/
def UniversalTheorem207DirectPaperPort
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat, exists n : Nat,
    n >= 2 ^ 20 /\
    4 * (c + 1) <= Nat.log 2 n /\
    Theorem207DirectPaperAt enc n

/-- Main port theorem: direct paper Theorem-207 contract implies the strict
live-boundary extraction theorem required by the new route. -/
theorem universalStrictDynamicNFrameLagrangianExtraction_of_directPaperPort
    (enc : ThreeCNFEncoding)
    (H : UniversalTheorem207DirectPaperPort enc) :
    UniversalStrictDynamicNFrameLagrangianExtraction enc := by
  intro c
  rcases H c with ⟨n, hn20, hlog, Hat⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro L
  rcases Hat L with ⟨W⟩
  exact ⟨strictLiveMinor_of_theorem207DirectPaperWitness W⟩

/-- The witness inequalities collapse to the same-object lower bound on strict
live boundary rank.  This is the explicit sandwich identity. -/
theorem liveBoundary_lower_of_theorem207DirectPaperWitness
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : StrictDynamicNFrameLagrangianObserver enc}
    (W : Theorem207DirectPaperWitness enc n L) :
    Nat.choose (n / 3) (Nat.log 2 n) <=
      L.toTrajectory.liveBoundaryRank n W.input W.time :=
  Nat.le_trans W.sheet_rank_lower W.sheet_rank_le_liveBoundary

/-- Boundary-budget obstruction at fixed scale: if an observer presentation has
strict live-boundary rank uniformly below the binomial floor, then no direct
paper witness can inhabit that scale for that observer. -/
theorem no_theorem207DirectPaperWitness_of_boundaryBudget
    {enc : ThreeCNFEncoding}
    {n : Nat}
    {L : StrictDynamicNFrameLagrangianObserver enc}
    (hbudget :
      forall input : Fin n -> Bool,
        forall time : Nat,
          L.toTrajectory.liveBoundaryRank n input time <
            Nat.choose (n / 3) (Nat.log 2 n)) :
    IsEmpty (Theorem207DirectPaperWitness enc n L) := by
  refine ⟨?_⟩
  intro W
  have hlower := liveBoundary_lower_of_theorem207DirectPaperWitness W
  exact (Nat.not_le_of_lt (hbudget W.input W.time)) hlower

/-- Book-1 style exclusion surface: the key target is an incompatibility
statement between finite observer boundary budgets and the binomial SAT-side
floor, not an unconditional extraction inhabitant. -/
def Book1BoundaryBudgetObstructionAt
    (enc : ThreeCNFEncoding)
    (n : Nat) : Prop :=
  forall L : StrictDynamicNFrameLagrangianObserver enc,
    forall input : Fin n -> Bool,
    forall time : Nat,
      L.toTrajectory.liveBoundaryRank n input time <
        Nat.choose (n / 3) (Nat.log 2 n)

/-- At any scale where Book-1 boundary-budget obstruction holds, direct paper
witnesses are excluded for every strict observer. -/
theorem no_directPaperWitness_of_book1BoundaryBudgetObstructionAt
    {enc : ThreeCNFEncoding}
    {n : Nat}
    (H : Book1BoundaryBudgetObstructionAt enc n) :
    forall L : StrictDynamicNFrameLagrangianObserver enc,
      IsEmpty (Theorem207DirectPaperWitness enc n L) := by
  intro L
  exact no_theorem207DirectPaperWitness_of_boundaryBudget
    (fun input time => H L input time)

/-- If direct-paper extraction-at-scale and Book-1 obstruction-at-scale are both
assumed, then the strict observer class must be empty at that encoding. -/
theorem strictObserverClass_empty_of_directPaperAt_and_book1ObstructionAt
    {enc : ThreeCNFEncoding}
    {n : Nat}
    (Hat : Theorem207DirectPaperAt enc n)
    (Hobs : Book1BoundaryBudgetObstructionAt enc n) :
    IsEmpty (StrictDynamicNFrameLagrangianObserver enc) := by
  refine ⟨?_⟩
  intro L
  have hnowit := no_directPaperWitness_of_book1BoundaryBudgetObstructionAt
    (enc := enc) (n := n) Hobs L
  rcases Hat L with ⟨W⟩
  exact hnowit.false W

/-- With at least one strict SAT observer, Book-1 obstruction at scale `n`
excludes direct-paper extraction at that same scale. -/
theorem no_directPaperAt_of_nonemptyObserver_and_book1ObstructionAt
    {enc : ThreeCNFEncoding}
    {n : Nat}
    (hL : Nonempty (StrictDynamicNFrameLagrangianObserver enc))
    (Hobs : Book1BoundaryBudgetObstructionAt enc n) :
    Not (Theorem207DirectPaperAt enc n) := by
  intro Hat
  have hempty := strictObserverClass_empty_of_directPaperAt_and_book1ObstructionAt
    (enc := enc) (n := n) Hat Hobs
  rcases hL with ⟨L⟩
  exact hempty.false L

/-- Strong Book-1 obstruction route: every paper-scale candidate length is
boundary-budget infeasible for strict observers.  This is an exclusion-first
endpoint, not an extraction witness endpoint. -/
def UniversalBook1BoundaryBudgetObstruction
    (enc : ThreeCNFEncoding) : Prop :=
  forall c n : Nat,
    n >= 2 ^ 20 ->
    4 * (c + 1) <= Nat.log 2 n ->
    Book1BoundaryBudgetObstructionAt enc n

/-- Under universal Book-1 obstruction and nonempty strict observer class, the
universal direct-paper extraction port is impossible. -/
theorem no_universalDirectPaperPort_of_nonemptyObserver_and_universalBook1Obstruction
    (enc : ThreeCNFEncoding)
    (hL : Nonempty (StrictDynamicNFrameLagrangianObserver enc))
    (Hobs : UniversalBook1BoundaryBudgetObstruction enc) :
    Not (UniversalTheorem207DirectPaperPort enc) := by
  intro Hport
  rcases Hport 0 with ⟨n, hn20, hlog, Hat⟩
  exact no_directPaperAt_of_nonemptyObserver_and_book1ObstructionAt
    (enc := enc) (n := n) hL (Hobs 0 n hn20 hlog) Hat

/-- Strict universal extraction induces the direct-paper port by taking
`extractedSheetRank := liveBoundaryRank`. -/
theorem universalDirectPaperPort_of_universalStrictDynamicNFrameLagrangianExtraction
    (enc : ThreeCNFEncoding)
    (H : UniversalStrictDynamicNFrameLagrangianExtraction enc) :
    UniversalTheorem207DirectPaperPort enc := by
  intro c
  rcases H c with ⟨n, hn20, hlog, HextractAt⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro L
  rcases HextractAt L with ⟨minor⟩
  refine ⟨{
    input := minor.input
    formula := minor.formula
    encoded := minor.encoded
    formula_satisfiable := minor.formula_satisfiable
    time := minor.time
    state := minor.state
    state_matches := minor.state_matches
    nframe_lagrangian_payload := minor.nframe_lagrangian_payload
    nframe_lagrangian_payload_realized := minor.nframe_lagrangian_payload_realized
    pac_holographic_payload := minor.pac_holographic_payload
    pac_holographic_payload_realized := minor.pac_holographic_payload_realized
    amplituhedron_payload := minor.amplituhedron_payload
    amplituhedron_payload_realized := minor.amplituhedron_payload_realized
    extractedSheetRank := minor.liveActionRank
    sheet_rank_lower := minor.rank_lower
    sheet_rank_le_liveBoundary := by
      simp [minor.liveActionRank_eq_boundary]
  }⟩

/-- Book-1 obstruction closure in strict theorem shape: with a nonempty strict
observer class, universal strict extraction is impossible under universal
boundary-budget obstruction. -/
theorem no_universalStrictDynamicNFrameLagrangianExtraction_of_nonemptyObserver_and_universalBook1Obstruction
    (enc : ThreeCNFEncoding)
    (hL : Nonempty (StrictDynamicNFrameLagrangianObserver enc))
    (Hobs : UniversalBook1BoundaryBudgetObstruction enc) :
    Not (UniversalStrictDynamicNFrameLagrangianExtraction enc) := by
  intro Hstrict
  exact no_universalDirectPaperPort_of_nonemptyObserver_and_universalBook1Obstruction
    enc hL Hobs
    (universalDirectPaperPort_of_universalStrictDynamicNFrameLagrangianExtraction
      enc Hstrict)

#print axioms strictLiveMinor_of_theorem207DirectPaperWitness
#print axioms liveBoundary_lower_of_theorem207DirectPaperWitness
#print axioms no_theorem207DirectPaperWitness_of_boundaryBudget
#print axioms no_directPaperWitness_of_book1BoundaryBudgetObstructionAt
#print axioms universalStrictDynamicNFrameLagrangianExtraction_of_directPaperPort
#print axioms universalDirectPaperPort_of_universalStrictDynamicNFrameLagrangianExtraction
#print axioms no_universalStrictDynamicNFrameLagrangianExtraction_of_nonemptyObserver_and_universalBook1Obstruction

end PallLean.Paper93.DeepMath.PathB
