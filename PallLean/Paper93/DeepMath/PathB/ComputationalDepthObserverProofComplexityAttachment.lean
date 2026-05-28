import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompleteGraphExpansion
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionMediumClause
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung3Complete

/-!
# Observer/N-frame attachment to proof-complexity rungs 1 and 2

**STATUS: SAFE ATTACHMENT LAYER, NOT A P-vs-NP BRIDGE.**

The bottom proof-complexity rungs are now real Lean mathematics:

* rung 1: expansion gives a Tseitin boundary/support lower bound;
* rung 2: tree-like resolution width lower bounds give tree-like size lower
  bounds, and the BSW medium-clause descent skeleton is proved.

This file attaches the N-frame/observer vocabulary to those proved rungs without
changing the payload.  The observer words are deliberately thin wrappers:

* "observer boundary" means a concrete lower bound on the visible edge support
  of a Tseitin constraint combination;
* "visibility" means an actual derivable clause/edge-support witness in the
  proof-complexity object;
* "N-frame local channel" means a bounded tree-like resolution channel;
* "God-Move boundary" means a restricted width lower bound for that channel;
* "counterfactual interpretation" means a medium vertex-set contrast whose
  boundary is visible by the expansion theorem.

No theorem here says that arbitrary polynomial-time SAT deciders induce such a
restricted channel.  That generalization remains the P-vs-NP-strength wall.

The later rung-3 attachment follows the same rule: observer vocabulary means
resource visibility for a restricted algebraic/semi-algebraic proof system, not a
new proof of the underlying Tseitin lower bounds.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-! ## Rung 1 as observer-combinatorial visibility -/

/-- A concrete observer boundary at rung 1: the F₂ combination over `region`
has at least `visibleLowerBound` live edge directions. -/
structure ObserverCombinatorialBoundary
    (G : TseitinGraph V Edge) (region : Finset V) (visibleLowerBound : Nat) :
    Prop where
  visible_support :
    visibleLowerBound <= (edgeSupport (G.combination region)).card

/-- The boundary is "visible" to the restricted observer exactly when its
support lower bound is available as a proof-complexity fact. -/
def BoundaryVisibleToRestrictedObserver
    (G : TseitinGraph V Edge) (region : Finset V) (visibleLowerBound : Nat) :
    Prop :=
  ObserverCombinatorialBoundary G region visibleLowerBound

/-- Rung 1 attaches directly to observer visibility: expansion makes the
boundary visible with lower bound `c * |S|`. -/
theorem observerBoundaryVisible_of_expansion
    (G : TseitinGraph V Edge) {c : Nat} (hexp : G.HasExpansion c)
    (S : Finset V) (h1 : 1 <= S.card)
    (h2 : 2 * S.card <= Fintype.card V) :
    BoundaryVisibleToRestrictedObserver G S (c * S.card) where
  visible_support :=
    G.combination_support_card_ge_of_expansion hexp S h1 h2

/-- The complete-graph family gives an explicit asymptotic observer-visible
boundary at every scale. -/
theorem completeGraph_observerBoundaryVisible
    (n : Nat) (S : Finset (Fin n))
    (h1 : 1 <= S.card) (h2 : 2 * S.card <= Fintype.card (Fin n)) :
    BoundaryVisibleToRestrictedObserver (completeGraph n) S S.card := by
  simpa using
    observerBoundaryVisible_of_expansion
      (completeGraph n) (completeGraph_hasExpansion n) S h1 h2

/-! ## Counterfactual reading of rung 1 -/

/-- A counterfactual Tseitin contrast in the restricted sense: a nonempty medium
vertex set whose parity combination exposes a visible edge boundary.  This is
not a SAT-decider claim; it is the proof-complexity boundary object that the
observer interpretation reads. -/
structure CounterfactualObserverBoundary
    (G : TseitinGraph V Edge) (region : Finset V) (visibleLowerBound : Nat) :
    Prop where
  nonempty_region : 1 <= region.card
  medium_region : 2 * region.card <= Fintype.card V
  visible_boundary :
    BoundaryVisibleToRestrictedObserver G region visibleLowerBound

/-- Expansion supplies the counterfactual observer boundary for every medium
region. -/
theorem counterfactualObserverBoundary_of_expansion
    (G : TseitinGraph V Edge) {c : Nat} (hexp : G.HasExpansion c)
    (S : Finset V) (h1 : 1 <= S.card)
    (h2 : 2 * S.card <= Fintype.card V) :
    CounterfactualObserverBoundary G S (c * S.card) where
  nonempty_region := h1
  medium_region := h2
  visible_boundary := observerBoundaryVisible_of_expansion G hexp S h1 h2

/-- The complete-graph family gives a concrete asymptotic counterfactual
boundary. -/
theorem completeGraph_counterfactualObserverBoundary
    (n : Nat) (S : Finset (Fin n))
    (h1 : 1 <= S.card) (h2 : 2 * S.card <= Fintype.card (Fin n)) :
    CounterfactualObserverBoundary (completeGraph n) S S.card := by
  simpa using
    counterfactualObserverBoundary_of_expansion
      (completeGraph n) (completeGraph_hasExpansion n) S h1 h2

/-! ## Rung 2 as an N-frame local channel -/

universe u

variable {Lit : Type u} [DecidableEq Lit]

/-- A restricted N-frame local channel is a tree-like resolution channel with
explicit axiom-width and size budgets.  This is intentionally a restricted proof
system, not an arbitrary polynomial-time computation model. -/
structure NFrameLocalResolutionChannel
    (compl : Lit -> Lit)
    (Axiom : ResolutionClause Lit -> Prop)
    (Target : ResolutionClause Lit) where
  axiomWidthBudget : Nat
  sizeBudget : Nat
  axioms_width :
    AxiomsWidthAtMost Axiom axiomWidthBudget

namespace NFrameLocalResolutionChannel

/-- The channel realizes the target if there is a tree-like derivation within
its size budget. -/
def realizes
    {compl : Lit -> Lit}
    {Axiom : ResolutionClause Lit -> Prop}
    {Target : ResolutionClause Lit}
    (C : NFrameLocalResolutionChannel compl Axiom Target) : Prop :=
  exists D : ResolutionDerivation compl Axiom Target, D.size <= C.sizeBudget

end NFrameLocalResolutionChannel

/-- A restricted God-Move boundary for a local resolution channel is exactly a
real width lower bound for the target.  The name is interpretive; the payload is
`ResolutionWidthLowerBound`. -/
structure RestrictedGodMoveResolutionBoundary
    (compl : Lit -> Lit)
    (Axiom : ResolutionClause Lit -> Prop)
    (Target : ResolutionClause Lit)
    (requiredWidth : Nat) : Prop where
  width_lower_bound :
    ResolutionWidthLowerBound compl Axiom Target requiredWidth

/-- If the God-Move boundary requires more width than the local channel's total
tree-like budget can carry, the restricted N-frame channel cannot realize it. -/
theorem nframeLocalChannel_blocked_by_restrictedGodMoveBoundary
    {compl : Lit -> Lit}
    {Axiom : ResolutionClause Lit -> Prop}
    {Target : ResolutionClause Lit}
    {requiredWidth : Nat}
    (C : NFrameLocalResolutionChannel compl Axiom Target)
    (B : RestrictedGodMoveResolutionBoundary compl Axiom Target requiredWidth)
    (hgap : C.axiomWidthBudget * C.sizeBudget < requiredWidth) :
    Not C.realizes :=
  no_small_tree_like_derivation_of_width_lower_bound
    C.axioms_width B.width_lower_bound hgap

/-! ## Medium-clause visibility inside a derivation -/

/-- A clause visibly crossing the medium band of a BSW-style measure inside a
tree-like derivation. -/
structure MediumClauseVisible
    (compl : Lit -> Lit)
    (Axiom : ResolutionClause Lit -> Prop)
    (μ : ResolutionClause Lit -> Nat)
    (t : Nat) : Type u where
  clause : ResolutionClause Lit
  lower : t <= μ clause
  upper : μ clause < 2 * t
  derivable : Nonempty (ResolutionDerivation compl Axiom clause)

/-- The proved BSW descent skeleton becomes an observer-visibility theorem:
any derivation whose measure rises from small axioms to a large target contains
a visible medium clause. -/
theorem mediumClauseVisible_of_derivation
    {compl : Lit -> Lit}
    {Axiom : ResolutionClause Lit -> Prop}
    {a t : Nat}
    (μ : ResolutionClause Lit -> Nat)
    (hsub : ∀ {C D : ResolutionClause Lit} (p : Lit),
      μ (ResolutionClause.resolvent compl C D p) <= μ C + μ D)
    (hax : ∀ {C : ResolutionClause Lit}, Axiom C -> μ C <= a)
    (ht : a < 2 * t)
    {Target : ResolutionClause Lit}
    (Der : ResolutionDerivation compl Axiom Target)
    (hroot : t <= μ Target) :
    Nonempty (MediumClauseVisible compl Axiom μ t) := by
  rcases ResolutionDerivation.exists_medium_measure μ hsub hax ht Der hroot with
    ⟨C', hlow, hup, hder⟩
  exact ⟨⟨C', hlow, hup, hder⟩⟩

/-! ## Signed 3-CNF specialization -/

/-- Signed 3-CNF local N-frame channel: the axiom width budget is fixed at `3`.
-/
def signedThreeCNFLocalResolutionChannel
    (φ : SignedThreeCNF) (sizeBudget : Nat) :
    NFrameLocalResolutionChannel SignedLiteral.compl
      (SignedThreeCNFResolutionAxiom φ)
      (emptyResolutionClause (SignedLiteral φ.numVars)) where
  axiomWidthBudget := 3
  sizeBudget := sizeBudget
  axioms_width := signedThreeCNFResolutionAxioms_width_le_three φ

/-- A signed 3-CNF God-Move boundary is just the signed 3-CNF width lower-bound
interface, re-expressed in observer vocabulary. -/
def SignedThreeCNFGodMoveBoundary
    (φ : SignedThreeCNF) (requiredWidth : Nat) : Prop :=
  RestrictedGodMoveResolutionBoundary SignedLiteral.compl
    (SignedThreeCNFResolutionAxiom φ)
    (emptyResolutionClause (SignedLiteral φ.numVars))
    requiredWidth

/-- Signed 3-CNF specialization of the local-channel obstruction. -/
theorem signedThreeCNF_localChannel_blocked_by_godMoveBoundary
    (φ : SignedThreeCNF) {requiredWidth sizeBudget : Nat}
    (B : SignedThreeCNFGodMoveBoundary φ requiredWidth)
    (hgap : 3 * sizeBudget < requiredWidth) :
    Not ((signedThreeCNFLocalResolutionChannel φ sizeBudget).realizes) :=
  nframeLocalChannel_blocked_by_restrictedGodMoveBoundary
    (signedThreeCNFLocalResolutionChannel φ sizeBudget) B hgap

/-! ## Rung 3 as algebraic/semi-algebraic observer visibility -/

/-- A polynomial-calculus observer boundary is exactly a degree lower bound for
that restricted algebraic channel.  The observer word adds interpretation; the
payload remains the formal PC lower-bound interface. -/
structure ObserverPolynomialCalculusBoundary
    (φ : SignedThreeCNF) (requiredDegree : Nat) : Prop where
  degree_lower_bound :
    PolynomialCalculusDegreeLowerBound
      (SignedThreeCNFPolynomialCalculusAxiom φ)
      polynomialCalculusContradictionLine requiredDegree

/-- A Nullstellensatz observer boundary is the static certificate-degree analogue
of the polynomial-calculus boundary. -/
structure ObserverNullstellensatzBoundary
    (φ : SignedThreeCNF) (requiredDegree : Nat) : Prop where
  degree_lower_bound :
    NullstellensatzDegreeLowerBound
      (SignedThreeCNFPolynomialCalculusAxiom φ)
      polynomialCalculusContradictionLine requiredDegree

/-- A cutting-planes observer boundary is a rank lower bound for the restricted
semi-algebraic channel. -/
structure ObserverCuttingPlanesBoundary
    (φ : SignedThreeCNF) (requiredRank : Nat) : Prop where
  rank_lower_bound :
    Rung3ResourceLowerBound
      (SignedThreeCNFCuttingPlanesAxiom φ)
      cuttingPlanesContradictionLine requiredRank

/-- A bounded-depth Frege observer boundary is a depth/resource lower bound for
the restricted Frege channel. -/
structure ObserverBoundedDepthFregeBoundary
    (φ : SignedThreeCNF) (requiredDepth : Nat) : Prop where
  depth_lower_bound :
    Rung3ResourceLowerBound
      (SignedThreeCNFBoundedDepthFregeAxiom φ)
      boundedDepthFregeContradictionLine requiredDepth

/-- A polynomial-calculus boundary blocks any visible algebraic channel whose
size budget cannot carry the required degree. -/
theorem polynomialCalculusChannel_blocked_by_observerBoundary
    (φ : SignedThreeCNF) {requiredDegree sizeBudget : Nat}
    (B : ObserverPolynomialCalculusBoundary φ requiredDegree)
    (hgap : 3 + sizeBudget < requiredDegree) :
    Not (exists D : SignedThreeCNFPolynomialCalculusRefutation φ,
      D.size <= sizeBudget) :=
  no_small_signedThreeCNF_polynomialCalculus_refutation_of_degree_lower_bound
    φ B.degree_lower_bound hgap

/-- Nullstellensatz inherits the same observer attachment as the static
certificate face of polynomial calculus. -/
theorem nullstellensatzChannel_blocked_by_observerBoundary
    (φ : SignedThreeCNF) {requiredDegree sizeBudget : Nat}
    (B : ObserverNullstellensatzBoundary φ requiredDegree)
    (hgap : 3 + sizeBudget < requiredDegree) :
    Not (exists D : SignedThreeCNFNullstellensatzRefutation φ,
      D.size <= sizeBudget) :=
  no_small_signedThreeCNF_nullstellensatz_refutation_of_degree_lower_bound
    φ B.degree_lower_bound hgap

/-- A cutting-planes rank boundary blocks bounded visible semi-algebraic
channels. -/
theorem cuttingPlanesChannel_blocked_by_observerBoundary
    (φ : SignedThreeCNF) {requiredRank sizeBudget : Nat}
    (B : ObserverCuttingPlanesBoundary φ requiredRank)
    (hgap : 0 + sizeBudget < requiredRank) :
    Not (exists D : SignedThreeCNFCuttingPlanesRefutation φ,
      D.size <= sizeBudget) :=
  no_small_signedThreeCNF_cuttingPlanes_refutation_of_rank_lower_bound
    φ B.rank_lower_bound hgap

/-- A bounded-depth Frege resource boundary blocks channels below the required
visible depth/resource. -/
theorem boundedDepthFregeChannel_blocked_by_observerBoundary
    (φ : SignedThreeCNF) {requiredDepth sizeBudget : Nat}
    (B : ObserverBoundedDepthFregeBoundary φ requiredDepth)
    (hgap : 3 + sizeBudget < requiredDepth) :
    Not (exists D : SignedThreeCNFBoundedDepthFregeRefutation φ,
      D.size <= sizeBudget) :=
  no_small_signedThreeCNF_boundedDepthFrege_refutation_of_depth_lower_bound
    φ B.depth_lower_bound hgap

/-- Rung-3 observer attachment bundle: every rung-3 substrate has a matching
observer-boundary-to-channel-obstruction theorem. -/
structure ObserverRung3Attachment (φ : SignedThreeCNF) : Prop where
  polynomialCalculus :
    forall {requiredDegree sizeBudget : Nat},
      ObserverPolynomialCalculusBoundary φ requiredDegree ->
      3 + sizeBudget < requiredDegree ->
      Not (exists D : SignedThreeCNFPolynomialCalculusRefutation φ,
        D.size <= sizeBudget)
  nullstellensatz :
    forall {requiredDegree sizeBudget : Nat},
      ObserverNullstellensatzBoundary φ requiredDegree ->
      3 + sizeBudget < requiredDegree ->
      Not (exists D : SignedThreeCNFNullstellensatzRefutation φ,
        D.size <= sizeBudget)
  cuttingPlanes :
    forall {requiredRank sizeBudget : Nat},
      ObserverCuttingPlanesBoundary φ requiredRank ->
      0 + sizeBudget < requiredRank ->
      Not (exists D : SignedThreeCNFCuttingPlanesRefutation φ,
        D.size <= sizeBudget)
  boundedDepthFrege :
    forall {requiredDepth sizeBudget : Nat},
      ObserverBoundedDepthFregeBoundary φ requiredDepth ->
      3 + sizeBudget < requiredDepth ->
      Not (exists D : SignedThreeCNFBoundedDepthFregeRefutation φ,
        D.size <= sizeBudget)

/-- The observer vocabulary survives rung 3 as a comparison/invariant layer: in
each algebraic or semi-algebraic substrate, the relevant visible boundary is a
resource lower bound, and resource gaps block bounded local channels. -/
theorem observerRung3Attachment_of_substrates
    (φ : SignedThreeCNF) : ObserverRung3Attachment φ where
  polynomialCalculus := by
    intro requiredDegree sizeBudget B hgap
    exact polynomialCalculusChannel_blocked_by_observerBoundary φ B hgap
  nullstellensatz := by
    intro requiredDegree sizeBudget B hgap
    exact nullstellensatzChannel_blocked_by_observerBoundary φ B hgap
  cuttingPlanes := by
    intro requiredRank sizeBudget B hgap
    exact cuttingPlanesChannel_blocked_by_observerBoundary φ B hgap
  boundedDepthFrege := by
    intro requiredDepth sizeBudget B hgap
    exact boundedDepthFregeChannel_blocked_by_observerBoundary φ B hgap

/-! ## Kernel-only axiom trace -/

#print axioms observerBoundaryVisible_of_expansion
#print axioms completeGraph_observerBoundaryVisible
#print axioms counterfactualObserverBoundary_of_expansion
#print axioms completeGraph_counterfactualObserverBoundary
#print axioms nframeLocalChannel_blocked_by_restrictedGodMoveBoundary
#print axioms mediumClauseVisible_of_derivation
#print axioms signedThreeCNF_localChannel_blocked_by_godMoveBoundary
#print axioms polynomialCalculusChannel_blocked_by_observerBoundary
#print axioms nullstellensatzChannel_blocked_by_observerBoundary
#print axioms cuttingPlanesChannel_blocked_by_observerBoundary
#print axioms boundedDepthFregeChannel_blocked_by_observerBoundary
#print axioms observerRung3Attachment_of_substrates

end PallLean.Paper93.DeepMath.PathB
