import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompleteGraphExpansion
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionMediumClause
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung3Complete
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitSubstrates
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4ParityDecisionTreeCore
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4SwitchingCore

/-!
# Observer/N-frame attachment to proof-complexity rungs 1--4

**STATUS: SAFE ATTACHMENT LAYER, NOT A P-vs-NP BRIDGE.**

The bottom proof-complexity rungs are now real Lean mathematics:

* rung 1: expansion gives a Tseitin boundary/support lower bound;
* rung 2: tree-like resolution width lower bounds give tree-like size lower
  bounds, and the BSW medium-clause descent skeleton is proved.
* rung 3: algebraic/semi-algebraic substrates expose degree/rank/depth
  lower-bound channels.
* rung 4: bounded-depth circuit substrates expose AC⁰/AC⁰[p] lower-bound
  channels, the parity decision-tree endpoint lower bound is proved, and a
  deterministic DNF-to-decision-tree switching core is proved.

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

The later rung-3 and rung-4 attachments follow the same rule: observer
vocabulary means resource visibility for restricted proof systems.  For
Nullstellensatz and cutting planes this now attaches to genuine polynomial and
integer-inequality systems; for bounded-depth Frege it now attaches to a real
formula-level Frege kernel.  For rung 4, observer channels are AC⁰/AC⁰[p]
circuits, decision trees, or DNF switching channels, and observer boundaries are
the corresponding resource lower bounds.  None of this proves the underlying
Tseitin, full Håstad random-restriction, or Razborov--Smolensky lower bounds.
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

/-- A real Nullstellensatz observer boundary is a static polynomial-certificate
degree lower bound over `MvPolynomial`, not a derivation-size claim. -/
structure ObserverNullstellensatzBoundaryReal
    {ι σ F : Type*} [Fintype ι] [CommRing F] [DecidableEq σ]
    (ax : ι → MvPolynomial σ F) (requiredDegree : Nat) : Prop where
  degree_lower_bound :
    NullstellensatzDegreeLowerBoundReal ax requiredDegree

/-- A real cutting-planes observer boundary is a rank lower bound for actual
integer-inequality cutting-planes derivations. -/
structure ObserverCuttingPlanesBoundaryReal
    {σ : Type*} [Fintype σ]
    (Axiom : CuttingPlanesLine σ -> Prop)
    (Target : CuttingPlanesLine σ)
    (requiredRank : Nat) : Prop where
  rank_lower_bound :
    CuttingPlanesRankLowerBound Axiom Target requiredRank

/-- A real bounded-depth Frege observer boundary is a proof-depth lower bound
for the formula-level Frege channel over signed-3-CNF clause axioms. -/
structure ObserverBoundedDepthFregeBoundaryReal
    (φ : SignedThreeCNF) (requiredDepth : Nat) : Prop where
  depth_lower_bound :
    FregeDepthLowerBound
      (SignedThreeCNFFregeAxiom φ)
      (fregeContradictionFormula φ.numVars) requiredDepth

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

/-- A real Nullstellensatz observer boundary forces high-degree coefficient
polynomials once axiom degree is bounded. -/
theorem nullstellensatzChannel_blocked_by_observerBoundaryReal
    {ι σ F : Type*} [Fintype ι] [CommRing F] [DecidableEq σ]
    {ax : ι → MvPolynomial σ F} {requiredDegree axiomDegreeBound : Nat}
    (B : ObserverNullstellensatzBoundaryReal ax requiredDegree)
    (hax : NullstellensatzCertificate.maxAxiomDegree ax ≤ axiomDegreeBound)
    (c : NullstellensatzCertificate ax) :
    requiredDegree ≤ c.maxCoeffDegree + axiomDegreeBound :=
  realNullstellensatz_coeffDegree_forced B.degree_lower_bound hax c

/-- A real cutting-planes rank boundary blocks bounded visible semi-algebraic
channels. -/
theorem cuttingPlanesChannel_blocked_by_observerBoundaryReal
    {σ : Type*} [Fintype σ]
    {Axiom : CuttingPlanesLine σ -> Prop}
    {Target : CuttingPlanesLine σ}
    {requiredRank sizeBudget : Nat}
    (B : ObserverCuttingPlanesBoundaryReal Axiom Target requiredRank)
    (hgap : sizeBudget < requiredRank) :
    Not (exists D : CuttingPlanesDerivation Axiom Target,
      D.size <= sizeBudget) :=
  realCuttingPlanes_no_small_of_rank_lower_bound B.rank_lower_bound hgap

/-- A real bounded-depth Frege proof-depth boundary blocks clause-axiom
refutations once the required depth exceeds the clause depth. -/
theorem boundedDepthFregeChannel_blocked_by_observerBoundaryReal
    (φ : SignedThreeCNF) {requiredDepth : Nat}
    (B : ObserverBoundedDepthFregeBoundaryReal φ requiredDepth)
    (hgap : 3 < requiredDepth) :
    Not (Nonempty (SignedThreeCNFFregeRefutation φ)) :=
  realBoundedDepthFrege_no_refutation_of_depth_lower_bound
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
  realNullstellensatz :
    forall {ι σ F : Type*} [Fintype ι] [CommRing F] [DecidableEq σ]
      {ax : ι → MvPolynomial σ F} {requiredDegree axiomDegreeBound : Nat},
      ObserverNullstellensatzBoundaryReal ax requiredDegree ->
      NullstellensatzCertificate.maxAxiomDegree ax ≤ axiomDegreeBound ->
      forall c : NullstellensatzCertificate ax,
        requiredDegree ≤ c.maxCoeffDegree + axiomDegreeBound
  realCuttingPlanes :
    forall {σ : Type*} [Fintype σ]
      {Axiom : CuttingPlanesLine σ -> Prop}
      {Target : CuttingPlanesLine σ}
      {requiredRank sizeBudget : Nat},
      ObserverCuttingPlanesBoundaryReal Axiom Target requiredRank ->
      sizeBudget < requiredRank ->
      Not (exists D : CuttingPlanesDerivation Axiom Target,
        D.size <= sizeBudget)
  realBoundedDepthFrege :
    forall {requiredDepth : Nat},
      ObserverBoundedDepthFregeBoundaryReal φ requiredDepth ->
      3 < requiredDepth ->
      Not (Nonempty (SignedThreeCNFFregeRefutation φ))

/-- The observer vocabulary survives rung 3 as a comparison/invariant layer: in
each algebraic or semi-algebraic substrate, the relevant visible boundary is a
resource lower bound, and resource gaps block bounded local channels. -/
theorem observerRung3Attachment_of_substrates
    (φ : SignedThreeCNF) : ObserverRung3Attachment φ where
  polynomialCalculus := by
    intro requiredDegree sizeBudget B hgap
    exact polynomialCalculusChannel_blocked_by_observerBoundary φ B hgap
  realNullstellensatz := by
    intro ι σ F _instFintype _instRing _instDecEq ax requiredDegree axiomDegreeBound B hax c
    exact nullstellensatzChannel_blocked_by_observerBoundaryReal B hax c
  realCuttingPlanes := by
    intro σ _instFintype Axiom Target requiredRank sizeBudget B hgap
    exact cuttingPlanesChannel_blocked_by_observerBoundaryReal B hgap
  realBoundedDepthFrege := by
    intro requiredDepth B hgap
    exact boundedDepthFregeChannel_blocked_by_observerBoundaryReal φ B hgap

/-! ## Rung 3 as explicit observer channels -/

/-- A polynomial-calculus observer channel is a signed-3-CNF PC refutation with
a visible size budget. -/
structure NFramePolynomialCalculusChannel (φ : SignedThreeCNF) where
  sizeBudget : Nat

namespace NFramePolynomialCalculusChannel

/-- The PC channel realizes the contradiction if there is a refutation within
its size budget. -/
def realizes {φ : SignedThreeCNF}
    (C : NFramePolynomialCalculusChannel φ) : Prop :=
  exists D : SignedThreeCNFPolynomialCalculusRefutation φ, D.size <= C.sizeBudget

end NFramePolynomialCalculusChannel

/-- Rung-3 polynomial-calculus observer attachment in channel form. -/
theorem nframePolynomialCalculusChannel_blocked_by_observerBoundary
    (φ : SignedThreeCNF) {requiredDegree : Nat}
    (C : NFramePolynomialCalculusChannel φ)
    (B : ObserverPolynomialCalculusBoundary φ requiredDegree)
    (hgap : 3 + C.sizeBudget < requiredDegree) :
    Not C.realizes :=
  polynomialCalculusChannel_blocked_by_observerBoundary φ B hgap

/-- A Nullstellensatz observer channel is a static certificate with bounded
coefficient degree, under a visible axiom-degree budget. -/
structure NFrameNullstellensatzChannel
    {ι σ K : Type*} [Fintype ι] [CommRing K] [DecidableEq σ]
    (ax : ι → MvPolynomial σ K) where
  axiomDegreeBudget : Nat
  coeffDegreeBudget : Nat
  axioms_degree :
    NullstellensatzCertificate.maxAxiomDegree ax <= axiomDegreeBudget

namespace NFrameNullstellensatzChannel

/-- The Nullstellensatz channel realizes the contradiction if it has a bounded
coefficient-degree certificate. -/
def realizes
    {ι σ K : Type*} [Fintype ι] [CommRing K] [DecidableEq σ]
    {ax : ι → MvPolynomial σ K}
    (C : NFrameNullstellensatzChannel ax) : Prop :=
  exists cert : NullstellensatzCertificate ax,
    cert.maxCoeffDegree <= C.coeffDegreeBudget

end NFrameNullstellensatzChannel

/-- Rung-3 Nullstellensatz observer attachment in channel form. -/
theorem nframeNullstellensatzChannel_blocked_by_observerBoundaryReal
    {ι σ K : Type*} [Fintype ι] [CommRing K] [DecidableEq σ]
    {ax : ι → MvPolynomial σ K} {requiredDegree : Nat}
    (C : NFrameNullstellensatzChannel ax)
    (B : ObserverNullstellensatzBoundaryReal ax requiredDegree)
    (hgap : C.coeffDegreeBudget + C.axiomDegreeBudget < requiredDegree) :
    Not C.realizes := by
  rintro ⟨cert, hcert⟩
  have hreq :
      requiredDegree <= cert.maxCoeffDegree + C.axiomDegreeBudget :=
    nullstellensatzChannel_blocked_by_observerBoundaryReal
      B C.axioms_degree cert
  have hbudget :
      cert.maxCoeffDegree + C.axiomDegreeBudget <=
        C.coeffDegreeBudget + C.axiomDegreeBudget :=
    Nat.add_le_add_right hcert _
  exact Nat.not_lt_of_ge (Nat.le_trans hreq hbudget) hgap

/-- A cutting-planes observer channel is a cutting-planes derivation with a
visible size budget. -/
structure NFrameCuttingPlanesChannel
    {σ : Type*} [Fintype σ]
    (Axiom : CuttingPlanesLine σ -> Prop)
    (Target : CuttingPlanesLine σ) where
  sizeBudget : Nat

namespace NFrameCuttingPlanesChannel

/-- The cutting-planes channel realizes the target if there is a derivation
within its size budget. -/
def realizes
    {σ : Type*} [Fintype σ]
    {Axiom : CuttingPlanesLine σ -> Prop}
    {Target : CuttingPlanesLine σ}
    (C : NFrameCuttingPlanesChannel Axiom Target) : Prop :=
  exists D : CuttingPlanesDerivation Axiom Target, D.size <= C.sizeBudget

end NFrameCuttingPlanesChannel

/-- Rung-3 cutting-planes observer attachment in channel form. -/
theorem nframeCuttingPlanesChannel_blocked_by_observerBoundaryReal
    {σ : Type*} [Fintype σ]
    {Axiom : CuttingPlanesLine σ -> Prop}
    {Target : CuttingPlanesLine σ} {requiredRank : Nat}
    (C : NFrameCuttingPlanesChannel Axiom Target)
    (B : ObserverCuttingPlanesBoundaryReal Axiom Target requiredRank)
    (hgap : C.sizeBudget < requiredRank) :
    Not C.realizes :=
  cuttingPlanesChannel_blocked_by_observerBoundaryReal B hgap

/-- A bounded-depth Frege observer channel is a signed-3-CNF Frege refutation
attempt.  Its obstruction is currently the formula-depth lower-bound substrate,
not a full Frege size lower bound. -/
structure NFrameBoundedDepthFregeChannel (φ : SignedThreeCNF) where
  witness : Prop := True

namespace NFrameBoundedDepthFregeChannel

/-- The bounded-depth Frege channel realizes the contradiction if a Frege
refutation exists in the signed-3-CNF Frege substrate. -/
def realizes {φ : SignedThreeCNF}
    (_C : NFrameBoundedDepthFregeChannel φ) : Prop :=
  Nonempty (SignedThreeCNFFregeRefutation φ)

end NFrameBoundedDepthFregeChannel

/-- Rung-3 bounded-depth Frege observer attachment in channel form. -/
theorem nframeBoundedDepthFregeChannel_blocked_by_observerBoundaryReal
    (φ : SignedThreeCNF) {requiredDepth : Nat}
    (C : NFrameBoundedDepthFregeChannel φ)
    (B : ObserverBoundedDepthFregeBoundaryReal φ requiredDepth)
    (hgap : 3 < requiredDepth) :
    Not C.realizes :=
  boundedDepthFregeChannel_blocked_by_observerBoundaryReal φ B hgap

/-- Channel-level observer attachment for rung 3.  This is still restricted
proof-complexity infrastructure; it does not claim arbitrary SAT algorithms
induce these channels. -/
structure ObserverRung3ChannelAttachment (φ : SignedThreeCNF) : Prop where
  polynomialCalculus :
    forall {requiredDegree : Nat} (C : NFramePolynomialCalculusChannel φ),
      ObserverPolynomialCalculusBoundary φ requiredDegree ->
      3 + C.sizeBudget < requiredDegree ->
      Not C.realizes
  realNullstellensatz :
    forall {ι σ K : Type*} [Fintype ι] [CommRing K] [DecidableEq σ]
      {ax : ι → MvPolynomial σ K} {requiredDegree : Nat}
      (C : NFrameNullstellensatzChannel ax),
      ObserverNullstellensatzBoundaryReal ax requiredDegree ->
      C.coeffDegreeBudget + C.axiomDegreeBudget < requiredDegree ->
      Not C.realizes
  realCuttingPlanes :
    forall {σ : Type*} [Fintype σ]
      {Axiom : CuttingPlanesLine σ -> Prop}
      {Target : CuttingPlanesLine σ} {requiredRank : Nat}
      (C : NFrameCuttingPlanesChannel Axiom Target),
      ObserverCuttingPlanesBoundaryReal Axiom Target requiredRank ->
      C.sizeBudget < requiredRank ->
      Not C.realizes
  realBoundedDepthFrege :
    forall {requiredDepth : Nat} (C : NFrameBoundedDepthFregeChannel φ),
      ObserverBoundedDepthFregeBoundaryReal φ requiredDepth ->
      3 < requiredDepth ->
      Not C.realizes

/-- Rung 3 has an explicit observer-channel attachment for each completed
substrate. -/
theorem observerRung3ChannelAttachment_of_substrates
    (φ : SignedThreeCNF) : ObserverRung3ChannelAttachment φ where
  polynomialCalculus := by
    intro requiredDegree C B hgap
    exact nframePolynomialCalculusChannel_blocked_by_observerBoundary
      φ C B hgap
  realNullstellensatz := by
    intro ι σ K _instFintype _instRing _instDecEq ax requiredDegree C B hgap
    exact nframeNullstellensatzChannel_blocked_by_observerBoundaryReal C B hgap
  realCuttingPlanes := by
    intro σ _instFintype Axiom Target requiredRank C B hgap
    exact nframeCuttingPlanesChannel_blocked_by_observerBoundaryReal C B hgap
  realBoundedDepthFrege := by
    intro requiredDepth C B hgap
    exact nframeBoundedDepthFregeChannel_blocked_by_observerBoundaryReal
      φ C B hgap

/-! ## Rung 4 as bounded-depth observer channels -/

/-- An AC⁰ observer boundary is exactly a pointwise AC⁰ size lower bound. -/
structure ObserverAC0CircuitBoundary
    (F : (n : Nat) -> BoolFunction n)
    (n depthBudget requiredSize : Nat) : Prop where
  size_lower_bound :
    AC0SizeLowerBoundAt F n depthBudget requiredSize

/-- An AC⁰[p] observer boundary is exactly a pointwise AC⁰[p] size lower
bound. -/
structure ObserverAC0pCircuitBoundary
    (p : Nat) (F : (n : Nat) -> BoolFunction n)
    (n depthBudget requiredSize : Nat) : Prop where
  size_lower_bound :
    AC0pSizeLowerBoundAt p F n depthBudget requiredSize

/-- A parity decision-tree observer boundary is the proved lower bound that
every decision tree computing parity on `n` bits has depth at least `n`. -/
structure ObserverParityDecisionTreeBoundary (n : Nat) : Prop where
  depth_lower_bound :
    forall T : BoolDecisionTree n,
      T.Computes (parityFunction n) -> n <= T.depth

/-- A DNF switching observer boundary is the proved deterministic switching
kernel: every DNF computing parity on `n` bits has total literal width at least
`n`. -/
structure ObserverDNFSwitchingBoundary (n : Nat) : Prop where
  totalWidth_lower_bound :
    forall D : Rung4DNF n,
      D.Computes (parityFunction n) -> n <= D.totalWidth

/-- The parity decision-tree observer boundary is actually proved in this
repository. -/
theorem observerParityDecisionTreeBoundary (n : Nat) :
    ObserverParityDecisionTreeBoundary n where
  depth_lower_bound := by
    intro T hcomp
    exact BoolDecisionTree.depth_ge_of_computes_parity T hcomp

/-- The DNF switching observer boundary is actually proved in this repository.
It is the deterministic endpoint of the switching route, not Håstad's full
probabilistic switching lemma. -/
theorem observerDNFSwitchingBoundary (n : Nat) :
    ObserverDNFSwitchingBoundary n where
  totalWidth_lower_bound := by
    intro D hcomp
    exact Rung4DNF.totalWidth_ge_of_computes_parity D hcomp

/-- A restricted AC⁰ observer channel is a bounded-depth, bounded-size AC⁰
circuit attempt for a target Boolean-function family. -/
structure NFrameAC0CircuitChannel
    (F : (n : Nat) -> BoolFunction n) (n : Nat) where
  depthBudget : Nat
  sizeBudget : Nat

namespace NFrameAC0CircuitChannel

/-- The AC⁰ channel realizes the target if such a circuit exists within both
budgets. -/
def realizes
    {F : (n : Nat) -> BoolFunction n} {n : Nat}
    (C : NFrameAC0CircuitChannel F n) : Prop :=
  exists A : AC0Circuit n,
    A.computes = F n /\ A.depth <= C.depthBudget /\ A.size <= C.sizeBudget

end NFrameAC0CircuitChannel

/-- An AC⁰ observer boundary blocks smaller bounded-depth AC⁰ observer
channels. -/
theorem nframeAC0CircuitChannel_blocked_by_observerBoundary
    {F : (n : Nat) -> BoolFunction n} {n requiredSize : Nat}
    (C : NFrameAC0CircuitChannel F n)
    (B : ObserverAC0CircuitBoundary F n C.depthBudget requiredSize)
    (hgap : C.sizeBudget < requiredSize) :
    Not C.realizes :=
  no_small_AC0Circuit_of_size_lower_bound B.size_lower_bound hgap

/-- A restricted AC⁰[p] observer channel is a bounded-depth, bounded-size
AC⁰[p] circuit attempt for a target Boolean-function family. -/
structure NFrameAC0pCircuitChannel
    (p : Nat) (F : (n : Nat) -> BoolFunction n) (n : Nat) where
  depthBudget : Nat
  sizeBudget : Nat

namespace NFrameAC0pCircuitChannel

/-- The AC⁰[p] channel realizes the target if such a circuit exists within both
budgets and with the requested modulus. -/
def realizes
    {p : Nat} {F : (n : Nat) -> BoolFunction n} {n : Nat}
    (C : NFrameAC0pCircuitChannel p F n) : Prop :=
  exists A : AC0pCircuit n,
    A.p = p /\ A.computes = F n /\
      A.depth <= C.depthBudget /\ A.size <= C.sizeBudget

end NFrameAC0pCircuitChannel

/-- An AC⁰[p] observer boundary blocks smaller bounded-depth AC⁰[p] observer
channels. -/
theorem nframeAC0pCircuitChannel_blocked_by_observerBoundary
    {p : Nat} {F : (n : Nat) -> BoolFunction n} {n requiredSize : Nat}
    (C : NFrameAC0pCircuitChannel p F n)
    (B : ObserverAC0pCircuitBoundary p F n C.depthBudget requiredSize)
    (hgap : C.sizeBudget < requiredSize) :
    Not C.realizes :=
  no_small_AC0pCircuit_of_size_lower_bound B.size_lower_bound hgap

/-- A restricted decision-tree observer channel for parity. -/
structure NFrameParityDecisionTreeChannel (n : Nat) where
  depthBudget : Nat

namespace NFrameParityDecisionTreeChannel

/-- The parity decision-tree channel realizes parity if a decision tree computes
parity within the visible depth budget. -/
def realizes {n : Nat}
    (C : NFrameParityDecisionTreeChannel n) : Prop :=
  exists T : BoolDecisionTree n,
    T.Computes (parityFunction n) /\ T.depth <= C.depthBudget

end NFrameParityDecisionTreeChannel

/-- The proved parity decision-tree boundary blocks shallow decision-tree
observer channels. -/
theorem nframeParityDecisionTreeChannel_blocked_by_observerBoundary
    {n : Nat} (C : NFrameParityDecisionTreeChannel n)
    (B : ObserverParityDecisionTreeBoundary n)
    (hgap : C.depthBudget < n) :
    Not C.realizes := by
  rintro ⟨T, hcomp, hdepth⟩
  have hlower : n <= T.depth := B.depth_lower_bound T hcomp
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hdepth) hgap

/-- A restricted DNF switching channel for parity.  The resource is total
literal width, not AC⁰ circuit size. -/
structure NFrameDNFSwitchingChannel (n : Nat) where
  totalWidthBudget : Nat

namespace NFrameDNFSwitchingChannel

/-- The DNF switching channel realizes parity if a DNF computes parity within
the visible total-width budget. -/
def realizes {n : Nat}
    (C : NFrameDNFSwitchingChannel n) : Prop :=
  exists D : Rung4DNF n,
    D.Computes (parityFunction n) /\ D.totalWidth <= C.totalWidthBudget

end NFrameDNFSwitchingChannel

/-- The proved DNF switching boundary blocks total-width-bounded DNF observer
channels for parity. -/
theorem nframeDNFSwitchingChannel_blocked_by_observerBoundary
    {n : Nat} (C : NFrameDNFSwitchingChannel n)
    (B : ObserverDNFSwitchingBoundary n)
    (hgap : C.totalWidthBudget < n) :
    Not C.realizes := by
  rintro ⟨D, hcomp, hwidth⟩
  have hlower : n <= D.totalWidth := B.totalWidth_lower_bound D hcomp
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hwidth) hgap

/-- AC⁰ parity is just the AC⁰ observer attachment specialized to parity. -/
theorem nframeAC0ParityChannel_blocked_by_observerBoundary
    {n requiredSize : Nat}
    (C : NFrameAC0CircuitChannel parityFunction n)
    (B : ObserverAC0CircuitBoundary parityFunction n C.depthBudget requiredSize)
    (hgap : C.sizeBudget < requiredSize) :
    Not C.realizes :=
  nframeAC0CircuitChannel_blocked_by_observerBoundary C B hgap

/-- AC⁰[p] parity is just the AC⁰[p] observer attachment specialized to parity.
-/
theorem nframeAC0pParityChannel_blocked_by_observerBoundary
    {p n requiredSize : Nat}
    (C : NFrameAC0pCircuitChannel p parityFunction n)
    (B : ObserverAC0pCircuitBoundary p parityFunction n C.depthBudget requiredSize)
    (hgap : C.sizeBudget < requiredSize) :
    Not C.realizes :=
  nframeAC0pCircuitChannel_blocked_by_observerBoundary C B hgap

/-- Rung-4 observer attachment bundle: the observer vocabulary is now wired to
AC⁰, AC⁰[p], parity-specialized circuits, and the proved parity decision-tree
core. -/
structure ObserverRung4Attachment : Prop where
  ac0 :
    forall {F : (n : Nat) -> BoolFunction n} {n requiredSize : Nat}
      (C : NFrameAC0CircuitChannel F n),
      ObserverAC0CircuitBoundary F n C.depthBudget requiredSize ->
      C.sizeBudget < requiredSize ->
      Not C.realizes
  ac0p :
    forall {p : Nat} {F : (n : Nat) -> BoolFunction n} {n requiredSize : Nat}
      (C : NFrameAC0pCircuitChannel p F n),
      ObserverAC0pCircuitBoundary p F n C.depthBudget requiredSize ->
      C.sizeBudget < requiredSize ->
      Not C.realizes
  ac0Parity :
    forall {n requiredSize : Nat}
      (C : NFrameAC0CircuitChannel parityFunction n),
      ObserverAC0CircuitBoundary parityFunction n C.depthBudget requiredSize ->
      C.sizeBudget < requiredSize ->
      Not C.realizes
  ac0pParity :
    forall {p n requiredSize : Nat}
      (C : NFrameAC0pCircuitChannel p parityFunction n),
      ObserverAC0pCircuitBoundary p parityFunction n C.depthBudget requiredSize ->
      C.sizeBudget < requiredSize ->
      Not C.realizes
  parityDecisionTreeBoundary :
    forall n : Nat, ObserverParityDecisionTreeBoundary n
  parityDecisionTreeChannel :
    forall {n : Nat} (C : NFrameParityDecisionTreeChannel n),
      ObserverParityDecisionTreeBoundary n ->
      C.depthBudget < n ->
      Not C.realizes
  dnfSwitchingBoundary :
    forall n : Nat, ObserverDNFSwitchingBoundary n
  dnfSwitchingChannel :
    forall {n : Nat} (C : NFrameDNFSwitchingChannel n),
      ObserverDNFSwitchingBoundary n ->
      C.totalWidthBudget < n ->
      Not C.realizes

/-- Rung 4 has a formal observer attachment to the circuit substrates and to
the proved parity decision-tree and DNF switching cores. -/
theorem observerRung4Attachment_of_substrates :
    ObserverRung4Attachment where
  ac0 := by
    intro F n requiredSize C B hgap
    exact nframeAC0CircuitChannel_blocked_by_observerBoundary C B hgap
  ac0p := by
    intro p F n requiredSize C B hgap
    exact nframeAC0pCircuitChannel_blocked_by_observerBoundary C B hgap
  ac0Parity := by
    intro n requiredSize C B hgap
    exact nframeAC0ParityChannel_blocked_by_observerBoundary C B hgap
  ac0pParity := by
    intro p n requiredSize C B hgap
    exact nframeAC0pParityChannel_blocked_by_observerBoundary C B hgap
  parityDecisionTreeBoundary := observerParityDecisionTreeBoundary
  parityDecisionTreeChannel := by
    intro n C B hgap
    exact nframeParityDecisionTreeChannel_blocked_by_observerBoundary C B hgap
  dnfSwitchingBoundary := observerDNFSwitchingBoundary
  dnfSwitchingChannel := by
    intro n C B hgap
    exact nframeDNFSwitchingChannel_blocked_by_observerBoundary C B hgap

/-! ## Kernel-only axiom trace -/

#print axioms observerBoundaryVisible_of_expansion
#print axioms completeGraph_observerBoundaryVisible
#print axioms counterfactualObserverBoundary_of_expansion
#print axioms completeGraph_counterfactualObserverBoundary
#print axioms nframeLocalChannel_blocked_by_restrictedGodMoveBoundary
#print axioms mediumClauseVisible_of_derivation
#print axioms signedThreeCNF_localChannel_blocked_by_godMoveBoundary
#print axioms polynomialCalculusChannel_blocked_by_observerBoundary
#print axioms nullstellensatzChannel_blocked_by_observerBoundaryReal
#print axioms cuttingPlanesChannel_blocked_by_observerBoundaryReal
#print axioms boundedDepthFregeChannel_blocked_by_observerBoundaryReal
#print axioms observerRung3Attachment_of_substrates
#print axioms nframePolynomialCalculusChannel_blocked_by_observerBoundary
#print axioms nframeNullstellensatzChannel_blocked_by_observerBoundaryReal
#print axioms nframeCuttingPlanesChannel_blocked_by_observerBoundaryReal
#print axioms nframeBoundedDepthFregeChannel_blocked_by_observerBoundaryReal
#print axioms observerRung3ChannelAttachment_of_substrates
#print axioms observerParityDecisionTreeBoundary
#print axioms observerDNFSwitchingBoundary
#print axioms nframeAC0CircuitChannel_blocked_by_observerBoundary
#print axioms nframeAC0pCircuitChannel_blocked_by_observerBoundary
#print axioms nframeParityDecisionTreeChannel_blocked_by_observerBoundary
#print axioms nframeDNFSwitchingChannel_blocked_by_observerBoundary
#print axioms nframeAC0ParityChannel_blocked_by_observerBoundary
#print axioms nframeAC0pParityChannel_blocked_by_observerBoundary
#print axioms observerRung4Attachment_of_substrates

end PallLean.Paper93.DeepMath.PathB
