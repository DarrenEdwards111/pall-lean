import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinInstance
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinCNF
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHypercubeTseitin
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionDAG
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHypercubeDAGWidth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHypercubeTseitinFamily
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationExpSize
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung3Complete
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitSubstrates
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4ParityDecisionTreeCore
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4SwitchingCore
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitReal
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung5IntermediateModels
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverInvariantTransfer
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung5ToyLowerBounds
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung5VariableAccessLowerBounds
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung5FormulaVariableAccessLowerBounds
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSubfunctionObserverInvariant
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSubfunctionCapacityWall
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingCapacityLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDNFEqualityLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEqualityUpperBounds
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung6GeneralModelWall
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMetacomplexityFrontier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTC0NC1ObserverRoute
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthThresholdCompositionFrontier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayeredThresholdInvariant

/-!
# Proof-complexity bridge ladder (a map, with both ends anchored to real theorems)

**STATUS: A MAP, NOT A PROOF OF P≠NP.** This file records the stepwise ladder
from a real, proved lower bound up to the P-vs-NP wall.  Each rung is a
*theorem*, a *cited known result*, or an *explicitly open bridge* — never a wish,
and never an assumed `Prop` field.  Two rungs are anchored to actual Lean facts
in this repo: the bottom (proved) and the top (proven equal to the separation).

## The ladder

* **Rung 1 — Resolution width.  PROVED (here).**
  Expander-Tseitin forces resolution width `≥ c · |S|`.  Anchored by
  `ladder_rung1_width_lower_bound` (the kernel) and `ladder_rung1_concrete`
  (the `K4` instance with expansion proved by decision procedure).

* **Rung 2 — Resolution size.  PROVED (here), for tree-like / weakening
  resolution.**  The full Ben-Sasson–Wigderson width⇒size argument is now
  formalized ground-up: the tree-like size–width theorem
  (`proofWidth ≤ w₀ + ⌈log₂ size⌉`) composed with the rung-1 width bound gives an
  exponential size lower bound for the canonical Tseitin CNF on any expander
  (`ladder_rung2_size_lower_bound`, anchored by `TseitinResolution.tseitinCNF_exp_size`),
  and the hypercube instance discharges the expander concretely, yielding a fully
  explicit numeric `2^{Ω(|V|)}` bound (`ladder_rung2_concrete`), self-contained with
  no free parameters for every `k ≥ 5` (`ladder_rung2_family`), all anchored by
  `Hypercube.*`.  The **width** bound moreover holds for *unrestricted (DAG)*
  resolution, not just tree-like (`ladder_rung1_dag_width`, `ladder_rung1_dag_concrete`,
  anchored by `dag_resolution_width_lower_bound` / `Hypercube.hypercube_dag_width`).
  The general **DAG-resolution *size*** bound (the `√` size–width method) is now
  also PROVED ground-up in the list-derivation model: restriction-with-removal,
  the popular-literal fat-count decay, the asymmetric branching recombination, and
  the variable-count recursion give `W(F) ≤ w₀+d+b` under `(n-d)^b·#fat < n^b`,
  which composed with the rung-1 width bound yields a size lower bound on actual
  refutation length and an explicit exponential `2^j ≤ |L|`
  (`ladder_rung2_dag_size_length`, `ladder_rung2_dag_size_exp`, anchored by
  `LDeriv.tseitin_size_lower` / `LDeriv.tseitin_size_exp`).
  Cf. Ben-Sasson–Wigderson, "Short proofs are narrow" (2001); Urquhart (1987).
  Resolution *space* lower bounds (Esteban–Torán, Ben-Sasson) remain cited.

* **Rung 3 — Polynomial calculus / Nullstellensatz / cutting planes /
  bounded-depth Frege.  SUBSTRATES PROVED; SYSTEM LOWER BOUNDS CITED/OPEN.**
  This repo now proves the rung-3 substrate bundle in
  `ComputationalDepthRung3Complete`: polynomial-calculus degree, Nullstellensatz
  degree, cutting-planes rank, and bounded-depth Frege depth each get a formal
  lower-bound interface plus a proved small-tree obstruction theorem for signed
  3-CNF.  The hard family-specific lower bounds remain literature results, not
  assumed Lean fields: PC degree & size lower bounds for Tseitin:
  Buss–Grigoriev–Impagliazzo–Pitassi, Alekhnovich–Razborov; cutting-planes lower
  bounds via interpolation: Pudlák (1997); bounded-depth (AC⁰-)Frege lower bounds
  for Tseitin: Håstad, Pitassi–Rossman–Servedio–Tan.

* **Rung 4 — Bounded-depth circuits (AC⁰, AC⁰[p]).  SUBSTRATES PROVED;
  PARITY DECISION-TREE CORE PROVED; DNF SWITCHING CORE PROVED;
  FULL SWITCHING-LEMMA/POLYNOMIAL-METHOD LOWER BOUNDS CITED.**
  `ComputationalDepthRung4CircuitSubstrates` formalizes Boolean functions,
  parity, AC⁰/AC⁰[p] circuit families, size/depth lower-bound interfaces, and
  no-small-circuit consequences.  `ComputationalDepthRung4ParityDecisionTreeCore`
  proves the endpoint lower-bound engine used after switching-lemma
  simplification: every decision tree computing parity on `n` variables has
  depth at least `n`.  `ComputationalDepthRung4SwitchingCore` proves the
  deterministic DNF-to-decision-tree endpoint and a restricted switching
  substrate: restricting a DNF, simplifying the residual, and compiling it into
  a decision tree whose depth is bounded by the residual total literal width.
  The full probabilistic switching lemma and polynomial-method engines remain
  cited: parity ∉ AC⁰ by Håstad; AC⁰[p] lower bounds by Razborov–Smolensky.

* **Rung 5 — TC⁰ / NC¹ / branching programs / bounded space.  SUBSTRATES
  PROVED; STRONG LOWER BOUNDS MOSTLY OPEN.**
  `ComputationalDepthRung5IntermediateModels` formalizes TC⁰-style threshold
  circuits, NC¹-style formulas, deterministic branching programs, bounded-space
  finite-configuration machines, and a Barrington-style transfer interface with
  lower-bound consequence theorems.  It also proves two tiny real endpoint
  kernels: width-1 branching programs and one-configuration machines cannot
  compute parity on nonempty inputs.  Unconditional TC⁰ lower bounds for
  explicit functions remain largely open; Barrington (width-5 BP = NC¹) shows
  how quickly "bounded" stops being weak.  `ComputationalDepthObserverInvariantTransfer`
  extracts the common observer invariant from rungs 1--4 and extends it to
  TC⁰, NC¹/formulas, width-5 BP, and bounded-space as formal transfer theorems:
  if the relevant frontier lower bound is supplied, the invariant blocks the
  budgeted model.  `ComputationalDepthRung5ToyLowerBounds` proves the same
  mechanism against deliberately weakened input-blind TC⁰/NC¹ toy subclasses.
  `ComputationalDepthRung5VariableAccessLowerBounds` proves a stronger
  variable-access toy theorem: any query branching program computing parity must
  query every variable, hence has length at least `n`.  `ComputationalDepthRung5FormulaVariableAccessLowerBounds`
  proves the analogous formula floor: any formula computing parity must mention
  every variable, hence has size at least `n`.  `ComputationalDepthSubfunctionObserverInvariant`
  upgrades the observer vocabulary to residual/subfunction counts, an invariant
  with exponential range, and proves the generic super-polynomial transfer schema.
  `ComputationalDepthDNFEqualityLowerBound` proves an actual exponential lower
  bound using this invariant: equality-split requires `2^n` ordinary DNF terms.
  `ComputationalDepthEqualityUpperBounds` proves why this lower bound cannot lift
  to full formula/NC¹-style computation for equality: equality has a linear-size
  split formula.  `ComputationalDepthSubfunctionCapacityWall` proves the corresponding wall:
  unrestricted semantic models can expose `2^n` residuals at unit syntactic
  budget. `ComputationalDepthCrossingCapacityLowerBound` proves the positive
  restricted counterpart: if computation crosses a block boundary through `c`
  states, it exposes at most `c` residuals, and storage access forces `2^m`
  states. The TC⁰/NC¹/width-5 frontier lower bounds themselves are not proved
  here. This is where current techniques stall — the barriers bite here.

* **Rung 6 — General polynomial-time computation.  WALL SUBSTRATE PROVED;
  OPEN = P vs NP.**
  THE WALL.  `ComputationalDepthRung6GeneralModelWall` proves the conservation
  theorem for unrestricted bridges: any universal map from arbitrary P-time SAT
  deciders into an impossible restricted obstruction is equivalent to the
  no-decider endpoint itself.  A general-model lower bound for the family is
  *equivalent* to the separation — anchored by `ladder_rung6_wall_substrate` and
  `ladder_top_rung_iff_separation` (reusing the metacomplexity bridge).

## The honest reading of the climb

The ladder is real and worth climbing rung by rung: rungs 1–5 now have proved
substrates or checked cores, the hard lower-bound engines thin out at rung 5,
and rung 6 is the separation.  But the pattern across rungs **cannot be assumed
to generalise** to rung 6.  The final
generalisation is not a way around the wall — it *is* the wall: by
`ladder_top_rung_iff_separation`, the top-rung bridge is logically equivalent to
`¬(SAT ∈ P-class)`.  So this file gives a map for gradual progress and a precise
marker of where the wall stands; it does not, and cannot, cross it by extrapolating
a pattern that "P-observers can't see" — in formal mathematics the unseen
generalisation still needs a proof, and that proof is P≠NP.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

/-! ## Rung 1 (PROVED): expander-Tseitin forces resolution width -/

/-- **Rung 1, general.**  On any graph with vertex expansion `c`, the F₂
combination of a medium vertex set's Tseitin constraints has width `≥ c · |S|`.
This is the proved bottom of the ladder. -/
theorem ladder_rung1_width_lower_bound
    {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
    (G : TseitinGraph V Edge) {c : ℕ} (hexp : G.HasExpansion c)
    (S : Finset V) (h1 : 1 ≤ S.card) (h2 : 2 * S.card ≤ Fintype.card V) :
    c * S.card ≤ (edgeSupport (G.combination S)).card :=
  G.combination_support_card_ge_of_expansion hexp S h1 h2

/-- **Rung 1, concrete witness.**  The bottom rung is non-vacuously inhabited by
`K4` (expansion proved by decision procedure). -/
theorem ladder_rung1_concrete (S : Finset (Fin 4))
    (h1 : 1 ≤ S.card) (h2 : 2 * S.card ≤ Fintype.card (Fin 4)) :
    2 * S.card ≤ (edgeSupport (K4.combination S)).card :=
  K4_combination_width S h1 h2

/-! ## Rung 2 (PROVED): width ⇒ exponential resolution size -/

/-- **Rung 2, general.**  Width ⇒ size, formalized: on any expander, every
tree-like/weakening resolution refutation of the canonical Tseitin CNF (odd charge,
degrees `≤ w₀`, `w₀ < c·t`, `4t ≤ |V|`) has size `> 2^{c·t - w₀ - 1}`.  The full
Ben-Sasson–Wigderson width⇒size argument, proved ground-up rather than cited. -/
theorem ladder_rung2_size_lower_bound
    {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
    (G : TseitinGraph V Edge) (charge : V → ZMod 2) (hodd : ∑ v : V, charge v = 1)
    {c t w₀ : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht1 : 1 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V)
    (hdeg : ∀ v, (TseitinResolution.incident G v).card ≤ w₀) (hgap : w₀ < c * t)
    (Der : ResolutionDerivation TseitinResolution.tcompl
      (TseitinResolution.TseitinCNF G charge) ∅) :
    2 ^ (c * t - w₀ - 1) < ResolutionDerivation.size Der :=
  TseitinResolution.tseitinCNF_exp_size G charge hodd hc hexp ht1 hcard hdeg hgap Der

/-- **Rung 2, concrete witness.**  The hypercube `Q_k` discharges the expander,
giving a fully explicit, numeric exponential lower bound: the hypercube-Tseitin CNF
needs resolution size `> 2^{t-k-1}` (so `2^{Ω(|V|)}` at `t = 2^k/4`). -/
theorem ladder_rung2_concrete (k : ℕ) {t : ℕ}
    (ht1 : 1 ≤ t) (hcard : 4 * t ≤ 2 ^ k) (hgap : k < t)
    (Der : ResolutionDerivation TseitinResolution.tcompl
      (TseitinResolution.TseitinCNF (Hypercube.hypercubeGraph k)
        (fun v => if v = 0 then 1 else 0)) ∅) :
    2 ^ (t - k - 1) < ResolutionDerivation.size Der :=
  Hypercube.hypercube_tseitin_exp_size k ht1 hcard hgap Der

/-- **Rung 2, self-contained family.**  No free parameters: for every `k ≥ 5`, the
hypercube-Tseitin CNF (an explicit unsatisfiable CNF on `k·2^{k-1}` variables) needs
tree-like resolution refutations of size `> 2^{2^{k-2}-k-1} = 2^{Ω(|V|)}`. -/
theorem ladder_rung2_family (k : ℕ) (hk : 5 ≤ k)
    (Der : ResolutionDerivation TseitinResolution.tcompl
      (TseitinResolution.TseitinCNF (Hypercube.hypercubeGraph k)
        (fun v => if v = 0 then 1 else 0)) ∅) :
    2 ^ (2 ^ (k - 2) - k - 1) < ResolutionDerivation.size Der :=
  Hypercube.hypercube_tseitin_family k hk Der

/-! ## Rung 1–2 strengthening (PROVED): general (DAG) resolution width -/

/-- **General-resolution width.**  The width bound holds not only for tree-like but
for *unrestricted (DAG)* resolution: every DAG refutation of expander-Tseitin
contains a clause of width `≥ c·t`. -/
theorem ladder_rung1_dag_width
    {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
    (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TseitinResolution.TConstr G charge v a)
    (Axiom : ResolutionClause (TseitinResolution.TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C →
      ∃ v : V, SemanticMeasure.Implies TseitinResolution.TSat (TseitinResolution.TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) {n : ℕ}
    (D : ResolutionDAG TseitinResolution.tcompl Axiom n) (i₀ : Fin n)
    (hi₀ : D.clause i₀ = (∅ : ResolutionClause (TseitinResolution.TLit Edge))) :
    ∃ i : Fin n, c * t ≤ ResolutionClause.width (D.clause i) :=
  dag_resolution_width_lower_bound G charge hunsat Axiom haxiom hc hexp ht2 hcard D i₀ hi₀

/-- **General-resolution width, concrete.**  Every DAG resolution refutation of the
explicit hypercube-Tseitin CNF has a clause of width `≥ t` (`Ω(|V|)` at `t=2^k/4`). -/
theorem ladder_rung1_dag_concrete (k : ℕ) {t : ℕ} (ht2 : 2 ≤ t) (hcard : 4 * t ≤ 2 ^ k) {n : ℕ}
    (D : ResolutionDAG TseitinResolution.tcompl
      (TseitinResolution.TseitinCNF (Hypercube.hypercubeGraph k)
        (fun v => if v = 0 then 1 else 0)) n)
    (i₀ : Fin n) (hi₀ : D.clause i₀ = (∅ : ResolutionClause (TseitinResolution.TLit (Hypercube.HCEdge k)))) :
    ∃ i : Fin n, t ≤ ResolutionClause.width (D.clause i) :=
  Hypercube.hypercube_dag_width k ht2 hcard D i₀ hi₀

/-! ## Rung 2 strengthening (PROVED): general (DAG) resolution *size*

The size lower bound, like the width bound, holds for *unrestricted* resolution —
not only tree-like.  The Ben-Sasson–Wigderson general (DAG) size–width method is
formalized ground-up in the list-derivation (`LDeriv`) model: restriction with
clause removal, the popular-literal fat-count decay, the asymmetric branching
recombination, the variable-count termination measure, and the resulting
recursion `W(F) ≤ w₀ + d + b` under the invariant `(n-d)^b·#fat < n^b`.  Composed
with the rung-1 width lower bound `c·t`, this gives an honest size lower bound on
the actual refutation length, and an explicit exponential `2^j ≤ |L|`. -/

/-- **General-resolution size, length form.**  For unrestricted (DAG/weakening)
resolution in the list model: any refutation of expander-Tseitin axioms has length
`≥ n^b / (n-d)^b`, i.e. `n^b ≤ (n-d)^b · |L|`, whenever the width budget `w₀+d+b`
stays below the rung-1 lower bound `c·t`. -/
theorem ladder_rung2_dag_size_length
    {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge] [Nonempty Edge]
    (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TseitinResolution.TConstr G charge v a)
    (Ax : List (ResolutionClause (TseitinResolution.TLit Edge)))
    (hAxiom : ∀ C, C ∈ Ax →
      ∃ v : V, SemanticMeasure.Implies TseitinResolution.TSat (TseitinResolution.TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) {w₀ : ℕ} (hw0 : ∀ C ∈ Ax, ResolutionClause.width C ≤ w₀)
    {d b : ℕ} (hd : 0 < d) {L : List (ResolutionClause (TseitinResolution.TLit Edge))}
    (hLD : LDeriv TseitinResolution.tcompl (· ∈ Ax) L)
    (hmt : (∅ : ResolutionClause (TseitinResolution.TLit Edge)) ∈ L)
    (hsmall : w₀ + d + b < c * t) :
    Fintype.card (TseitinResolution.TLit Edge) ^ b
      ≤ (Fintype.card (TseitinResolution.TLit Edge) - d) ^ b * L.length :=
  LDeriv.tseitin_size_lower G charge hunsat Ax hAxiom hc hexp ht2 hcard hw0 hd hLD hmt hsmall

/-- **General-resolution size, explicit exponential.**  Every DAG/weakening
resolution refutation of expander-Tseitin has length `≥ 2^j`, whenever the
doubling condition `n-d ≤ k·d` holds (`n = |literals|`) and the width budget
`w₀+d+k·j` stays below the rung-1 lower bound `c·t`. -/
theorem ladder_rung2_dag_size_exp
    {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge] [Nonempty Edge]
    (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TseitinResolution.TConstr G charge v a)
    (Ax : List (ResolutionClause (TseitinResolution.TLit Edge)))
    (hAxiom : ∀ C, C ∈ Ax →
      ∃ v : V, SemanticMeasure.Implies TseitinResolution.TSat (TseitinResolution.TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) {w₀ : ℕ} (hw0 : ∀ C ∈ Ax, ResolutionClause.width C ≤ w₀)
    {d k j : ℕ} (hd : 0 < d) (hk1 : 1 ≤ k)
    (hdn : d < Fintype.card (TseitinResolution.TLit Edge))
    (hkd : Fintype.card (TseitinResolution.TLit Edge) - d ≤ k * d)
    {L : List (ResolutionClause (TseitinResolution.TLit Edge))}
    (hLD : LDeriv TseitinResolution.tcompl (· ∈ Ax) L)
    (hmt : (∅ : ResolutionClause (TseitinResolution.TLit Edge)) ∈ L)
    (hsmall : w₀ + d + k * j < c * t) :
    2 ^ j ≤ L.length :=
  LDeriv.tseitin_size_exp G charge hunsat Ax hAxiom hc hexp ht2 hcard hw0 hd hk1 hdn hkd hLD hmt hsmall

/-! ## Rung 3 (SUBSTRATES PROVED): algebraic/semi-algebraic systems -/

/-- **Rung 3, signed-3-CNF polynomial-calculus substrate.**  If a signed 3-CNF
formula has polynomial-calculus degree lower bound `d`, then no tree-like
polynomial-calculus refutation of size `s` exists whenever `3 + s < d`.

This is deliberately not advertised as the full Tseitin polynomial-calculus lower
bound; it is the formal accounting layer that such a lower bound plugs into. -/
theorem ladder_rung3_polynomial_calculus_substrate
    (φ : SignedThreeCNF) {d s : Nat}
    (Hdeg : PolynomialCalculusDegreeLowerBound
      (SignedThreeCNFPolynomialCalculusAxiom φ)
      polynomialCalculusContradictionLine d)
    (hgap : 3 + s < d) :
    Not (exists D : SignedThreeCNFPolynomialCalculusRefutation φ, D.size <= s) :=
  no_small_signedThreeCNF_polynomialCalculus_refutation_of_degree_lower_bound
    φ Hdeg hgap

/-- **Rung 3, completed substrate bundle.**  The rung-3 map now has real
substrates for polynomial calculus, Nullstellensatz, cutting planes, and a
formula-level bounded-depth Frege kernel.  This is not a claim that the
family-specific lower-bound engines have been formalized. -/
theorem ladder_rung3_completed_substrates
    (φ : SignedThreeCNF) : Rung3CompletedSubstrates φ :=
  rung3_completed_substrates φ

/-! ## Rung 4 (SUBSTRATES PROVED): bounded-depth circuits -/

/-- **Rung 4, abstract substrate bundle.**  The older rung-4 map has formal
no-small-circuit interfaces for AC⁰ and AC⁰[p], including parity targets. -/
theorem ladder_rung4_completed_substrates : Rung4CompletedSubstrates :=
  rung4_completed_substrates

/-- **Rung 4, formal substrate bundle.**  The completed rung-4 substrate now has
real Boolean circuit syntax/semantics for AC⁰-style and AC⁰[p]-style circuits,
plus the parity decision-tree endpoint.  This is still not a formalization of
Håstad's switching lemma or Razborov--Smolensky. -/
theorem ladder_rung4_formal_substrates : Rung4FormalSubstrates :=
  rung4_formal_substrates

/-- **Rung 4, parity/AC⁰ pointwise substrate.**  A supplied AC⁰ parity size
lower bound at length `n` rules out smaller AC⁰ parity circuits at the same
depth. -/
theorem ladder_rung4_AC0_parity_substrate
    {n d lower s : Nat}
    (H : AC0ParitySizeLowerBoundAt n d lower)
    (hgap : s < lower) :
    Not (exists C : AC0Circuit n,
      C.computes = parityFunction n /\ C.depth <= d /\ C.size <= s) :=
  no_small_AC0_parity_circuit_of_lower_bound H hgap

/-- **Rung 4, proved parity decision-tree core.**  This is the formal endpoint
behind the switching-lemma route: once a restricted AC⁰ circuit is simplified to
a decision tree, parity still forces decision-tree depth `≥ n`. -/
theorem ladder_rung4_parity_decision_tree_core
    {n : Nat} (T : BoolDecisionTree n)
    (hcomputes : T.Computes (parityFunction n)) :
    n <= T.depth :=
  BoolDecisionTree.depth_ge_of_computes_parity T hcomputes

/-- **Rung 4, proved deterministic switching core.**  A DNF can be evaluated by
a decision tree of depth at most its total literal width.  Therefore any DNF
computing parity has total literal width at least `n`.  This is a real endpoint
kernel for the Håstad route, but not the full random-restriction switching
lemma. -/
theorem ladder_rung4_dnf_switching_core
    {n : Nat} (D : Rung4DNF n)
    (hcomputes : D.Computes (parityFunction n)) :
    n <= D.totalWidth :=
  Rung4DNF.totalWidth_ge_of_computes_parity D hcomputes

/-- **Rung 4, restricted switching substrate.**  If a concrete restriction
leaves a DNF residual of total literal width at most `depthBudget`, then there
is a decision tree of depth at most `depthBudget` computing the original DNF on
the restricted subcube.  This is the actual substrate a probabilistic switching
lemma would feed; the random-restriction probability bound is not assumed here.
-/
theorem ladder_rung4_restricted_switching_substrate
    {n depthBudget : Nat} (D : Rung4DNF n) (ρ : Rung4Restriction n)
    (hwidth : (D.restrict ρ).totalWidth <= depthBudget) :
    exists T : BoolDecisionTree n,
      T.depth <= depthBudget /\
      forall x : Fin n -> Bool,
        Rung4Restriction.Extends ρ x -> T.eval x = D.eval x :=
  Rung4DNF.exists_restrictedDecisionTree_of_residualWidth_le D ρ hwidth

/-! ## Rung 5 (FRONTIER SUBSTRATES): TC⁰ / NC¹ / branching programs -/

/-- **Observer invariant extraction.**  The common rungs-1--4 pattern is a
numerical demand/capacity invariant.  The generic transfer theorem says a rung-5
lower bound follows if a preservation theorem maps every correct rung-5 model to
an invariant witness whose capacity is bounded by the model budget.  This is a
precise frontier target, not a proof of TC⁰/NC¹/BP/space lower bounds. -/
theorem ladder_rung5_observerInvariant_transfer
    {Model Witness : Type}
    {Computes : Model -> Prop}
    {Budget : Model -> Nat}
    {I : ObserverInvariant Witness}
    {demandLower budgetUpper : Nat}
    (Pres : Rung5ObserverInvariantPreservation
      Model Witness Computes Budget I demandLower budgetUpper)
    (hgap : budgetUpper < demandLower) :
    Not (exists M : Model, Computes M) :=
  no_rung5_model_of_observerInvariant_preservation Pres hgap


/-- **Rung 5, formal frontier bundle.**  The rung-5 substrate has real syntax or
semantics for TC⁰-style threshold circuits, NC¹-style formulas, deterministic
branching programs, bounded-space configuration machines, and a Barrington-style
transfer interface, plus generic lower-bound consequence theorems.  This is not
a claim of new TC⁰/NC¹/BP/space lower bounds. -/
theorem ladder_rung5_formal_substrates : Rung5FormalSubstrates :=
  rung5_formal_substrates

/-- **Rung 5, concrete observer-boundary kernels.**  The invariant transfer is
not only abstract: it recovers the tiny proved rung-5 endpoints for width-1
branching programs and one-configuration bounded-space machines.  This still
leaves TC⁰, NC¹, width-5 BP, and real space lower bounds at the frontier. -/
theorem ladder_rung5_concreteObserverBoundaryKernels :
    Rung5ConcreteObserverBoundaryKernels :=
  rung5_concreteObserverBoundaryKernels

/-- **Rung 5, extended observer-invariant frontier.**  The observer invariant now
covers TC⁰, NC¹/formulas, width-5 branching programs, and bounded-space machines
as transfer layers: supplied lower bounds in those models become invariant
obstructions for budgeted models.  The supplied lower bounds remain the hard
frontier inputs. -/
theorem ladder_rung5_extendedObserverInvariantFrontier :
    Rung5ExtendedObserverInvariantFrontier :=
  rung5_extendedObserverInvariantFrontier

/-- **Rung 5, toy lower bounds.**  The observer invariant proves actual lower
bounds for deliberately weakened toy subclasses: input-blind threshold circuits,
input-blind formulas, width-1 branching programs, and one-configuration space
machines cannot compute parity on nonempty inputs under insufficient budgets.
These are toy endpoints, not TC⁰/NC¹/width-5 breakthroughs. -/
theorem ladder_rung5_toyLowerBounds : Rung5ToyLowerBounds :=
  rung5_toyLowerBounds

/-- **Rung 5, variable-access lower bounds.**  Query branching programs must
query every variable to compute parity, so their length is at least `n`, for any
width.  This is a genuine restricted rung-5 lower bound, stronger than
input-blindness but still far below unrestricted width-5 BP / NC¹. -/
theorem ladder_rung5_variableAccessLowerBounds :
    Rung5VariableAccessLowerBounds :=
  rung5_variableAccessLowerBounds

/-- **Rung 5, formula variable-access floor.**  Any formula computing parity
must mention every variable, and the number of mentioned variables is bounded by
formula size.  Therefore parity formulas have size at least `n`, independent of
depth.  This is an unrestricted-formula linear floor, not a super-polynomial NC¹
lower bound. -/
theorem ladder_rung5_formulaVariableAccessLowerBounds :
    Rung5FormulaVariableAccessLowerBounds :=
  rung5_formulaVariableAccessLowerBounds

/-- **Rung 5, subfunction-count observer frontier.**  This replaces the linear
variable-presence measure by residual/subfunction count, which can be exponential:
the equality split has `2^n` residuals.  The generic transfer theorem proves that
a model with subfunction capacity below the required count cannot compute the
target, and the family-level theorem shows super-polynomial requirements beat
polynomial budgets eventually.  Model-specific capacity bounds remain the hard
frontier. -/
theorem ladder_rung5_subfunctionObserverFrontier :
    SubfunctionObserverFrontier :=
  subfunctionObserverFrontier

/-- **Rung 5, subfunction-capacity wall.**  The subfunction invariant is strong,
but unrestricted semantic models can expose exponentially many residuals at unit
syntactic budget.  Hence the missing TC⁰/NC¹/width-5 BP step cannot be obtained
from the observer invariant alone; it must be a genuine model-specific capacity
upper bound. -/
theorem ladder_rung5_subfunctionCapacityWall :
    SubfunctionCapacityWall :=
  subfunctionCapacityWall

/-- **Rung 5, crossing-state capacity theorem.**  If a computation is forced to
pass from an `XR` block to an `XB` block through one of `c` crossing states, then
it exposes at most `c` residual functions.  Storage access has `2^m` residuals,
so every crossing model for it needs at least `2^m` states.  This is the genuine
restricted capacity theorem behind OBDD/one-way/Nechiporuk-style arguments. -/
theorem ladder_rung5_crossingCapacityLowerBound :
    CrossingCapacityLowerBound :=
  crossingCapacityLowerBound

/-- **Rung 5, actual exponential DNF lower bound.**  Any ordinary literal-DNF
computing equality between two `n`-bit blocks needs at least `2^n` terms.  The
proof is the rectangle/subfunction argument: one DNF term cannot cover two
different diagonal equality points without also accepting an unequal mixed point.
This is a genuine super-polynomial restricted lower bound. -/
theorem ladder_rung5_dnfEqualityExponentialLowerBound :
    DNFEqualityExponentialLowerBound :=
  dnfEqualityExponentialLowerBound

/-- **Rung 5, equality upper bound for stronger formulas.**  Equality between
two `n`-bit blocks has a split formula of size at most `10*n+1`.  Thus the
exponential DNF lower bound is genuinely a DNF restriction; it is false for full
formula/NC¹-style computation of equality. -/
theorem ladder_rung5_equalityFormulaLinearUpperBound :
    SplitFormula.EqualityFormulaLinearUpperBound :=
  SplitFormula.equalityFormulaLinearUpperBound

/-- **Rung 5, TC⁰/NC¹ observer-route constraint (barrier atlas only).**  A
successful observer route consists of model preservation plus an explicit target
gap; under a supplied natural-proofs barrier, the induced observer property must
be non-natural.  This is a formal design constraint, not a lower-bound engine and
not progress toward full TC⁰ by itself. -/
theorem ladder_rung5_TC0_NC1_observerRoute_constraint {n : Nat}
    {N : NaturalProofInterface n} {C : BudgetedClass n} {f : BoolFun n} {B : Nat}
    (R : NonNaturalObserverRoute N C f B) : LowerBound C f B :=
  lower_bound_of_nonNaturalObserverRoute R

/-- **Rung 5, KW conservation for NC¹/formulas.**  Given an explicit
Karchmer--Wigderson interface, formula-depth lower bounds and KW communication
lower bounds are literally equivalent.  Thus KW is an exact observer language for
NC¹, not a shortcut around the open lower-bound problem. -/
theorem ladder_rung5_KW_formula_conservation {n : Nat}
    (K : KWFormulaInterface n) (f : BoolFun n) (B : Nat) :
    (∀ d, d < B -> ¬ K.FormulaDepth f d) ↔
      (∀ d, d < B -> ¬ K.KWCost f d) :=
  formula_lower_bound_iff_KW_lower_bound K f B

/-- **Rung 5, sign-rank partial threshold route.**  Sign-rank gives the honest
conservation theorem for depth-2 threshold/UPP models: a sign-rank lower bound
plus a depth-2-to-sign-rank bridge rules out all budgets whose induced dimension
falls below the sign-rank lower bound.  This does not lift to full TC⁰. -/
theorem ladder_rung5_signRank_depth2_threshold_route
    {m n : Nat} {M : Fin m -> Fin n -> Bool} {B : Nat}
    (Compute : Nat -> Prop) (bound : Nat -> Nat)
    (hF : ForsterLowerBound M B)
    (hbridge : ∀ s, Compute s -> HasSignRankLE M (bound s))
    {s : Nat} (hs : Compute s) (hsmall : bound s < B) : False :=
  signRank_depth2_threshold_route Compute bound hF hbridge hs hsmall

/-- **Rung 5, threshold-composition signpost (conditional on a barrier-strength
hypothesis).**  If an invariant is bounded on variables/constants and one assumes
`ThresholdLayerStable` for every threshold layer, then every layered threshold
circuit has bounded invariant.  This is only structural induction over circuits;
all hard TC⁰ content is in the unproved `ThresholdLayerStable` hypothesis. -/
theorem ladder_rung5_threshold_composition_frontier {n : Nat}
    (I : TCObserverInvariant n) (B : Nat -> Nat)
    (hleaf : ThresholdLayer.LeafPreserved I B)
    (hstable : ThresholdLayer.ThresholdLayerStable I B) :
    ∀ {d : Nat} (C : ThresholdLayer n d), I.Q (ThresholdLayer.eval C) ≤ B d :=
  ThresholdLayer.thresholdCircuit_preservation I B hleaf hstable

/-- **Rung 5, threshold-composition conditional consequence.**  A completed
threshold-composition route — invariant, layer stability, and target gap — rules
out depth-`d` layered threshold circuits.  This theorem is intentionally
conditional: producing such a route for an explicit TC⁰-hard target is the open
barrier-class breakthrough, not something proved here. -/
theorem ladder_rung5_threshold_composition_lower_bound {n d : Nat}
    {f : BoolFun n} (R : ThresholdLayer.ThresholdCompositionRoute f d) :
    ¬ ∃ C : ThresholdLayer n d, ThresholdLayer.eval C = f :=
  ThresholdLayer.lower_bound_of_thresholdCompositionRoute R

/-- **Rung 5, layered-invariant climb shape.**  A hierarchy `I₀,I₁,...` plus
layer-transfer rules controls layered threshold circuits at the corresponding
depth.  This is the honest version of "change/enrich the invariant per layer";
it remains conditional because the transfer rules and target gaps are the hard
open content. -/
theorem ladder_rung5_layered_threshold_invariant_frontier {n : Nat}
    (L : ThresholdLayer.LayeredInvariant n) (B : ThresholdLayer.LayerBudget)
    (hleaf : ThresholdLayer.LayeredLeafPreserved L B)
    (htransfer : ThresholdLayer.LayerTransferStable L B) :
    ∀ {d : Nat} (C : ThresholdLayer n d),
      (L.I d).Q (ThresholdLayer.eval C) ≤ B d :=
  ThresholdLayer.layered_threshold_preservation L B hleaf htransfer

/-- **Rung 5, layered-invariant lower-bound consequence.**  A completed layered
route gives a depth-`d` lower bound.  Supplying such a route with non-vacuous
transfer rules for an explicit hard target is the actual frontier task. -/
theorem ladder_rung5_layered_threshold_lower_bound {n d : Nat}
    {f : BoolFun n} (R : ThresholdLayer.LayeredThresholdRoute f d) :
    ¬ ∃ C : ThresholdLayer n d, ThresholdLayer.eval C = f :=
  ThresholdLayer.lower_bound_of_layeredThresholdRoute R

/-- **Rung 5, finite-prefix layered climb.**  For a depth-`d` lower bound one
only needs the first `d` transfer steps, not an infinite transfer theorem.  This
is the operational climb interface: prove `0→1`, then `1→2`, and so on, stopping
at the depth under attack. -/
theorem ladder_rung5_layered_threshold_finite_prefix_lower_bound {n d : Nat}
    {f : BoolFun n} (R : ThresholdLayer.LayeredThresholdRouteUpTo f d) :
    ¬ ∃ C : ThresholdLayer n d, ThresholdLayer.eval C = f :=
  ThresholdLayer.lower_bound_of_layeredThresholdRouteUpTo R

/-- **Rung 5, TC⁰ pointwise substrate.**  A supplied threshold-circuit lower
bound rules out smaller TC⁰-style circuits at the given depth. -/
theorem ladder_rung5_TC0_substrate
    {F : (n : Nat) -> BoolFunction n} {n d lower s : Nat}
    (H : TC0SizeLowerBoundAt F n d lower)
    (hgap : s < lower) :
    Not (exists C : ThresholdCircuitSyntax n,
      C.Computes (F n) /\ C.depth <= d /\ C.size <= s) :=
  no_small_TC0Circuit_of_size_lower_bound H hgap

/-- **Rung 5, branching-program substrate.**  A supplied fixed-width branching
program length lower bound rules out shorter branching programs. -/
theorem ladder_rung5_branching_program_substrate
    {F : (n : Nat) -> BoolFunction n} {n width lower len : Nat}
    (H : BranchingProgramLengthLowerBoundAt F n width lower)
    (hgap : len < lower) :
    Not (exists P : BranchingProgram n width,
      P.Computes (F n) /\ P.length <= len) :=
  no_short_branchingProgram_of_length_lower_bound H hgap

/-- **Rung 5, tiny real BP kernel.**  Width-1 branching programs are
input-blind, so they cannot compute parity on a nonempty input set.  Therefore
any length lower bound for width-1 parity branching programs holds.  This is a
real endpoint theorem, not a width-5/NC¹ lower bound. -/
theorem ladder_rung5_width_one_bp_parity_kernel
    {n lower : Nat} (i : Fin n) :
    BranchingProgramLengthLowerBoundAt parityFunction n 1 lower :=
  width_one_branchingProgram_parity_length_lower_bound i lower

/-- **Rung 5, bounded-space substrate.**  A supplied finite-configuration lower
bound rules out machines with too few configurations. -/
theorem ladder_rung5_bounded_space_substrate
    {F : (n : Nat) -> BoolFunction n} {n lowerConfigs configBudget : Nat}
    (H : SpaceBoundedConfigLowerBoundAt F n lowerConfigs)
    (hgap : configBudget < lowerConfigs) :
    Not (exists configs : Nat, exists M : SpaceBoundedMachine n configs,
      M.Computes (F n) /\ configs <= configBudget) :=
  no_small_spaceBoundedMachine_of_config_lower_bound H hgap

/-- **Rung 5, tiny real bounded-space kernel.**  A one-configuration machine is
input-blind, so parity on a nonempty input set needs at least two configurations
in this finite-configuration substrate.  This is not a space hierarchy theorem.
-/
theorem ladder_rung5_bounded_space_parity_two_config_kernel
    {n : Nat} (i : Fin n) :
    SpaceBoundedConfigLowerBoundAt parityFunction n 2 :=
  parity_spaceBounded_config_lower_bound_two i

/-- **Rung 5, Barrington transfer interface.**  If an NC¹-to-width-5 branching
program simulation is supplied and width-5 branching programs require more than
the simulated length, then no formula in that depth regime computes the function.
The simulation theorem and BP lower bound are explicit inputs, not hidden facts. -/
theorem ladder_rung5_barrington_transfer
    {F : (n : Nat) -> BoolFunction n} {n depthBound lengthBound lower : Nat}
    (B : BarringtonWidth5SimulationAt F n depthBound lengthBound)
    (Hbp : BranchingProgramLengthLowerBoundAt F n 5 lower)
    (hgap : lengthBound < lower) :
    Not (exists A : PropFormula n,
      A.Computes (F n) /\ A.depth <= depthBound) :=
  no_NC1Formula_of_barrington_and_bp_lower_bound B Hbp hgap

/-! ## Rung 6 / top rung (THE WALL): the general-model bridge is the separation -/

/-- **Rung 6, wall substrate.**  The completed rung-6 layer proves a conservation
principle: a universal bridge from arbitrary P-time signed-SAT deciders into any
impossible obstruction target is equivalent to the no-decider endpoint.  This is
not a lower-bound engine; it is the formal reason the unrestricted lift is the
wall. -/
theorem ladder_rung6_wall_substrate : Rung6WallSubstrate :=
  rung6_wall_substrate


/-- **Rung 6 is the wall.**  At a channel gap, the general-model boundary bridge
is *equivalent* to "no decider in the P-time class" — i.e. the top of the ladder
is P≠NP itself, not a further generalisation one can extrapolate into.  Anchored
to the metacomplexity bridge. -/
theorem ladder_top_rung_iff_separation
    {enc : SignedFormulaEncoding} (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver) (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections) :
    Nonempty (PTimeDeciderDimensionalForce PT O B) ↔
      MetacomplexityNoPTimeDecider enc PT :=
  observerBoundary_iff_metacomplexityObstruction PT O B hgap

/-! ## Kernel-only axiom trace -/

#print axioms ladder_rung1_width_lower_bound
#print axioms ladder_rung1_concrete
#print axioms ladder_rung2_size_lower_bound
#print axioms ladder_rung2_concrete
#print axioms ladder_rung2_family
#print axioms ladder_rung1_dag_width
#print axioms ladder_rung1_dag_concrete
#print axioms ladder_rung3_polynomial_calculus_substrate
#print axioms ladder_rung3_completed_substrates
#print axioms ladder_rung4_completed_substrates
#print axioms ladder_rung4_formal_substrates
#print axioms ladder_rung4_AC0_parity_substrate
#print axioms ladder_rung4_parity_decision_tree_core
#print axioms ladder_rung4_dnf_switching_core
#print axioms ladder_rung4_restricted_switching_substrate
#print axioms ladder_rung5_observerInvariant_transfer
#print axioms ladder_rung5_formal_substrates
#print axioms ladder_rung5_concreteObserverBoundaryKernels
#print axioms ladder_rung5_extendedObserverInvariantFrontier
#print axioms ladder_rung5_toyLowerBounds
#print axioms ladder_rung5_variableAccessLowerBounds
#print axioms ladder_rung5_formulaVariableAccessLowerBounds
#print axioms ladder_rung5_subfunctionObserverFrontier
#print axioms ladder_rung5_subfunctionCapacityWall
#print axioms ladder_rung5_crossingCapacityLowerBound
#print axioms ladder_rung5_dnfEqualityExponentialLowerBound
#print axioms ladder_rung5_equalityFormulaLinearUpperBound
#print axioms ladder_rung5_TC0_NC1_observerRoute_constraint
#print axioms ladder_rung5_KW_formula_conservation
#print axioms ladder_rung5_signRank_depth2_threshold_route
#print axioms ladder_rung5_threshold_composition_frontier
#print axioms ladder_rung5_threshold_composition_lower_bound
#print axioms ladder_rung5_layered_threshold_invariant_frontier
#print axioms ladder_rung5_layered_threshold_lower_bound
#print axioms ladder_rung5_layered_threshold_finite_prefix_lower_bound
#print axioms ladder_rung5_TC0_substrate
#print axioms ladder_rung5_branching_program_substrate
#print axioms ladder_rung5_width_one_bp_parity_kernel
#print axioms ladder_rung5_bounded_space_substrate
#print axioms ladder_rung5_bounded_space_parity_two_config_kernel
#print axioms ladder_rung5_barrington_transfer
#print axioms ladder_rung6_wall_substrate
#print axioms ladder_top_rung_iff_separation

end PallLean.Paper93.DeepMath.PathB
