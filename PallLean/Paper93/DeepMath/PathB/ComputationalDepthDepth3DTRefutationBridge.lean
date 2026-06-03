import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTRefutation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4ParityDecisionTreeCore

/-!
# Relabelling bridge: `BoolDecisionTree` ⟹ `DTRef` ⟹ `LDeriv` refutation

`ComputationalDepthDepth3DTRefutation` proved the proof-complexity core: a clause-labelled
refutation tree (`DTRef`) yields a short, width-`depth` resolution refutation.  This file supplies
the remaining **relabelling**: it turns the canonical Boolean decision tree `BoolDecisionTree`
(Bool leaves, `Fin n` queries) into a `DTRef` over resolution literals `Lit`, and threads the
two together into one end-to-end statement.

The map needs:

* `posLit : Fin n → Lit` — the literal "variable `i` is *true*"; `compl (posLit i)` is "`i` false".
  Following `BoolDecisionTree.eval` (`if x i then high else low`), the `low` child is the `i`-false
  branch, so descending `low` makes `posLit i` *false*; the `high` child is the `i`-true branch, so
  descending it makes `compl (posLit i)` false.  This is exactly the `t0`/`t1` convention of
  `DTRef.node`.
* `lab : Finset Lit → ResolutionClause Lit` — the leaf labelling: given the set `F` of literals
  the path has forced *false*, `lab F` is the axiom clause that path violates.

The single semantic hypothesis is `hsub : ∀ F, lab F ⊆ F` — *the labelled axiom is falsified by the
path* (its literals are among the path's false literals).  This is the honest content: the bridge
reduces "the canonical tree refutes" to "each leaf path violates an axiom".  Threading `F` (the
literal false-set) directly through the relabelling makes `DTRef.Refutes` a trivial structural
induction — no injectivity/involutivity assumption on `posLit`/`compl` is needed for the
*construction*; those would only enter when *discharging* `hsub`/`hax` for a concrete circuit.

`boolDT_to_ldderiv` is the end-to-end theorem: any `BoolDecisionTree` with such a labelling maps to
an `LDeriv compl Axiom` refutation of length `< 2^(depth+1)` and width `≤ depth`, with `depth` the
*original* tree's depth (`relabel_depth`).

What is still **not** discharged (honest scope): producing the labelling `lab` with `hsub`/`hax` for
the actual restricted refuting circuit — i.e. that a `false` leaf of the canonical tree genuinely
falsifies a specific Tseitin axiom — is the semantic obligation that depends on the concrete
circuit/axiom set, not on this structural bridge.
-/

namespace PallLean.Paper93.DeepMath.PathB

variable {n : ℕ} {Lit : Type*} [DecidableEq Lit]

/-- Relabel a Boolean decision tree into a clause-labelled refutation tree, threading the set `F`
of literals forced *false* by the path: the `low` (`i`-false) child adds `posLit i`, the `high`
(`i`-true) child adds `compl (posLit i)`.  Leaves are labelled by `lab F`. -/
def relabel (posLit : Fin n → Lit) (compl : Lit → Lit)
    (lab : Finset Lit → ResolutionClause Lit) :
    ResolutionClause Lit → BoolDecisionTree n → DTRef Lit
  | F, .leaf _ => DTRef.leaf (lab F)
  | F, .query i low high =>
      DTRef.node (posLit i)
        (relabel posLit compl lab (insert (posLit i) F) low)
        (relabel posLit compl lab (insert (compl (posLit i)) F) high)

/-- The relabelling preserves depth: the `DTRef` has the same depth as the original tree. -/
theorem relabel_depth (posLit : Fin n → Lit) (compl : Lit → Lit)
    (lab : Finset Lit → ResolutionClause Lit) (T : BoolDecisionTree n) :
    ∀ F, (relabel posLit compl lab F T).depth = T.depth := by
  induction T with
  | leaf b => intro F; rfl
  | query i low high ihl ihh =>
    intro F
    simp only [relabel, DTRef.depth, BoolDecisionTree.depth, ihl, ihh]

/-- Every leaf of the relabelling is an axiom, provided `lab` always returns one. -/
theorem labeled_relabel (posLit : Fin n → Lit) (compl : Lit → Lit)
    (lab : Finset Lit → ResolutionClause Lit) {Axiom : ResolutionClause Lit → Prop}
    (hax : ∀ F, Axiom (lab F)) (T : BoolDecisionTree n) :
    ∀ F, DTRef.Labeled Axiom (relabel posLit compl lab F T) := by
  induction T with
  | leaf b => intro F; exact hax F
  | query i low high ihl ihh =>
    intro F
    exact ⟨ihl (insert (posLit i) F), ihh (insert (compl (posLit i)) F)⟩

/-- **The refutation condition transfers.**  If `lab F ⊆ F` always (the labelled axiom is falsified
by the path's false-literal set), then the relabelled tree refutes relative to that same `F` —
because the relabelling threads exactly the `F` that `DTRef.Refutes` accumulates. -/
theorem refutes_relabel (posLit : Fin n → Lit) (compl : Lit → Lit)
    (lab : Finset Lit → ResolutionClause Lit) (hsub : ∀ F, lab F ⊆ F) (T : BoolDecisionTree n) :
    ∀ F, DTRef.Refutes compl (relabel posLit compl lab F T) F := by
  induction T with
  | leaf b => intro F; exact hsub F
  | query i low high ihl ihh =>
    intro F
    exact ⟨ihl (insert (posLit i) F), ihh (insert (compl (posLit i)) F)⟩

/-- **The relabelling bridge (end-to-end).**  A Boolean decision tree `T`, together with a leaf
labelling `lab` that (i) always returns an axiom (`hax`) and (ii) returns a clause falsified by the
path (`hsub : lab F ⊆ F`), maps to a resolution refutation `toList compl (relabel … ∅ T)` that:

1. is a valid `LDeriv compl Axiom`;
2. contains the empty clause (a refutation);
3. has length `< 2^(T.depth + 1)`;
4. has every clause of width `≤ T.depth`.

So a depth-`d` refuting decision tree yields a **width-`d`** `LDeriv` refutation of the axioms.

**Caveat (over-strong hypotheses).**  This `∀ F` form is *sound* but its hypotheses are only
satisfiable when `∅` is itself an axiom: taking `F = ∅` forces `lab ∅ ⊆ ∅` (so `lab ∅ = ∅`) and
`Axiom ∅`.  Real Tseitin axioms do not contain `∅` (it is the *goal*).  The relabelling only ever
evaluates `lab` at the `F`'s actually reached along the tree, so the usable form is the
reachability-restricted `boolDT_to_ldderiv_of_valid` below, keyed on the `ValidSearch` predicate.
This `∀ F` version is retained only as the unconditional (but vacuous-for-Tseitin) shape. -/
theorem boolDT_to_ldderiv (posLit : Fin n → Lit) (compl : Lit → Lit)
    (lab : Finset Lit → ResolutionClause Lit) {Axiom : ResolutionClause Lit → Prop}
    (hax : ∀ F, Axiom (lab F)) (hsub : ∀ F, lab F ⊆ F) (T : BoolDecisionTree n) :
    LDeriv compl Axiom (DTRef.toList compl (relabel posLit compl lab ∅ T)) ∧
      (∅ : ResolutionClause Lit) ∈ DTRef.toList compl (relabel posLit compl lab ∅ T) ∧
      (DTRef.toList compl (relabel posLit compl lab ∅ T)).length < 2 ^ (T.depth + 1) ∧
      (∀ C ∈ DTRef.toList compl (relabel posLit compl lab ∅ T), C.width ≤ T.depth) := by
  have hlab : DTRef.Labeled Axiom (relabel posLit compl lab ∅ T) :=
    labeled_relabel posLit compl lab hax T ∅
  have href : DTRef.Refutes compl (relabel posLit compl lab ∅ T) (∅ : ResolutionClause Lit) :=
    refutes_relabel posLit compl lab hsub T ∅
  obtain ⟨hLD, hmem, hlen, hwid⟩ := DTRef.dtRef_to_ldderiv _ hlab href
  have hd : (relabel posLit compl lab ∅ T).depth = T.depth := relabel_depth posLit compl lab T ∅
  refine ⟨hLD, hmem, ?_, ?_⟩
  · rw [hd] at hlen; exact hlen
  · intro C hC; have := hwid C hC; rwa [hd] at this

/-! ### Reachability-restricted bridge (the usable form)

`ValidSearch` is the structural predicate that the labelling is *only* constrained at the `F`'s the
relabelling actually reaches: at every reachable leaf (accumulated false-set `F`), `lab F` is an
axiom (`hax`-locally) that is falsified by the path (`lab F ⊆ F`).  This is exactly the
"decision tree solves the Search problem for the axioms" condition, and unlike the `∀ F` form it is
satisfiable for real (non-trivial) axiom sets. -/

/-- The tree solves the axiom Search problem: at every reachable leaf, with accumulated false-set
`F`, `lab F` is an axiom falsified by the path. -/
def ValidSearch (posLit : Fin n → Lit) (compl : Lit → Lit)
    (lab : Finset Lit → ResolutionClause Lit) (Axiom : ResolutionClause Lit → Prop) :
    ResolutionClause Lit → BoolDecisionTree n → Prop
  | F, .leaf _ => Axiom (lab F) ∧ lab F ⊆ F
  | F, .query i low high =>
      ValidSearch posLit compl lab Axiom (insert (posLit i) F) low ∧
      ValidSearch posLit compl lab Axiom (insert (compl (posLit i)) F) high

/-- Under `ValidSearch`, every relabelled leaf is an axiom. -/
theorem labeled_of_validSearch (posLit : Fin n → Lit) (compl : Lit → Lit)
    (lab : Finset Lit → ResolutionClause Lit) {Axiom : ResolutionClause Lit → Prop}
    (T : BoolDecisionTree n) :
    ∀ F, ValidSearch posLit compl lab Axiom F T → DTRef.Labeled Axiom (relabel posLit compl lab F T) := by
  induction T with
  | leaf b => intro F hv; exact hv.1
  | query i low high ihl ihh =>
    intro F hv
    exact ⟨ihl _ hv.1, ihh _ hv.2⟩

/-- Under `ValidSearch`, the relabelled tree refutes relative to the same `F`. -/
theorem refutes_of_validSearch (posLit : Fin n → Lit) (compl : Lit → Lit)
    (lab : Finset Lit → ResolutionClause Lit) {Axiom : ResolutionClause Lit → Prop}
    (T : BoolDecisionTree n) :
    ∀ F, ValidSearch posLit compl lab Axiom F T → DTRef.Refutes compl (relabel posLit compl lab F T) F := by
  induction T with
  | leaf b => intro F hv; exact hv.2
  | query i low high ihl ihh =>
    intro F hv
    exact ⟨ihl _ hv.1, ihh _ hv.2⟩

/-- **The usable relabelling bridge.**  A Boolean decision tree that solves the axiom Search
problem (`ValidSearch … ∅ T`) maps to a resolution refutation that is valid, contains `∅`, has
length `< 2^(T.depth+1)`, and width `≤ T.depth`.  Unlike `boolDT_to_ldderiv`, the hypothesis is
reachability-restricted and hence satisfiable for genuine (`∅`-free) axiom sets. -/
theorem boolDT_to_ldderiv_of_valid (posLit : Fin n → Lit) (compl : Lit → Lit)
    (lab : Finset Lit → ResolutionClause Lit) {Axiom : ResolutionClause Lit → Prop}
    (T : BoolDecisionTree n)
    (hvalid : ValidSearch posLit compl lab Axiom (∅ : ResolutionClause Lit) T) :
    LDeriv compl Axiom (DTRef.toList compl (relabel posLit compl lab ∅ T)) ∧
      (∅ : ResolutionClause Lit) ∈ DTRef.toList compl (relabel posLit compl lab ∅ T) ∧
      (DTRef.toList compl (relabel posLit compl lab ∅ T)).length < 2 ^ (T.depth + 1) ∧
      (∀ C ∈ DTRef.toList compl (relabel posLit compl lab ∅ T), C.width ≤ T.depth) := by
  have hlab := labeled_of_validSearch posLit compl lab T ∅ hvalid
  have href := refutes_of_validSearch posLit compl lab T ∅ hvalid
  obtain ⟨hLD, hmem, hlen, hwid⟩ := DTRef.dtRef_to_ldderiv _ hlab href
  have hd : (relabel posLit compl lab ∅ T).depth = T.depth := relabel_depth posLit compl lab T ∅
  refine ⟨hLD, hmem, ?_, ?_⟩
  · rw [hd] at hlen; exact hlen
  · intro C hC; have := hwid C hC; rwa [hd] at this

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.refutes_relabel
#print axioms PallLean.Paper93.DeepMath.PathB.boolDT_to_ldderiv
