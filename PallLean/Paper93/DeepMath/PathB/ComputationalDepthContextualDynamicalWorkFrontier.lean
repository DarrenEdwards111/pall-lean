import PallLean.Paper93.DeepMath.PathB.ComputationalDepthContextualSummaryInvalidationFrontier

/-!
# Contextual dynamical-work frontier

The exact-syntax summary defeats representation invalidation: it survives every
restriction context without growing.  This file charges actual syntactic update
work in the strongest simple way—one full traversal of all current clauses and
literals per context step—and sums that cost over an arbitrary restriction
path.

Restriction decreases both clause count and literal count.  Therefore a path of
`T` context changes costs at most `T` times the original traversal size; paths
whose length is bounded by the input size cost at most quadratically.  The final
summary is already the restricted CNF, so no reconstruction pass beyond reading
that summary is required.

Combining this unconditional polynomial update mechanism with a polynomial
uniform evaluator is again equivalent to polynomial SAT decision.  Thus update,
cache repair, and reconstruction are not hidden sources of hardness for exact
CNF summaries.  The unresolved resource is evaluating arbitrary cached CNFs.
-/

namespace PallLean.Paper93.DeepMath.PathB.ContextualDynamicalWorkFrontier

open CNFSelfReduction
open SATDepthMachine
open UniformFutureEvaluatorFrontier
open ContextualSummaryInvalidationFrontier

/-- Size charged for one full syntactic scan: every clause header plus every
literal occurrence. -/
def cnfTraversalSize {n : ℕ} (φ : CNF n) : ℕ :=
  φ.length + descLen φ

/-- Restriction cannot increase the number of clauses. -/
theorem restrict_length_le {n : ℕ} (φ : CNF n)
    (i : Fin n) (value : Bool) :
    (restrict φ i value).length ≤ φ.length := by
  unfold restrict
  rw [List.length_map]
  exact List.length_filter_le _ _

/-- Hence restriction cannot increase full traversal size. -/
theorem restrict_cnfTraversalSize_le {n : ℕ} (φ : CNF n)
    (i : Fin n) (value : Bool) :
    cnfTraversalSize (restrict φ i value) ≤ cnfTraversalSize φ := by
  unfold cnfTraversalSize
  exact Nat.add_le_add (restrict_length_le φ i value)
    (restrict_descLen_le φ i value)

/-- Work of maintaining the exact-syntax cache along a context path.  Each
step is pessimistically charged one complete scan of the current CNF. -/
def restrictionPathWork {n : ℕ} :
    CNF n → List (RestrictionStep n) → ℕ
  | _, [] => 0
  | φ, step :: rest =>
      cnfTraversalSize φ +
        restrictionPathWork (restrict φ step.1 step.2) rest

/-- Total exact-cache update work is at most path length times original syntax
size. -/
theorem restrictionPathWork_le {n : ℕ}
    (φ : CNF n) (path : List (RestrictionStep n)) :
    restrictionPathWork φ path ≤ path.length * cnfTraversalSize φ := by
  induction path generalizing φ with
  | nil => simp [restrictionPathWork]
  | cons step rest ih =>
      have htail := ih (restrict φ step.1 step.2)
      have hsize := restrict_cnfTraversalSize_le φ step.1 step.2
      calc
        restrictionPathWork φ (step :: rest)
            = cnfTraversalSize φ +
                restrictionPathWork (restrict φ step.1 step.2) rest := rfl
        _ ≤ cnfTraversalSize φ +
              rest.length * cnfTraversalSize (restrict φ step.1 step.2) :=
            Nat.add_le_add_left htail _
        _ ≤ cnfTraversalSize φ + rest.length * cnfTraversalSize φ :=
            Nat.add_le_add_left (Nat.mul_le_mul_left rest.length hsize) _
        _ = (step :: rest).length * cnfTraversalSize φ := by
            simp [Nat.add_mul, Nat.add_comm]

/-- In the natural regime where the number of context moves is at most the
input traversal size, exact summary maintenance is at most quadratic. -/
theorem restrictionPathWork_quadratic {n : ℕ}
    (φ : CNF n) (path : List (RestrictionStep n))
    (hpath : path.length ≤ cnfTraversalSize φ) :
    restrictionPathWork φ path ≤ cnfTraversalSize φ ^ 2 := by
  calc
    restrictionPathWork φ path
        ≤ path.length * cnfTraversalSize φ := restrictionPathWork_le φ path
    _ ≤ cnfTraversalSize φ * cnfTraversalSize φ :=
      Nat.mul_le_mul_right (cnfTraversalSize φ) hpath
    _ = cnfTraversalSize φ ^ 2 := by ring

/-- The maintained object after all charged updates is exactly the semantic
restriction summary; no separate reconstruction object is needed. -/
theorem exact_cache_after_path {n : ℕ}
    (φ : CNF n) (path : List (RestrictionStep n)) :
    (exactSyntaxSummaryScheme n).realize
      ((exactSyntaxSummaryScheme n).advanceAlong
        ((exactSyntaxSummaryScheme n).summarize φ) path) =
      restrictAlong φ path := by
  exact (exactSyntaxSummaryScheme n).realize_advanceAlong φ path

/-- Package the unconditional dynamical calibration. -/
structure CanonicalContextUpdateCalibration : Prop where
  traversalMonotone : ∀ {n : ℕ} (φ : CNF n) (i : Fin n) (value : Bool),
    cnfTraversalSize (restrict φ i value) ≤ cnfTraversalSize φ
  pathLinearInLength : ∀ {n : ℕ} (φ : CNF n)
    (path : List (RestrictionStep n)),
    restrictionPathWork φ path ≤ path.length * cnfTraversalSize φ
  boundedPathQuadratic : ∀ {n : ℕ} (φ : CNF n)
    (path : List (RestrictionStep n)),
    path.length ≤ cnfTraversalSize φ →
    restrictionPathWork φ path ≤ cnfTraversalSize φ ^ 2
  reconstructionExact : ∀ {n : ℕ} (φ : CNF n)
    (path : List (RestrictionStep n)),
    (exactSyntaxSummaryScheme n).realize
      ((exactSyntaxSummaryScheme n).advanceAlong
        ((exactSyntaxSummaryScheme n).summarize φ) path) =
      restrictAlong φ path

theorem canonicalContextUpdateCalibration :
    CanonicalContextUpdateCalibration where
  traversalMonotone := restrict_cnfTraversalSize_le
  pathLinearInLength := restrictionPathWork_le
  boundedPathQuadratic := restrictionPathWork_quadratic
  reconstructionExact := exact_cache_after_path

/-- The complete easy dynamical package plus a polynomial evaluator. -/
def PolynomialContextDynamicsWithEvaluator (U : MachineModel) : Prop :=
  CanonicalContextUpdateCalibration ∧
    Nonempty (UniformFutureQueryEvaluator U)

/-- **Exact dynamical frontier.**  Even after supplying monotone summaries,
quadratic path updates, and exact reconstruction, polynomial evaluation exists
iff SAT itself has a polynomial-budget decider. -/
theorem polynomialContextDynamicsWithEvaluator_iff_SATDecisionInP
    (U : MachineModel) :
    PolynomialContextDynamicsWithEvaluator U ↔ SATDecisionInP U := by
  constructor
  · rintro ⟨_, hEval⟩
    exact (uniformFutureQueryEvaluator_iff_SATDecisionInP U).1 hEval
  · intro hSAT
    exact ⟨canonicalContextUpdateCalibration,
      (uniformFutureQueryEvaluator_iff_SATDecisionInP U).2 hSAT⟩

theorem no_polynomialContextDynamicsWithEvaluator_iff_no_SATDecisionInP
    (U : MachineModel) :
    (¬ PolynomialContextDynamicsWithEvaluator U) ↔ ¬ SATDecisionInP U := by
  rw [polynomialContextDynamicsWithEvaluator_iff_SATDecisionInP]

/-!
## Audit verdict

For exact CNF caches, contextual transport is cheap in every structural sense
now tested: representation size is non-growing, one update is linear-scan cost,
a size-bounded path is quadratic total work, and reconstruction is exact.

Consequently, the thermodynamic lower bound cannot be placed in generic bubble
movement or summary repair.  It must prove that *evaluation* of some genuine SAT
family consumes superpolynomial machine work despite these cheap transports.
For unrestricted polynomial-time observers that is exactly the open SAT lower
bound.  Further formal renaming of this endpoint would add no leverage.
-/

end PallLean.Paper93.DeepMath.PathB.ContextualDynamicalWorkFrontier

#print axioms PallLean.Paper93.DeepMath.PathB.ContextualDynamicalWorkFrontier.restrict_cnfTraversalSize_le
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualDynamicalWorkFrontier.restrictionPathWork_le
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualDynamicalWorkFrontier.restrictionPathWork_quadratic
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualDynamicalWorkFrontier.exact_cache_after_path
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualDynamicalWorkFrontier.polynomialContextDynamicsWithEvaluator_iff_SATDecisionInP
