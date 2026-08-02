import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNoncommutativeActionHolonomyAudit

/-!
# Solver-relative future-continuation quotient

The coordinate-action audit shows that neither action-word capacity nor
commutators see the hard part of SAT continuation semantics.  This file moves
to the exact Myhill--Nerode-style object suggested by that audit.

For a family of boundary states and legal future contexts, two states are
equivalent precisely when every context gives the same observed answer.  The
resulting semantic quotient is represented extensionally by the state's full
future-answer signature.  We prove:

* future equivalence is an equivalence relation;
* restricting the legal contexts can only merge quotient classes;
* any faithful finite representation has at least as many states as the
  semantic quotient has classes;
* the expander SAT-query family has exactly `2^r` solver-relative future
  classes for every SAT-correct decider;
* this exponential quotient nevertheless has a canonical length-`r` Boolean
  representation and is queried one coordinate at a time.

The last point is decisive.  Polynomial running time does not imply a
polynomial *number* of future-equivalence classes: a succinct polynomial-time
procedure may operate on `r`-bit states and hence distinguish `2^r` semantic
classes.  Consequently a proposed theorem giving every P solver only
polynomially many classes is not a conservation law derived from P; at the
expander scale it is already incompatible with SAT correctness.
-/

namespace PallLean.Paper93.DeepMath.PathB.SolverRelativeFutureContinuationQuotient

open SATDepthMachine
open BranchSpanningDynamicHolonomy
open ExpanderSATQueryContinuation
open NoncommutativeActionHolonomyAudit
open NonLocalActionHolonomyConservation

variable {State Context Answer : Type*}

/-- A solver-relative continuation experiment.  `answer s c` is the observed
answer after boundary state `s` is completed by legal future context `c`. -/
structure FutureExperiment (State Context Answer : Type*) where
  answer : State → Context → Answer

namespace FutureExperiment

/-- Full future-answer signature of a boundary state. -/
def signature (E : FutureExperiment State Context Answer) :
    State → (Context → Answer) :=
  E.answer

/-- Syntactic/future equivalence: no legal continuation distinguishes the two
states. -/
def Equivalent (E : FutureExperiment State Context Answer)
    (x y : State) : Prop :=
  ∀ c, E.answer x c = E.answer y c

theorem equivalent_refl (E : FutureExperiment State Context Answer) :
    Reflexive E.Equivalent := by
  intro x c
  rfl

theorem equivalent_symm (E : FutureExperiment State Context Answer) :
    Symmetric E.Equivalent := by
  intro x y h c
  exact (h c).symm

theorem equivalent_trans (E : FutureExperiment State Context Answer) :
    Transitive E.Equivalent := by
  intro x y z hxy hyz c
  exact (hxy c).trans (hyz c)

/-- The actual setoid quotient by all legal future continuations. -/
def futureSetoid (E : FutureExperiment State Context Answer) : Setoid State where
  r := E.Equivalent
  iseqv := ⟨E.equivalent_refl,
    (fun {_ _} h => E.equivalent_symm h),
    (fun {_ _ _} hxy hyz => E.equivalent_trans hxy hyz)⟩

theorem equivalent_iff_signature_eq
    (E : FutureExperiment State Context Answer) (x y : State) :
    E.Equivalent x y ↔ E.signature x = E.signature y := by
  constructor
  · intro h
    funext c
    exact h c
  · intro h c
    exact congrFun h c

/-- Number of semantic future-continuation classes, represented as the image
of the full future signature. -/
noncomputable def quotientRank [Fintype State]
    (E : FutureExperiment State Context Answer) : ℕ :=
  familyImageRank E.signature

/-- Pull back to a chosen family of legal contexts. -/
def restrictContexts {SmallContext : Type*}
    (E : FutureExperiment State Context Answer)
    (embed : SmallContext → Context) :
    FutureExperiment State SmallContext Answer where
  answer := fun state context => E.answer state (embed context)

/-- **Quotient monotonicity.**  Removing legal future contexts cannot create
new distinguishable boundary classes. -/
theorem restrictContexts_quotientRank_le [Fintype State]
    {SmallContext : Type*}
    (E : FutureExperiment State Context Answer)
    (embed : SmallContext → Context) :
    (E.restrictContexts embed).quotientRank ≤ E.quotientRank := by
  classical
  unfold quotientRank familyImageRank signature restrictContexts
  let project : (Context → Answer) → (SmallContext → Answer) :=
    fun sig c => sig (embed c)
  calc
    (Finset.univ.image (fun s => fun c => E.answer s (embed c))).card =
        (Finset.univ.image (fun s => project (E.answer s))).card := by rfl
    _ = ((Finset.univ.image E.answer).image project).card := by
      congr 1
      ext sig
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨state, rfl⟩
        exact ⟨E.answer state, ⟨state, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨state, rfl⟩, rfl⟩
        exact ⟨state, rfl⟩
    _ ≤ (Finset.univ.image E.answer).card := Finset.card_image_le

/-- A finite code is future-faithful when it decodes the answer to every legal
context. -/
structure FaithfulRepresentation [Fintype State]
    (E : FutureExperiment State Context Answer) (Code : Type*)
    [Fintype Code] where
  encode : State → Code
  decode : Code → Context → Answer
  faithful : ∀ state context, decode (encode state) context = E.answer state context

/-- Every faithful representation surjects onto the realized future
signatures, so its state space is at least the semantic quotient rank. -/
theorem quotientRank_le_code_card [Fintype State]
    (E : FutureExperiment State Context Answer)
    (Code : Type*) [Fintype Code]
    (R : FaithfulRepresentation E Code) :
    E.quotientRank ≤ Fintype.card Code := by
  classical
  unfold quotientRank familyImageRank
  calc
    (Finset.univ.image E.signature).card
        ≤ (Finset.univ.image R.decode).card := by
          apply Finset.card_le_card
          intro sig hsig
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hsig ⊢
          rcases hsig with ⟨state, rfl⟩
          refine ⟨R.encode state, ?_⟩
          funext context
          exact R.faithful state context
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card Code := Finset.card_univ

end FutureExperiment

/-! ## Exact SAT/expander instantiation -/

variable {V Edge ι : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype Edge] [DecidableEq Edge]
variable [Fintype ι] [DecidableEq ι]

/-- The solver-relative experiment whose states are genuine Tseitin edge
assignments and whose future contexts are the coordinate SAT queries. -/
noncomputable def expanderSolverFutureExperiment
    {U : MachineModel} (D : DecisionMachine U)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    FutureExperiment (Edge → ZMod 2) (Fin (Fintype.card ι)) Bool where
  answer := fun x i =>
    (expanderResidualSATQueries G hc hexp readSet hread hmed).answers D x i

/-- SAT correctness identifies future equivalence exactly with equality of the
natural residual vector. -/
theorem expanderSolver_equivalent_iff_residualBits_eq
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    (x y : Edge → ZMod 2) :
    (expanderSolverFutureExperiment D G hc hexp readSet hread hmed).Equivalent x y ↔
      expanderResidualBits G readSet x = expanderResidualBits G readSet y := by
  let F := expanderResidualSATQueries G hc hexp readSet hread hmed
  have hx := F.answers_eq_label D hD x
  have hy := F.answers_eq_label D hD y
  rw [FutureExperiment.equivalent_iff_signature_eq]
  change F.answers D x = F.answers D y ↔ F.label x = F.label y
  rw [hx, hy]

/-- **Exact future quotient.**  Every SAT-correct solver induces precisely
`2^r` future-continuation classes on the expanded residual family. -/
theorem expanderSolver_quotientRank_eq_two_pow
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    (expanderSolverFutureExperiment D G hc hexp readSet hread hmed).quotientRank =
      2 ^ Fintype.card ι := by
  let F := expanderResidualSATQueries G hc hexp readSet hread hmed
  have hsignature :
      (expanderSolverFutureExperiment D G hc hexp readSet hread hmed).signature =
        expanderResidualBits G readSet := by
    funext x
    exact F.answers_eq_label D hD x
  rw [FutureExperiment.quotientRank]
  rw [hsignature, familyImageRank_eq_card_of_surjective
    (expanderResidualBits G readSet)
    (expanderResidualBits_surjective G hc hexp readSet hread hmed)]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- The full residual bit-vector is a canonical faithful representation.  It
has a linear-width description but, necessarily, exponentially many values. -/
noncomputable def expanderResidualFaithfulRepresentation
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V) :
    FutureExperiment.FaithfulRepresentation
      (expanderSolverFutureExperiment D G hc hexp readSet hread hmed)
      (Fin (Fintype.card ι) → Bool) where
  encode := expanderResidualBits G readSet
  decode := fun bits i => bits i
  faithful := by
    intro x i
    let F := expanderResidualSATQueries G hc hexp readSet hread hmed
    have hx := congrFun (F.answers_eq_label D hD x) i
    exact hx.symm

/-- Any finite future-faithful representation of these solver answers has at
least `2^r` values. -/
theorem two_pow_le_card_of_expanderSolver_faithful
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    (Code : Type*) [Fintype Code]
    (R : FutureExperiment.FaithfulRepresentation
      (expanderSolverFutureExperiment D G hc hexp readSet hread hmed) Code) :
    2 ^ Fintype.card ι ≤ Fintype.card Code := by
  rw [← expanderSolver_quotientRank_eq_two_pow
    D hD G hc hexp readSet hread hmed]
  exact FutureExperiment.quotientRank_le_code_card _ Code R

/-- A proposed polynomial-cardinality P-side quotient at this scale.  This is
the exact extra object a quotient-based Route G would have to construct; it is
not implied merely by a polynomial running-time bound. -/
structure PolynomialFutureQuotientAt
    {U : MachineModel} (D : DecisionMachine U)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    (k : ℕ) : Type 1 where
  Code : Type
  [codeFintype : Fintype Code]
  representation : FutureExperiment.FaithfulRepresentation
    (expanderSolverFutureExperiment D G hc hexp readSet hread hmed) Code
  polynomialCard : Fintype.card Code ≤ (Fintype.card ι) ^ k

/-- **P-side guardrail.**  Once the ordinary exponential gap opens, SAT
correctness rules out the claimed polynomial-cardinality quotient. -/
theorem no_polynomialFutureQuotientAt
    {U : MachineModel} (D : DecisionMachine U) (hD : DecidesSAT U D)
    (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c)
    (readSet : ι → V) (hread : Function.Injective readSet)
    (hmed : 2 * Fintype.card ι ≤ Fintype.card V)
    (k : ℕ) (hgap : (Fintype.card ι) ^ k < 2 ^ Fintype.card ι) :
    PolynomialFutureQuotientAt D G hc hexp readSet hread hmed k → False := by
  intro Q
  letI : Fintype Q.Code := Q.codeFintype
  have hlower : 2 ^ Fintype.card ι ≤ Fintype.card Q.Code :=
    two_pow_le_card_of_expanderSolver_faithful
      D hD G hc hexp readSet hread hmed Q.Code Q.representation
  exact (Nat.not_le_of_lt hgap) (hlower.trans Q.polynomialCard)

/-!
## Audit verdict

The continuation quotient is mathematically sound and continuation-faithful,
and its monotonicity is now explicit.  It also gives the desired exponential
lower bound immediately: the expanded SAT residual has `2^r` future classes.

But this does not separate P from NP.  The same quotient is represented by an
ordinary `r`-bit vector, so its exponential *cardinality* is compatible with a
linear-width, succinct computation.  A polynomial-time trace does not have
only polynomially many configurations or future signatures.  Therefore the
missing theorem cannot be "P has polynomial quotient cardinality"; that claim
is refuted by the exact SAT-correct calibration above.

Any viable continuation invariant must instead lower-bound a succinct
description/transition resource that is itself independently conserved by
general polynomial-time machines.  Establishing such a conservation theorem
and a superpolynomial SAT lower bound is precisely a general complexity lower
bound, not a quotient-construction detail.
-/

end PallLean.Paper93.DeepMath.PathB.SolverRelativeFutureContinuationQuotient

#print axioms PallLean.Paper93.DeepMath.PathB.SolverRelativeFutureContinuationQuotient.FutureExperiment.restrictContexts_quotientRank_le
#print axioms PallLean.Paper93.DeepMath.PathB.SolverRelativeFutureContinuationQuotient.FutureExperiment.quotientRank_le_code_card
#print axioms PallLean.Paper93.DeepMath.PathB.SolverRelativeFutureContinuationQuotient.expanderSolver_equivalent_iff_residualBits_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SolverRelativeFutureContinuationQuotient.expanderSolver_quotientRank_eq_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.SolverRelativeFutureContinuationQuotient.two_pow_le_card_of_expanderSolver_faithful
#print axioms PallLean.Paper93.DeepMath.PathB.SolverRelativeFutureContinuationQuotient.no_polynomialFutureQuotientAt
