import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSubfunctionCapacityWall

/-!
# Crossing-state capacity theorem (genuine restricted lower bound)

**STATUS: GENUINE RESTRICTED CAPACITY LOWER BOUND, NOT A P vs NP BRIDGE.**

This file is the provable, restricted counterpart to the subfunction-capacity
*wall* (`ComputationalDepthSubfunctionCapacityWall`).  The wall shows that a
fully unrestricted semantic model has no capacity bound at all: it can expose
`2^n` residual subfunctions at unit budget.  Here we identify the precise
restriction under which the subfunction-capacity resource becomes a real,
exponentially strong lower bound: the **crossing-state** (Nečiporuk) model.

A crossing-state model forces the entire influence of the left input block to
pass through a single intermediate *state* of bounded size before the right
block is read.  The kernel theorem (`subfunctionCount_le_width`) says: the
number of distinct residual subfunctions on the left block is at most the number
of crossing states.  This is the clean core underneath OBDD/read-once width,
one-way communication complexity, and Nečiporuk's formula lower bound method.

Instantiated on equality split, it yields a genuine exponential lower bound:
any crossing-state model computing equality split has width `≥ 2^n`
(`crossing_width_ge_exponential`).

## Honest ceiling (stated up front, not oversold)

The crossing-state hypothesis is exactly what makes capacity bite, and exactly
what a general computation need not satisfy.  General circuits, `TC⁰`, `NC¹`, and
width-5 branching programs are **not** forced through one small crossing state:
they reread variables many times, so the residual subfunctions are smeared
across re-reads rather than factoring through a single cut.  Hence this method
does **not** bound those classes and does **not** cross to P vs NP; Nečiporuk's
method provably tops out around `n^2 / log n` for formulas.  This is a real,
restricted theorem — not a bridge.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

/-! ## The crossing-state (Nečiporuk) model -/

/-- A **crossing-state model** for split functions.  The left assignment is first
compressed into a single `State` via `encode`; the output then depends only on
that state and the right assignment via `out`.  Thus all influence of the left
block crosses to the right block through one state of size `|State|`. -/
structure CrossingStateModel (Left Right State : Type) where
  /-- Compress the left block into one crossing state. -/
  encode : (Left -> Bool) -> State
  /-- Produce the output from the crossing state and the right block. -/
  out : State -> (Right -> Bool) -> Bool

namespace CrossingStateModel

variable {Left Right State : Type}

/-- The model computes `Target` when its factored evaluation agrees everywhere. -/
def Computes (M : CrossingStateModel Left Right State)
    (Target : (Left -> Bool) -> (Right -> Bool) -> Bool) : Prop :=
  forall a b, M.out (M.encode a) b = Target a b

/-- The model's width is the number of crossing states. -/
noncomputable def width [Fintype State]
    (_M : CrossingStateModel Left Right State) : Nat :=
  Fintype.card State

/-! ## Kernel theorem: subfunction count ≤ crossing width -/

/-- **Crossing-state capacity bound (Nečiporuk kernel).**  If a crossing-state
model computes `Target`, then every residual subfunction of `Target` on the left
block factors through the crossing state, so the number of distinct residual
subfunctions is at most the model's width.

This is the genuine, restricted capacity theorem: capacity is provably bounded
by width for any model forced through one bounded crossing state. -/
theorem subfunctionCount_le_width
    [Fintype Left] [DecidableEq Left] [Fintype State]
    (M : CrossingStateModel Left Right State)
    (Target : (Left -> Bool) -> (Right -> Bool) -> Bool)
    (hM : M.Computes Target) :
    subfunctionCount Left Right Target <= M.width := by
  classical
  -- Each residual subfunction factors through the crossing state `encode a`.
  have hfact : forall a : Left -> Bool,
      residualFunction Left Right Target a
        = (fun s : State => fun b => M.out s b) (M.encode a) := by
    intro a
    funext b
    simp only [residualFunction]
    exact (hM a b).symm
  -- Hence the set of residual subfunctions is contained in the image of the
  -- finitely-many crossing states under `s ↦ (b ↦ out s b)`.
  have hsub : subfunctionSet Left Right Target ⊆
      (Finset.univ : Finset State).image (fun s => fun b => M.out s b) := by
    intro f hf
    simp only [subfunctionSet, Finset.mem_image, Finset.mem_univ, true_and] at hf ⊢
    obtain ⟨a, ha⟩ := hf
    exact ⟨M.encode a, by rw [← ha, hfact a]⟩
  -- Counting: |residuals| ≤ |image| ≤ |State| = width.
  calc
    subfunctionCount Left Right Target
        = (subfunctionSet Left Right Target).card := rfl
    _ <= ((Finset.univ : Finset State).image (fun s => fun b => M.out s b)).card :=
          Finset.card_le_card hsub
    _ <= (Finset.univ : Finset State).card := Finset.card_image_le
    _ = Fintype.card State := Finset.card_univ
    _ = M.width := rfl

end CrossingStateModel

/-! ## Genuine exponential lower bound via the existing capacity socket -/

/-- The crossing-state model satisfies the framework's
`SubfunctionCapacityPreservation` obligation for equality split, with the
nontrivial `capacity_sound` field discharged by the crossing kernel.  This is the
honest, model-specific capacity theorem the wall file flagged as the missing
ingredient — now supplied for the crossing-restricted model. -/
theorem crossing_capacity_preservation_equality
    (n : Nat) {State : Type} [Fintype State] :
    SubfunctionCapacityPreservation
      (CrossingStateModel (Fin n) (Fin n) State) (Fin n) (Fin n)
      (equalitySplitFunction (Fin n))
      (fun M => M.Computes (equalitySplitFunction (Fin n)))
      (fun M => M.width)
      (2 ^ n) (Fintype.card State) where
  lower_bound := by
    rw [subfunctionCount_equalitySplit_fin]
  capacity_sound := by
    intro M hM
    exact M.subfunctionCount_le_width (equalitySplitFunction (Fin n)) hM
  budget_le := by
    intro M
    exact Nat.le_refl _

/-- **Genuine exponential crossing-state lower bound.**  No crossing-state model
whose width is below `2^n` can compute equality split. -/
theorem no_crossing_model_below_exponential
    (n : Nat) {State : Type} [Fintype State]
    (hwidth : Fintype.card State < 2 ^ n) :
    Not (exists M : CrossingStateModel (Fin n) (Fin n) State,
      M.Computes (equalitySplitFunction (Fin n))) :=
  no_model_of_subfunction_capacity_gap
    (crossing_capacity_preservation_equality n) hwidth

/-- Contrapositive restatement: **any** crossing-state model that computes
equality split must have width at least `2^n`.  A real, restricted,
exponentially strong lower bound. -/
theorem crossing_width_ge_exponential
    (n : Nat) {State : Type} [Fintype State]
    (M : CrossingStateModel (Fin n) (Fin n) State)
    (hM : M.Computes (equalitySplitFunction (Fin n))) :
    2 ^ n <= Fintype.card State := by
  by_contra h
  push_neg at h
  exact no_crossing_model_below_exponential n h ⟨M, hM⟩

/-! ## Bundled crossing-state capacity theorem -/

/-- The completed crossing-state capacity theorem: the general crossing kernel
(`crossing_bound`) plus its exponential instantiation on equality split
(`equality_width_lower_bound`).  Restricted counterpart to
`SubfunctionCapacityWall`. -/
structure CrossingStateCapacityTheorem : Prop where
  /-- General kernel: capacity ≤ width for every crossing-state model. -/
  crossing_bound : forall {Left Right State : Type}
      [Fintype Left] [DecidableEq Left] [Fintype State]
      (M : CrossingStateModel Left Right State)
      (Target : (Left -> Bool) -> (Right -> Bool) -> Bool),
      M.Computes Target -> subfunctionCount Left Right Target <= M.width
  /-- Exponential lower bound for equality split. -/
  equality_width_lower_bound : forall (n : Nat) {State : Type} [Fintype State]
      (M : CrossingStateModel (Fin n) (Fin n) State),
      M.Computes (equalitySplitFunction (Fin n)) -> 2 ^ n <= Fintype.card State

/-- Completed crossing-state capacity theorem. -/
theorem crossingStateCapacityTheorem : CrossingStateCapacityTheorem where
  crossing_bound := by
    intro Left Right State _ _ _ M Target hM
    exact M.subfunctionCount_le_width Target hM
  equality_width_lower_bound := by
    intro n State _ M hM
    exact crossing_width_ge_exponential n M hM

/-! ## Kernel-only trace -/

#print axioms CrossingStateModel.subfunctionCount_le_width
#print axioms crossing_capacity_preservation_equality
#print axioms no_crossing_model_below_exponential
#print axioms crossing_width_ge_exponential
#print axioms crossingStateCapacityTheorem

end PallLean.Paper93.DeepMath.PathB
