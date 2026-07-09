import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSelfReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPObserverSwitchToy
import Mathlib

/-!
# P-vs-NP residual observer — first concrete interface

This file starts the real SAT-side instantiation of the observer-switch programme.

It reuses the repository's semantic SAT self-reduction layer:

* `CNF`, `RawAssignment`, `Satisfiable`, `SatisfiableWithPrefix` from
  `ComputationalDepthSelfReduction.lean` / `ComputationalDepthMachineSemantics.lean`;
* the finite pigeonhole core from `ComputationalDepthPvsNPObserverSwitchToy.lean`.

What is proved here is deliberately modest and honest:

* a residual observer is a map `(φ, prefix) ↦ boundary state`;
* restricting such an observer to full `n`-bit prefixes gives a finite observer on `2^n` branches;
* if that restricted observer is injective, the boundary has at least `2^n` states;
* therefore polynomial boundary plus full residual distinction contradicts `n^k < 2^n`.

This is not `P ≠ NP`; it is the next formal socket.  The missing hard theorem is that a *real* SAT/self-reduction
observer must be injective, or at least large, on enough residual branches while P-time computation implies polynomial
boundary size.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserver

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open SATDepthMachine

/-- A full Boolean assignment as a raw SAT prefix/list. -/
def assignmentPrefix {n : ℕ} (a : Assignment n) : RawAssignment :=
  List.ofFn a

/-- Full assignments become prefixes of length `n`. -/
theorem assignmentPrefix_length {n : ℕ} (a : Assignment n) :
    (assignmentPrefix a).length = n := by
  simp [assignmentPrefix]

/-- A SAT residual observer maps a formula and a current prefix/residual branch to a boundary state. -/
abbrev ResidualObserver (α : Type) := CNF → RawAssignment → α

/-- The induced finite observer on all full `n`-bit branches for a fixed formula. -/
def fullBranchObserver {n : ℕ} {α : Type} (obs : ResidualObserver α) (φ : CNF) :
    Assignment n → α :=
  fun a => obs φ (assignmentPrefix a)

/-- Full-branch residual distinction: the observer gives different boundary states to different full branches. -/
def FullResidualDistinguishing {n : ℕ} {α : Type} (obs : ResidualObserver α) (φ : CNF) : Prop :=
  Function.Injective (fullBranchObserver (n := n) obs φ)

/-- Polynomial boundary-size hypothesis at input length `n`. -/
def PolyBoundaryAt (n k : ℕ) (α : Type) [Fintype α] : Prop :=
  Fintype.card α ≤ n ^ k

/-- If the residual observer distinguishes all full `n`-bit branches, its boundary has at least `2^n` states. -/
theorem full_residual_boundary_card_ge_exp {n : ℕ} {α : Type} [Fintype α]
    (obs : ResidualObserver α) (φ : CNF)
    (hdist : FullResidualDistinguishing (n := n) obs φ) :
    2 ^ n ≤ Fintype.card α := by
  exact boundary_card_ge_exp (fullBranchObserver (n := n) obs φ) hdist

/-- No boundary smaller than `2^n` can distinguish all full residual branches. -/
theorem small_boundary_not_full_residual_distinguishing {n : ℕ} {α : Type} [Fintype α]
    (obs : ResidualObserver α) (φ : CNF) (hsmall : Fintype.card α < 2 ^ n) :
    ¬ FullResidualDistinguishing (n := n) obs φ := by
  exact small_boundary_not_residual_distinguishing (fullBranchObserver (n := n) obs φ) hsmall

/-- Polynomial boundary plus the exponential gap forbids full residual distinction. -/
theorem poly_boundary_not_full_residual_distinguishing {n k : ℕ} {α : Type} [Fintype α]
    (obs : ResidualObserver α) (φ : CNF)
    (hpoly : PolyBoundaryAt n k α) (hgap : n ^ k < 2 ^ n) :
    ¬ FullResidualDistinguishing (n := n) obs φ := by
  exact poly_boundary_not_residual_distinguishing
    (fullBranchObserver (n := n) obs φ) hpoly hgap

/-- Contradiction form of the residual-observer H4 socket. -/
theorem full_residual_distinguishing_contradicts_poly_boundary {n k : ℕ} {α : Type} [Fintype α]
    (obs : ResidualObserver α) (φ : CNF)
    (hdist : FullResidualDistinguishing (n := n) obs φ)
    (hpoly : PolyBoundaryAt n k α) (hgap : n ^ k < 2 ^ n) : False := by
  exact residual_distinguishing_contradicts_poly_boundary
    (fullBranchObserver (n := n) obs φ) hdist hpoly hgap

/-! ## Prefix-SAT semantics hooks

The next genuinely hard step is not combinatorial; it is semantic.  We name the hooks below so future work can state the
missing SAT-specific preservation theorem without smuggling it into the pigeonhole proof.
-/

/-- The SAT truth seen at a residual branch/prefix. -/
def residualSATTruth (φ : CNF) (p : RawAssignment) : Prop :=
  SatisfiableWithPrefix φ p

/-- A residual observer is truth-sound if equal boundary states never disagree about prefix satisfiability.  This is only
a weak semantic consistency condition; it does **not** imply full residual distinction. -/
def ResidualTruthSound {α : Type} (obs : ResidualObserver α) : Prop :=
  ∀ φ p q, obs φ p = obs φ q → (residualSATTruth φ p ↔ residualSATTruth φ q)

/-- Full residual distinction is stronger than truth-soundness on full branches.  This theorem records the direction that
is easy: injectivity makes equal observer states force equal prefixes, hence equal residual truth by substitution. -/
theorem full_distinguishing_truth_sound_on_full_branches {n : ℕ} {α : Type}
    (obs : ResidualObserver α) (φ : CNF)
    (hdist : FullResidualDistinguishing (n := n) obs φ) :
    ∀ a b : Assignment n,
      fullBranchObserver obs φ a = fullBranchObserver obs φ b →
        (residualSATTruth φ (assignmentPrefix a) ↔ residualSATTruth φ (assignmentPrefix b)) := by
  intro a b h
  have hab : a = b := hdist h
  subst hab
  rfl

/-!
Current state:

```text
Polynomial boundary + full residual distinction + n^k < 2^n ⇒ contradiction.
```

Remaining hard sockets:

1. **P-side compression:** a P-time SAT decider induces `PolyBoundaryAt n k α` for an appropriate residual observer;
2. **NP-side preservation:** SAT self-reduction / hard formula families force `FullResidualDistinguishing`, or a weaker
   many-residual lower bound, for that same observer;
3. **barrier check:** the observer must avoid being a computable large truth-table property.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserver

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserver.full_residual_boundary_card_ge_exp
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserver.poly_boundary_not_full_residual_distinguishing
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserver.full_residual_distinguishing_contradicts_poly_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserver.full_distinguishing_truth_sound_on_full_branches
