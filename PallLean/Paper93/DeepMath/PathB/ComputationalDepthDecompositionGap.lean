import PallLean.Paper93.DeepMath.PathB.ComputationalDepthContinuationObserver

/-!
# The decomposition gap: fixed-cut insufficiency, made a theorem

The continuation bridge proved every *faithful single-cut* (`prefix|suffix`) observer of EQUALITY has
boundary `≥ n`.  We kept saying this is *insufficient* for hardness because "EQUALITY is cheap under another
decomposition".  This file makes that a **theorem**: EQUALITY has a **constant-boundary streaming
(multi-cut) decider** — the running-AND that scans the `n` coordinate pairs keeping one bit of memory.

So for the *same* function:

* single-cut faithful boundary `≥ n` (`equality_continuation_forces_boundary`);
* multi-cut streaming boundary `= 1` (`equality_decomposition_gap`).

A single decomposition's lower bound therefore does **not** lower-bound the *minimum over decompositions*.
This is the precise content of "the machine chooses the decomposition", and it locates the open problem at
exactly one quantifier: a separation needs boundary `≥ ω(log n)` under **every** admissible decomposition
(`= CookLevinFrontierHyp`), not just one — and EQUALITY witnesses that one large cut is not enough.

## What is proved (all clean axioms, no `sorry`)

* `StreamObserver` — a finite-memory streaming observer; `boundary = log₂ |State|`.
* `eqStream_run` — the running-AND streaming observer decides "all scanned pairs are equal".
* `equality_decomposition_gap` — the gap, for the same EQUALITY function: single-cut `≥ n`, streaming `= 1`,
  and the streaming observer is correct (`run (zip p s) = (p == s)`).

## Honest scope

This proves fixed-decomposition bounds are insufficient (a real gap, `n` vs `1`).  It does **not** close the
separation: that needs a *lower* bound on the boundary under *every* decomposition for a *hard* family, which
remains open.  EQUALITY is the cautionary witness, not a target.
-/

namespace PallLean.Paper93.DeepMath.PathB.DecompositionGap

open PallLean.Paper93.DeepMath.PathB

/-- A finite-memory **streaming (multi-cut) observer**: a start state, a transition reading one input symbol,
and an accept predicate.  Its boundary is the memory it carries between symbols. -/
structure StreamObserver (State Sym : Type*) where
  start : State
  step : State → Sym → State
  accept : State → Bool

namespace StreamObserver

variable {State Sym : Type*}

/-- Run the observer over an input stream. -/
def run (O : StreamObserver State Sym) (input : List Sym) : Bool :=
  O.accept (input.foldl O.step O.start)

/-- **Boundary entropy** of a streaming observer: `log₂` of the number of memory states it can hold between
symbols (the multi-cut analogue of `BranchingObserver.entropy`). -/
def boundary [Fintype State] (_O : StreamObserver State Sym) : ℕ :=
  Nat.log 2 (Fintype.card State)

end StreamObserver

/-- The **EQUALITY streaming observer**: scan coordinate pairs `(pᵢ, sᵢ)`, keeping one bit "equal so far".
Memory is a single `Bool` — constant boundary. -/
def eqStream : StreamObserver Bool (Bool × Bool) where
  start := true
  step := fun acc pr => acc && decide (pr.1 = pr.2)
  accept := id

/-- Folding the running-AND over a list: result is `acc && (all pairs equal)`. -/
theorem foldl_step (l : List (Bool × Bool)) (acc : Bool) :
    l.foldl (fun a pr => a && decide (pr.1 = pr.2)) acc
      = (acc && decide (∀ pr ∈ l, pr.1 = pr.2)) := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
      simp only [List.foldl_cons, ih, List.forall_mem_cons, Bool.decide_and]
      rw [Bool.and_assoc]

/-- **The streaming observer decides "all scanned pairs are equal".** -/
theorem eqStream_run (input : List (Bool × Bool)) :
    eqStream.run input = decide (∀ pr ∈ input, pr.1 = pr.2) := by
  show List.foldl (fun a pr => a && decide (pr.1 = pr.2)) true input = _
  rw [foldl_step, Bool.true_and]

/-- The EQUALITY streaming observer has boundary `1` (one bit of memory). -/
theorem eqStream_boundary : eqStream.boundary = 1 := by
  show Nat.log 2 (Fintype.card Bool) = 1
  rw [Fintype.card_bool]
  exact Nat.log_eq_one_iff.mpr (by norm_num)

/-- **The decomposition gap (proved), for the same EQUALITY function.**

1. *single-cut*: every faithful `prefix|suffix` observer has boundary `≥ n`;
2. *multi-cut*: the streaming observer has boundary `1`;
3. and it is *correct* — `run (zip p s) = (p == s)`.

So a single decomposition's lower bound (`≥ n`) does **not** lower-bound the minimum over decompositions
(`≤ 1` here).  Fixed-cut insufficiency is now a theorem, not an assertion. -/
theorem equality_decomposition_gap (n : ℕ) :
    (∀ O : BranchingObserver (Fin n → Bool),
        ContinuationObserver.Faithful O (ContinuationObserver.eqDec n) → n ≤ O.entropy)
    ∧ eqStream.boundary = 1
    ∧ ∀ p s : Fin n → Bool,
        eqStream.run (List.ofFn (fun i => (p i, s i))) = ContinuationObserver.eqDec n p s := by
  refine ⟨fun O hf => ContinuationObserver.equality_continuation_forces_boundary n O hf,
    eqStream_boundary, ?_⟩
  intro p s
  rw [eqStream_run, ContinuationObserver.eqDec, decide_eq_decide]
  constructor
  · intro h
    funext i
    exact h (p i, s i) ((List.mem_ofFn' _ _).mpr (Set.mem_range.mpr ⟨i, rfl⟩))
  · intro h pr hpr
    obtain ⟨i, hi⟩ := Set.mem_range.mp ((List.mem_ofFn' _ _).mp hpr)
    rw [← hi]
    exact congrFun h i

end PallLean.Paper93.DeepMath.PathB.DecompositionGap

#print axioms PallLean.Paper93.DeepMath.PathB.DecompositionGap.eqStream_run
#print axioms PallLean.Paper93.DeepMath.PathB.DecompositionGap.equality_decomposition_gap
