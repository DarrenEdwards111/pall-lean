import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableMachine

/-!
# A verified finite-control compiler for `ComposableMachine`

The concrete MCSP verifier is an executable Lean function, but
`ComposableMachine.InP` deliberately accepts only a fixed finite-control,
forced-initialization tape machine.  This file introduces the small assembly
language used to close that representation gap.

The source language has finitely many labels.  Each label is either:

* `halt b`, returning decision bit `b`; or
* `act z o`, selecting a local transition according to the bit under the head.

A local transition contains only a next label, an optional bit write, and one
of the four `ComposableMachine.Move`s.  Thus source programs cannot inspect the
whole input, hide an oracle in initialization, or carry an unbounded value in
their control state.

`compile` lowers such a program to `ComposableMachine.Machine`.  Source
configurations and runs are defined independently, and the main theorems prove
exact preservation of initialization, one step, every finite run, halting,
output, and polynomial-time decision.  Later verifier files can therefore be
proved against the readable assembly semantics and transported to the faithful
machine model without another hand-written simulation argument.

This is the compiler backend, not yet the MCSP assembly program.
-/

namespace PallLean.Paper93.DeepMath.PathB.FiniteControlCompiler

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- One local tape action. -/
structure Action (Label : Type) where
  next : Label
  write : Option Bool
  move : Move

/-- A finite-control instruction. -/
inductive Instr (Label : Type)
  | halt (answer : Bool)
  | act (onFalse onTrue : Action Label)

/-- Select the action belonging to the currently scanned bit. -/
def Instr.select {Label : Type} : Instr Label → Bool → Option (Action Label)
  | .halt _, _ => none
  | .act z _, false => some z
  | .act _ o, true => some o

/-- The returned bit of a halting instruction. -/
def Instr.answer {Label : Type} : Instr Label → Bool
  | .halt b => b
  | .act _ _ => false

/-- A finite labelled tape program. -/
structure Program where
  Label : Type
  fin : Fintype Label
  dec : DecidableEq Label
  start : Label
  code : Label → Instr Label

attribute [instance] Program.fin Program.dec

/-- Independent source-level configuration. -/
structure AsmCfg (P : Program) where
  pc : P.Label
  hd : ℕ
  tp : List Bool

/-- Forced source initialization: the input is copied verbatim. -/
def asmInit (P : Program) (x : List Bool) : AsmCfg P :=
  ⟨P.start, 0, x⟩

/-- Source halting predicate. -/
def asmHalt (P : Program) (q : P.Label) : Bool :=
  match P.code q with
  | .halt _ => true
  | .act _ _ => false

/-- Source decision bit.  It is meaningful at a halting label. -/
def asmAccept (P : Program) (q : P.Label) : Bool :=
  (P.code q).answer

/-- One source step.  Halting configurations are stable. -/
def asmStep (P : Program) (c : AsmCfg P) : AsmCfg P :=
  match (P.code c.pc).select (c.tp.getD c.hd false) with
  | none => c
  | some a =>
      ⟨a.next, moveHead c.hd a.move,
        match a.write with
        | none => c.tp
        | some b => writeAt c.tp c.hd b⟩

/-- Run a source program for exactly `t` steps. -/
def asmRun (P : Program) (t : ℕ) (c : AsmCfg P) : AsmCfg P :=
  (asmStep P)^[t] c

@[simp] theorem asmRun_zero (P : Program) (c : AsmCfg P) :
    asmRun P 0 c = c := rfl

theorem asmRun_succ (P : Program) (t : ℕ) (c : AsmCfg P) :
    asmRun P (t + 1) c = asmStep P (asmRun P t c) :=
  Function.iterate_succ_apply' (asmStep P) t c

/-- Split a source run into consecutive phases. -/
theorem asmRun_add (P : Program) (a b : ℕ) (c : AsmCfg P) :
    asmRun P (a + b) c = asmRun P b (asmRun P a c) := by
  unfold asmRun
  rw [add_comm a b]
  exact Function.iterate_add_apply (asmStep P) b a c

/-- Lower the assembly program to the faithful finite-control machine model. -/
def compile (P : Program) : Machine where
  State := P.Label
  fin := inferInstance
  dec := inferInstance
  start := P.start
  halt := asmHalt P
  δ := fun q b =>
    match (P.code q).select b with
    | none => (q, none, 2)
    | some a => (a.next, a.write, a.move)
  accept := asmAccept P

/-- Configuration erasure into the compiled machine. -/
def lowerCfg (P : Program) (c : AsmCfg P) : Cfg (compile P) :=
  ⟨c.pc, c.hd, c.tp⟩

@[simp] theorem lowerCfg_asmInit (P : Program) (x : List Bool) :
    lowerCfg P (asmInit P x) = init (compile P) x := rfl

@[simp] theorem compile_halt (P : Program) (q : P.Label) :
    (compile P).halt q = asmHalt P q := rfl

@[simp] theorem compile_accept (P : Program) (q : P.Label) :
    (compile P).accept q = asmAccept P q := rfl

/-- The compiler preserves one source step exactly. -/
theorem compile_step (P : Program) (c : AsmCfg P) :
    step (compile P) (lowerCfg P c) = lowerCfg P (asmStep P c) := by
  rcases c with ⟨q, h, t⟩
  cases hcode : P.code q with
  | halt answer =>
      simp [step, compile, lowerCfg, asmStep, asmHalt, hcode, Instr.select]
  | act z o =>
      rcases z with ⟨zq, zw, zm⟩
      rcases o with ⟨oq, ow, om⟩
      simp only [step, compile, lowerCfg, asmStep, asmHalt, hcode,
        Bool.false_eq_true, ↓reduceIte]
      cases hb : t.getD h false <;>
        simp only [Instr.select] <;>
        cases zw <;> cases ow <;> rfl

/-- The compiler preserves every finite run exactly. -/
theorem compile_run (P : Program) (t : ℕ) (c : AsmCfg P) :
    run (compile P) t (lowerCfg P c) = lowerCfg P (asmRun P t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, asmRun_succ, ih, compile_step]

/-- Compiled runs from forced initialization are source runs. -/
theorem compile_run_init (P : Program) (x : List Bool) (t : ℕ) :
    run (compile P) t (init (compile P) x) =
      lowerCfg P (asmRun P t (asmInit P x)) := by
  rw [← lowerCfg_asmInit, compile_run]

/-- Source halting by a clock. -/
def AsmHaltsBy (P : Program) (x : List Bool) (T : ℕ) : Prop :=
  asmHalt P (asmRun P T (asmInit P x)).pc = true

/-- Source output after a clock. -/
def asmDecideOut (P : Program) (x : List Bool) (T : ℕ) : Bool :=
  asmAccept P (asmRun P T (asmInit P x)).pc

/-- A source program decides `L` within the length clock `T`. -/
def AsmDecides (P : Program) (L : List Bool → Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x, AsmHaltsBy P x (T x.length) ∧
    asmDecideOut P x (T x.length) = L x

/-- Exact preservation of the halting observation. -/
theorem compile_haltsBy_iff (P : Program) (x : List Bool) (t : ℕ) :
    HaltsBy (compile P) x t ↔ AsmHaltsBy P x t := by
  simp only [HaltsBy, AsmHaltsBy, compile_run_init, compile_halt, lowerCfg]

/-- Exact preservation of the decision observation. -/
theorem compile_decideOut (P : Program) (x : List Bool) (t : ℕ) :
    decideOut (compile P) x t = asmDecideOut P x t := by
  simp only [decideOut, asmDecideOut, compile_run_init, compile_accept, lowerCfg]

/-- A verified source decider compiles to a faithful machine decider with the
same clock. -/
theorem compile_decides {P : Program} {L : List Bool → Bool} {T : ℕ → ℕ}
    (h : AsmDecides P L T) :
    Decides (compile P) L T := by
  intro x
  obtain ⟨hh, ho⟩ := h x
  exact ⟨(compile_haltsBy_iff P x _).2 hh,
    (compile_decideOut P x _).trans ho⟩

/-- Polynomial-time source correctness transports directly to
`ComposableMachine.InP`. -/
theorem inP_of_asm {P : Program} {L : List Bool → Bool} {T : ℕ → ℕ}
    (hT : PolyBounded T) (h : AsmDecides P L T) :
    InP L :=
  ⟨compile P, T, hT, compile_decides h⟩

end PallLean.Paper93.DeepMath.PathB.FiniteControlCompiler

#print axioms PallLean.Paper93.DeepMath.PathB.FiniteControlCompiler.compile_step
#print axioms PallLean.Paper93.DeepMath.PathB.FiniteControlCompiler.compile_run
#print axioms PallLean.Paper93.DeepMath.PathB.FiniteControlCompiler.compile_decides
#print axioms PallLean.Paper93.DeepMath.PathB.FiniteControlCompiler.inP_of_asm
