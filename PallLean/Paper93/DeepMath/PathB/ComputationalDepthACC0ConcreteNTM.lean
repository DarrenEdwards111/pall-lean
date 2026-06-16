import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTM

/-!
# A concrete, encodable nondeterministic Turing machine model

The abstract `…ACC0NTM.NTM` has `Config : Type` — too abstract for a universal simulator or machine enumeration.  This
file gives a **concrete, encodable** model: a binary tape (`List Bool`), a head position and state (`ℕ`), and a
transition table that is a *finite list* of rules.  Because every component is `Encodable`, a machine is encodable as a
natural number — so **machines are enumerable**, exactly the ingredient the time-hierarchy sockets
(`enum_covers`) require.  A bridge `toNTM` realises each concrete machine as an abstract `NTM`, connecting this model
to the hierarchy framework.

## Model

* `Move := Fin 3` (`0`=left, `1`=right, `2`=stay); `TMTrans := (ℕ × Bool) × (ℕ × Bool × Move)` — a rule
  `(state, read) ↦ (state', write, move)`; `TMachine := List TMTrans` — a (nondeterministic) transition table.
* `CConfig := ℕ × ℕ × List Bool` — `(state, head, tape)`.  `concreteStep M` applies any matching rule.
* `toNTM M : NTM` — the abstract machine with `init x = (0,0,x)`, `accept = (state = 1)`.

## What is proved (clean axioms, no `sorry`)

* **`TMachine`** is `Encodable` and `Infinite`, hence **`machineEquiv : TMachine ≃ ℕ`** — the machine enumeration.
* **`toNTM`** — the bridge from a concrete machine to an abstract `NTM`; **`concrete_step_iff`** characterises its
  step relation; **`toNTM_init`** / **`toNTM_accept`** unfold the initialiser and accept predicate.

## Honest scope

This is the *encodable model* and the machine enumeration — genuine complexity-theory infrastructure that the abstract
model could not provide.  It does **not** yet build the universal simulator or prove the hierarchy: `enum_covers`
(that some enumeration covers `NTIME g`) and `diag_in_big` (the diagonal decidable in the bigger bound) still require a
time-bounded universal machine over this model — the next step.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM)

/-- A head move: `0` left, `1` right, `2` stay. -/
abbrev Move := Fin 3

/-- A transition rule: `(state, read) ↦ (state', write, move)`. -/
abbrev TMTrans := (ℕ × Bool) × (ℕ × Bool × Move)

/-- A nondeterministic transition table. -/
abbrev TMachine := List TMTrans

/-- A configuration: `(state, head, tape)`. -/
abbrev CConfig := ℕ × ℕ × List Bool

/-- The symbol under the head (`false` past the end of the tape). -/
def readSym (c : CConfig) : Bool := c.2.2.getD c.2.1 false

/-- Move the head according to a `Move`. -/
def moveHead (h : ℕ) (m : Move) : ℕ :=
  if m = 0 then h - 1 else if m = 1 then h + 1 else h

/-- Write `w` at position `p`, padding the tape with blanks (`false`) if needed. -/
def writeAt (tape : List Bool) (p : ℕ) (w : Bool) : List Bool :=
  (tape ++ List.replicate (p + 1 - tape.length) false).set p w

/-- Apply a transition rule to a configuration (its right-hand side determines the next configuration). -/
def applyTrans (c : CConfig) (t : TMTrans) : CConfig :=
  (t.2.1, moveHead c.2.1 t.2.2.2, writeAt c.2.2 c.2.1 t.2.2.1)

/-- **The concrete step relation**: some rule whose left-hand side matches `(state, read)` fires. -/
def concreteStep (M : TMachine) (c d : CConfig) : Prop :=
  ∃ t ∈ M, t.1 = (c.1, readSym c) ∧ d = applyTrans c t

/-- **Machines are enumerable (proved): `TMachine ≃ ℕ`.**  Every component is `Encodable`, so the transition-table
list is encodable and (being unbounded in length) infinite — hence countably infinite.  This is the enumeration the
time-hierarchy `enum_covers` socket needs. -/
noncomputable def machineEquiv : TMachine ≃ ℕ :=
  haveI : Denumerable TMachine := Denumerable.ofEncodableOfInfinite TMachine
  Denumerable.eqv TMachine

/-- **The bridge to the abstract model (proved): each concrete machine is an abstract `NTM`.**  Start state `0`, head
`0`, tape `= input`; accept iff the state is `1`. -/
def toNTM (M : TMachine) : NTM where
  Config := CConfig
  step := concreteStep M
  init := fun x => (0, 0, x)
  accept := fun c => c.1 = 1

@[simp] theorem toNTM_step (M : TMachine) (c d : CConfig) :
    (toNTM M).step c d ↔ concreteStep M c d := Iff.rfl

@[simp] theorem toNTM_init (M : TMachine) (x : List Bool) :
    (toNTM M).init x = (0, 0, x) := rfl

@[simp] theorem toNTM_accept (M : TMachine) (c : CConfig) :
    (toNTM M).accept c ↔ c.1 = 1 := Iff.rfl

/-- **The step relation is characterised (proved).** -/
theorem concrete_step_iff (M : TMachine) (c d : CConfig) :
    concreteStep M c d ↔ ∃ t ∈ M, t.1 = (c.1, readSym c) ∧ d = applyTrans c t := Iff.rfl

end PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM.machineEquiv
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM.toNTM
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM.concrete_step_iff
