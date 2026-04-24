import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic

/-!
# Nondeterministic Turing Machine (NTM)

A minimal, self-contained nondeterministic Turing machine structure
with a finite state and finite symbol alphabet, together with its
configuration type and basic predicates.

This file intentionally contains **definitions only** (no proofs beyond
`rfl`-level structural equalities), so that downstream files in the
Cook--Levin pipeline can depend on an axiom-clean notion of NTM.

Design notes:
* We store the state/symbol decidability and finiteness hypotheses as
  instance fields so that any `M : NTM` automatically carries them.
* The transition relation is represented as a total function returning
  a `List` of admissible successor triples, encoding nondeterminism.
* The tape-head move is encoded as an `Int` (`-1`, `0`, or `+1`); we
  do not constrain it to the three-valued set at the type level to
  keep the structure light; concrete constructions will normalise it.
-/

namespace PallLean.Paper93.DeepMath.CookLevin

/-- Nondeterministic Turing machine with finite state and symbol sets. -/
structure NTM where
  /-- Finite set of states. -/
  State : Type
  /-- Finite tape alphabet. -/
  Symbol : Type
  [stateFintype : Fintype State]
  [symbolFintype : Fintype Symbol]
  [stateDec : DecidableEq State]
  [symbolDec : DecidableEq Symbol]
  /-- Designated initial state. -/
  initialState : State
  /-- Set of accepting states. -/
  acceptStates : Set State
  /-- Transition relation: given current `(state, symbol)`, returns a list of
      possible `(new state, new symbol, tape-head move)` triples.
      The head move is encoded as an integer in `{-1, 0, +1}`. -/
  transitions : State × Symbol → List (State × Symbol × Int)

attribute [instance] NTM.stateFintype NTM.symbolFintype
attribute [instance] NTM.stateDec NTM.symbolDec

/-- A configuration of the NTM: current state, tape contents (indexed by `ℤ`),
    and current head position. -/
structure NTMConfig (M : NTM) where
  /-- Current internal state. -/
  state : M.State
  /-- Bi-infinite tape as a function `ℤ → Symbol`. -/
  tape : ℤ → M.Symbol
  /-- Current tape-head position. -/
  headPos : ℤ

namespace NTMConfig

/-- Initial configuration for a given input tape: start state, supplied tape,
    head at position `0`. -/
def initial (M : NTM) (inputTape : ℤ → M.Symbol) : NTMConfig M :=
  { state := M.initialState, tape := inputTape, headPos := 0 }

/-- An NTM configuration is accepting iff its current state is an accept state. -/
def isAccept {M : NTM} (c : NTMConfig M) : Prop :=
  c.state ∈ M.acceptStates

/-- Symbol currently under the tape head. -/
def currentSymbol {M : NTM} (c : NTMConfig M) : M.Symbol :=
  c.tape c.headPos

/-- List of admissible successor triples at the current head cell. -/
def availableTransitions {M : NTM} (c : NTMConfig M) :
    List (M.State × M.Symbol × Int) :=
  M.transitions (c.state, c.currentSymbol)

end NTMConfig

end PallLean.Paper93.DeepMath.CookLevin
