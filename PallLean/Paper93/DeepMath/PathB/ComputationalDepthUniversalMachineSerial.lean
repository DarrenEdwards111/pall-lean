import Mathlib.Data.List.Basic

/-!
# Universal machine, brick 1: Bool-tape serialization of a machine description

The universal machine that discharges the diagonal socket (`DiagonalAgainstCanon`) must read an
arbitrary machine's description OFF ITS OWN TAPE.  This file builds the genuine first component: a
Bool-tape serialization of a flat machine description with a machine-checked round-trip
`decode (encode m) = some (m, rest)`.  It is a real serialization to `List Bool` (self-delimiting
parser codecs, the `encPair`/`decodePair` discipline), NOT a structured repackaging that leaves the
data as Lean values.

## The codecs (each with a proved round-trip)

Every codec `enc/dec` satisfies `dec (enc a ++ rest) = some (a, rest)` — the composable parser law.

* `encNat`/`decNat` — self-delimiting unary naturals.
* `encBool`/`decBool` — one bit.
* `encOptBool`/`decOptBool` — `Option Bool` (`none`/`some false`/`some true`).
* `encListAux`/`decN`/`decList` — length-prefixed lists (decode recurses on the COUNT, so it is
  structurally terminating — the reason a length prefix is used rather than a terminator).

## The machine description

`SerialMachine`: a start state, a list of transition `Rule`s `(state, symbol) ↦ (state, write,
move)` (all `ℕ`/`Bool`-valued, flat — no `Fin k` dependency), and a list of accepting states.

* **`decodeMachine_encodeMachine`** (proved) — the round trip: `decodeMachine (encodeMachine m ++
  rest) = some (m, rest)`; in particular `decodeMachine (encodeMachine m) = some (m, [])`.  A
  machine description survives the trip onto and off the tape intact.

## Honest scope — what this is and what remains

This is brick 1 of the universal machine: the description is now a genuine `List Bool` the machine
can read, and the read-back is verified.  What remains (real labor, flagged, not faked): the
serialization is UNARY, so encodings are exponential — a binary refinement is needed for the
polynomial clock bound; the `SerialMachine ↔ FinMachineData` semantic bridge (brick 2); the
step-simulation loop reading this tape (brick 3); the clocked run and the lazy-delay diagonal
(bricks 4–5).  This file makes no claim beyond a verified Bool-tape codec.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial

/-! ### Naturals -/

/-- Self-delimiting unary encoding of a natural. -/
def encNat : ℕ → List Bool
  | 0 => [false]
  | n + 1 => true :: encNat n

/-- Decode a self-delimiting unary natural, returning the remainder. -/
def decNat : List Bool → Option (ℕ × List Bool)
  | false :: rest => some (0, rest)
  | true :: rest =>
      match decNat rest with
      | some (n, rest') => some (n + 1, rest')
      | none => none
  | [] => none

theorem decNat_encNat (n : ℕ) (rest : List Bool) :
    decNat (encNat n ++ rest) = some (n, rest) := by
  induction n generalizing rest with
  | zero => rfl
  | succ n ih => simp only [encNat, List.cons_append, decNat, ih]

/-! ### Booleans and `Option Bool` -/

def encBool (b : Bool) : List Bool := [b]

def decBool : List Bool → Option (Bool × List Bool)
  | b :: rest => some (b, rest)
  | [] => none

theorem decBool_encBool (b : Bool) (rest : List Bool) :
    decBool (encBool b ++ rest) = some (b, rest) := rfl

def encOptBool : Option Bool → List Bool
  | none => [false]
  | some b => [true, b]

def decOptBool : List Bool → Option (Option Bool × List Bool)
  | false :: rest => some (none, rest)
  | true :: b :: rest => some (some b, rest)
  | _ => none

theorem decOptBool_encOptBool (o : Option Bool) (rest : List Bool) :
    decOptBool (encOptBool o ++ rest) = some (o, rest) := by
  cases o <;> rfl

/-! ### Length-prefixed lists (structurally terminating decode) -/

/-- Concatenate element encodings (no length header). -/
def encListAux (encA : α → List Bool) : List α → List Bool
  | [] => []
  | a :: as => encA a ++ encListAux encA as

/-- Decode exactly `n` elements — structural recursion on the count `n`. -/
def decN (decA : List Bool → Option (α × List Bool)) : ℕ → List Bool → Option (List α × List Bool)
  | 0, rest => some ([], rest)
  | n + 1, l =>
      match decA l with
      | none => none
      | some (a, l') =>
          match decN decA n l' with
          | none => none
          | some (as, l'') => some (a :: as, l'')

theorem decN_encListAux {α : Type} (encA : α → List Bool) (decA : List Bool → Option (α × List Bool))
    (h : ∀ a rest, decA (encA a ++ rest) = some (a, rest)) (l : List α) (rest : List Bool) :
    decN decA l.length (encListAux encA l ++ rest) = some (l, rest) := by
  induction l generalizing rest with
  | nil => rfl
  | cons a as ih =>
    show decN decA (as.length + 1) ((encA a ++ encListAux encA as) ++ rest)
      = some (a :: as, rest)
    rw [List.append_assoc]
    simp only [decN, h, ih]

/-- Length-prefixed list encoding: a count, then the elements. -/
def encList (encA : α → List Bool) (l : List α) : List Bool :=
  encNat l.length ++ encListAux encA l

/-- Decode a length-prefixed list. -/
def decList (decA : List Bool → Option (α × List Bool)) (l : List Bool) :
    Option (List α × List Bool) :=
  match decNat l with
  | none => none
  | some (n, rest) => decN decA n rest

theorem decList_encList {α : Type} (encA : α → List Bool)
    (decA : List Bool → Option (α × List Bool))
    (h : ∀ a rest, decA (encA a ++ rest) = some (a, rest)) (l : List α) (rest : List Bool) :
    decList decA (encList encA l ++ rest) = some (l, rest) := by
  unfold encList decList
  rw [List.append_assoc, decNat_encNat]
  show decN decA l.length (encListAux encA l ++ rest) = some (l, rest)
  exact decN_encListAux encA decA h l rest

/-! ### The machine description -/

/-- A flat transition rule: on `(state, symbol)` go to `state`, write `Option Bool`, move `ℕ`. -/
abbrev Rule : Type := ℕ × Bool × ℕ × Option Bool × ℕ

def encRule (r : Rule) : List Bool :=
  encNat r.1 ++ encBool r.2.1 ++ encNat r.2.2.1 ++ encOptBool r.2.2.2.1 ++ encNat r.2.2.2.2

def decRule (l : List Bool) : Option (Rule × List Bool) :=
  match decNat l with
  | none => none
  | some (s, l1) =>
    match decBool l1 with
    | none => none
    | some (r, l2) =>
      match decNat l2 with
      | none => none
      | some (ns, l3) =>
        match decOptBool l3 with
        | none => none
        | some (w, l4) =>
          match decNat l4 with
          | none => none
          | some (m, l5) => some ((s, r, ns, w, m), l5)

theorem decRule_encRule (r : Rule) (rest : List Bool) :
    decRule (encRule r ++ rest) = some (r, rest) := by
  obtain ⟨s, rd, ns, w, m⟩ := r
  simp only [encRule, decRule, List.append_assoc, decNat_encNat, decBool_encBool,
    decOptBool_encOptBool]

/-- A serialized machine: start state, transition rules, accepting states. -/
structure SerialMachine where
  start : ℕ
  rules : List Rule
  accept : List ℕ

def encodeMachine (m : SerialMachine) : List Bool :=
  encNat m.start ++ encList encRule m.rules ++ encList encNat m.accept

def decodeMachine (l : List Bool) : Option (SerialMachine × List Bool) :=
  match decNat l with
  | none => none
  | some (s, l1) =>
    match decList decRule l1 with
    | none => none
    | some (rules, l2) =>
      match decList decNat l2 with
      | none => none
      | some (accept, l3) => some (⟨s, rules, accept⟩, l3)

/-- **The machine description round-trip (proved).**  A serialized machine survives the trip onto
and off the Bool tape intact: `decodeMachine (encodeMachine m ++ rest) = some (m, rest)`. -/
theorem decodeMachine_encodeMachine (m : SerialMachine) (rest : List Bool) :
    decodeMachine (encodeMachine m ++ rest) = some (m, rest) := by
  obtain ⟨s, rules, accept⟩ := m
  simp only [encodeMachine, decodeMachine, List.append_assoc, decNat_encNat,
    decList_encList encRule decRule decRule_encRule,
    decList_encList encNat decNat decNat_encNat]

/-- The clean form: decoding the exact encoding recovers the machine with empty remainder. -/
theorem decodeMachine_encodeMachine_nil (m : SerialMachine) :
    decodeMachine (encodeMachine m) = some (m, []) := by
  have h := decodeMachine_encodeMachine m []
  rwa [List.append_nil] at h

end PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial.decNat_encNat
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial.decRule_encRule
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial.decodeMachine_encodeMachine
