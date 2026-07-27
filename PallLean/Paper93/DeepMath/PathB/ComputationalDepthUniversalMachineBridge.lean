import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineSerial
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniformityGapDiagonal

/-!
# Universal machine, brick 2: the `SerialMachine ↔ FinMachineData` semantic bridge

Brick 1 gave a verified Bool-tape codec for a flat `SerialMachine`.  This brick connects that flat
description back to the actual `FinMachineData k` machine it represents: `serialOf` flattens a
finite-state machine into a `SerialMachine`, and the transitions/accepts are proved to survive
faithfully — the universal machine's decoded description genuinely IS the machine to simulate.

## What is proved

* **`serialOf`** — flatten `FinMachineData k` to a `SerialMachine`: start `= data.start.val`, one
  transition `Rule` per `(state, symbol)`, accepting states listed.
* **`serialOf_start`** — the start state survives.
* **`rule_mem`** — EVERY transition survives: `mkRule data i b ∈ (serialOf data).rules`, for every
  state `i` and symbol `b`.  The full transition table is faithfully present in the serialization.
* **`accept_mem`** — every accepting state is listed.
* **`lookupRule` + `lookupRule_cons_match` + `lookupRule_append_no_match`** — the recovery
  infrastructure: a rule lookup by `(state, symbol)`, with the two lemmas (a matching head returns
  its payload; a non-matching prefix is skipped) that recover a transition from the list.
* **`serialOf_roundtrips`** — the flattened machine survives the Bool-tape trip (brick 1 applied).

## Honest scope

Brick 2 establishes faithful CONTAINMENT (every transition and accept is in the serialization) plus
the lookup infrastructure that recovers a transition from the list.  The remaining step —
`lookupRule (serialRules data) i.val b` returns exactly `data`'s transition (first-match recovery) —
needs the `flatMap`/`finRange` ordering plus key-uniqueness argument; it is brick 2b and combines
`rule_mem`, the two lookup lemmas, and nodup of the rule keys.  Also flagged: `SerialMachine` carries
no `halt` field, so full faithfulness (for `HaltsBy`) wants a one-field extension of brick 1.  No
claim here beyond faithful containment + recovery infrastructure.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineBridge

open PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial
open PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal

variable {k : ℕ}

/-- The `Rule` encoding of `data`'s transition on `(state i, symbol b)`. -/
def mkRule (data : FinMachineData k) (i : Fin k) (b : Bool) : Rule :=
  let t := data.2.2.1 i b
  (i.val, b, t.1.val, t.2.1, t.2.2.val)

/-- The flattened transition table: one rule per `(state, symbol)`. -/
def serialRules (data : FinMachineData k) : List Rule :=
  (List.finRange k).flatMap (fun i => [mkRule data i false, mkRule data i true])

/-- The accepting states, listed. -/
def serialAccept (data : FinMachineData k) : List ℕ :=
  (List.finRange k).filterMap (fun i => if data.2.2.2 i = true then some i.val else none)

/-- Flatten a finite-state machine to a `SerialMachine`. -/
def serialOf (data : FinMachineData k) : SerialMachine :=
  ⟨data.1.val, serialRules data, serialAccept data⟩

/-- **The start state survives (proved).** -/
theorem serialOf_start (data : FinMachineData k) : (serialOf data).start = data.1.val := rfl

/-- **Every transition survives (proved).**  The rule for `(state i, symbol b)` is in the
serialization, for all `i`, `b` — the full transition table is faithfully present. -/
theorem rule_mem (data : FinMachineData k) (i : Fin k) (b : Bool) :
    mkRule data i b ∈ (serialOf data).rules := by
  show mkRule data i b ∈ serialRules data
  rw [serialRules, List.mem_flatMap]
  exact ⟨i, List.mem_finRange i, by cases b <;> simp⟩

/-- **Every accepting state is listed (proved).** -/
theorem accept_mem (data : FinMachineData k) (i : Fin k) (h : data.2.2.2 i = true) :
    i.val ∈ (serialOf data).accept := by
  show i.val ∈ serialAccept data
  rw [serialAccept, List.mem_filterMap]
  exact ⟨i, List.mem_finRange i, by simp [h]⟩

/-! ### Recovery infrastructure -/

/-- Look up the transition for `(state s, symbol b)` in a rule list — the first match's payload. -/
def lookupRule : List Rule → ℕ → Bool → Option (ℕ × Option Bool × ℕ)
  | [], _, _ => none
  | r :: rs, s, b =>
      if r.1 = s ∧ r.2.1 = b then some (r.2.2.1, r.2.2.2.1, r.2.2.2.2)
      else lookupRule rs s b

/-- **A matching head returns its payload (proved).** -/
theorem lookupRule_cons_match (r : Rule) (rs : List Rule) (s : ℕ) (b : Bool)
    (h : r.1 = s ∧ r.2.1 = b) :
    lookupRule (r :: rs) s b = some (r.2.2.1, r.2.2.2.1, r.2.2.2.2) := by
  simp only [lookupRule, if_pos h]

/-- **A non-matching prefix is skipped (proved).**  If no rule in `rs1` matches `(s, b)`, lookup on
`rs1 ++ rs2` is lookup on `rs2` — the mechanism that walks to the first real match. -/
theorem lookupRule_append_no_match (rs1 rs2 : List Rule) (s : ℕ) (b : Bool)
    (h : ∀ r ∈ rs1, ¬ (r.1 = s ∧ r.2.1 = b)) :
    lookupRule (rs1 ++ rs2) s b = lookupRule rs2 s b := by
  induction rs1 with
  | nil => rfl
  | cons r rs ih =>
    have hr : r ∈ r :: rs := by simp
    have hne : ¬ (r.1 = s ∧ r.2.1 = b) := h r hr
    simp only [List.cons_append, lookupRule]
    rw [if_neg hne]
    exact ih (fun r' hr' => h r' (List.mem_cons_of_mem r hr'))

/-! ### Round-trip through the tape -/

/-- **The flattened machine survives the Bool-tape trip (proved).**  Applying brick 1's round-trip:
`decodeMachine (encodeMachine (serialOf data)) = some (serialOf data, [])`. -/
theorem serialOf_roundtrips (data : FinMachineData k) :
    decodeMachine (encodeMachine (serialOf data)) = some (serialOf data, []) :=
  decodeMachine_encodeMachine_nil (serialOf data)

end PallLean.Paper93.DeepMath.PathB.UniversalMachineBridge

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineBridge.rule_mem
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineBridge.lookupRule_append_no_match
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineBridge.serialOf_roundtrips
