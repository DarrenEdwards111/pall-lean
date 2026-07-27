import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineSerial

/-!
# Universal machine, brick 3.5: configuration on the tape, round-trip proved

Brick 1 put a machine DESCRIPTION on the Bool tape; bricks 3/4 proved the step/run simulation
correct at the semantic level.  A real `ComposableMachine` universal machine holds, on its own tape,
the machine description AND the simulated CONFIGURATION `(state, head, tape)`.  This file gives the
configuration codec — `encodeConf`/`decodeConf` with a machine-checked round-trip — so the step loop
(the remaining tape-implementation) has a config it can read and write.

## What is proved

* **`encodeConf`** — a configuration `(s, hd, tp)` serialised as `encNat s ++ encNat hd ++
  encList encBool tp` (state, head, then the tape as a length-prefixed bit list).
* **`decodeConf_encodeConf`** (proved) — the round trip: `decodeConf (encodeConf c ++ rest) =
  some (c, rest)`, and the clean `decodeConf (encodeConf c) = some (c, [])`.  A configuration
  survives the trip onto and off the tape intact.

## Honest scope

With brick 1 (machine on tape) and this (configuration on tape), the universal machine's entire tape
content — description `++` configuration — is a verified, decodable `List Bool`.  What remains
(unchanged): the `ComposableMachine` that, in bounded steps, decodes the current config, applies one
`uStep` (bricks 3/4, using `lookupRule`), and re-encodes it — the tape-layout loop — plus the binary
refinement (brick 1 is unary) for the polynomial clock, and the lazy-delay diagonal (brick 5).  No
claim here beyond a verified configuration codec.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineConfig

open PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial

/-- A universal-machine configuration: `(state, head, tape)`. -/
abbrev Conf : Type := ℕ × ℕ × List Bool

/-- Serialise a configuration onto the Bool tape. -/
def encodeConf (c : Conf) : List Bool :=
  encNat c.1 ++ encNat c.2.1 ++ encList encBool c.2.2

/-- Decode a configuration from the tape. -/
def decodeConf (l : List Bool) : Option (Conf × List Bool) :=
  match decNat l with
  | none => none
  | some (s, l1) =>
    match decNat l1 with
    | none => none
    | some (hd, l2) =>
      match decList decBool l2 with
      | none => none
      | some (tp, l3) => some ((s, hd, tp), l3)

/-- **The configuration round-trip (proved).**  A configuration survives the trip onto and off the
Bool tape: `decodeConf (encodeConf c ++ rest) = some (c, rest)`. -/
theorem decodeConf_encodeConf (c : Conf) (rest : List Bool) :
    decodeConf (encodeConf c ++ rest) = some (c, rest) := by
  obtain ⟨s, hd, tp⟩ := c
  simp only [encodeConf, decodeConf, List.append_assoc, decNat_encNat,
    decList_encList encBool decBool decBool_encBool]

/-- The clean form: decoding the exact encoding recovers the configuration with empty remainder. -/
theorem decodeConf_encodeConf_nil (c : Conf) :
    decodeConf (encodeConf c) = some (c, []) := by
  have h := decodeConf_encodeConf c []
  rwa [List.append_nil] at h

end PallLean.Paper93.DeepMath.PathB.UniversalMachineConfig

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineConfig.decodeConf_encodeConf
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineConfig.decodeConf_encodeConf_nil
