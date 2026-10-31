import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteTradingClasses

/-!
# Base camp of the mountains: the `encPair` decode layer

Every machine construction in the padding, speedup, and slowdown mountains manipulates the
self-delimiting pairing `encPair` — verifiers must recover `(x, w)` from `encPair x w`,
pad-strippers must find the boundary, simulators must address into the components.  Before any
of those machines can be BUILT, the encoding must be PROVED faithful.  This file closes that
foundation completely: an explicit decoder with round-trip identities, injectivity in both
arguments, and the length arithmetic the clock bookkeeping will consume.

## What is proved (all of it — this layer has no open ends)

* **`decodePair`** — the parser: tagged bits (`true :: b`) accumulate into the first component;
  the `false` separator ends it; the tail is the second component.
* **`decodePair_encPair`** — the round trip: `decodePair (encPair x w) = some (x, w)`.
* **`encPair_injective`** — full injectivity in the pair, with the component corollaries
  `encPair_left_injective` / `encPair_right_injective`.
* **`encPair_length`** — `|encPair x w| = 2·|x| + 1 + |w|`, with the bounds
  (`length_le_encPair_length`, `encPair_length_le`) the clock estimates will use.

Nothing here is a mountain summit — it is the camp all three lower mountains share.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EncPairDecode

open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses

/-- The decoder: parse tagged bits until the separator, return the components. -/
def decodePair : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest =>
      match decodePair rest with
      | some (x, w) => some (b :: x, w)
      | none => none
  | _ => none

/-- `encPair` unfolds one input bit at a time. -/
theorem encPair_cons (b : Bool) (x w : List Bool) :
    encPair (b :: x) w = true :: b :: encPair x w := by
  simp [encPair]

/-- `encPair` on the empty input is the separator then the witness. -/
theorem encPair_nil (w : List Bool) : encPair [] w = false :: w := by
  simp [encPair]

/-- **The round trip (proved).**  The decoder inverts the encoder exactly. -/
theorem decodePair_encPair (x w : List Bool) :
    decodePair (encPair x w) = some (x, w) := by
  induction x with
  | nil => rw [encPair_nil]; rfl
  | cons b x ih =>
    rw [encPair_cons]
    show (match decodePair (encPair x w) with
      | some (x', w') => some (b :: x', w')
      | none => none) = some (b :: x, w)
    rw [ih]

/-- **Injectivity in the pair (proved).** -/
theorem encPair_injective {x w x' w' : List Bool}
    (h : encPair x w = encPair x' w') : x = x' ∧ w = w' := by
  have h2 : decodePair (encPair x w) = decodePair (encPair x' w') := by rw [h]
  rw [decodePair_encPair, decodePair_encPair] at h2
  have h3 : (x, w) = (x', w') := Option.some.inj h2
  exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

/-- Injectivity in the input component. -/
theorem encPair_left_injective {x x' w : List Bool}
    (h : encPair x w = encPair x' w) : x = x' :=
  (encPair_injective h).1

/-- Injectivity in the witness component. -/
theorem encPair_right_injective {x w w' : List Bool}
    (h : encPair x w = encPair x w') : w = w' :=
  (encPair_injective h).2

/-- **The length identity (proved).**  `|encPair x w| = 2·|x| + 1 + |w|`. -/
theorem encPair_length (x w : List Bool) :
    (encPair x w).length = 2 * x.length + 1 + w.length := by
  induction x with
  | nil =>
    rw [encPair_nil]
    simp only [List.length_cons, List.length_nil]
    omega
  | cons b x ih =>
    rw [encPair_cons]
    simp only [List.length_cons, ih]
    omega

/-- The pairing never shrinks below its components: input side. -/
theorem length_le_encPair_length (x w : List Bool) :
    x.length ≤ (encPair x w).length := by
  rw [encPair_length]; omega

/-- The pairing never shrinks below its components: witness side. -/
theorem witness_length_le_encPair_length (x w : List Bool) :
    w.length ≤ (encPair x w).length := by
  rw [encPair_length]; omega

/-- The clock-facing upper bound: the pairing is linear in its components. -/
theorem encPair_length_le (x w : List Bool) :
    (encPair x w).length ≤ 2 * (x.length + w.length) + 1 := by
  rw [encPair_length]; omega

end PallLean.Paper93.DeepMath.PathB.EncPairDecode

#print axioms PallLean.Paper93.DeepMath.PathB.EncPairDecode.decodePair_encPair
#print axioms PallLean.Paper93.DeepMath.PathB.EncPairDecode.encPair_injective
#print axioms PallLean.Paper93.DeepMath.PathB.EncPairDecode.encPair_length
