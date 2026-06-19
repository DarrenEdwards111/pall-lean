import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMLoop

/-!
# Entry 338 — universal-TM-table build, brick 5: the scannable encoding layer (proved)

Bricks 1–4 closed the simulation engine at the config/rule level.  The remaining work is the bridge from that engine to
a **bit-level concrete `TMachine` over a scannable tape format**.  Brick 2 (entry 335) gave an *opaque* `Encodable`
encoding — fine for recoverability, useless for a tape scanner.  This file replaces it with a **concrete, scannable
bit-grammar**: every value is written as an explicit list of bits a left-to-right scanner can consume, with a verified
*round-trip that leaves the rest of the tape intact* (the cursor lemma a scanner needs).

**The (intentionally dumb) format.**  A nat `n` is `n` `true`s followed by a `false` separator (`encodeNatBits`); a
transition is its five fields (`state, sym, state, sym, move`) concatenated; a machine is its length followed by its
transitions.  Efficiency is irrelevant; *scanability* and *correctness* are the point — each `decode (encode x ++ rest)
= some (x, rest)` says the scanner consumes exactly the encoding of `x` and stops, leaving `rest`.

## What is proved (clean axioms, no `sorry`)

* **`encodeNatBits` / `decodeNatBits`** + **`decodeNatBits_encodeNatBits`** — `decodeNatBits (encodeNatBits n ++ rest) =
  (n, rest)`: scan one nat, leave the rest.
* **`encodeTransBits` / `decodeTransBits`** + **`decodeTransBits_encodeTransBits`** — `decodeTransBits (encodeTransBits t
  ++ rest) = some (t, rest)`: scan one transition, leave the rest.
* **`encodeMachineBits` / `decodeMachineBits`** + **`decodeMachineBits_encodeMachineBits`** — `decodeMachineBits
  (encodeMachineBits M ++ rest) = some (M, rest)`: scan a whole transition table, leave the rest.

## Honest scope

This builds the **concrete scannable encoding** with verified scan-and-leave-rest round-trips at every level (nat,
transition, machine) — the cursor/traversal correctness a bit-level scanner stands on.  It does **not** yet build the
scanner as a `TMachine`: the next bricks implement `lookup` (rule scan-and-match) and `applyTrans` over this format as
concrete machine fragments (339–340), then assemble `U` and prove `Realizes physU U φ cost` (341).  Those remain the
construction, built as verified bricks, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMTrans Move)

/-- **Encode a nat** as `n` `true`s then a `false` separator. -/
def encodeNatBits (n : ℕ) : List Bool := List.replicate n true ++ [false]

theorem encodeNatBits_succ (n : ℕ) : encodeNatBits (n + 1) = true :: encodeNatBits n := by
  simp [encodeNatBits, List.replicate_succ]

/-- **Decode a nat**: count leading `true`s, consume the `false` separator, return `(count, rest)`. -/
def decodeNatBits : List Bool → ℕ × List Bool
  | [] => (0, [])
  | false :: rest => (0, rest)
  | true :: rest => Prod.map (· + 1) id (decodeNatBits rest)

/-- **Nat round-trip (PROVED).**  `decodeNatBits (encodeNatBits n ++ rest) = (n, rest)` — scan one nat, leave `rest`. -/
theorem decodeNatBits_encodeNatBits (n : ℕ) (rest : List Bool) :
    decodeNatBits (encodeNatBits n ++ rest) = (n, rest) := by
  induction n with
  | zero => simp [encodeNatBits, decodeNatBits]
  | succ n ih =>
      rw [encodeNatBits_succ, List.cons_append]
      simp only [decodeNatBits, ih, Prod.map, id_eq]

/-- **Encode a transition** `((rs, rsym), (ws, wsym, mv))` as `rs`-bits, `rsym`, `ws`-bits, `wsym`, `mv`-bits. -/
def encodeTransBits (t : TMTrans) : List Bool :=
  encodeNatBits t.1.1 ++ t.1.2 :: (encodeNatBits t.2.1 ++ t.2.2.1 :: encodeNatBits t.2.2.2.val)

/-- **Decode a transition** by scanning the five fields in order; `none` if a symbol bit is missing or the move is out
of range. -/
def decodeTransBits (l : List Bool) : Option (TMTrans × List Bool) :=
  let r1 := decodeNatBits l
  match r1.2 with
  | [] => none
  | rsym :: l2 =>
      let r2 := decodeNatBits l2
      match r2.2 with
      | [] => none
      | wsym :: l4 =>
          let r3 := decodeNatBits l4
          if h : r3.1 < 3 then some (((r1.1, rsym), (r2.1, wsym, ⟨r3.1, h⟩)), r3.2) else none

/-- **Transition round-trip (PROVED).**  `decodeTransBits (encodeTransBits t ++ rest) = some (t, rest)` — scan one
transition, leave `rest`. -/
theorem decodeTransBits_encodeTransBits (t : TMTrans) (rest : List Bool) :
    decodeTransBits (encodeTransBits t ++ rest) = some (t, rest) := by
  simp only [encodeTransBits, decodeTransBits, List.append_assoc, List.cons_append,
    decodeNatBits_encodeNatBits]
  simp only [t.2.2.2.isLt, dif_pos]

/-- **Encode a machine**: its length, then its transitions concatenated. -/
def encodeMachineBits (M : List TMTrans) : List Bool :=
  encodeNatBits M.length ++ M.flatMap encodeTransBits

/-- **Decode `k` transitions** in sequence. -/
def decodeTransListBits : ℕ → List Bool → Option (List TMTrans × List Bool)
  | 0, l => some ([], l)
  | k + 1, l =>
      match decodeTransBits l with
      | none => none
      | some (t, l') =>
          match decodeTransListBits k l' with
          | none => none
          | some (ts, l'') => some (t :: ts, l'')

/-- **Decode a machine**: read the length, then that many transitions. -/
def decodeMachineBits (l : List Bool) : Option (List TMTrans × List Bool) :=
  let r := decodeNatBits l
  decodeTransListBits r.1 r.2

theorem decodeTransListBits_roundtrip (M : List TMTrans) (rest : List Bool) :
    decodeTransListBits M.length (M.flatMap encodeTransBits ++ rest) = some (M, rest) := by
  induction M generalizing rest with
  | nil => simp [decodeTransListBits]
  | cons t ts ih =>
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeTransListBits,
        decodeTransBits_encodeTransBits, ih]

/-- **Machine round-trip (PROVED).**  `decodeMachineBits (encodeMachineBits M ++ rest) = some (M, rest)` — scan a whole
transition table, leave `rest`. -/
theorem decodeMachineBits_encodeMachineBits (M : List TMTrans) (rest : List Bool) :
    decodeMachineBits (encodeMachineBits M ++ rest) = some (M, rest) := by
  simp only [encodeMachineBits, decodeMachineBits, List.append_assoc, decodeNatBits_encodeNatBits]
  exact decodeTransListBits_roundtrip M rest

/-!
**Brick 5, built.**  A concrete scannable bit-grammar — nat, transition, machine — each with a verified round-trip
`decode (encode x ++ rest) = some (x, rest)`: the scanner consumes exactly `x`'s encoding and leaves the rest, the
cursor/traversal correctness for a bit-level reader.  Next: implement `lookup` (rule scan-and-match, brick 339) and
`applyTrans` (brick 340) over this format as concrete machine fragments, then assemble `U` and prove
`Realizes physU U φ cost` (brick 341) — built as verified bricks, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable.decodeNatBits_encodeNatBits
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable.decodeTransBits_encodeTransBits
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable.decodeMachineBits_encodeMachineBits
