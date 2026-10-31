import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM

/-!
# The tape layout — a faithful binary encoding of `(machine code, simulated config)`

The physical universal machine `U` lays a simulated machine `M`'s configuration, together with `M`'s code, onto its own
binary tape.  This file defines that **tape layout** — a serialisation `encodeTape : ℕ → CConfig → List Bool` of the
code and the simulated configuration into a binary string — and proves it **faithful**: it round-trips through a
decoder, hence is injective.  Faithfulness is the property the single-step simulation rests on (so the encoded tape
determines the simulated configuration uniquely).

The serialisation routes through `Encodable`: `(code, c)` is encoded to a natural number and that number is written in
binary via a bijection `List Bool ≃ ℕ` (the tape is the binary string).  Decoding inverts both.

## What is proved (clean axioms, no `sorry`)

* **`bitEquiv : List Bool ≃ ℕ`** — the binary-string ↔ number bijection (the tape numbering).
* **`encodeTape` / `decodeTape`** — the layout and its decoder.
* **`decodeTape_encodeTape`** — the round-trip: `decodeTape (encodeTape code c) = some (code, c)`.  Faithfulness.
* **`encodeTape_injective`** — hence the layout is injective in `(code, c)`.

## Honest scope

This is the *encoding the physical universal machine operates on*, with faithfulness proved — genuine infrastructure
for `hstep` (`…ACC0SimulationStep`).  It does **not** build the physical machine that reads/rewrites this layout in
one simulated step: locating the simulated head and applying `M`'s rule *as `U`-transitions over this layout* is the
remaining deep socket.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TapeEncoding

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (CConfig)

/-- The binary-string ↔ number bijection: a tape (`List Bool`) names a natural number. -/
noncomputable def bitEquiv : List Bool ≃ ℕ :=
  haveI : Denumerable (List Bool) := Denumerable.ofEncodableOfInfinite (List Bool)
  Denumerable.eqv (List Bool)

/-- **The tape layout**: serialise `(code, simulated config)` to a binary tape — encode the pair to a number, write it
in binary. -/
noncomputable def encodeTape (code : ℕ) (c : CConfig) : List Bool :=
  bitEquiv.symm (Encodable.encode (code, c))

/-- **The decoder**: read the binary tape as a number and decode it back to `(code, config)`. -/
noncomputable def decodeTape (bs : List Bool) : Option (ℕ × CConfig) :=
  Encodable.decode (bitEquiv bs)

/-- **The tape layout is faithful (proved): `decodeTape (encodeTape code c) = some (code, c)`.**  Decoding recovers
the code and the simulated configuration exactly — so the encoded tape determines the simulated state uniquely. -/
theorem decodeTape_encodeTape (code : ℕ) (c : CConfig) :
    decodeTape (encodeTape code c) = some (code, c) := by
  unfold decodeTape encodeTape
  rw [Equiv.apply_symm_apply]
  exact Encodable.encodek (code, c)

/-- **The tape layout is injective (proved).**  Same tape ⇒ same code and same simulated configuration. -/
theorem encodeTape_inj {code code' : ℕ} {c c' : CConfig}
    (h : encodeTape code c = encodeTape code' c') : code = code' ∧ c = c' := by
  have key : some (code, c) = some (code', c') := by
    rw [← decodeTape_encodeTape code c, ← decodeTape_encodeTape code' c', h]
  have hpair := Option.some_inj.mp key
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

end PallLean.Paper93.DeepMath.PathB.ACC0TapeEncoding

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TapeEncoding.decodeTape_encodeTape
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TapeEncoding.encodeTape_inj
