import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMBuild

/-!
# Entry 335 — universal-TM-table build, brick 2: the tape encoding of `(machine, input)` (proved)

Brick 1 (entry 334) showed the `Realizes` interface inhabited and verified the tape-traversal scanner.  Brick 2 builds
the **data representation** the universal machine reads off its tape: an injective, round-trip-decodable encoding of a
pair `(machine code, input)` as a tape (`List Bool`).

**The encoding.**  `(TMachine × List Bool)` is `Encodable` (every component — `ℕ`, `Bool`, `Fin 3`, products, lists — is),
and `List Bool` is denumerable (`List Bool ≃ ℕ`).  Composing: `encodeTape M x := tapeEquiv.symm (encode (M, x))` writes
the pair as a tape, and `decodeTape t := decode (tapeEquiv t)` reads it back.  The round-trip
`decodeTape (encodeTape M x) = some (M, x)` is the verified guarantee that the universal machine can recover the machine
to simulate and its input from the tape.

## What is proved (clean axioms, no `sorry`)

* **`tapeEquiv`** — `List Bool ≃ ℕ` (the denumerable structure of bit-tapes).
* **`encodeTape` / `decodeTape`** — write a `(machine, input)` pair to a tape / read it back.
* **`decodeTape_encodeTape`** (PROVED) — `decodeTape (encodeTape M x) = some (M, x)`: the round-trip, so the encoded
  machine and input are exactly recoverable.
* **`encodeTape_injective`** (PROVED) — distinct `(machine, input)` pairs get distinct tapes.

## Honest scope

This is **brick 2**: a verified injective, round-trip-decodable tape encoding of `(machine, input)` — the data
foundation for the universal machine.  It establishes that the pair is *recoverable* from the tape (`decodeTape_encodeTape`).
It does **not** yet give a *bit-by-bit scannable* format with a TM-level lookup procedure: that is brick 3 (the
rule-lookup scan, walking the encoded table to match the current `(state, symbol)`), followed by the apply-step, the
simulation loop, accept detection, and assembling `U` with `Realizes physU U φ cost`.  Those remain the substantial
construction, built as verified bricks, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEncoding

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine)

/-- **Bit-tapes are denumerable.**  `List Bool` is `Encodable` and infinite, hence `Denumerable`. -/
noncomputable instance : Denumerable (List Bool) := Denumerable.ofEncodableOfInfinite _

/-- **The bit-tape ↔ `ℕ` equivalence.** -/
noncomputable def tapeEquiv : List Bool ≃ ℕ := Denumerable.eqv (List Bool)

/-- **Encode a `(machine, input)` pair onto a tape.**  `Encodable.encode` the pair to a `ℕ`, then realise that `ℕ` as a
bit-tape. -/
noncomputable def encodeTape (M : TMachine) (x : List Bool) : List Bool :=
  tapeEquiv.symm (Encodable.encode (M, x))

/-- **Decode a tape back to a `(machine, input)` pair.** -/
noncomputable def decodeTape (t : List Bool) : Option (TMachine × List Bool) :=
  Encodable.decode (tapeEquiv t)

/-- **The encoding round-trips (PROVED).**  `decodeTape (encodeTape M x) = some (M, x)`: the universal machine recovers
exactly the machine to simulate and its input from the encoded tape. -/
theorem decodeTape_encodeTape (M : TMachine) (x : List Bool) :
    decodeTape (encodeTape M x) = some (M, x) := by
  unfold decodeTape encodeTape
  rw [Equiv.apply_symm_apply]
  exact Encodable.encodek (M, x)

/-- **The encoding is injective (PROVED).**  Distinct `(machine, input)` pairs get distinct tapes — follows from the
round-trip. -/
theorem encodeTape_injective {M₁ M₂ : TMachine} {x₁ x₂ : List Bool}
    (h : encodeTape M₁ x₁ = encodeTape M₂ x₂) : M₁ = M₂ ∧ x₁ = x₂ := by
  have : decodeTape (encodeTape M₁ x₁) = decodeTape (encodeTape M₂ x₂) := by rw [h]
  rw [decodeTape_encodeTape, decodeTape_encodeTape] at this
  exact Prod.mk.injEq _ _ _ _ |>.mp (Option.some.injEq _ _ |>.mp this)

/-!
**Brick 2, built.**  `encodeTape`/`decodeTape` give an injective, round-trip-decodable tape representation of
`(machine, input)` (`decodeTape_encodeTape`, `encodeTape_injective`) — the universal machine's input format, with the
machine-to-simulate and its input provably recoverable from the tape.  Next bricks: the bit-level scannable layout with
the rule-lookup scan (brick 3, using the traversal of brick 1), the apply-step, the simulation loop, accept detection,
and `Realizes physU U φ cost` — built as verified components, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEncoding

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEncoding.decodeTape_encodeTape
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEncoding.encodeTape_injective
